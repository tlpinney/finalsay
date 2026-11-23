import FinalSay.Authority

/-!
# Approver authority and attenuation along a delegation chain

Invariant 6 (`FinalSay.Authority`) checks that an approval is exact and
current, but not that the person who gave it could. "A human with authority"
means: someone who holds authority over this effect, either as the root
(the resource owner) or through a chain of delegations from the root.

* A `Scope` says which actions, which resources, up to what amount, and until
  when.
* A `Link` delegates a scope from an issuer to a holder. A link can only be
  issued by the root, within the root scope, or by the live holder of an
  existing link, within that link's scope. So authority only narrows.
* Revoking a link also kills every link delegated beneath it.
* `commitDecideAuth` counts an approval only if it is exact and current
  *and* its approver holds authority over the exact effect right now.

Proved, for every sequence of delegations and revocations:
* `links_within_root` / `no_amplification`: nobody can hold authority the root
  did not have.
* `links_attenuated`: every delegated link is within the scope of the link it
  was issued from, and was issued by that link's holder.
* `revocation_cascades`: after revoking a link, it and everything below it stay
  dead.
* `irreversible_commit_authorized`: an irreversible commit has an approval that
  is exact, current, and given by someone who holds authority over that effect,
  within the root's scope.
* `unauthorized_approver_refused`: a concrete case where an approval from someone
  without authority would pass invariant 6 alone and is refused here.

Related work: capability attenuation along delegation chains (Tallam, arXiv
2606.12320, Def. 4); monotone lineage cuts (Zhu & Wang, arXiv 2610.00347).
-/

namespace FinalSay

/-- What a delegation covers. -/
structure Scope where
  actions   : List String
  resources : List String
  maxAmount : Nat
  /-- Valid while `now < expires`. -/
  expires   : Nat
  deriving Repr

def Scope.covers (sc : Scope) (t : Target) (now : Nat) : Bool :=
  sc.actions.contains t.action && sc.resources.contains t.resource &&
    decide (t.amount ≤ sc.maxAmount) && decide (now < sc.expires)

/-- `a` is within `b`: no new actions or resources, no higher limit, no later expiry. -/
def Scope.within (a b : Scope) : Bool :=
  a.actions.all (b.actions.contains ·) && a.resources.all (b.resources.contains ·) &&
    decide (a.maxAmount ≤ b.maxAmount) && decide (a.expires ≤ b.expires)

theorem Scope.within_iff (a b : Scope) : a.within b = true ↔
    (∀ x ∈ a.actions, x ∈ b.actions) ∧ (∀ x ∈ a.resources, x ∈ b.resources) ∧
      a.maxAmount ≤ b.maxAmount ∧ a.expires ≤ b.expires := by
  simp [Scope.within, List.all_eq_true, and_assoc]

theorem Scope.covers_iff (sc : Scope) (t : Target) (now : Nat) : sc.covers t now = true ↔
    t.action ∈ sc.actions ∧ t.resource ∈ sc.resources ∧ t.amount ≤ sc.maxAmount ∧
      now < sc.expires := by
  simp [Scope.covers, and_assoc]

theorem Scope.within_trans {a b c : Scope} (h₁ : a.within b = true) (h₂ : b.within c = true) :
    a.within c = true := by
  rw [Scope.within_iff] at *
  obtain ⟨a1, a2, a3, a4⟩ := h₁
  obtain ⟨b1, b2, b3, b4⟩ := h₂
  exact ⟨fun x hx => b1 x (a1 x hx), fun x hx => b2 x (a2 x hx), by omega, by omega⟩

/-- A narrower scope covers less. -/
theorem Scope.covers_mono {a b : Scope} {t : Target} {now : Nat} (hw : a.within b = true)
    (hc : a.covers t now = true) : b.covers t now = true := by
  rw [Scope.within_iff] at hw
  rw [Scope.covers_iff] at *
  obtain ⟨w1, w2, w3, w4⟩ := hw
  obtain ⟨c1, c2, c3, c4⟩ := hc
  exact ⟨w1 _ c1, w2 _ c2, by omega, by omega⟩

/-- A delegation of `scope` from `issuer` to `holder`. -/
structure Link where
  id        : Nat
  issuer    : String
  holder    : String
  scope     : Scope
  /-- Ids of the links this one was delegated beneath, root-most first. -/
  ancestors : List Nat
  deriving Repr

/-- Who holds authority, and how. -/
structure Org where
  root      : String
  rootScope : Scope
  links     : List Link := []
  revoked   : List Nat := []
  deriving Repr

/-- A link is live if neither it nor anything above it has been revoked. -/
def Org.live (o : Org) (l : Link) : Bool :=
  !(o.revoked.contains l.id) && l.ancestors.all (fun a => !(o.revoked.contains a))

/-- Does `who` hold authority over target `t` at time `now`? -/
def Org.holds (o : Org) (who : String) (t : Target) (now : Nat) : Bool :=
  (who == o.root && o.rootScope.covers t now) ||
    o.links.any (fun l => o.live l && l.holder == who && l.scope.covers t now)

inductive DOp where
  /-- `issuer` delegates `scope` to `holder`, from the root (`via = none`) or
  from a link `issuer` holds. -/
  | delegate (id : Nat) (issuer holder : String) (scope : Scope) (via : Option Nat)
  | revoke (id : Nat)

def Org.step (o : Org) : DOp → Org
  | .delegate id iss hol sc none =>
    if iss == o.root && sc.within o.rootScope then
      { o with links := o.links ++ [⟨id, iss, hol, sc, []⟩] }
    else o
  | .delegate id iss hol sc (some pid) =>
    match o.links.find? (fun l => l.id == pid) with
    | some p =>
      if o.live p && p.holder == iss && sc.within p.scope then
        { o with links := o.links ++ [⟨id, iss, hol, sc, p.ancestors ++ [p.id]⟩] }
      else o
    | none => o
  | .revoke id => { o with revoked := id :: o.revoked }

def Org.run (o : Org) (ops : List DOp) : Org := ops.foldl Org.step o

theorem Org.run_cons (o : Org) (op : DOp) (ops : List DOp) :
    o.run (op :: ops) = (o.step op).run ops := rfl

theorem Org.step_root (o : Org) (op : DOp) :
    (o.step op).root = o.root ∧ (o.step op).rootScope = o.rootScope := by
  cases op with
  | delegate id iss hol sc via =>
    cases via with
    | none => simp only [Org.step]; split <;> simp
    | some pid =>
      simp only [Org.step]; split
      · split <;> simp
      · simp
  | revoke id => simp [Org.step]

/-- Links are only ever added. -/
theorem Org.step_links (o : Org) (op : DOp) :
    ∃ new, (o.step op).links = o.links ++ new := by
  cases op with
  | delegate id iss hol sc via =>
    cases via with
    | none =>
      simp only [Org.step]; split
      · exact ⟨_, rfl⟩
      · exact ⟨[], by simp⟩
    | some pid =>
      simp only [Org.step]; split
      · split
        · exact ⟨_, rfl⟩
        · exact ⟨[], by simp⟩
      · exact ⟨[], by simp⟩
  | revoke id => exact ⟨[], by simp [Org.step]⟩

/-! ### No amplification -/

def Org.WithinRoot (o : Org) : Prop := ∀ l ∈ o.links, l.scope.within o.rootScope = true

theorem Org.step_withinRoot (o : Org) (op : DOp) (h : o.WithinRoot) : (o.step op).WithinRoot := by
  intro l hl
  rw [(o.step_root op).2]
  cases op with
  | delegate id iss hol sc via =>
    cases via with
    | none =>
      simp only [Org.step] at hl; split at hl
      · next hc =>
        simp only [Bool.and_eq_true] at hc
        rw [List.mem_append] at hl
        rcases hl with hl | hl
        · exact h l hl
        · simp at hl; subst hl; exact hc.2
      · exact h l hl
    | some pid =>
      simp only [Org.step] at hl; split at hl
      · next p hp =>
        split at hl
        · next hc =>
          simp only [Bool.and_eq_true] at hc
          rw [List.mem_append] at hl
          rcases hl with hl | hl
          · exact h l hl
          · simp at hl; subst hl
            exact Scope.within_trans hc.2 (h p (List.mem_of_find?_eq_some hp))
        · exact h l hl
      · exact h l hl
  | revoke id => exact h l (by simpa [Org.step] using hl)

theorem Org.run_withinRoot (ops : List DOp) : ∀ (o : Org), o.WithinRoot → (o.run ops).WithinRoot := by
  induction ops with
  | nil => intro o h; exact h
  | cons op ops ih => intro o h; exact ih _ (o.step_withinRoot op h)

theorem Org.run_root (ops : List DOp) : ∀ (o : Org),
    (o.run ops).root = o.root ∧ (o.run ops).rootScope = o.rootScope := by
  induction ops with
  | nil => intro o; exact ⟨rfl, rfl⟩
  | cons op ops ih =>
    intro o
    rw [Org.run_cons, (ih _).1, (ih _).2, (o.step_root op).1, (o.step_root op).2]
    exact ⟨rfl, rfl⟩

/-- **Every delegated link stays within the root's scope**, for any sequence of
delegations and revocations from an organisation with no links yet. -/
theorem links_within_root (root : String) (sc : Scope) (ops : List DOp) :
    ∀ l ∈ (Org.run { root, rootScope := sc } ops).links, l.scope.within sc = true := by
  intro l hl
  have h := Org.run_withinRoot ops { root, rootScope := sc } (by simp [Org.WithinRoot]) l hl
  rwa [(Org.run_root ops _).2] at h

theorem holds_within_root (o : Org) (h : o.WithinRoot) (who : String) (t : Target) (now : Nat)
    (hh : o.holds who t now = true) : o.rootScope.covers t now = true := by
  simp only [Org.holds, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at hh
  rcases hh with ⟨_, hc⟩ | ⟨l, hl, ⟨_, _⟩, hc⟩
  · exact hc
  · exact Scope.covers_mono (h l hl) hc

/-- **No amplification:** whoever holds authority over an effect, the root held
authority over it too. Delegation can only narrow. -/
theorem no_amplification (root : String) (sc : Scope) (ops : List DOp)
    (who : String) (t : Target) (now : Nat)
    (hh : (Org.run { root, rootScope := sc } ops).holds who t now = true) :
    sc.covers t now = true := by
  have hw := Org.run_withinRoot ops { root, rootScope := sc } (by simp [Org.WithinRoot])
  have := holds_within_root _ hw who t now hh
  rwa [(Org.run_root ops _).2] at this

/-! ### Attenuation link by link -/

/-- Why link `l` is legitimate in `o`: issued by the root within the root scope,
or by the holder of its parent link within the parent's scope. -/
def Org.Just (o : Org) (l : Link) : Prop :=
  match l.ancestors.getLast? with
  | none => l.issuer = o.root ∧ l.scope.within o.rootScope = true
  | some pid => ∃ p ∈ o.links, p.id = pid ∧ p.holder = l.issuer ∧ l.scope.within p.scope = true

def Org.Attenuated (o : Org) : Prop := ∀ l ∈ o.links, o.Just l

/-- Justifications survive appending links. -/
theorem Org.just_mono {o o' : Org} (hr : o'.root = o.root) (hs : o'.rootScope = o.rootScope)
    (new : List Link) (hl : o'.links = o.links ++ new) (l : Link) (h : o.Just l) : o'.Just l := by
  unfold Org.Just at *
  split at h
  · exact ⟨hr ▸ h.1, hs ▸ h.2⟩
  · obtain ⟨p, hp, h1, h2, h3⟩ := h
    exact ⟨p, hl ▸ List.mem_append_left _ hp, h1, h2, h3⟩

theorem Org.step_attenuated (o : Org) (op : DOp) (h : o.Attenuated) : (o.step op).Attenuated := by
  cases op with
  | delegate id iss hol sc via =>
    cases via with
    | none =>
      simp only [Org.step]; split
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        intro l hl
        rw [List.mem_append] at hl
        rcases hl with hl | hl
        · exact Org.just_mono (o := o) (by rfl) (by rfl) _ (by rfl) l (h l hl)
        · simp at hl; subst hl
          simp [Org.Just, hc]
      · exact h
    | some pid =>
      simp only [Org.step]; split
      · next p hp =>
        split
        · next hc =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          intro l hl
          rw [List.mem_append] at hl
          rcases hl with hl | hl
          · exact Org.just_mono (o := o) (by rfl) (by rfl) _ (by rfl) l (h l hl)
          · simp at hl; subst hl
            simp only [Org.Just, List.getLast?_append, List.getLast?_singleton, Option.some_or]
            exact ⟨p, List.mem_append_left _ (List.mem_of_find?_eq_some hp), rfl, hc.1.2, hc.2⟩
        · exact h
      · exact h
  | revoke id =>
    intro l hl
    exact Org.just_mono (o := o) rfl rfl [] (by simp) l (h l (by simpa [Org.step] using hl))

/-- **Attenuation:** in any run from an organisation with no links, every link was
issued by the root within the root scope, or by the holder of its parent link
within the parent's scope. -/
theorem links_attenuated (root : String) (sc : Scope) (ops : List DOp) :
    (Org.run { root, rootScope := sc } ops).Attenuated := by
  suffices ∀ o : Org, o.Attenuated → (o.run ops).Attenuated from
    this _ (by simp [Org.Attenuated])
  induction ops with
  | nil => intro o h; exact h
  | cons op ops ih => intro o h; exact ih _ (o.step_attenuated op h)

/-! ### Revocation cascades -/

theorem Org.step_revoked_mono (o : Org) (op : DOp) (id : Nat) (h : id ∈ o.revoked) :
    id ∈ (o.step op).revoked := by
  cases op with
  | delegate _ _ _ _ via =>
    cases via with
    | none => simp only [Org.step]; split <;> simpa using h
    | some pid =>
      simp only [Org.step]; split
      · split <;> simpa using h
      · simpa using h
  | revoke i => simp [Org.step, h]

theorem dead_if_revoked (o : Org) (l : Link) (id : Nat) (h : id ∈ o.revoked)
    (hl : l.id = id ∨ id ∈ l.ancestors) : o.live l = false := by
  simp only [Org.live, Bool.and_eq_false_iff, List.contains_eq_mem,
    decide_eq_true_eq, List.all_eq_false, Bool.not_eq_eq_eq_not, Bool.not_false]
  rcases hl with hl | hl
  · left; exact hl ▸ h
  · right; exact ⟨id, hl, by simpa using h⟩

/-- **Revocation cascades:** once link `id` is revoked, in every later state that
link and every link delegated beneath it are dead. -/
theorem revocation_cascades (o : Org) (id : Nat) (post : List DOp) (l : Link)
    (hl : l.id = id ∨ id ∈ l.ancestors) :
    ((o.step (.revoke id)).run post).live l = false := by
  apply dead_if_revoked _ l id _ hl
  suffices ∀ (ops : List DOp) (o' : Org), id ∈ o'.revoked → id ∈ (o'.run ops).revoked from
    this post _ (by simp [Org.step])
  intro ops
  induction ops with
  | nil => intro o' h; exact h
  | cons op ops ih => intro o' h; exact ih _ (o'.step_revoked_mono op id h)

/-! ### Commit with approver authority -/

/-- The approval the gate would consume: exact, current, and from someone who
holds authority over the effect now. -/
def Store.pickAuth (s : Store) (o : Org) (r : Request) : Option Approval :=
  s.granted.find? (fun a => a.validFor s r && o.holds a.approver r.target s.now)

def commitDecideAuth (p : Policy) (o : Org) (s : Store) (r : Request) : Response :=
  evaluate p { r with approved := (s.pickAuth o r).isSome }

/-- **Authorized approval at commit:** an irreversible effect allowed at commit has
an approval that is exact, current, and given by someone who holds authority over
that exact effect; and the root's scope covers it. -/
theorem irreversible_commit_authorized (p : Policy) (o : Org) (hw : o.WithinRoot)
    (s : Store) (r : Request)
    (ht : r.tier = .irreversible) (hal : (commitDecideAuth p o s r).decision = .allow) :
    ∃ a ∈ s.granted, a.target = r.target ∧ s.now < a.expires ∧ a.id ∉ s.revoked ∧
      o.holds a.approver r.target s.now = true ∧ o.rootScope.covers r.target s.now = true := by
  cases hp : s.pickAuth o r with
  | none =>
    exact absurd hal (irreversible_needs_approval p { r with approved := _ } ht (by simp [hp]))
  | some a =>
    have hmem := List.mem_of_find?_eq_some hp
    have hv := List.find?_some hp
    simp only [Bool.and_eq_true] at hv
    -- unpack `validFor` the same way `pick_valid` does
    have hva := hv.1
    simp only [Approval.validFor, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not] at hva
    exact ⟨a, hmem, hva.1.1.1, hva.1.1.2, hva.1.2, hv.2,
      holds_within_root o hw _ _ _ hv.2⟩

/-! ### A concrete case -/

def authExample.org : Org :=
  { root := "user:me",
    rootScope := { actions := ["bank.refund"], resources := ["acct"], maxAmount := 1000,
                   expires := 100 } }

/-- An approval of exactly the right refund, current, but given by the agent's
own sub-agent, who holds no authority. -/
def authExample.store : Store :=
  { granted := [{ id := 7, target := staleExample.req.target, approver := "agent:helper",
                  expires := 10 }] }

/-- **An approval from someone without authority:** it passes invariant 6 on its
own (exact, current, unused) and is refused once approver authority is checked. -/
theorem unauthorized_approver_refused :
    (commitDecide [] authExample.store staleExample.req).decision = .allow ∧
    (commitDecideAuth [] authExample.org authExample.store staleExample.req).decision ≠ .allow := by
  decide

end FinalSay
