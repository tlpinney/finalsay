import FinalSay.Core
import FinalSay.Classify

/-!
# A toy world

A small sandboxed world the toy agent acts on. It makes the three tiers
concrete:

* **reversible:** notes live under a checkpoint, and restoring it puts the
  world back exactly as it was;
* **compensatable:** a refund is counteracted by a charge. The balance comes
  back, but the statement keeps both entries (residue);
* **irreversible:** a sent email has no compensating action at all.

Related work: compensating actions are the saga pattern (Garcia-Molina & Salem,
SIGMOD 1987). The residue reading (compensation adds history instead of removing
it) follows Landauer (1961) and Bennett (1973) on logical reversibility.
-/

namespace FinalSay

structure Email where
  to   : String
  body : String
  deriving Repr, DecidableEq

structure World where
  notes    : List String
  drafts   : List Email
  sent     : List Email
  events   : List String
  /-- Everyone notified about calendar changes: invites and cancellations. -/
  notified : List String
  balance  : Int
  /-- The bank statement: every movement ever made. -/
  ledger   : List (String × Int)
  /-- Inbox messages, flagged `true` when the content is untrusted. -/
  inbox    : List (String × Bool)
  deriving Repr, DecidableEq

/-! ## Tool effects -/

def World.writeNote (w : World) (text : String) : World :=
  { w with notes := w.notes ++ [text] }

def World.draft (w : World) (e : Email) : World :=
  { w with drafts := w.drafts ++ [e] }

def World.send (w : World) (e : Email) : World :=
  { w with sent := w.sent ++ [e], drafts := w.drafts.erase e }

def World.createEvent (w : World) (title : String) : World :=
  { w with events := w.events ++ [title], notified := w.notified ++ [s!"invite: {title}"] }

def World.deleteEvent (w : World) (title : String) : World :=
  { w with events := w.events.erase title, notified := w.notified ++ [s!"cancelled: {title}"] }

def World.refund (w : World) (amt : Int) : World :=
  { w with balance := w.balance - amt, ledger := w.ledger ++ [("refund", -amt)] }

def World.charge (w : World) (amt : Int) : World :=
  { w with balance := w.balance + amt, ledger := w.ledger ++ [("charge", amt)] }

/-! ## What the tiers mean, as theorems -/

/-- Compensatable: the compensating charge restores the balance... -/
theorem compensation_restores_balance (w : World) (amt : Int) :
    ((w.refund amt).charge amt).balance = w.balance := by
  simp [World.refund, World.charge]

/-- ...but leaves two entries on the statement. -/
theorem compensation_leaves_residue (w : World) (amt : Int) :
    ((w.refund amt).charge amt).ledger.length = w.ledger.length + 2 := by
  simp [World.refund, World.charge]

/-- So compensation is not undo: the world after compensating is not the original. -/
theorem compensation_is_not_undo (w : World) (amt : Int) :
    (w.refund amt).charge amt ≠ w := by
  intro h
  have := congrArg (fun w => w.ledger.length) h
  simp [World.refund, World.charge] at this

/-- Same for calendar events: deleting the event doesn't un-notify anyone. -/
theorem cancelled_event_was_still_seen (w : World) (title : String) :
    ((w.createEvent title).deleteEvent title).notified.length = w.notified.length + 2 := by
  simp [World.createEvent, World.deleteEvent]

/-! ## Tools the agent can call -/

inductive Tool where
  | writeNote (text : String)
  | draftEmail (e : Email)
  | sendEmail (e : Email)
  | createEvent (title : String)
  | refund (amt : Nat)
  | readInbox
  | mystery
  deriving Repr

def Tool.action : Tool → String
  | .writeNote _   => "notes.write"
  | .draftEmail _  => "email.draft"
  | .sendEmail _   => "email.send"
  | .createEvent _ => "calendar.create_event"
  | .refund _      => "bank.refund"
  | .readInbox     => "inbox.read"
  | .mystery       => "mystery.tool"

def Tool.amount : Tool → Nat
  | .refund a => a
  | _ => 0

/-- Upper bound on bytes a call sends to people outside: what recipients,
attendees, or customers get to see. -/
def Tool.bytesOut : Tool → Nat
  | .sendEmail e   => e.to.length + e.body.length
  | .createEvent t => t.length
  | .refund _      => 8
  | _ => 0

/-- What the tool claims about itself (like an MCP annotation). Only used if the
owner opts in to trusting hints. -/
def Tool.hint : Tool → Option Tier
  | .mystery => some .reversible
  | _ => none

/-- A registered compensation, to run if the session is rolled back. -/
inductive Compensation where
  | deleteEvent (title : String)
  | charge (amt : Int)
  deriving Repr

def Compensation.apply (w : World) : Compensation → World
  | .deleteEvent t => w.deleteEvent t
  | .charge a      => w.charge a

/-- Run a tool. Returns the new world, a compensation to register (compensatable
tools only), and whether untrusted content entered the session. -/
def Tool.run (w : World) : Tool → World × Option Compensation × Bool
  | .writeNote t   => (w.writeNote t, none, false)
  | .draftEmail e  => (w.draft e, none, false)
  | .sendEmail e   => (w.send e, none, false)
  | .createEvent t => (w.createEvent t, some (.deleteEvent t), false)
  | .refund a      => (w.refund a, some (.charge a), false)
  | .readInbox     => (w, none, w.inbox.any (·.2))
  | .mystery       => (w, none, false)

end FinalSay
