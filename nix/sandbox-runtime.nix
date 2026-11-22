# Anthropic's Sandbox Runtime (`srt`), built from whatever revision the
# `sandbox-runtime` flake input points at. Dependencies come from upstream's
# package-lock.json via importNpmLock, so updating needs no hash edits:
#
#   nix flake update sandbox-runtime
#
# Adapted from nixpkgs' pkgs/by-name/sa/sandbox-runtime/package.nix.
{
  lib,
  stdenv,
  buildNpmPackage,
  importNpmLock,
  ripgrep,
  which,
  bubblewrap,
  socat,
  src,
}:

let
  pkgJson = lib.importJSON "${src}/package.json";
  runtimeDeps = [ ripgrep which ] ++ lib.optionals stdenv.hostPlatform.isLinux [ bubblewrap socat ];
in
buildNpmPackage {
  pname = "sandbox-runtime";
  version = "${pkgJson.version}-${src.shortRev or "dirty"}";
  inherit src;

  npmDeps = importNpmLock { npmRoot = src; };
  npmConfigHook = importNpmLock.npmConfigHook;

  postFixup = ''
    wrapProgram $out/bin/srt --prefix PATH : ${lib.makeBinPath runtimeDeps}
  '';

  meta = {
    description = "OS-level filesystem and network sandboxing for arbitrary processes (Seatbelt / bubblewrap)";
    homepage = "https://github.com/anthropics/sandbox-runtime";
    license = lib.licenses.asl20;
    mainProgram = "srt";
    platforms = lib.platforms.linux ++ lib.platforms.darwin;
  };
}
