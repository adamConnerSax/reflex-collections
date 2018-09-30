(import ./reflex-platform {}).project ({ pkgs, ... }:
let nixpkgs = import <nixpkgs> {};
in
{        
  packages = {
    reflex-collections = ./. ; 
  };

  shells = {
   ghc = ["reflex-collections"];
   ghc8_2 = ["reflex-collections"];
   ghcjs = ["reflex-collections"];
  };

  overrides = import ./package-overlay.nix {};

  withHoogle = false;
})
