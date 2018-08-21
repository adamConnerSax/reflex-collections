{nixpkgs ? import <nixpkgs> {} }:
self: super: {
#  quickcheck = super.callHackage "quickcheck" "2.11.3" {};
#  validation = super.callHackage "validation" "0.6.0" {}; #fix doctest error
#  perConstructor-sop = super.callCabal2nix "perConstructor-sop" (nixpkgs.pkgs.fetchFromGitHub {
#    owner = "adamConnerSax";
#    repo = "perConstructor-sop";
#    rev = "b0c8fd5c4b1576b4ad713821f35d06b0c00ff5f6";
#    sha256 = "1lyzzn1bfjgk6p8v62r5r0xqkp6ry4y26f52d3zfix7n1xqfqaq4";
#   }) {};
#   reflex-dom-contrib = super.callCabal2nix "reflex-dom-contrib" (nixpkgs.pkgs.fetchFromGitHub {
#     owner = "adamConnerSax";
#     repo = "reflex-dom-contrib";
#     rev = "0eed765f1945d76293238cca32f83d00fb04c61d";
#     sha256 = "0b0zlzbhd7c1syggn196jhhm67s4nsddmyd29njjnk537lw1d2qv";
#   }) {};
}      
