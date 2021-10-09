{
  description = "Idris Frex";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; }; in
      {
        devShell = with pkgs; mkShell {
          buildInputs = [ idris2 ];
        };
      }
    );
}
