# Installing Agda on some kind of Linux

This short guide will help you get Agda 2.6.2.2 running on a Linux machine.

0\. If using bash: Add "export PATH=$HOME/.cabal/bin:$PATH" to the bottom of your .profile file if it isn't already there. Else if using tcsh: Add "set path = ($home/.cabal/bin $path)" to the bottom of your .cshrc file if it isn't already there.

1\. Install the [GHC Haskell compiler](https://www.haskell.org/downloads/) either using a package managager, or using [GHCup](https://www.haskell.org/ghcup/).

2\. Run
```
cabal update
cabal install alex happy Agda
```
This will compile Agda on your machine. The process might take very long time (> 30 minutes) and is quite memory intensive (make sure you have at least 4GB free).

4\. Install emacs, probably using a package manager.

5\. Run `agda-mode setup`.

6\. Get the [agda standard library](https://github.com/agda/agda-stdlib/releases/tag/v1.7.1). Unzip it to a destination of your choice, call that parent directory `$DIR`.

7\. Create a directory `~/.agda` by running `mkdir ~/.agda`.

8.\ Create the file `~/.agda/libraries` (note: no file extension!) and add the following line to it, replacing `$DIR` with the concrete path:
```
$DIR/agda-stdlib-1.7.1/standard-library.agda-lib
```

8\. (OPTIONAL) Create `~/.agda/defaults` (again no file extension!) and add the following line to it:
```
standard-library
```
This means that all your files will know about the standard library by default. (The coursework, however, explicitly depends on the standard library, so it doesn't rely on this step.)

9\. That's it; if you open a file with a `.agda` extension in Emacs, you should see the Agda menu at the top. Happy hacking!
