Target conference: ITP'23 https://mizar.uwb.edu.pl/ITP2023/

Abstract deadline: February 13, 2023 (AOE)

Paper submission deadline: February 20, 2023 (AOE)

Author notification: April 17, 2023

TODO:

- [X] Implement Peirce's law
- [X] Make code presentable 
- [X] Sync paper and code
- [X] Sync taint ordering with paper (remove unused taint?)
- [X] Add GitHub actions with some basic CI
- [X] Prepare repo for going public
- [X] Make short documentation on how to use code
- [X] Make `thm` opaque
- [ ] Make test case for the following pre-tactics: 
      `AllE`,
      `AllI`,
      `Appcong`,
      `Beta`,
      `Eta`,
      `ExE`,
      `ExI`,
      `Lamcong`,
      `Subst`,
      `Tysubst`
- [ ] Add licence & copyright to code (if needed)
- [ ] Make repo public

## 31.1.2023
- DONE Proved (a & y) -> !(!x | !y)
- DONE Added a lot more simple test cases
- DONE Started implementing a tactics transformer for Goedel-Gentzen style double-negation. Very early work
## 30.1.2023
- DONE Can I import `ThmClass` only as/via `ProofSystem`?
- DONE make `Goal` opaque?
- DONE make `HoleID` opaque?
- DONE make `Thm` itself opaque!
- DONE Write short explanation of how to compile and run
- DONE fix taint ordering relations
- DONE removed old set-theory definitions
- DONE implement Try(tac) 
- DONE implement Repeat(tac)
- DONE Look many the TODO comments
- DONE Remove the log option in tactics
- DONE Handle failing term tests.
- DONE Handle failing tactic tests.
- DONE Make code more presentable
- DONE Clean up debugging artefacts even more
## 29.1.2023
- DONE Set up basic CI
- DONE Finish Peirce
- DONE Clean up debugging artefacts
## 28.1.2023
- DONE Migrate repo for code
- DONE Debug double-negation proof
- DONE Streamline tactic generation
- DONE Implement Peirce (started)

