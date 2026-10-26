import V185TrunkScan23Chunk0714

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4227343 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 10]
def baseStart_4227343 : Nat := 118140960795 + 4227343 * 2 ^ 59
def prefixEnd_4227343 : Nat := 4983230072969 + 3 ^ 40 * 4227343 * 2
def baseEnd_4227343 : Nat := 723552950139853078257103

theorem tailTrace_4227343 : CollatzResearch.WordTrace tailWord_4227343 prefixEnd_4227343 723552950139853078257103 := by
  unfold tailWord_4227343
  simp only [CollatzResearch.WordTrace]
  refine ⟨154183865924065758550326683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102789243949377172366884455 154183865924065758550326683)
  ·
    refine ⟨231275798886098637825490025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154183865924065758550326683 231275798886098637825490025)
    ·
      refine ⟨173456849164573978369117519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231275798886098637825490025 173456849164573978369117519)
      ·
        refine ⟨260185273746860967553676279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173456849164573978369117519 260185273746860967553676279)
        ·
          refine ⟨390277910620291451330514419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260185273746860967553676279 390277910620291451330514419)
          ·
            refine ⟨585416865930437176995771629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390277910620291451330514419 585416865930437176995771629)
            ·
              refine ⟨219531324723913941373414361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 585416865930437176995771629 219531324723913941373414361)
              ·
                refine ⟨164648493542935456030060771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219531324723913941373414361 164648493542935456030060771)
                ·
                  refine ⟨246972740314403184045091157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164648493542935456030060771 246972740314403184045091157)
                  ·
                    refine ⟨723552950139853078257103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 246972740314403184045091157 723552950139853078257103)
                    ·
                      rfl

theorem cell23_4227343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_4227343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227343 prefixEnd_4227343 := by exact prefixLift 4227343
  have htrace : WordTrace (prefixWord ++ tailWord_4227343) baseStart_4227343 baseEnd_4227343 := by
    simpa [prefixWord, tailWord_4227343, baseEnd_4227343] using wordTrace_append hprefix tailTrace_4227343
  have hstable : (prefixWord ++ tailWord_4227343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227343).length < 2 ^ (prefixWord ++ tailWord_4227343).sum := by decide
  have hdescent : baseEnd_4227343 < baseStart_4227343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227410 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_4227410 : Nat := 118140960795 + 4227410 * 2 ^ 59
def prefixEnd_4227410 : Nat := 4983230072969 + 3 ^ 40 * 4227410 * 2
def baseEnd_4227410 : Nat := 2170693253623410472633501

theorem tailTrace_4227410 : CollatzResearch.WordTrace tailWord_4227410 prefixEnd_4227410 2170693253623410472633501 := by
  unfold tailWord_4227410
  simp only [CollatzResearch.WordTrace]
  refine ⟨38546577403705757248253921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102790873076548685995343789 38546577403705757248253921)
  ·
    refine ⟨28909933052779317936190441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38546577403705757248253921 28909933052779317936190441)
    ·
      refine ⟨21682449789584488452142831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28909933052779317936190441 21682449789584488452142831)
      ·
        refine ⟨32523674684376732678214247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21682449789584488452142831 32523674684376732678214247)
        ·
          refine ⟨48785512026565099017321371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32523674684376732678214247 48785512026565099017321371)
          ·
            refine ⟨73178268039847648525982057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48785512026565099017321371 73178268039847648525982057)
            ·
              refine ⟨54883701029885736394486543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73178268039847648525982057 54883701029885736394486543)
              ·
                refine ⟨82325551544828604591729815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54883701029885736394486543 82325551544828604591729815)
                ·
                  refine ⟨123488327317242906887594723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82325551544828604591729815 123488327317242906887594723)
                  ·
                    refine ⟨185232490975864360331392085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123488327317242906887594723 185232490975864360331392085)
                    ·
                      refine ⟨2170693253623410472633501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 185232490975864360331392085 2170693253623410472633501)
                      ·
                        rfl

theorem cell23_4227410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_4227410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227410 prefixEnd_4227410 := by exact prefixLift 4227410
  have htrace : WordTrace (prefixWord ++ tailWord_4227410) baseStart_4227410 baseEnd_4227410 := by
    simpa [prefixWord, tailWord_4227410, baseEnd_4227410] using wordTrace_append hprefix tailTrace_4227410
  have hstable : (prefixWord ++ tailWord_4227410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227410).length < 2 ^ (prefixWord ++ tailWord_4227410).sum := by decide
  have hdescent : baseEnd_4227410 < baseStart_4227410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227437 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_4227437 : Nat := 118140960795 + 4227437 * 2 ^ 59
def prefixEnd_4227437 : Nat := 4983230072969 + 3 ^ 40 * 4227437 * 2
def baseEnd_4227437 : Nat := 723569039200360622331959

theorem tailTrace_4227437 : CollatzResearch.WordTrace tailWord_4227437 prefixEnd_4227437 723569039200360622331959 := by
  unfold tailWord_4227437
  simp only [CollatzResearch.WordTrace]
  refine ⟨154187294385725212604248565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102791529590483475069499043 154187294385725212604248565)
  ·
    refine ⟨14455058848661738681648303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154187294385725212604248565 14455058848661738681648303)
    ·
      refine ⟨21682588272992608022472455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14455058848661738681648303 21682588272992608022472455)
      ·
        refine ⟨32523882409488912033708683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21682588272992608022472455 32523882409488912033708683)
        ·
          refine ⟨48785823614233368050563025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32523882409488912033708683 48785823614233368050563025)
          ·
            refine ⟨36589367710675026037922269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48785823614233368050563025 36589367710675026037922269)
            ·
              refine ⟨13721012891503134764220851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36589367710675026037922269 13721012891503134764220851)
              ·
                refine ⟨20581519337254702146331277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13721012891503134764220851 20581519337254702146331277)
                ·
                  refine ⟨7718069751470513304874229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20581519337254702146331277 7718069751470513304874229)
                  ·
                    refine ⟨723569039200360622331959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7718069751470513304874229 723569039200360622331959)
                    ·
                      rfl

theorem cell23_4227437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_4227437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227437 prefixEnd_4227437 := by exact prefixLift 4227437
  have htrace : WordTrace (prefixWord ++ tailWord_4227437) baseStart_4227437 baseEnd_4227437 := by
    simpa [prefixWord, tailWord_4227437, baseEnd_4227437] using wordTrace_append hprefix tailTrace_4227437
  have hstable : (prefixWord ++ tailWord_4227437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227437).length < 2 ^ (prefixWord ++ tailWord_4227437).sum := by decide
  have hdescent : baseEnd_4227437 < baseStart_4227437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227468 : List Nat := [2, 2, 1, 2, 1, 4, 4, 2, 1, 1, 3]
def baseStart_4227468 : Nat := 118140960795 + 4227468 * 2 ^ 59
def prefixEnd_4227468 : Nat := 4983230072969 + 3 ^ 40 * 4227468 * 2
def baseEnd_4227468 : Nat := 2170723035501371245708235

theorem tailTrace_4227468 : CollatzResearch.WordTrace tailWord_4227468 prefixEnd_4227468 2170723035501371245708235 := by
  unfold tailWord_4227468
  simp only [CollatzResearch.WordTrace]
  refine ⟨77094212524306452449313529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102792283365741936599084705 77094212524306452449313529)
  ·
    refine ⟨57820659393229839336985147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77094212524306452449313529 57820659393229839336985147)
    ·
      refine ⟨86730989089844759005477721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57820659393229839336985147 86730989089844759005477721)
      ·
        refine ⟨65048241817383569254108291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86730989089844759005477721 65048241817383569254108291)
        ·
          refine ⟨97572362726075353881162437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65048241817383569254108291 97572362726075353881162437)
          ·
            refine ⟨18294818011139128852717957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97572362726075353881162437 18294818011139128852717957)
            ·
              refine ⟨3430278377088586659884617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18294818011139128852717957 3430278377088586659884617)
              ·
                refine ⟨2572708782816439994913463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430278377088586659884617 2572708782816439994913463)
                ·
                  refine ⟨3859063174224659992370195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572708782816439994913463 3859063174224659992370195)
                  ·
                    refine ⟨5788594761336989988555293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3859063174224659992370195 5788594761336989988555293)
                    ·
                      refine ⟨2170723035501371245708235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788594761336989988555293 2170723035501371245708235)
                      ·
                        rfl

theorem cell23_4227468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_4227468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227468 prefixEnd_4227468 := by exact prefixLift 4227468
  have htrace : WordTrace (prefixWord ++ tailWord_4227468) baseStart_4227468 baseEnd_4227468 := by
    simpa [prefixWord, tailWord_4227468, baseEnd_4227468] using wordTrace_append hprefix tailTrace_4227468
  have hstable : (prefixWord ++ tailWord_4227468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227468).length < 2 ^ (prefixWord ++ tailWord_4227468).sum := by decide
  have hdescent : baseEnd_4227468 < baseStart_4227468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227491 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 3, 2, 2]
def baseStart_4227491 : Nat := 118140960795 + 4227491 * 2 ^ 59
def prefixEnd_4227491 : Nat := 4983230072969 + 3 ^ 40 * 4227491 * 2
def baseEnd_4227491 : Nat := 2170734845556424655720629

theorem tailTrace_4227491 : CollatzResearch.WordTrace tailWord_4227491 prefixEnd_4227491 2170734845556424655720629 := by
  unfold tailWord_4227491
  simp only [CollatzResearch.WordTrace]
  refine ⟨154189263927529579826714327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102792842618353053217809551 154189263927529579826714327)
  ·
    refine ⟨231283895891294369740071491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154189263927529579826714327 231283895891294369740071491)
    ·
      refine ⟨346925843836941554610107237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231283895891294369740071491 346925843836941554610107237)
      ·
        refine ⟨65048595719426541489395107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 346925843836941554610107237 65048595719426541489395107)
        ·
          refine ⟨97572893579139812234092661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65048595719426541489395107 97572893579139812234092661)
          ·
            refine ⟨9147458773044357396946187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97572893579139812234092661 9147458773044357396946187)
            ·
              refine ⟨13721188159566536095419281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9147458773044357396946187 13721188159566536095419281)
              ·
                refine ⟨10290891119674902071564461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13721188159566536095419281 10290891119674902071564461)
                ·
                  refine ⟨3859084169878088276836673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10290891119674902071564461 3859084169878088276836673)
                  ·
                    refine ⟨2894313127408566207627505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3859084169878088276836673 2894313127408566207627505)
                    ·
                      refine ⟨2170734845556424655720629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894313127408566207627505 2170734845556424655720629)
                      ·
                        rfl

theorem cell23_4227491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_4227491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227491 prefixEnd_4227491 := by exact prefixLift 4227491
  have htrace : WordTrace (prefixWord ++ tailWord_4227491) baseStart_4227491 baseEnd_4227491 := by
    simpa [prefixWord, tailWord_4227491, baseEnd_4227491] using wordTrace_append hprefix tailTrace_4227491
  have hstable : (prefixWord ++ tailWord_4227491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227491).length < 2 ^ (prefixWord ++ tailWord_4227491).sum := by decide
  have hdescent : baseEnd_4227491 < baseStart_4227491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227511 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 1, 2, 3]
def baseStart_4227511 : Nat := 118140960795 + 4227511 * 2 ^ 59
def prefixEnd_4227511 : Nat := 4983230072969 + 3 ^ 40 * 4227511 * 2
def baseEnd_4227511 : Nat := 2170745115169514577470537

theorem tailTrace_4227511 : CollatzResearch.WordTrace tailWord_4227511 prefixEnd_4227511 2170745115169514577470537 := by
  unfold tailWord_4227511
  simp only [CollatzResearch.WordTrace]
  refine ⟨154189993387457123242442387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102793328924971415494961591 154189993387457123242442387)
  ·
    refine ⟨231284990081185684863663581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154189993387457123242442387 231284990081185684863663581)
    ·
      refine ⟨86731871280444631823873843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231284990081185684863663581 86731871280444631823873843)
      ·
        refine ⟨130097806920666947735810765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86731871280444631823873843 130097806920666947735810765)
        ·
          refine ⟨48786677595250105400929037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130097806920666947735810765 48786677595250105400929037)
          ·
            refine ⟨18295004098218789525348389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48786677595250105400929037 18295004098218789525348389)
            ·
              refine ⟨3430313268416023036002823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18295004098218789525348389 3430313268416023036002823)
              ·
                refine ⟨5145469902624034554004235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3430313268416023036002823 5145469902624034554004235)
                ·
                  refine ⟨7718204853936051831006353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5145469902624034554004235 7718204853936051831006353)
                  ·
                    refine ⟨5788653640452038873254765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7718204853936051831006353 5788653640452038873254765)
                    ·
                      refine ⟨2170745115169514577470537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788653640452038873254765 2170745115169514577470537)
                      ·
                        rfl

theorem cell23_4227511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_4227511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227511 prefixEnd_4227511 := by exact prefixLift 4227511
  have htrace : WordTrace (prefixWord ++ tailWord_4227511) baseStart_4227511 baseEnd_4227511 := by
    simpa [prefixWord, tailWord_4227511, baseEnd_4227511] using wordTrace_append hprefix tailTrace_4227511
  have hstable : (prefixWord ++ tailWord_4227511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227511).length < 2 ^ (prefixWord ++ tailWord_4227511).sum := by decide
  have hdescent : baseEnd_4227511 < baseStart_4227511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227538 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4227538 : Nat := 118140960795 + 4227538 * 2 ^ 59
def prefixEnd_4227538 : Nat := 4983230072969 + 3 ^ 40 * 4227538 * 2
def baseEnd_4227538 : Nat := 2170758979147185971832913

theorem tailTrace_4227538 : CollatzResearch.WordTrace tailWord_4227538 prefixEnd_4227538 2170758979147185971832913 := by
  unfold tailWord_4227538
  simp only [CollatzResearch.WordTrace]
  refine ⟨38547744539589826713418817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102793985438906204569116845 38547744539589826713418817)
  ·
    refine ⟨28910808404692370035064113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38547744539589826713418817 28910808404692370035064113)
    ·
      refine ⟨21683106303519277526298085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28910808404692370035064113 21683106303519277526298085)
      ·
        refine ⟨4065582431909864536180891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21683106303519277526298085 4065582431909864536180891)
        ·
          refine ⟨6098373647864796804271337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065582431909864536180891 6098373647864796804271337)
          ·
            refine ⟨4573780235898597603203503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6098373647864796804271337 4573780235898597603203503)
            ·
              refine ⟨6860670353847896404805255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4573780235898597603203503 6860670353847896404805255)
              ·
                refine ⟨10291005530771844607207883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6860670353847896404805255 10291005530771844607207883)
                ·
                  refine ⟨15436508296157766910811825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10291005530771844607207883 15436508296157766910811825)
                  ·
                    refine ⟨11577381222118325183108869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15436508296157766910811825 11577381222118325183108869)
                    ·
                      refine ⟨2170758979147185971832913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11577381222118325183108869 2170758979147185971832913)
                      ·
                        rfl

theorem cell23_4227538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4227538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227538 prefixEnd_4227538 := by exact prefixLift 4227538
  have htrace : WordTrace (prefixWord ++ tailWord_4227538) baseStart_4227538 baseEnd_4227538 := by
    simpa [prefixWord, tailWord_4227538, baseEnd_4227538] using wordTrace_append hprefix tailTrace_4227538
  have hstable : (prefixWord ++ tailWord_4227538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227538).length < 2 ^ (prefixWord ++ tailWord_4227538).sum := by decide
  have hdescent : baseEnd_4227538 < baseStart_4227538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227541 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_4227541 : Nat := 118140960795 + 4227541 * 2 ^ 59
def prefixEnd_4227541 : Nat := 4983230072969 + 3 ^ 40 * 4227541 * 2
def baseEnd_4227541 : Nat := 2170760519589149460095399

theorem tailTrace_4227541 : CollatzResearch.WordTrace tailWord_4227541 prefixEnd_4227541 2170760519589149460095399 := by
  unfold tailWord_4227541
  simp only [CollatzResearch.WordTrace]
  refine ⟨154191087577348438366034477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102794058384898958910689651 154191087577348438366034477)
  ·
    refine ⟨57821657841505664387262929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154191087577348438366034477 57821657841505664387262929)
    ·
      refine ⟨43366243381129248290447197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57821657841505664387262929 43366243381129248290447197)
      ·
        refine ⟨16262341267923468108917699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43366243381129248290447197 16262341267923468108917699)
        ·
          refine ⟨24393511901885202163376549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16262341267923468108917699 24393511901885202163376549)
          ·
            refine ⟨4573783481603475405633103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24393511901885202163376549 4573783481603475405633103)
            ·
              refine ⟨6860675222405213108449655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4573783481603475405633103 6860675222405213108449655)
              ·
                refine ⟨10291012833607819662674483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6860675222405213108449655 10291012833607819662674483)
                ·
                  refine ⟨15436519250411729494011725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10291012833607819662674483 15436519250411729494011725)
                  ·
                    refine ⟨5788694718904398560254397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15436519250411729494011725 5788694718904398560254397)
                    ·
                      refine ⟨2170760519589149460095399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788694718904398560254397 2170760519589149460095399)
                      ·
                        rfl

theorem cell23_4227541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_4227541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227541 prefixEnd_4227541 := by exact prefixLift 4227541
  have htrace : WordTrace (prefixWord ++ tailWord_4227541) baseStart_4227541 baseEnd_4227541 := by
    simpa [prefixWord, tailWord_4227541, baseEnd_4227541] using wordTrace_append hprefix tailTrace_4227541
  have hstable : (prefixWord ++ tailWord_4227541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227541).length < 2 ^ (prefixWord ++ tailWord_4227541).sum := by decide
  have hdescent : baseEnd_4227541 < baseStart_4227541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227551 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 1, 3, 2]
def baseStart_4227551 : Nat := 118140960795 + 4227551 * 2 ^ 59
def prefixEnd_4227551 : Nat := 4983230072969 + 3 ^ 40 * 4227551 * 2
def baseEnd_4227551 : Nat := 2170765654395694420970353

theorem tailTrace_4227551 : CollatzResearch.WordTrace tailWord_4227551 prefixEnd_4227551 2170765654395694420970353 := by
  unfold tailWord_4227551
  simp only [CollatzResearch.WordTrace]
  refine ⟨154191452307312210073898507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102794301538208140049265671 154191452307312210073898507)
  ·
    refine ⟨231287178460968315110847761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154191452307312210073898507 231287178460968315110847761)
    ·
      refine ⟨173465383845726236333135821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231287178460968315110847761 173465383845726236333135821)
      ·
        refine ⟨65049518942147338624925933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173465383845726236333135821 65049518942147338624925933)
        ·
          refine ⟨24393569603305251984347225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65049518942147338624925933 24393569603305251984347225)
          ·
            refine ⟨18295177202478938988260419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24393569603305251984347225 18295177202478938988260419)
            ·
              refine ⟨27442765803718408482390629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18295177202478938988260419 27442765803718408482390629)
              ·
                refine ⟨5145518588197201590448243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27442765803718408482390629 5145518588197201590448243)
                ·
                  refine ⟨7718277882295802385672365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5145518588197201590448243 7718277882295802385672365)
                  ·
                    refine ⟨2894354205860925894627137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7718277882295802385672365 2894354205860925894627137)
                    ·
                      refine ⟨2170765654395694420970353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894354205860925894627137 2170765654395694420970353)
                      ·
                        rfl

theorem cell23_4227551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_4227551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227551 prefixEnd_4227551 := by exact prefixLift 4227551
  have htrace : WordTrace (prefixWord ++ tailWord_4227551) baseStart_4227551 baseEnd_4227551 := by
    simpa [prefixWord, tailWord_4227551, baseEnd_4227551] using wordTrace_append hprefix tailTrace_4227551
  have hstable : (prefixWord ++ tailWord_4227551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227551).length < 2 ^ (prefixWord ++ tailWord_4227551).sum := by decide
  have hdescent : baseEnd_4227551 < baseStart_4227551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227564 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 3, 4, 2]
def baseStart_4227564 : Nat := 118140960795 + 4227564 * 2 ^ 59
def prefixEnd_4227564 : Nat := 4983230072969 + 3 ^ 40 * 4227564 * 2
def baseEnd_4227564 : Nat := 2170772329644202870107793

theorem tailTrace_4227564 : CollatzResearch.WordTrace tailWord_4227564 prefixEnd_4227564 2170772329644202870107793 := by
  unfold tailWord_4227564
  simp only [CollatzResearch.WordTrace]
  refine ⟨77095963228132556647060873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102794617637510075529414497 77095963228132556647060873)
  ·
    refine ⟨57821972421099417485295655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77095963228132556647060873 57821972421099417485295655)
    ·
      refine ⟨86732958631649126227943483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57821972421099417485295655 86732958631649126227943483)
      ·
        refine ⟨130099437947473689341915225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86732958631649126227943483 130099437947473689341915225)
        ·
          refine ⟨97574578460605267006436419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130099437947473689341915225 97574578460605267006436419)
          ·
            refine ⟨146361867690907900509654629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97574578460605267006436419 146361867690907900509654629)
            ·
              refine ⟨27442850192045231345560243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146361867690907900509654629 27442850192045231345560243)
              ·
                refine ⟨41164275288067847018340365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27442850192045231345560243 41164275288067847018340365)
                ·
                  refine ⟨15436603233025442631877637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41164275288067847018340365 15436603233025442631877637)
                  ·
                    refine ⟨2894363106192270493477057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15436603233025442631877637 2894363106192270493477057)
                    ·
                      refine ⟨2170772329644202870107793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894363106192270493477057 2170772329644202870107793)
                      ·
                        rfl

theorem cell23_4227564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_4227564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227564 prefixEnd_4227564 := by exact prefixLift 4227564
  have htrace : WordTrace (prefixWord ++ tailWord_4227564) baseStart_4227564 baseEnd_4227564 := by
    simpa [prefixWord, tailWord_4227564, baseEnd_4227564] using wordTrace_append hprefix tailTrace_4227564
  have hstable : (prefixWord ++ tailWord_4227564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227564).length < 2 ^ (prefixWord ++ tailWord_4227564).sum := by decide
  have hdescent : baseEnd_4227564 < baseStart_4227564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227567 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 3]
def baseStart_4227567 : Nat := 118140960795 + 4227567 * 2 ^ 59
def prefixEnd_4227567 : Nat := 4983230072969 + 3 ^ 40 * 4227567 * 2
def baseEnd_4227567 : Nat := 2170773870086166358370279

theorem tailTrace_4227567 : CollatzResearch.WordTrace tailWord_4227567 prefixEnd_4227567 2170773870086166358370279 := by
  unfold tailWord_4227567
  simp only [CollatzResearch.WordTrace]
  refine ⟨154192035875254244806480955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102794690583502829870987303 154192035875254244806480955)
  ·
    refine ⟨231288053812881367209721433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154192035875254244806480955 231288053812881367209721433)
    ·
      refine ⟨173466040359661025407291075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231288053812881367209721433 173466040359661025407291075)
      ·
        refine ⟨260199060539491538110936613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173466040359661025407291075 260199060539491538110936613)
        ·
          refine ⟨48787323851154663395800615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260199060539491538110936613 48787323851154663395800615)
          ·
            refine ⟨73180985776731995093700923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48787323851154663395800615 73180985776731995093700923)
            ·
              refine ⟨109771478665097992640551385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73180985776731995093700923 109771478665097992640551385)
              ·
                refine ⟨82328608998823494480413539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109771478665097992640551385 82328608998823494480413539)
                ·
                  refine ⟨123492913498235241720620309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82328608998823494480413539 123492913498235241720620309)
                  ·
                    refine ⟨5788730320229776955654077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123492913498235241720620309 5788730320229776955654077)
                    ·
                      refine ⟨2170773870086166358370279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5788730320229776955654077 2170773870086166358370279)
                      ·
                        rfl

theorem cell23_4227567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_4227567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227567 prefixEnd_4227567 := by exact prefixLift 4227567
  have htrace : WordTrace (prefixWord ++ tailWord_4227567) baseStart_4227567 baseEnd_4227567 := by
    simpa [prefixWord, tailWord_4227567, baseEnd_4227567] using wordTrace_append hprefix tailTrace_4227567
  have hstable : (prefixWord ++ tailWord_4227567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227567).length < 2 ^ (prefixWord ++ tailWord_4227567).sum := by decide
  have hdescent : baseEnd_4227567 < baseStart_4227567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227577 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_4227577 : Nat := 118140960795 + 4227577 * 2 ^ 59
def prefixEnd_4227577 : Nat := 4983230072969 + 3 ^ 40 * 4227577 * 2
def baseEnd_4227577 : Nat := 2170779004892711319245233

theorem tailTrace_4227577 : CollatzResearch.WordTrace tailWord_4227577 prefixEnd_4227577 2170779004892711319245233 := by
  unfold tailWord_4227577
  simp only [CollatzResearch.WordTrace]
  refine ⟨154192400605218016514344985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102794933736812011009563323 154192400605218016514344985)
  ·
    refine ⟨115644300453913512385758739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154192400605218016514344985 115644300453913512385758739)
    ·
      refine ⟨173466450680870268578638109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115644300453913512385758739 173466450680870268578638109)
      ·
        refine ⟨65049919005326350716989291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173466450680870268578638109 65049919005326350716989291)
        ·
          refine ⟨97574878507989526075483937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65049919005326350716989291 97574878507989526075483937)
          ·
            refine ⟨73181158880992144556612953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97574878507989526075483937 73181158880992144556612953)
            ·
              refine ⟨54885869160744108417459715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73181158880992144556612953 54885869160744108417459715)
              ·
                refine ⟨82328803741116162626189573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54885869160744108417459715 82328803741116162626189573)
                ·
                  refine ⟨15436650701459280492410545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82328803741116162626189573 15436650701459280492410545)
                  ·
                    refine ⟨11577488026094460369307909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15436650701459280492410545 11577488026094460369307909)
                    ·
                      refine ⟨2170779004892711319245233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11577488026094460369307909 2170779004892711319245233)
                      ·
                        rfl

theorem cell23_4227577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_4227577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227577 prefixEnd_4227577 := by exact prefixLift 4227577
  have htrace : WordTrace (prefixWord ++ tailWord_4227577) baseStart_4227577 baseEnd_4227577 := by
    simpa [prefixWord, tailWord_4227577, baseEnd_4227577] using wordTrace_append hprefix tailTrace_4227577
  have hstable : (prefixWord ++ tailWord_4227577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227577).length < 2 ^ (prefixWord ++ tailWord_4227577).sum := by decide
  have hdescent : baseEnd_4227577 < baseStart_4227577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227581 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_4227581 : Nat := 118140960795 + 4227581 * 2 ^ 59
def prefixEnd_4227581 : Nat := 4983230072969 + 3 ^ 40 * 4227581 * 2
def baseEnd_4227581 : Nat := 2170781058815329303595215

theorem tailTrace_4227581 : CollatzResearch.WordTrace tailWord_4227581 prefixEnd_4227581 2170781058815329303595215 := by
  unfold tailWord_4227581
  simp only [CollatzResearch.WordTrace]
  refine ⟨154192546497203525197490597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102795030998135683464993731 154192546497203525197490597)
  ·
    refine ⟨28911102468225660974529487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154192546497203525197490597 28911102468225660974529487)
    ·
      refine ⟨43366653702338491461794231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28911102468225660974529487 43366653702338491461794231)
      ·
        refine ⟨65049980553507737192691347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43366653702338491461794231 65049980553507737192691347)
        ·
          refine ⟨97574970830261605789037021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65049980553507737192691347 97574970830261605789037021)
          ·
            refine ⟨36590614061348102170888883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97574970830261605789037021 36590614061348102170888883)
            ·
              refine ⟨54885921092022153256333325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36590614061348102170888883 54885921092022153256333325)
              ·
                refine ⟨20582220409508307471124997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54885921092022153256333325 20582220409508307471124997)
                ·
                  refine ⟨3859166326782807650835937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20582220409508307471124997 3859166326782807650835937)
                  ·
                    refine ⟨2894374745087105738126953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3859166326782807650835937 2894374745087105738126953)
                    ·
                      refine ⟨2170781058815329303595215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894374745087105738126953 2170781058815329303595215)
                      ·
                        rfl

theorem cell23_4227581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_4227581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227581 prefixEnd_4227581 := by exact prefixLift 4227581
  have htrace : WordTrace (prefixWord ++ tailWord_4227581) baseStart_4227581 baseEnd_4227581 := by
    simpa [prefixWord, tailWord_4227581, baseEnd_4227581] using wordTrace_append hprefix tailTrace_4227581
  have hstable : (prefixWord ++ tailWord_4227581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227581).length < 2 ^ (prefixWord ++ tailWord_4227581).sum := by decide
  have hdescent : baseEnd_4227581 < baseStart_4227581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227634 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_4227634 : Nat := 118140960795 + 4227634 * 2 ^ 59
def prefixEnd_4227634 : Nat := 4983230072969 + 3 ^ 40 * 4227634 * 2
def baseEnd_4227634 : Nat := 723602757763339198744157

theorem tailTrace_4227634 : CollatzResearch.WordTrace tailWord_4227634 prefixEnd_4227634 723602757763339198744157 := by
  unfold tailWord_4227634
  simp only [CollatzResearch.WordTrace]
  refine ⟨38548619891502878812292489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102796319710674343499446637 38548619891502878812292489)
  ·
    refine ⟨28911464918627159109219367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38548619891502878812292489 28911464918627159109219367)
    ·
      refine ⟨43367197377940738663829051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28911464918627159109219367 43367197377940738663829051)
      ·
        refine ⟨65050796066911107995743577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43367197377940738663829051 65050796066911107995743577)
        ·
          refine ⟨48788097050183330996807683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65050796066911107995743577 48788097050183330996807683)
          ·
            refine ⟨73182145575274996495211525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48788097050183330996807683 73182145575274996495211525)
            ·
              refine ⟨13721652295364061842852161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73182145575274996495211525 13721652295364061842852161)
              ·
                refine ⟨10291239221523046382139121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13721652295364061842852161 10291239221523046382139121)
                ·
                  refine ⟨7718429416142284786604341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10291239221523046382139121 7718429416142284786604341)
                  ·
                    refine ⟨723602757763339198744157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7718429416142284786604341 723602757763339198744157)
                    ·
                      rfl

theorem cell23_4227634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_4227634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227634 prefixEnd_4227634 := by exact prefixLift 4227634
  have htrace : WordTrace (prefixWord ++ tailWord_4227634) baseStart_4227634 baseEnd_4227634 := by
    simpa [prefixWord, tailWord_4227634, baseEnd_4227634] using wordTrace_append hprefix tailTrace_4227634
  have hstable : (prefixWord ++ tailWord_4227634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227634).length < 2 ^ (prefixWord ++ tailWord_4227634).sum := by decide
  have hdescent : baseEnd_4227634 < baseStart_4227634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227638 : List Nat := [5, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_4227638 : Nat := 118140960795 + 4227638 * 2 ^ 59
def prefixEnd_4227638 : Nat := 4983230072969 + 3 ^ 40 * 4227638 * 2
def baseEnd_4227638 : Nat := 241201147468070620064717

theorem tailTrace_4227638 : CollatzResearch.WordTrace tailWord_4227638 prefixEnd_4227638 241201147468070620064717 := by
  unfold tailWord_4227638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9637164091124813995769723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102796416971998015954877045 9637164091124813995769723)
  ·
    refine ⟨14455746136687220993654585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9637164091124813995769723 14455746136687220993654585)
    ·
      refine ⟨10841809602515415745240939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14455746136687220993654585 10841809602515415745240939)
      ·
        refine ⟨16262714403773123617861409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10841809602515415745240939 16262714403773123617861409)
        ·
          refine ⟨12197035802829842713396057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16262714403773123617861409 12197035802829842713396057)
          ·
            refine ⟨9147776852122382035047043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12197035802829842713396057 9147776852122382035047043)
            ·
              refine ⟨13721665278183573052570565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9147776852122382035047043 13721665278183573052570565)
              ·
                refine ⟨2572812239659419947356981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13721665278183573052570565 2572812239659419947356981)
                ·
                  refine ⟨241201147468070620064717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572812239659419947356981 241201147468070620064717)
                  ·
                    rfl

theorem cell23_4227638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_4227638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227638 prefixEnd_4227638 := by exact prefixLift 4227638
  have htrace : WordTrace (prefixWord ++ tailWord_4227638) baseStart_4227638 baseEnd_4227638 := by
    simpa [prefixWord, tailWord_4227638, baseEnd_4227638] using wordTrace_append hprefix tailTrace_4227638
  have hstable : (prefixWord ++ tailWord_4227638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227638).length < 2 ^ (prefixWord ++ tailWord_4227638).sum := by decide
  have hdescent : baseEnd_4227638 < baseStart_4227638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227644 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_4227644 : Nat := 118140960795 + 4227644 * 2 ^ 59
def prefixEnd_4227644 : Nat := 4983230072969 + 3 ^ 40 * 4227644 * 2
def baseEnd_4227644 : Nat := 2170813408096562557107425

theorem tailTrace_4227644 : CollatzResearch.WordTrace tailWord_4227644 prefixEnd_4227644 2170813408096562557107425 := by
  unfold tailWord_4227644
  simp only [CollatzResearch.WordTrace]
  refine ⟨77097422147987643478516993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102796562863983524638022657 77097422147987643478516993)
  ·
    refine ⟨57823066610990732608887745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77097422147987643478516993 57823066610990732608887745)
    ·
      refine ⟨43367299958243049456665809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57823066610990732608887745 43367299958243049456665809)
      ·
        refine ⟨32525474968682287092499357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43367299958243049456665809 32525474968682287092499357)
        ·
          refine ⟨12197053113255857659687259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32525474968682287092499357 12197053113255857659687259)
          ·
            refine ⟨18295579669883786489530889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12197053113255857659687259 18295579669883786489530889)
            ·
              refine ⟨13721684752412839867148167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18295579669883786489530889 13721684752412839867148167)
              ·
                refine ⟨20582527128619259800722251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13721684752412839867148167 20582527128619259800722251)
                ·
                  refine ⟨30873790692928889701083377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20582527128619259800722251 30873790692928889701083377)
                  ·
                    refine ⟨23155343019696667275812533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30873790692928889701083377 23155343019696667275812533)
                    ·
                      refine ⟨2170813408096562557107425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23155343019696667275812533 2170813408096562557107425)
                      ·
                        rfl

theorem cell23_4227644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_4227644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227644 prefixEnd_4227644 := by exact prefixLift 4227644
  have htrace : WordTrace (prefixWord ++ tailWord_4227644) baseStart_4227644 baseEnd_4227644 := by
    simpa [prefixWord, tailWord_4227644, baseEnd_4227644] using wordTrace_append hprefix tailTrace_4227644
  have hstable : (prefixWord ++ tailWord_4227644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227644).length < 2 ^ (prefixWord ++ tailWord_4227644).sum := by decide
  have hdescent : baseEnd_4227644 < baseStart_4227644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227698 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_4227698 : Nat := 118140960795 + 4227698 * 2 ^ 59
def prefixEnd_4227698 : Nat := 4983230072969 + 3 ^ 40 * 4227698 * 2
def baseEnd_4227698 : Nat := 723613712017301781944059

theorem tailTrace_4227698 : CollatzResearch.WordTrace tailWord_4227698 prefixEnd_4227698 723613712017301781944059 := by
  unfold tailWord_4227698
  simp only [CollatzResearch.WordTrace]
  refine ⟨38549203459444913544874937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102797875891853102786333165 38549203459444913544874937)
  ·
    refine ⟨28911902594583685158656203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38549203459444913544874937 28911902594583685158656203)
    ·
      refine ⟨43367853891875527737984305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28911902594583685158656203 43367853891875527737984305)
      ·
        refine ⟨32525890418906645803488229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43367853891875527737984305 32525890418906645803488229)
        ·
          refine ⟨6098604453544996088154043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32525890418906645803488229 6098604453544996088154043)
          ·
            refine ⟨9147906680317494132231065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098604453544996088154043 9147906680317494132231065)
            ·
              refine ⟨6860930010238120599173299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9147906680317494132231065 6860930010238120599173299)
              ·
                refine ⟨10291395015357180898759949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6860930010238120599173299 10291395015357180898759949)
                ·
                  refine ⟨3859273130758942837034981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10291395015357180898759949 3859273130758942837034981)
                  ·
                    refine ⟨723613712017301781944059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3859273130758942837034981 723613712017301781944059)
                    ·
                      rfl

theorem cell23_4227698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_4227698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227698 prefixEnd_4227698 := by exact prefixLift 4227698
  have htrace : WordTrace (prefixWord ++ tailWord_4227698) baseStart_4227698 baseEnd_4227698 := by
    simpa [prefixWord, tailWord_4227698, baseEnd_4227698] using wordTrace_append hprefix tailTrace_4227698
  have hstable : (prefixWord ++ tailWord_4227698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227698).length < 2 ^ (prefixWord ++ tailWord_4227698).sum := by decide
  have hdescent : baseEnd_4227698 < baseStart_4227698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227707 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 9]
def baseStart_4227707 : Nat := 118140960795 + 4227707 * 2 ^ 59
def prefixEnd_4227707 : Nat := 4983230072969 + 3 ^ 40 * 4227707 * 2
def baseEnd_4227707 : Nat := 723615252459265270206545

theorem tailTrace_4227707 : CollatzResearch.WordTrace tailWord_4227707 prefixEnd_4227707 723615252459265270206545 := by
  unfold tailWord_4227707
  simp only [CollatzResearch.WordTrace]
  refine ⟨154197142094747048716577375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102798094729831365811051583 154197142094747048716577375)
  ·
    refine ⟨231295713142120573074866063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154197142094747048716577375 231295713142120573074866063)
    ·
      refine ⟨346943569713180859612299095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231295713142120573074866063 346943569713180859612299095)
      ·
        refine ⟨520415354569771289418448643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346943569713180859612299095 520415354569771289418448643)
        ·
          refine ⟨780623031854656934127672965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520415354569771289418448643 780623031854656934127672965)
          ·
            refine ⟨146366818472748175148938681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 780623031854656934127672965 146366818472748175148938681)
            ·
              refine ⟨109775113854561131361704011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146366818472748175148938681 109775113854561131361704011)
              ·
                refine ⟨164662670781841697042556017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109775113854561131361704011 164662670781841697042556017)
                ·
                  refine ⟨123497003086381272781917013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164662670781841697042556017 123497003086381272781917013)
                  ·
                    refine ⟨723615252459265270206545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123497003086381272781917013 723615252459265270206545)
                    ·
                      rfl

theorem cell23_4227707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 9].length) (baseStart_4227707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227707 prefixEnd_4227707 := by exact prefixLift 4227707
  have htrace : WordTrace (prefixWord ++ tailWord_4227707) baseStart_4227707 baseEnd_4227707 := by
    simpa [prefixWord, tailWord_4227707, baseEnd_4227707] using wordTrace_append hprefix tailTrace_4227707
  have hstable : (prefixWord ++ tailWord_4227707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227707).length < 2 ^ (prefixWord ++ tailWord_4227707).sum := by decide
  have hdescent : baseEnd_4227707 < baseStart_4227707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227732 : List Nat := [2, 4, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4227732 : Nat := 118140960795 + 4227732 * 2 ^ 59
def prefixEnd_4227732 : Nat := 4983230072969 + 3 ^ 40 * 4227732 * 2
def baseEnd_4227732 : Nat := 723619531464719404269007

theorem tailTrace_4227732 : CollatzResearch.WordTrace tailWord_4227732 prefixEnd_4227732 723619531464719404269007 := by
  unfold tailWord_4227732
  simp only [CollatzResearch.WordTrace]
  refine ⟨77099026959828238993118725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102798702613104318657491633 77099026959828238993118725)
  ·
    refine ⟨14456067554967794811209761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77099026959828238993118725 14456067554967794811209761)
    ·
      refine ⟨10842050666225846108407321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14456067554967794811209761 10842050666225846108407321)
      ·
        refine ⟨8131537999669384581305491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10842050666225846108407321 8131537999669384581305491)
        ·
          refine ⟨12197306999504076871958237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8131537999669384581305491 12197306999504076871958237)
          ·
            refine ⟨4573990124814028826984339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12197306999504076871958237 4573990124814028826984339)
            ·
              refine ⟨6860985187221043240476509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4573990124814028826984339 6860985187221043240476509)
              ·
                refine ⟨2572869445207891215178691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6860985187221043240476509 2572869445207891215178691)
                ·
                  refine ⟨3859304167811836822768037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572869445207891215178691 3859304167811836822768037)
                  ·
                    refine ⟨723619531464719404269007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3859304167811836822768037 723619531464719404269007)
                    ·
                      rfl

theorem cell23_4227732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4227732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227732 prefixEnd_4227732 := by exact prefixLift 4227732
  have htrace : WordTrace (prefixWord ++ tailWord_4227732) baseStart_4227732 baseEnd_4227732 := by
    simpa [prefixWord, tailWord_4227732, baseEnd_4227732] using wordTrace_append hprefix tailTrace_4227732
  have hstable : (prefixWord ++ tailWord_4227732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227732).length < 2 ^ (prefixWord ++ tailWord_4227732).sum := by decide
  have hdescent : baseEnd_4227732 < baseStart_4227732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227741 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_4227741 : Nat := 118140960795 + 4227741 * 2 ^ 59
def prefixEnd_4227741 : Nat := 4983230072969 + 3 ^ 40 * 4227741 * 2
def baseEnd_4227741 : Nat := 723621071906682892531493

theorem tailTrace_4227741 : CollatzResearch.WordTrace tailWord_4227741 prefixEnd_4227741 723621071906682892531493 := by
  unfold tailWord_4227741
  simp only [CollatzResearch.WordTrace]
  refine ⟨154198382176623872523315077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102798921451082581682210051 154198382176623872523315077)
  ·
    refine ⟨28912196658116976098121577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154198382176623872523315077 28912196658116976098121577)
    ·
      refine ⟨21684147493587732073591183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28912196658116976098121577 21684147493587732073591183)
      ·
        refine ⟨32526221240381598110386775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21684147493587732073591183 32526221240381598110386775)
        ·
          refine ⟨48789331860572397165580163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32526221240381598110386775 48789331860572397165580163)
          ·
            refine ⟨73183997790858595748370245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48789331860572397165580163 73183997790858595748370245)
            ·
              refine ⟨13721999585785986702819421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73183997790858595748370245 13721999585785986702819421)
              ·
                refine ⟨5145749844669745013557283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13721999585785986702819421 5145749844669745013557283)
                ·
                  refine ⟨7718624767004617520335925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5145749844669745013557283 7718624767004617520335925)
                  ·
                    refine ⟨723621071906682892531493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7718624767004617520335925 723621071906682892531493)
                    ·
                      rfl

theorem cell23_4227741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_4227741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227741 prefixEnd_4227741 := by exact prefixLift 4227741
  have htrace : WordTrace (prefixWord ++ tailWord_4227741) baseStart_4227741 baseEnd_4227741 := by
    simpa [prefixWord, tailWord_4227741, baseEnd_4227741] using wordTrace_append hprefix tailTrace_4227741
  have hstable : (prefixWord ++ tailWord_4227741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227741).length < 2 ^ (prefixWord ++ tailWord_4227741).sum := by decide
  have hdescent : baseEnd_4227741 < baseStart_4227741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227748 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_4227748 : Nat := 118140960795 + 4227748 * 2 ^ 59
def prefixEnd_4227748 : Nat := 4983230072969 + 3 ^ 40 * 4227748 * 2
def baseEnd_4227748 : Nat := 2170866810084630150206947

theorem tailTrace_4227748 : CollatzResearch.WordTrace tailWord_4227748 prefixEnd_4227748 2170866810084630150206947 := by
  unfold tailWord_4227748
  simp only [CollatzResearch.WordTrace]
  refine ⟨77099318743799256359409949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102799091658399008479213265 77099318743799256359409949)
  ·
    refine ⟨28912244528924721134778731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77099318743799256359409949 28912244528924721134778731)
    ·
      refine ⟨43368366793387081702168097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28912244528924721134778731 43368366793387081702168097)
      ·
        refine ⟨32526275095040311276626073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43368366793387081702168097 32526275095040311276626073)
        ·
          refine ⟨24394706321280233457469555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32526275095040311276626073 24394706321280233457469555)
          ·
            refine ⟨36592059481920350186204333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24394706321280233457469555 36592059481920350186204333)
            ·
              refine ⟨13722022305720131319826625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36592059481920350186204333 13722022305720131319826625)
              ·
                refine ⟨10291516729290098489869969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13722022305720131319826625 10291516729290098489869969)
                ·
                  refine ⟨7718637546967573867402477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10291516729290098489869969 7718637546967573867402477)
                  ·
                    refine ⟨2894489080112840200275929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7718637546967573867402477 2894489080112840200275929)
                    ·
                      refine ⟨2170866810084630150206947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894489080112840200275929 2170866810084630150206947)
                      ·
                        rfl

theorem cell23_4227748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_4227748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227748 prefixEnd_4227748 := by exact prefixLift 4227748
  have htrace : WordTrace (prefixWord ++ tailWord_4227748) baseStart_4227748 baseEnd_4227748 := by
    simpa [prefixWord, tailWord_4227748, baseEnd_4227748] using wordTrace_append hprefix tailTrace_4227748
  have hstable : (prefixWord ++ tailWord_4227748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227748).length < 2 ^ (prefixWord ++ tailWord_4227748).sum := by decide
  have hdescent : baseEnd_4227748 < baseStart_4227748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227784 : List Nat := [2, 1, 3, 1, 2, 3, 2, 9]
def baseStart_4227784 : Nat := 118140960795 + 4227784 * 2 ^ 59
def prefixEnd_4227784 : Nat := 4983230072969 + 3 ^ 40 * 4227784 * 2
def baseEnd_4227784 : Nat := 80403159088451555902103

theorem tailTrace_4227784 : CollatzResearch.WordTrace tailWord_4227784 prefixEnd_4227784 80403159088451555902103 := by
  unfold tailWord_4227784
  simp only [CollatzResearch.WordTrace]
  refine ⟨77099975257734045433565203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102799967010312060578086937 77099975257734045433565203)
  ·
    refine ⟨115649962886601068150347805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77099975257734045433565203 115649962886601068150347805)
    ·
      refine ⟨43368736082475400556380427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115649962886601068150347805 43368736082475400556380427)
      ·
        refine ⟨65053104123713100834570641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43368736082475400556380427 65053104123713100834570641)
        ·
          refine ⟨48789828092784825625927981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65053104123713100834570641 48789828092784825625927981)
          ·
            refine ⟨18296185534794309609722993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48789828092784825625927981 18296185534794309609722993)
            ·
              refine ⟨13722139151095732207292245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18296185534794309609722993 13722139151095732207292245)
              ·
                refine ⟨80403159088451555902103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13722139151095732207292245 80403159088451555902103)
                ·
                  rfl

theorem cell23_4227784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 9].length) (baseStart_4227784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227784 prefixEnd_4227784 := by exact prefixLift 4227784
  have htrace : WordTrace (prefixWord ++ tailWord_4227784) baseStart_4227784 baseEnd_4227784 := by
    simpa [prefixWord, tailWord_4227784, baseEnd_4227784] using wordTrace_append hprefix tailTrace_4227784
  have hstable : (prefixWord ++ tailWord_4227784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227784).length < 2 ^ (prefixWord ++ tailWord_4227784).sum := by decide
  have hdescent : baseEnd_4227784 < baseStart_4227784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227812 : List Nat := [2, 3, 1, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_4227812 : Nat := 118140960795 + 4227812 * 2 ^ 59
def prefixEnd_4227812 : Nat := 4983230072969 + 3 ^ 40 * 4227812 * 2
def baseEnd_4227812 : Nat := 2170899672846517899806653

theorem tailTrace_4227812 : CollatzResearch.WordTrace tailWord_4227812 prefixEnd_4227812 2170899672846517899806653 := by
  unfold tailWord_4227812
  simp only [CollatzResearch.WordTrace]
  refine ⟨77100485879683325824574845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102800647839577767766099793 77100485879683325824574845)
  ·
    refine ⟨28912682204881247184215567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77100485879683325824574845 28912682204881247184215567)
    ·
      refine ⟨43369023307321870776323351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28912682204881247184215567 43369023307321870776323351)
      ·
        refine ⟨65053534960982806164485027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43369023307321870776323351 65053534960982806164485027)
        ·
          refine ⟨97580302441474209246727541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65053534960982806164485027 97580302441474209246727541)
          ·
            refine ⟨9148153353888207116880707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97580302441474209246727541 9148153353888207116880707)
            ·
              refine ⟨13722230030832310675321061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9148153353888207116880707 13722230030832310675321061)
              ·
                refine ⟨2572918130781058251622699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13722230030832310675321061 2572918130781058251622699)
                ·
                  refine ⟨3859377196171587377434049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2572918130781058251622699 3859377196171587377434049)
                  ·
                    refine ⟨2894532897128690533075537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3859377196171587377434049 2894532897128690533075537)
                    ·
                      refine ⟨2170899672846517899806653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894532897128690533075537 2170899672846517899806653)
                      ·
                        rfl

theorem cell23_4227812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_4227812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227812 prefixEnd_4227812 := by exact prefixLift 4227812
  have htrace : WordTrace (prefixWord ++ tailWord_4227812) baseStart_4227812 baseEnd_4227812 := by
    simpa [prefixWord, tailWord_4227812, baseEnd_4227812] using wordTrace_append hprefix tailTrace_4227812
  have hstable : (prefixWord ++ tailWord_4227812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227812).length < 2 ^ (prefixWord ++ tailWord_4227812).sum := by decide
  have hdescent : baseEnd_4227812 < baseStart_4227812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227891 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 7]
def baseStart_4227891 : Nat := 118140960795 + 4227891 * 2 ^ 59
def prefixEnd_4227891 : Nat := 4983230072969 + 3 ^ 40 * 4227891 * 2
def baseEnd_4227891 : Nat := 241215581979802565635421

theorem tailTrace_4227891 : CollatzResearch.WordTrace tailWord_4227891 prefixEnd_4227891 241215581979802565635421 := by
  unfold tailWord_4227891
  simp only [CollatzResearch.WordTrace]
  refine ⟨154203853126080448141275527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102802568750720298760850351 154203853126080448141275527)
  ·
    refine ⟨231305779689120672211913291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154203853126080448141275527 231305779689120672211913291)
    ·
      refine ⟨346958669533681008317869937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231305779689120672211913291 346958669533681008317869937)
      ·
        refine ⟨260219002150260756238402453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346958669533681008317869937 260219002150260756238402453)
        ·
          refine ⟨12197765725793472948675115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 260219002150260756238402453 12197765725793472948675115)
          ·
            refine ⟨18296648588690209423012673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12197765725793472948675115 18296648588690209423012673)
            ·
              refine ⟨13722486441517657067259505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18296648588690209423012673 13722486441517657067259505)
              ·
                refine ⟨10291864831138242800444629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13722486441517657067259505 10291864831138242800444629)
                ·
                  refine ⟨241215581979802565635421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10291864831138242800444629 241215581979802565635421)
                  ·
                    rfl

theorem cell23_4227891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 7].length) (baseStart_4227891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227891 prefixEnd_4227891 := by exact prefixLift 4227891
  have htrace : WordTrace (prefixWord ++ tailWord_4227891) baseStart_4227891 baseEnd_4227891 := by
    simpa [prefixWord, tailWord_4227891, baseEnd_4227891] using wordTrace_append hprefix tailTrace_4227891
  have hstable : (prefixWord ++ tailWord_4227891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227891).length < 2 ^ (prefixWord ++ tailWord_4227891).sum := by decide
  have hdescent : baseEnd_4227891 < baseStart_4227891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227905 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4227905 : Nat := 118140960795 + 4227905 * 2 ^ 59
def prefixEnd_4227905 : Nat := 4983230072969 + 3 ^ 40 * 4227905 * 2
def baseEnd_4227905 : Nat := 2170947426547386035943725

theorem tailTrace_4227905 : CollatzResearch.WordTrace tailWord_4227905 prefixEnd_4227905 2170947426547386035943725 := by
  unfold tailWord_4227905
  simp only [CollatzResearch.WordTrace]
  refine ⟨154204363748029728532285169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102802909165353152354856779 154204363748029728532285169)
  ·
    refine ⟨115653272811022296399213877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154204363748029728532285169 115653272811022296399213877)
    ·
      refine ⟨10842494326033340287426301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115653272811022296399213877 10842494326033340287426301)
      ·
        refine ⟨4065935372262502607784863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10842494326033340287426301 4065935372262502607784863)
        ·
          refine ⟨6098903058393753911677295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4065935372262502607784863 6098903058393753911677295)
          ·
            refine ⟨9148354587590630867515943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6098903058393753911677295 9148354587590630867515943)
            ·
              refine ⟨13722531881385946301273915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9148354587590630867515943 13722531881385946301273915)
              ·
                refine ⟨20583797822078919451910873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13722531881385946301273915 20583797822078919451910873)
                ·
                  refine ⟨15437848366559189588933155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20583797822078919451910873 15437848366559189588933155)
                  ·
                    refine ⟨23156772549838784383399733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15437848366559189588933155 23156772549838784383399733)
                    ·
                      refine ⟨2170947426547386035943725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23156772549838784383399733 2170947426547386035943725)
                      ·
                        rfl

theorem cell23_4227905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4227905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227905 prefixEnd_4227905 := by exact prefixLift 4227905
  have htrace : WordTrace (prefixWord ++ tailWord_4227905) baseStart_4227905 baseEnd_4227905 := by
    simpa [prefixWord, tailWord_4227905, baseEnd_4227905] using wordTrace_append hprefix tailTrace_4227905
  have hstable : (prefixWord ++ tailWord_4227905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227905).length < 2 ^ (prefixWord ++ tailWord_4227905).sum := by decide
  have hdescent : baseEnd_4227905 < baseStart_4227905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227925 : List Nat := [1, 3, 2, 2, 2, 1, 5, 2, 5]
def baseStart_4227925 : Nat := 118140960795 + 4227925 * 2 ^ 59
def prefixEnd_4227925 : Nat := 4983230072969 + 3 ^ 40 * 4227925 * 2
def baseEnd_4227925 : Nat := 241217521795608439743737

theorem tailTrace_4227925 : CollatzResearch.WordTrace tailWord_4227925 prefixEnd_4227925 241217521795608439743737 := by
  unfold tailWord_4227925
  simp only [CollatzResearch.WordTrace]
  refine ⟨154205093207957271948013229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102803395471971514632008819 154205093207957271948013229)
  ·
    refine ⟨57826909952983976980504961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154205093207957271948013229 57826909952983976980504961)
    ·
      refine ⟨43370182464737982735378721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57826909952983976980504961 43370182464737982735378721)
      ·
        refine ⟨32527636848553487051534041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43370182464737982735378721 32527636848553487051534041)
        ·
          refine ⟨24395727636415115288650531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32527636848553487051534041 24395727636415115288650531)
          ·
            refine ⟨36593591454622672932975797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24395727636415115288650531 36593591454622672932975797)
            ·
              refine ⟨3430649198870875587466481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36593591454622672932975797 3430649198870875587466481)
              ·
                refine ⟨2572986899153156690599861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430649198870875587466481 2572986899153156690599861)
                ·
                  refine ⟨241217521795608439743737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572986899153156690599861 241217521795608439743737)
                  ·
                    rfl

theorem cell23_4227925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_4227925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227925 prefixEnd_4227925 := by exact prefixLift 4227925
  have htrace : WordTrace (prefixWord ++ tailWord_4227925) baseStart_4227925 baseEnd_4227925 := by
    simpa [prefixWord, tailWord_4227925, baseEnd_4227925] using wordTrace_append hprefix tailTrace_4227925
  have hstable : (prefixWord ++ tailWord_4227925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227925).length < 2 ^ (prefixWord ++ tailWord_4227925).sum := by decide
  have hdescent : baseEnd_4227925 < baseStart_4227925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227941 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4227941 : Nat := 118140960795 + 4227941 * 2 ^ 59
def prefixEnd_4227941 : Nat := 4983230072969 + 3 ^ 40 * 4227941 * 2
def baseEnd_4227941 : Nat := 2170965911850947895093559

theorem tailTrace_4227941 : CollatzResearch.WordTrace tailWord_4227941 prefixEnd_4227941 2170965911850947895093559 := by
  unfold tailWord_4227941
  simp only [CollatzResearch.WordTrace]
  refine ⟨154205676775899306680595677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102803784517266204453730451 154205676775899306680595677)
  ·
    refine ⟨57827128790962240005223379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154205676775899306680595677 57827128790962240005223379)
    ·
      refine ⟨86740693186443360007835069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57827128790962240005223379 86740693186443360007835069)
      ·
        refine ⟨32527759944916260002938151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86740693186443360007835069 32527759944916260002938151)
        ·
          refine ⟨48791639917374390004407227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32527759944916260002938151 48791639917374390004407227)
          ·
            refine ⟨73187459876061585006610841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48791639917374390004407227 73187459876061585006610841)
            ·
              refine ⟨54890594907046188754958131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73187459876061585006610841 54890594907046188754958131)
              ·
                refine ⟨82335892360569283132437197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54890594907046188754958131 82335892360569283132437197)
                ·
                  refine ⟨30875959635213481174663949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82335892360569283132437197 30875959635213481174663949)
                  ·
                    refine ⟨11578484863205055440498981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30875959635213481174663949 11578484863205055440498981)
                    ·
                      refine ⟨2170965911850947895093559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11578484863205055440498981 2170965911850947895093559)
                      ·
                        rfl

theorem cell23_4227941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4227941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227941 prefixEnd_4227941 := by exact prefixLift 4227941
  have htrace : WordTrace (prefixWord ++ tailWord_4227941) baseStart_4227941 baseEnd_4227941 := by
    simpa [prefixWord, tailWord_4227941, baseEnd_4227941] using wordTrace_append hprefix tailTrace_4227941
  have hstable : (prefixWord ++ tailWord_4227941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227941).length < 2 ^ (prefixWord ++ tailWord_4227941).sum := by decide
  have hdescent : baseEnd_4227941 < baseStart_4227941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4227971 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6]
def baseStart_4227971 : Nat := 118140960795 + 4227971 * 2 ^ 59
def prefixEnd_4227971 : Nat := 4983230072969 + 3 ^ 40 * 4227971 * 2
def baseEnd_4227971 : Nat := 2170981316270582777718421

theorem tailTrace_4227971 : CollatzResearch.WordTrace tailWord_4227971 prefixEnd_4227971 2170981316270582777718421 := by
  unfold tailWord_4227971
  simp only [CollatzResearch.WordTrace]
  refine ⟨154206770965790621804187767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102804513977193747869458511 154206770965790621804187767)
  ·
    refine ⟨231310156448685932706281651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154206770965790621804187767 231310156448685932706281651)
    ·
      refine ⟨346965234673028899059422477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231310156448685932706281651 346965234673028899059422477)
      ·
        refine ⟨130111963002385837147283429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346965234673028899059422477 130111963002385837147283429)
        ·
          refine ⟨24395993062947344465115643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130111963002385837147283429 24395993062947344465115643)
          ·
            refine ⟨36593989594421016697673465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24395993062947344465115643 36593989594421016697673465)
            ·
              refine ⟨27445492195815762523255099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36593989594421016697673465 27445492195815762523255099)
              ·
                refine ⟨41168238293723643784882649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27445492195815762523255099 41168238293723643784882649)
                ·
                  refine ⟨30876178720292732838661987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41168238293723643784882649 30876178720292732838661987)
                  ·
                    refine ⟨46314268080439099257992981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30876178720292732838661987 46314268080439099257992981)
                    ·
                      refine ⟨2170981316270582777718421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46314268080439099257992981 2170981316270582777718421)
                      ·
                        rfl

theorem cell23_4227971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_4227971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4227971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4227971 prefixEnd_4227971 := by exact prefixLift 4227971
  have htrace : WordTrace (prefixWord ++ tailWord_4227971) baseStart_4227971 baseEnd_4227971 := by
    simpa [prefixWord, tailWord_4227971, baseEnd_4227971] using wordTrace_append hprefix tailTrace_4227971
  have hstable : (prefixWord ++ tailWord_4227971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4227971).length < 2 ^ (prefixWord ++ tailWord_4227971).sum := by decide
  have hdescent : baseEnd_4227971 < baseStart_4227971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4227971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228119 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4228119 : Nat := 118140960795 + 4228119 * 2 ^ 59
def prefixEnd_4228119 : Nat := 4983230072969 + 3 ^ 40 * 4228119 * 2
def baseEnd_4228119 : Nat := 2171057311407448198667741

theorem tailTrace_4228119 : CollatzResearch.WordTrace tailWord_4228119 prefixEnd_4228119 2171057311407448198667741 := by
  unfold tailWord_4228119
  simp only [CollatzResearch.WordTrace]
  refine ⟨154212168969254443080575411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102808112646169628720383607 154212168969254443080575411)
  ·
    refine ⟨231318253453881664620863117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154212168969254443080575411 231318253453881664620863117)
    ·
      refine ⟨86744345045205624232823669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231318253453881664620863117 86744345045205624232823669)
      ·
        refine ⟨8132282347988027271827219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86744345045205624232823669 8132282347988027271827219)
        ·
          refine ⟨12198423521982040907740829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8132282347988027271827219 12198423521982040907740829)
          ·
            refine ⟨4574408820743265340402811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12198423521982040907740829 4574408820743265340402811)
            ·
              refine ⟨6861613231114898010604217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574408820743265340402811 6861613231114898010604217)
              ·
                refine ⟨5146209923336173507953163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6861613231114898010604217 5146209923336173507953163)
                ·
                  refine ⟨7719314885004260261929745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5146209923336173507953163 7719314885004260261929745)
                  ·
                    refine ⟨5789486163753195196447309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7719314885004260261929745 5789486163753195196447309)
                    ·
                      refine ⟨2171057311407448198667741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5789486163753195196447309 2171057311407448198667741)
                      ·
                        rfl

theorem cell23_4228119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4228119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228119 prefixEnd_4228119 := by exact prefixLift 4228119
  have htrace : WordTrace (prefixWord ++ tailWord_4228119) baseStart_4228119 baseEnd_4228119 := by
    simpa [prefixWord, tailWord_4228119, baseEnd_4228119] using wordTrace_append hprefix tailTrace_4228119
  have hstable : (prefixWord ++ tailWord_4228119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228119).length < 2 ^ (prefixWord ++ tailWord_4228119).sum := by decide
  have hdescent : baseEnd_4228119 < baseStart_4228119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228132 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4228132 : Nat := 118140960795 + 4228132 * 2 ^ 59
def prefixEnd_4228132 : Nat := 4983230072969 + 3 ^ 40 * 4228132 * 2
def baseEnd_4228132 : Nat := 2171063986655956647805181

theorem tailTrace_4228132 : CollatzResearch.WordTrace tailWord_4228132 prefixEnd_4228132 2171063986655956647805181 := by
  unfold tailWord_4228132
  simp only [CollatzResearch.WordTrace]
  refine ⟨77106321559103673150399325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102808428745471564200532433 77106321559103673150399325)
  ·
    refine ⟨28914870584663877431399747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77106321559103673150399325 28914870584663877431399747)
    ·
      refine ⟨43372305876995816147099621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28914870584663877431399747 43372305876995816147099621)
      ·
        refine ⟨8132307351936715527581179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43372305876995816147099621 8132307351936715527581179)
        ·
          refine ⟨12198461027905073291371769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8132307351936715527581179 12198461027905073291371769)
          ·
            refine ⟨9148845770928804968528827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12198461027905073291371769 9148845770928804968528827)
            ·
              refine ⟨13723268656393207452793241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9148845770928804968528827 13723268656393207452793241)
              ·
                refine ⟨10292451492294905589594931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13723268656393207452793241 10292451492294905589594931)
                ·
                  refine ⟨15438677238442358384392397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10292451492294905589594931 15438677238442358384392397)
                  ·
                    refine ⟨5789503964415884394147149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15438677238442358384392397 5789503964415884394147149)
                    ·
                      refine ⟨2171063986655956647805181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5789503964415884394147149 2171063986655956647805181)
                      ·
                        rfl

theorem cell23_4228132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4228132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228132 prefixEnd_4228132 := by exact prefixLift 4228132
  have htrace : WordTrace (prefixWord ++ tailWord_4228132) baseStart_4228132 baseEnd_4228132 := by
    simpa [prefixWord, tailWord_4228132, baseEnd_4228132] using wordTrace_append hprefix tailTrace_4228132
  have hstable : (prefixWord ++ tailWord_4228132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228132).length < 2 ^ (prefixWord ++ tailWord_4228132).sum := by decide
  have hdescent : baseEnd_4228132 < baseStart_4228132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228150 : List Nat := [5, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_4228150 : Nat := 118140960795 + 4228150 * 2 ^ 59
def prefixEnd_4228150 : Nat := 4983230072969 + 3 ^ 40 * 4228150 * 2
def baseEnd_4228150 : Nat := 2171073229307737577380099

theorem tailTrace_4228150 : CollatzResearch.WordTrace tailWord_4228150 prefixEnd_4228150 2171073229307737577380099 := by
  unfold tailWord_4228150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9638331227008883460934619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102808866421428090249969269 9638331227008883460934619)
  ·
    refine ⟨14457496840513325191401929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9638331227008883460934619 14457496840513325191401929)
    ·
      refine ⟨10843122630384993893551447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14457496840513325191401929 10843122630384993893551447)
      ·
        refine ⟨16264683945577490840327171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10843122630384993893551447 16264683945577490840327171)
        ·
          refine ⟨24397025918366236260490757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16264683945577490840327171 24397025918366236260490757)
          ·
            refine ⟨4574442359693669298842017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24397025918366236260490757 4574442359693669298842017)
            ·
              refine ⟨3430831769770251974131513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574442359693669298842017 3430831769770251974131513)
              ·
                refine ⟨2573123827327688980598635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3430831769770251974131513 2573123827327688980598635)
                ·
                  refine ⟨3859685740991533470897953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573123827327688980598635 3859685740991533470897953)
                  ·
                    refine ⟨2894764305743650103173465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3859685740991533470897953 2894764305743650103173465)
                    ·
                      refine ⟨2171073229307737577380099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894764305743650103173465 2171073229307737577380099)
                      ·
                        rfl

theorem cell23_4228150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_4228150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228150 prefixEnd_4228150 := by exact prefixLift 4228150
  have htrace : WordTrace (prefixWord ++ tailWord_4228150) baseStart_4228150 baseEnd_4228150 := by
    simpa [prefixWord, tailWord_4228150, baseEnd_4228150] using wordTrace_append hprefix tailTrace_4228150
  have hstable : (prefixWord ++ tailWord_4228150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228150).length < 2 ^ (prefixWord ++ tailWord_4228150).sum := by decide
  have hdescent : baseEnd_4228150 < baseStart_4228150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228166 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4228166 : Nat := 118140960795 + 4228166 * 2 ^ 59
def prefixEnd_4228166 : Nat := 4983230072969 + 3 ^ 40 * 4228166 * 2
def baseEnd_4228166 : Nat := 2171081444998209514780025

theorem tailTrace_4228166 : CollatzResearch.WordTrace tailWord_4228166 prefixEnd_4228166 2171081444998209514780025 := by
  unfold tailWord_4228166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4819183850002630315860511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102809255466722780071690901 4819183850002630315860511)
  ·
    refine ⟨7228775775003945473790767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4819183850002630315860511 7228775775003945473790767)
    ·
      refine ⟨10843163662505918210686151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7228775775003945473790767 10843163662505918210686151)
      ·
        refine ⟨16264745493758877316029227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10843163662505918210686151 16264745493758877316029227)
        ·
          refine ⟨24397118240638315974043841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16264745493758877316029227 24397118240638315974043841)
          ·
            refine ⟨18297838680478736980532881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24397118240638315974043841 18297838680478736980532881)
            ·
              refine ⟨13723379010359052735399661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18297838680478736980532881 13723379010359052735399661)
              ·
                refine ⟨5146267128884644775774873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13723379010359052735399661 5146267128884644775774873)
                ·
                  refine ⟨3859700346663483581831155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5146267128884644775774873 3859700346663483581831155)
                  ·
                    refine ⟨5789550519995225372746733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3859700346663483581831155 5789550519995225372746733)
                    ·
                      refine ⟨2171081444998209514780025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5789550519995225372746733 2171081444998209514780025)
                      ·
                        rfl

theorem cell23_4228166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4228166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228166 prefixEnd_4228166 := by exact prefixLift 4228166
  have htrace : WordTrace (prefixWord ++ tailWord_4228166) baseStart_4228166 baseEnd_4228166 := by
    simpa [prefixWord, tailWord_4228166, baseEnd_4228166] using wordTrace_append hprefix tailTrace_4228166
  have hstable : (prefixWord ++ tailWord_4228166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228166).length < 2 ^ (prefixWord ++ tailWord_4228166).sum := by decide
  have hdescent : baseEnd_4228166 < baseStart_4228166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228172 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 6, 2, 2]
def baseStart_4228172 : Nat := 118140960795 + 4228172 * 2 ^ 59
def prefixEnd_4228172 : Nat := 4983230072969 + 3 ^ 40 * 4228172 * 2
def baseEnd_4228172 : Nat := 2171084525882136491304997

theorem tailTrace_4228172 : CollatzResearch.WordTrace tailWord_4228172 prefixEnd_4228172 2171084525882136491304997 := by
  unfold tailWord_4228172
  simp only [CollatzResearch.WordTrace]
  refine ⟨77107051019031216566127385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102809401358708288754836513 77107051019031216566127385)
  ·
    refine ⟨57830288264273412424595539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77107051019031216566127385 57830288264273412424595539)
    ·
      refine ⟨86745432396410118636893309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57830288264273412424595539 86745432396410118636893309)
      ·
        refine ⟨32529537148653794488834991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86745432396410118636893309 32529537148653794488834991)
        ·
          refine ⟨48794305722980691733252487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32529537148653794488834991 48794305722980691733252487)
          ·
            refine ⟨73191458584471037599878731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48794305722980691733252487 73191458584471037599878731)
            ·
              refine ⟨109787187876706556399818097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73191458584471037599878731 109787187876706556399818097)
              ·
                refine ⟨82340390907529917299863573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109787187876706556399818097 82340390907529917299863573)
                ·
                  refine ⟨3859705823790464873431105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82340390907529917299863573 3859705823790464873431105)
                  ·
                    refine ⟨2894779367842848655073329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3859705823790464873431105 2894779367842848655073329)
                    ·
                      refine ⟨2171084525882136491304997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894779367842848655073329 2171084525882136491304997)
                      ·
                        rfl

theorem cell23_4228172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_4228172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228172 prefixEnd_4228172 := by exact prefixLift 4228172
  have htrace : WordTrace (prefixWord ++ tailWord_4228172) baseStart_4228172 baseEnd_4228172 := by
    simpa [prefixWord, tailWord_4228172, baseEnd_4228172] using wordTrace_append hprefix tailTrace_4228172
  have hstable : (prefixWord ++ tailWord_4228172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228172).length < 2 ^ (prefixWord ++ tailWord_4228172).sum := by decide
  have hdescent : baseEnd_4228172 < baseStart_4228172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228206 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_4228206 : Nat := 118140960795 + 4228206 * 2 ^ 59
def prefixEnd_4228206 : Nat := 4983230072969 + 3 ^ 40 * 4228206 * 2
def baseEnd_4228206 : Nat := 2171101984224389358279841

theorem tailTrace_4228206 : CollatzResearch.WordTrace tailWord_4228206 prefixEnd_4228206 2171101984224389358279841 := by
  unfold tailWord_4228206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19276917764992407117374059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102810228079959504625994981 19276917764992407117374059)
  ·
    refine ⟨28915376647488610676061089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19276917764992407117374059 28915376647488610676061089)
    ·
      refine ⟨21686532485616458007045817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28915376647488610676061089 21686532485616458007045817)
      ·
        refine ⟨16264899364212343505284363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21686532485616458007045817 16264899364212343505284363)
        ·
          refine ⟨24397349046318515257926545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16264899364212343505284363 24397349046318515257926545)
          ·
            refine ⟨18298011784738886443444909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24397349046318515257926545 18298011784738886443444909)
            ·
              refine ⟨6861754419277082416291841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18298011784738886443444909 6861754419277082416291841)
              ·
                refine ⟨5146315814457811812218881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6861754419277082416291841 5146315814457811812218881)
                ·
                  refine ⟨3859736860843358859164161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5146315814457811812218881 3859736860843358859164161)
                  ·
                    refine ⟨2894802645632519144373121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3859736860843358859164161 2894802645632519144373121)
                    ·
                      refine ⟨2171101984224389358279841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894802645632519144373121 2171101984224389358279841)
                      ·
                        rfl

theorem cell23_4228206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_4228206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228206 prefixEnd_4228206 := by exact prefixLift 4228206
  have htrace : WordTrace (prefixWord ++ tailWord_4228206) baseStart_4228206 baseEnd_4228206 := by
    simpa [prefixWord, tailWord_4228206, baseEnd_4228206] using wordTrace_append hprefix tailTrace_4228206
  have hstable : (prefixWord ++ tailWord_4228206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228206).length < 2 ^ (prefixWord ++ tailWord_4228206).sum := by decide
  have hdescent : baseEnd_4228206 < baseStart_4228206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228225 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 1, 7]
def baseStart_4228225 : Nat := 118140960795 + 4228225 * 2 ^ 59
def prefixEnd_4228225 : Nat := 4983230072969 + 3 ^ 40 * 4228225 * 2
def baseEnd_4228225 : Nat := 723703913452274927980751

theorem tailTrace_4228225 : CollatzResearch.WordTrace tailWord_4228225 prefixEnd_4228225 723703913452274927980751 := by
  unfold tailWord_4228225
  simp only [CollatzResearch.WordTrace]
  refine ⟨154216035106870423183934129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102810690071246948789289419 154216035106870423183934129)
  ·
    refine ⟨115662026330152817387950597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154216035106870423183934129 115662026330152817387950597)
    ·
      refine ⟨21686629936903653260240737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115662026330152817387950597 21686629936903653260240737)
      ·
        refine ⟨16264972452677739945180553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21686629936903653260240737 16264972452677739945180553)
        ·
          refine ⟨12198729339508304958885415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16264972452677739945180553 12198729339508304958885415)
          ·
            refine ⟨18298094009262457438328123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12198729339508304958885415 18298094009262457438328123)
            ·
              refine ⟨27447141013893686157492185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18298094009262457438328123 27447141013893686157492185)
              ·
                refine ⟨20585355760420264618119139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27447141013893686157492185 20585355760420264618119139)
                ·
                  refine ⟨30878033640630396927178709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20585355760420264618119139 30878033640630396927178709)
                  ·
                    refine ⟨723703913452274927980751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30878033640630396927178709 723703913452274927980751)
                    ·
                      rfl

theorem cell23_4228225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_4228225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228225 prefixEnd_4228225 := by exact prefixLift 4228225
  have htrace : WordTrace (prefixWord ++ tailWord_4228225) baseStart_4228225 baseEnd_4228225 := by
    simpa [prefixWord, tailWord_4228225, baseEnd_4228225] using wordTrace_append hprefix tailTrace_4228225
  have hstable : (prefixWord ++ tailWord_4228225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228225).length < 2 ^ (prefixWord ++ tailWord_4228225).sum := by decide
  have hdescent : baseEnd_4228225 < baseStart_4228225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228295 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_4228295 : Nat := 118140960795 + 4228295 * 2 ^ 59
def prefixEnd_4228295 : Nat := 4983230072969 + 3 ^ 40 * 4228295 * 2
def baseEnd_4228295 : Nat := 2171147684002639510066931

theorem tailTrace_4228295 : CollatzResearch.WordTrace tailWord_4228295 prefixEnd_4228295 2171147684002639510066931 := by
  unfold tailWord_4228295
  simp only [CollatzResearch.WordTrace]
  refine ⟨154218588216616825138982339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102812392144411216759321559 154218588216616825138982339)
  ·
    refine ⟨231327882324925237708473509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154218588216616825138982339 231327882324925237708473509)
    ·
      refine ⟨43373977935923482070338783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231327882324925237708473509 43373977935923482070338783)
      ·
        refine ⟨65060966903885223105508175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43373977935923482070338783 65060966903885223105508175)
        ·
          refine ⟨97591450355827834658262263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65060966903885223105508175 97591450355827834658262263)
          ·
            refine ⟨146387175533741751987393395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97591450355827834658262263 146387175533741751987393395)
            ·
              refine ⟨219580763300612627981090093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146387175533741751987393395 219580763300612627981090093)
              ·
                refine ⟨82342786237729735492908785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219580763300612627981090093 82342786237729735492908785)
                ·
                  refine ⟨61757089678297301619681589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82342786237729735492908785 61757089678297301619681589)
                  ·
                    refine ⟨5789727157340372026845149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61757089678297301619681589 5789727157340372026845149)
                    ·
                      refine ⟨2171147684002639510066931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5789727157340372026845149 2171147684002639510066931)
                      ·
                        rfl

theorem cell23_4228295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_4228295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228295 prefixEnd_4228295 := by exact prefixLift 4228295
  have htrace : WordTrace (prefixWord ++ tailWord_4228295) baseStart_4228295 baseEnd_4228295 := by
    simpa [prefixWord, tailWord_4228295, baseEnd_4228295] using wordTrace_append hprefix tailTrace_4228295
  have hstable : (prefixWord ++ tailWord_4228295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228295).length < 2 ^ (prefixWord ++ tailWord_4228295).sum := by decide
  have hdescent : baseEnd_4228295 < baseStart_4228295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228352 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4]
def baseStart_4228352 : Nat := 118140960795 + 4228352 * 2 ^ 59
def prefixEnd_4228352 : Nat := 4983230072969 + 3 ^ 40 * 4228352 * 2
def baseEnd_4228352 : Nat := 2171176952399945787054169

theorem tailTrace_4228352 : CollatzResearch.WordTrace tailWord_4228352 prefixEnd_4228352 2171176952399945787054169 := by
  unfold tailWord_4228352
  simp only [CollatzResearch.WordTrace]
  refine ⟨77110333588705161936903655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102813778118273549249204873 77110333588705161936903655)
  ·
    refine ⟨115665500383057742905355483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77110333588705161936903655 115665500383057742905355483)
    ·
      refine ⟨173498250574586614358033225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115665500383057742905355483 173498250574586614358033225)
      ·
        refine ⟨130123687930939960768524919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173498250574586614358033225 130123687930939960768524919)
        ·
          refine ⟨195185531896409941152787379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130123687930939960768524919 195185531896409941152787379)
          ·
            refine ⟨292778297844614911729181069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195185531896409941152787379 292778297844614911729181069)
            ·
              refine ⟨109791861691730591898442901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292778297844614911729181069 109791861691730591898442901)
              ·
                refine ⟨5146493516799871495239511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109791861691730591898442901 5146493516799871495239511)
                ·
                  refine ⟨7719740275199807242859267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5146493516799871495239511 7719740275199807242859267)
                  ·
                    refine ⟨11579610412799710864288901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7719740275199807242859267 11579610412799710864288901)
                    ·
                      refine ⟨2171176952399945787054169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11579610412799710864288901 2171176952399945787054169)
                      ·
                        rfl

theorem cell23_4228352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_4228352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228352 prefixEnd_4228352 := by exact prefixLift 4228352
  have htrace : WordTrace (prefixWord ++ tailWord_4228352) baseStart_4228352 baseEnd_4228352 := by
    simpa [prefixWord, tailWord_4228352, baseEnd_4228352] using wordTrace_append hprefix tailTrace_4228352
  have hstable : (prefixWord ++ tailWord_4228352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228352).length < 2 ^ (prefixWord ++ tailWord_4228352).sum := by decide
  have hdescent : baseEnd_4228352 < baseStart_4228352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228356 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_4228356 : Nat := 118140960795 + 4228356 * 2 ^ 59
def prefixEnd_4228356 : Nat := 4983230072969 + 3 ^ 40 * 4228356 * 2
def baseEnd_4228356 : Nat := 2171179006322563771404151

theorem tailTrace_4228356 : CollatzResearch.WordTrace tailWord_4228356 prefixEnd_4228356 2171179006322563771404151 := by
  unfold tailWord_4228356
  simp only [CollatzResearch.WordTrace]
  refine ⟨77110406534697916278476461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102813875379597221704635281 77110406534697916278476461)
  ·
    refine ⟨28916402450511718604428673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77110406534697916278476461 28916402450511718604428673)
    ·
      refine ⟨21687301837883788953321505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28916402450511718604428673 21687301837883788953321505)
      ·
        refine ⟨16265476378412841714991129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21687301837883788953321505 16265476378412841714991129)
        ·
          refine ⟨12199107283809631286243347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16265476378412841714991129 12199107283809631286243347)
          ·
            refine ⟨18298660925714446929365021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12199107283809631286243347 18298660925714446929365021)
            ·
              refine ⟨6861997847142917598511883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18298660925714446929365021 6861997847142917598511883)
              ·
                refine ⟨10292996770714376397767825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6861997847142917598511883 10292996770714376397767825)
                ·
                  refine ⟨7719747578035782298325869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10292996770714376397767825 7719747578035782298325869)
                  ·
                    refine ⟨2894905341763418361872201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7719747578035782298325869 2894905341763418361872201)
                    ·
                      refine ⟨2171179006322563771404151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894905341763418361872201 2171179006322563771404151)
                      ·
                        rfl

theorem cell23_4228356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_4228356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228356 prefixEnd_4228356 := by exact prefixLift 4228356
  have htrace : WordTrace (prefixWord ++ tailWord_4228356) baseStart_4228356 baseEnd_4228356 := by
    simpa [prefixWord, tailWord_4228356, baseEnd_4228356] using wordTrace_append hprefix tailTrace_4228356
  have hstable : (prefixWord ++ tailWord_4228356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228356).length < 2 ^ (prefixWord ++ tailWord_4228356).sum := by decide
  have hdescent : baseEnd_4228356 < baseStart_4228356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228362 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_4228362 : Nat := 118140960795 + 4228362 * 2 ^ 59
def prefixEnd_4228362 : Nat := 4983230072969 + 3 ^ 40 * 4228362 * 2
def baseEnd_4228362 : Nat := 723727362402163582643041

theorem tailTrace_4228362 : CollatzResearch.WordTrace tailWord_4228362 prefixEnd_4228362 723727362402163582643041 := by
  unfold tailWord_4228362
  simp only [CollatzResearch.WordTrace]
  refine ⟨38555257976843523895417835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102814021271582730387780893 38555257976843523895417835)
  ·
    refine ⟨57832886965265285843126753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38555257976843523895417835 57832886965265285843126753)
    ·
      refine ⟨43374665223948964382345065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57832886965265285843126753 43374665223948964382345065)
      ·
        refine ⟨32530998917961723286758799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43374665223948964382345065 32530998917961723286758799)
        ·
          refine ⟨48796498376942584930138199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32530998917961723286758799 48796498376942584930138199)
          ·
            refine ⟨73194747565413877395207299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48796498376942584930138199 73194747565413877395207299)
            ·
              refine ⟨109792121348120816092810949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73194747565413877395207299 109792121348120816092810949)
              ·
                refine ⟨20586022752772653017402053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109792121348120816092810949 20586022752772653017402053)
                ·
                  refine ⟨3859879266144872440762885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20586022752772653017402053 3859879266144872440762885)
                  ·
                    refine ⟨723727362402163582643041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3859879266144872440762885 723727362402163582643041)
                    ·
                      rfl

theorem cell23_4228362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_4228362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228362 prefixEnd_4228362 := by exact prefixLift 4228362
  have htrace : WordTrace (prefixWord ++ tailWord_4228362) baseStart_4228362 baseEnd_4228362 := by
    simpa [prefixWord, tailWord_4228362, baseEnd_4228362] using wordTrace_append hprefix tailTrace_4228362
  have hstable : (prefixWord ++ tailWord_4228362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228362).length < 2 ^ (prefixWord ++ tailWord_4228362).sum := by decide
  have hdescent : baseEnd_4228362 < baseStart_4228362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228366 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_4228366 : Nat := 118140960795 + 4228366 * 2 ^ 59
def prefixEnd_4228366 : Nat := 4983230072969 + 3 ^ 40 * 4228366 * 2
def baseEnd_4228366 : Nat := 723728047043036244093035

theorem tailTrace_4228366 : CollatzResearch.WordTrace tailWord_4228366 prefixEnd_4228366 723728047043036244093035 := by
  unfold tailWord_4228366
  simp only [CollatzResearch.WordTrace]
  refine ⟨19277647224919950533102119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102814118532906402843211301 19277647224919950533102119)
  ·
    refine ⟨28916470837379925799653179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19277647224919950533102119 28916470837379925799653179)
    ·
      refine ⟨43374706256069888699479769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28916470837379925799653179 43374706256069888699479769)
      ·
        refine ⟨32531029692052416524609827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43374706256069888699479769 32531029692052416524609827)
        ·
          refine ⟨48796544538078624786914741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32531029692052416524609827 48796544538078624786914741)
          ·
            refine ⟨4574676050444871073773257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48796544538078624786914741 4574676050444871073773257)
            ·
              refine ⟨3431007037833653305329943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4574676050444871073773257 3431007037833653305329943)
              ·
                refine ⟨5146510556750479957994915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431007037833653305329943 5146510556750479957994915)
                ·
                  refine ⟨7719765835125719936992373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5146510556750479957994915 7719765835125719936992373)
                  ·
                    refine ⟨723728047043036244093035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7719765835125719936992373 723728047043036244093035)
                    ·
                      rfl

theorem cell23_4228366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_4228366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228366 prefixEnd_4228366 := by exact prefixLift 4228366
  have htrace : WordTrace (prefixWord ++ tailWord_4228366) baseStart_4228366 baseEnd_4228366 := by
    simpa [prefixWord, tailWord_4228366, baseEnd_4228366] using wordTrace_append hprefix tailTrace_4228366
  have hstable : (prefixWord ++ tailWord_4228366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228366).length < 2 ^ (prefixWord ++ tailWord_4228366).sum := by decide
  have hdescent : baseEnd_4228366 < baseStart_4228366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228369 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 5, 2, 2]
def baseStart_4228369 : Nat := 118140960795 + 4228369 * 2 ^ 59
def prefixEnd_4228369 : Nat := 4983230072969 + 3 ^ 40 * 4228369 * 2
def baseEnd_4228369 : Nat := 2171185681571072220541591

theorem tailTrace_4228369 : CollatzResearch.WordTrace tailWord_4228369 prefixEnd_4228369 2171185681571072220541591 := by
  unfold tailWord_4228369
  simp only [CollatzResearch.WordTrace]
  refine ⟨154221287218348735777176161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102814191478899157184784107 154221287218348735777176161)
  ·
    refine ⟨115665965413761551832882121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154221287218348735777176161 115665965413761551832882121)
    ·
      refine ⟨86749474060321163874661591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115665965413761551832882121 86749474060321163874661591)
      ·
        refine ⟨130124211090481745811992387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86749474060321163874661591 130124211090481745811992387)
        ·
          refine ⟨195186316635722618717988581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130124211090481745811992387 195186316635722618717988581)
          ·
            refine ⟨36597434369197991009622859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195186316635722618717988581 36597434369197991009622859)
            ·
              refine ⟨54896151553796986514434289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36597434369197991009622859 54896151553796986514434289)
              ·
                refine ⟨41172113665347739885825717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54896151553796986514434289 41172113665347739885825717)
                ·
                  refine ⟨3859885656126350614296161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41172113665347739885825717 3859885656126350614296161)
                  ·
                    refine ⟨2894914242094762960722121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3859885656126350614296161 2894914242094762960722121)
                    ·
                      refine ⟨2171185681571072220541591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2894914242094762960722121 2171185681571072220541591)
                      ·
                        rfl

theorem cell23_4228369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_4228369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228369 prefixEnd_4228369 := by exact prefixLift 4228369
  have htrace : WordTrace (prefixWord ++ tailWord_4228369) baseStart_4228369 baseEnd_4228369 := by
    simpa [prefixWord, tailWord_4228369, baseEnd_4228369] using wordTrace_append hprefix tailTrace_4228369
  have hstable : (prefixWord ++ tailWord_4228369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228369).length < 2 ^ (prefixWord ++ tailWord_4228369).sum := by decide
  have hdescent : baseEnd_4228369 < baseStart_4228369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228375 : List Nat := [1, 1, 3, 4, 1, 1, 12]
def baseStart_4228375 : Nat := 118140960795 + 4228375 * 2 ^ 59
def prefixEnd_4228375 : Nat := 4983230072969 + 3 ^ 40 * 4228375 * 2
def baseEnd_4228375 : Nat := 26804799536481471568723

theorem tailTrace_4228375 : CollatzResearch.WordTrace tailWord_4228375 prefixEnd_4228375 26804799536481471568723 := by
  unfold tailWord_4228375
  simp only [CollatzResearch.WordTrace]
  refine ⟨154221506056326998801894579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102814337370884665867929719 154221506056326998801894579)
  ·
    refine ⟨231332259084490498202841869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154221506056326998801894579 231332259084490498202841869)
    ·
      refine ⟨86749597156683936826065701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231332259084490498202841869 86749597156683936826065701)
      ·
        refine ⟨16265549466878238154887319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86749597156683936826065701 16265549466878238154887319)
        ·
          refine ⟨24398324200317357232330979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16265549466878238154887319 24398324200317357232330979)
          ·
            refine ⟨36597486300476035848496469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24398324200317357232330979 36597486300476035848496469)
            ·
              refine ⟨26804799536481471568723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 36597486300476035848496469 26804799536481471568723)
              ·
                rfl

theorem cell23_4228375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 12].length) (baseStart_4228375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228375 prefixEnd_4228375 := by exact prefixLift 4228375
  have htrace : WordTrace (prefixWord ++ tailWord_4228375) baseStart_4228375 baseEnd_4228375 := by
    simpa [prefixWord, tailWord_4228375, baseEnd_4228375] using wordTrace_append hprefix tailTrace_4228375
  have hstable : (prefixWord ++ tailWord_4228375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228375).length < 2 ^ (prefixWord ++ tailWord_4228375).sum := by decide
  have hdescent : baseEnd_4228375 < baseStart_4228375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228385 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_4228385 : Nat := 118140960795 + 4228385 * 2 ^ 59
def prefixEnd_4228385 : Nat := 4983230072969 + 3 ^ 40 * 4228385 * 2
def baseEnd_4228385 : Nat := 2171193897261544157941517

theorem tailTrace_4228385 : CollatzResearch.WordTrace tailWord_4228385 prefixEnd_4228385 2171193897261544157941517 := by
  unfold tailWord_4228385
  simp only [CollatzResearch.WordTrace]
  refine ⟨154221870786290770509758609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102814580524193847006505739 154221870786290770509758609)
  ·
    refine ⟨115666403089718077882318957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154221870786290770509758609 115666403089718077882318957)
    ·
      refine ⟨43374901158644279205869609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115666403089718077882318957 43374901158644279205869609)
      ·
        refine ⟨32531175868983209404402207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43374901158644279205869609 32531175868983209404402207)
        ·
          refine ⟨48796763803474814106603311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32531175868983209404402207 48796763803474814106603311)
          ·
            refine ⟨73195145705212221159904967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48796763803474814106603311 73195145705212221159904967)
            ·
              refine ⟨109792718557818331739857451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73195145705212221159904967 109792718557818331739857451)
              ·
                refine ⟨164689077836727497609786177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109792718557818331739857451 164689077836727497609786177)
                ·
                  refine ⟨123516808377545623207339633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164689077836727497609786177 123516808377545623207339633)
                  ·
                    refine ⟨92637606283159217405504725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123516808377545623207339633 92637606283159217405504725)
                    ·
                      refine ⟨2171193897261544157941517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92637606283159217405504725 2171193897261544157941517)
                      ·
                        rfl

theorem cell23_4228385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_4228385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228385 prefixEnd_4228385 := by exact prefixLift 4228385
  have htrace : WordTrace (prefixWord ++ tailWord_4228385) baseStart_4228385 baseEnd_4228385 := by
    simpa [prefixWord, tailWord_4228385, baseEnd_4228385] using wordTrace_append hprefix tailTrace_4228385
  have hstable : (prefixWord ++ tailWord_4228385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228385).length < 2 ^ (prefixWord ++ tailWord_4228385).sum := by decide
  have hdescent : baseEnd_4228385 < baseStart_4228385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228436 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_4228436 : Nat := 118140960795 + 4228436 * 2 ^ 59
def prefixEnd_4228436 : Nat := 4983230072969 + 3 ^ 40 * 4228436 * 2
def baseEnd_4228436 : Nat := 2171220084774923458403783

theorem tailTrace_4228436 : CollatzResearch.WordTrace tailWord_4228436 prefixEnd_4228436 2171220084774923458403783 := by
  unfold tailWord_4228436
  simp only [CollatzResearch.WordTrace]
  refine ⟨77111865454553003109932581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102815820606070670813243441 77111865454553003109932581)
  ·
    refine ⟨14458474772728688083112359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77111865454553003109932581 14458474772728688083112359)
    ·
      refine ⟨21687712159093032124668539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14458474772728688083112359 21687712159093032124668539)
      ·
        refine ⟨32531568238639548187002809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21687712159093032124668539 32531568238639548187002809)
        ·
          refine ⟨24398676178979661140252107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32531568238639548187002809 24398676178979661140252107)
          ·
            refine ⟨36598014268469491710378161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24398676178979661140252107 36598014268469491710378161)
            ·
              refine ⟨27448510701352118782783621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36598014268469491710378161 27448510701352118782783621)
              ·
                refine ⟨5146595756503522271771929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27448510701352118782783621 5146595756503522271771929)
                ·
                  refine ⟨3859946817377641703828947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5146595756503522271771929 3859946817377641703828947)
                  ·
                    refine ⟨5789920226066462555743421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3859946817377641703828947 5789920226066462555743421)
                    ·
                      refine ⟨2171220084774923458403783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5789920226066462555743421 2171220084774923458403783)
                      ·
                        rfl

theorem cell23_4228436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_4228436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228436 prefixEnd_4228436 := by exact prefixLift 4228436
  have htrace : WordTrace (prefixWord ++ tailWord_4228436) baseStart_4228436 baseEnd_4228436 := by
    simpa [prefixWord, tailWord_4228436, baseEnd_4228436] using wordTrace_append hprefix tailTrace_4228436
  have hstable : (prefixWord ++ tailWord_4228436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228436).length < 2 ^ (prefixWord ++ tailWord_4228436).sum := by decide
  have hdescent : baseEnd_4228436 < baseStart_4228436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228509 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_4228509 : Nat := 118140960795 + 4228509 * 2 ^ 59
def prefixEnd_4228509 : Nat := 4983230072969 + 3 ^ 40 * 4228509 * 2
def baseEnd_4228509 : Nat := 2171257568862701672790947

theorem tailTrace_4228509 : CollatzResearch.WordTrace tailWord_4228509 prefixEnd_4228509 2171257568862701672790947 := by
  unfold tailWord_4228509
  simp only [CollatzResearch.WordTrace]
  refine ⟨154226393437841539687272581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102817595625227693124848387 154226393437841539687272581)
  ·
    refine ⟨28917448769595288691363609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154226393437841539687272581 28917448769595288691363609)
    ·
      refine ⟨21688086577196466518522707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28917448769595288691363609 21688086577196466518522707)
      ·
        refine ⟨32532129865794699777784061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21688086577196466518522707 32532129865794699777784061)
        ·
          refine ⟨12199548699673012416669023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32532129865794699777784061 12199548699673012416669023)
          ·
            refine ⟨18299323049509518625003535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12199548699673012416669023 18299323049509518625003535)
            ·
              refine ⟨27448984574264277937505303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18299323049509518625003535 27448984574264277937505303)
              ·
                refine ⟨41173476861396416906257955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27448984574264277937505303 41173476861396416906257955)
                ·
                  refine ⟨61760215292094625359386933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41173476861396416906257955 61760215292094625359386933)
                  ·
                    refine ⟨5790020183633871127442525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61760215292094625359386933 5790020183633871127442525)
                    ·
                      refine ⟨2171257568862701672790947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790020183633871127442525 2171257568862701672790947)
                      ·
                        rfl

theorem cell23_4228509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_4228509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228509 prefixEnd_4228509 := by exact prefixLift 4228509
  have htrace : WordTrace (prefixWord ++ tailWord_4228509) baseStart_4228509 baseEnd_4228509 := by
    simpa [prefixWord, tailWord_4228509, baseEnd_4228509] using wordTrace_append hprefix tailTrace_4228509
  have hstable : (prefixWord ++ tailWord_4228509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228509).length < 2 ^ (prefixWord ++ tailWord_4228509).sum := by decide
  have hdescent : baseEnd_4228509 < baseStart_4228509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228510 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4228510 : Nat := 118140960795 + 4228510 * 2 ^ 59
def prefixEnd_4228510 : Nat := 4983230072969 + 3 ^ 40 * 4228510 * 2
def baseEnd_4228510 : Nat := 2171258082343356168878443

theorem tailTrace_4228510 : CollatzResearch.WordTrace tailWord_4228510 prefixEnd_4228510 2171258082343356168878443 := by
  unfold tailWord_4228510
  simp only [CollatzResearch.WordTrace]
  refine ⟨19278303738854739607257373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102817619940558611238705989 19278303738854739607257373)
  ·
    refine ⟨7229363902070527352721515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19278303738854739607257373 7229363902070527352721515)
    ·
      refine ⟨10844045853105791029082273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229363902070527352721515 10844045853105791029082273)
      ·
        refine ⟨8133034389829343271811705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10844045853105791029082273 8133034389829343271811705)
        ·
          refine ⟨6099775792372007453858779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8133034389829343271811705 6099775792372007453858779)
          ·
            refine ⟨9149663688558011180788169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6099775792372007453858779 9149663688558011180788169)
            ·
              refine ⟨6862247766418508385591127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9149663688558011180788169 6862247766418508385591127)
              ·
                refine ⟨10293371649627762578386691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6862247766418508385591127 10293371649627762578386691)
                ·
                  refine ⟨15440057474441643867580037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10293371649627762578386691 15440057474441643867580037)
                  ·
                    refine ⟨2895010776457808225171257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15440057474441643867580037 2895010776457808225171257)
                    ·
                      refine ⟨2171258082343356168878443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895010776457808225171257 2171258082343356168878443)
                      ·
                        rfl

theorem cell23_4228510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4228510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228510 prefixEnd_4228510 := by exact prefixLift 4228510
  have htrace : WordTrace (prefixWord ++ tailWord_4228510) baseStart_4228510 baseEnd_4228510 := by
    simpa [prefixWord, tailWord_4228510, baseEnd_4228510] using wordTrace_append hprefix tailTrace_4228510
  have hstable : (prefixWord ++ tailWord_4228510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228510).length < 2 ^ (prefixWord ++ tailWord_4228510).sum := by decide
  have hdescent : baseEnd_4228510 < baseStart_4228510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228512 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 1, 7]
def baseStart_4228512 : Nat := 118140960795 + 4228512 * 2 ^ 59
def prefixEnd_4228512 : Nat := 4983230072969 + 3 ^ 40 * 4228512 * 2
def baseEnd_4228512 : Nat := 723753036434888387017811

theorem tailTrace_4228512 : CollatzResearch.WordTrace tailWord_4228512 prefixEnd_4228512 723753036434888387017811 := by
  unfold tailWord_4228512
  simp only [CollatzResearch.WordTrace]
  refine ⟨77113251428415335599815895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102817668571220447466421193 77113251428415335599815895)
  ·
    refine ⟨115669877142623003399723843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77113251428415335599815895 115669877142623003399723843)
    ·
      refine ⟨173504815713934505099585765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115669877142623003399723843 173504815713934505099585765)
      ·
        refine ⟨32532152946362719706172331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173504815713934505099585765 32532152946362719706172331)
        ·
          refine ⟨48798229419544079559258497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32532152946362719706172331 48798229419544079559258497)
          ·
            refine ⟨36598672064658059669443873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48798229419544079559258497 36598672064658059669443873)
            ·
              refine ⟨27449004048493544752082905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36598672064658059669443873 27449004048493544752082905)
              ·
                refine ⟨20586753036370158564062179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27449004048493544752082905 20586753036370158564062179)
                ·
                  refine ⟨30880129554555237846093269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20586753036370158564062179 30880129554555237846093269)
                  ·
                    refine ⟨723753036434888387017811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30880129554555237846093269 723753036434888387017811)
                    ·
                      rfl

theorem cell23_4228512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 7].length) (baseStart_4228512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228512 prefixEnd_4228512 := by exact prefixLift 4228512
  have htrace : WordTrace (prefixWord ++ tailWord_4228512) baseStart_4228512 baseEnd_4228512 := by
    simpa [prefixWord, tailWord_4228512, baseEnd_4228512] using wordTrace_append hprefix tailTrace_4228512
  have hstable : (prefixWord ++ tailWord_4228512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228512).length < 2 ^ (prefixWord ++ tailWord_4228512).sum := by decide
  have hdescent : baseEnd_4228512 < baseStart_4228512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228559 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 3, 4]
def baseStart_4228559 : Nat := 118140960795 + 4228559 * 2 ^ 59
def prefixEnd_4228559 : Nat := 4983230072969 + 3 ^ 40 * 4228559 * 2
def baseEnd_4228559 : Nat := 723761080965142159055239

theorem tailTrace_4228559 : CollatzResearch.WordTrace tailWord_4228559 prefixEnd_4228559 723761080965142159055239 := by
  unfold tailWord_4228559
  simp only [CollatzResearch.WordTrace]
  refine ⟨154228217087660398226592731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102818811391773598817728487 154228217087660398226592731)
  ·
    refine ⟨231342325631490597339889097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154228217087660398226592731 231342325631490597339889097)
    ·
      refine ⟨173506744223617948004916823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231342325631490597339889097 173506744223617948004916823)
      ·
        refine ⟨260260116335426922007375235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173506744223617948004916823 260260116335426922007375235)
        ·
          refine ⟨390390174503140383011062853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260260116335426922007375235 390390174503140383011062853)
          ·
            refine ⟨73198157719338821814574285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 390390174503140383011062853 73198157719338821814574285)
            ·
              refine ⟨27449309144752058180465357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73198157719338821814574285 27449309144752058180465357)
              ·
                refine ⟨10293490929282021817674509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27449309144752058180465357 10293490929282021817674509)
                ·
                  refine ⟨3860059098480758181627941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10293490929282021817674509 3860059098480758181627941)
                  ·
                    refine ⟨723761080965142159055239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860059098480758181627941 723761080965142159055239)
                    ·
                      rfl

theorem cell23_4228559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_4228559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228559 prefixEnd_4228559 := by exact prefixLift 4228559
  have htrace : WordTrace (prefixWord ++ tailWord_4228559) baseStart_4228559 baseEnd_4228559 := by
    simpa [prefixWord, tailWord_4228559, baseEnd_4228559] using wordTrace_append hprefix tailTrace_4228559
  have hstable : (prefixWord ++ tailWord_4228559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228559).length < 2 ^ (prefixWord ++ tailWord_4228559).sum := by decide
  have hdescent : baseEnd_4228559 < baseStart_4228559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228566 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4228566 : Nat := 118140960795 + 4228566 * 2 ^ 59
def prefixEnd_4228566 : Nat := 4983230072969 + 3 ^ 40 * 4228566 * 2
def baseEnd_4228566 : Nat := 2171286837260007949778185

theorem tailTrace_4228566 : CollatzResearch.WordTrace tailWord_4228566 prefixEnd_4228566 2171286837260007949778185 := by
  unfold tailWord_4228566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9639279524914689901381097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102818981599090025614731701 9639279524914689901381097)
  ·
    refine ⟨7229459643686017426035823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9639279524914689901381097 7229459643686017426035823)
    ·
      refine ⟨10844189465529026139053735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229459643686017426035823 10844189465529026139053735)
      ·
        refine ⟨16266284198293539208580603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10844189465529026139053735 16266284198293539208580603)
        ·
          refine ⟨24399426297440308812870905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16266284198293539208580603 24399426297440308812870905)
          ·
            refine ⟨18299569723080231609653179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24399426297440308812870905 18299569723080231609653179)
            ·
              refine ⟨27449354584620347414479769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18299569723080231609653179 27449354584620347414479769)
              ·
                refine ⟨20587015938465260560859827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27449354584620347414479769 20587015938465260560859827)
                ·
                  refine ⟨30880523907697890841289741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20587015938465260560859827 30880523907697890841289741)
                  ·
                    refine ⟨11580196465386709065483653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30880523907697890841289741 11580196465386709065483653)
                    ·
                      refine ⟨2171286837260007949778185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11580196465386709065483653 2171286837260007949778185)
                      ·
                        rfl

theorem cell23_4228566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4228566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228566 prefixEnd_4228566 := by exact prefixLift 4228566
  have htrace : WordTrace (prefixWord ++ tailWord_4228566) baseStart_4228566 baseEnd_4228566 := by
    simpa [prefixWord, tailWord_4228566, baseEnd_4228566] using wordTrace_append hprefix tailTrace_4228566
  have hstable : (prefixWord ++ tailWord_4228566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228566).length < 2 ^ (prefixWord ++ tailWord_4228566).sum := by decide
  have hdescent : baseEnd_4228566 < baseStart_4228566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228569 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 3]
def baseStart_4228569 : Nat := 118140960795 + 4228569 * 2 ^ 59
def prefixEnd_4228569 : Nat := 4983230072969 + 3 ^ 40 * 4228569 * 2
def baseEnd_4228569 : Nat := 2171288377701971438040671

theorem tailTrace_4228569 : CollatzResearch.WordTrace tailWord_4228569 prefixEnd_4228569 2171288377701971438040671 := by
  unfold tailWord_4228569
  simp only [CollatzResearch.WordTrace]
  refine ⟨154228581817624169934456761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102819054545082779956304507 154228581817624169934456761)
  ·
    refine ⟨115671436363218127450842571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154228581817624169934456761 115671436363218127450842571)
    ·
      refine ⟨173507154544827191176263857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115671436363218127450842571 173507154544827191176263857)
      ·
        refine ⟨130130365908620393382197893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173507154544827191176263857 130130365908620393382197893)
        ·
          refine ⟨24399443607866323759162105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130130365908620393382197893 24399443607866323759162105)
          ·
            refine ⟨18299582705899742819371579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24399443607866323759162105 18299582705899742819371579)
            ·
              refine ⟨27449374058849614229057369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18299582705899742819371579 27449374058849614229057369)
              ·
                refine ⟨20587030544137210671793027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27449374058849614229057369 20587030544137210671793027)
                ·
                  refine ⟨30880545816205816007689541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20587030544137210671793027 30880545816205816007689541)
                  ·
                    refine ⟨5790102340538590501441789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30880545816205816007689541 5790102340538590501441789)
                    ·
                      refine ⟨2171288377701971438040671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790102340538590501441789 2171288377701971438040671)
                      ·
                        rfl

theorem cell23_4228569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_4228569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228569 prefixEnd_4228569 := by exact prefixLift 4228569
  have htrace : WordTrace (prefixWord ++ tailWord_4228569) baseStart_4228569 baseEnd_4228569 := by
    simpa [prefixWord, tailWord_4228569, baseEnd_4228569] using wordTrace_append hprefix tailTrace_4228569
  have hstable : (prefixWord ++ tailWord_4228569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228569).length < 2 ^ (prefixWord ++ tailWord_4228569).sum := by decide
  have hdescent : baseEnd_4228569 < baseStart_4228569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228593 : List Nat := [1, 2, 2, 2, 3, 2, 3, 3, 1, 4]
def baseStart_4228593 : Nat := 118140960795 + 4228593 * 2 ^ 59
def prefixEnd_4228593 : Nat := 4983230072969 + 3 ^ 40 * 4228593 * 2
def baseEnd_4228593 : Nat := 723766900412559781380187

theorem tailTrace_4228593 : CollatzResearch.WordTrace tailWord_4228593 prefixEnd_4228593 723766900412559781380187 := by
  unfold tailWord_4228593
  simp only [CollatzResearch.WordTrace]
  refine ⟨154229457169537222033330433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102819638113024814688886955 154229457169537222033330433)
  ·
    refine ⟨115672092877152916524997825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154229457169537222033330433 115672092877152916524997825)
    ·
      refine ⟨86754069657864687393748369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115672092877152916524997825 86754069657864687393748369)
      ·
        refine ⟨65065552243398515545311277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86754069657864687393748369 65065552243398515545311277)
        ·
          refine ⟨24399582091274443329491729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65065552243398515545311277 24399582091274443329491729)
          ·
            refine ⟨18299686568455832497118797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24399582091274443329491729 18299686568455832497118797)
            ·
              refine ⟨6862382463170937186419549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18299686568455832497118797 6862382463170937186419549)
              ·
                refine ⟨2573393423689101444907331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6862382463170937186419549 2573393423689101444907331)
                ·
                  refine ⟨3860090135533652167360997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573393423689101444907331 3860090135533652167360997)
                  ·
                    refine ⟨723766900412559781380187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860090135533652167360997 723766900412559781380187)
                    ·
                      rfl

theorem cell23_4228593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_4228593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228593 prefixEnd_4228593 := by exact prefixLift 4228593
  have htrace : WordTrace (prefixWord ++ tailWord_4228593) baseStart_4228593 baseEnd_4228593 := by
    simpa [prefixWord, tailWord_4228593, baseEnd_4228593] using wordTrace_append hprefix tailTrace_4228593
  have hstable : (prefixWord ++ tailWord_4228593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228593).length < 2 ^ (prefixWord ++ tailWord_4228593).sum := by decide
  have hdescent : baseEnd_4228593 < baseStart_4228593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228610 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_4228610 : Nat := 118140960795 + 4228610 * 2 ^ 59
def prefixEnd_4228610 : Nat := 4983230072969 + 3 ^ 40 * 4228610 * 2
def baseEnd_4228610 : Nat := 723769810136268592542661

theorem tailTrace_4228610 : CollatzResearch.WordTrace tailWord_4228610 prefixEnd_4228610 723769810136268592542661 := by
  unfold tailWord_4228610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38557519302618908484174821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102820051473650422624466189 38557519302618908484174821)
  ·
    refine ⟨7229534869241045340782779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38557519302618908484174821 7229534869241045340782779)
    ·
      refine ⟨10844302303861568011174169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7229534869241045340782779 10844302303861568011174169)
      ·
        refine ⟨8133226727896176008380627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10844302303861568011174169 8133226727896176008380627)
        ·
          refine ⟨12199840091844264012570941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8133226727896176008380627 12199840091844264012570941)
          ·
            refine ⟨4574940034441599004714103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12199840091844264012570941 4574940034441599004714103)
            ·
              refine ⟨6862410051662398507071155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4574940034441599004714103 6862410051662398507071155)
              ·
                refine ⟨10293615077493597760606733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6862410051662398507071155 10293615077493597760606733)
                ·
                  refine ⟨3860105654060099160227525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10293615077493597760606733 3860105654060099160227525)
                  ·
                    refine ⟨723769810136268592542661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860105654060099160227525 723769810136268592542661)
                    ·
                      rfl

theorem cell23_4228610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_4228610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228610 prefixEnd_4228610 := by exact prefixLift 4228610
  have htrace : WordTrace (prefixWord ++ tailWord_4228610) baseStart_4228610 baseEnd_4228610 := by
    simpa [prefixWord, tailWord_4228610, baseEnd_4228610] using wordTrace_append hprefix tailTrace_4228610
  have hstable : (prefixWord ++ tailWord_4228610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228610).length < 2 ^ (prefixWord ++ tailWord_4228610).sum := by decide
  have hdescent : baseEnd_4228610 < baseStart_4228610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228650 : List Nat := [3, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_4228650 : Nat := 118140960795 + 4228650 * 2 ^ 59
def prefixEnd_4228650 : Nat := 4983230072969 + 3 ^ 40 * 4228650 * 2
def baseEnd_4228650 : Nat := 2171329969634985621127799

theorem tailTrace_4228650 : CollatzResearch.WordTrace tailWord_4228650 prefixEnd_4228650 2171329969634985621127799 := by
  unfold tailWord_4228650
  simp only [CollatzResearch.WordTrace]
  refine ⟨38557884032582680192038851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102821024086887147178770269 38557884032582680192038851)
  ·
    refine ⟨57836826048874020288058277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38557884032582680192038851 57836826048874020288058277)
    ·
      refine ⟨10844404884163878804010927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57836826048874020288058277 10844404884163878804010927)
      ·
        refine ⟨16266607326245818206016391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10844404884163878804010927 16266607326245818206016391)
        ·
          refine ⟨24399910989368727309024587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16266607326245818206016391 24399910989368727309024587)
          ·
            refine ⟨36599866484053090963536881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24399910989368727309024587 36599866484053090963536881)
            ·
              refine ⟨27449899863039818222652661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36599866484053090963536881 27449899863039818222652661)
              ·
                refine ⟨2573428112159982958373687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27449899863039818222652661 2573428112159982958373687)
                ·
                  refine ⟨3860142168239974437560531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573428112159982958373687 3860142168239974437560531)
                  ·
                    refine ⟨5790213252359961656340797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3860142168239974437560531 5790213252359961656340797)
                    ·
                      refine ⟨2171329969634985621127799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790213252359961656340797 2171329969634985621127799)
                      ·
                        rfl

theorem cell23_4228650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_4228650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228650 prefixEnd_4228650 := by exact prefixLift 4228650
  have htrace : WordTrace (prefixWord ++ tailWord_4228650) baseStart_4228650 baseEnd_4228650 := by
    simpa [prefixWord, tailWord_4228650, baseEnd_4228650] using wordTrace_append hprefix tailTrace_4228650
  have hstable : (prefixWord ++ tailWord_4228650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228650).length < 2 ^ (prefixWord ++ tailWord_4228650).sum := by decide
  have hdescent : baseEnd_4228650 < baseStart_4228650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228690 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_4228690 : Nat := 118140960795 + 4228690 * 2 ^ 59
def prefixEnd_4228690 : Nat := 4983230072969 + 3 ^ 40 * 4228690 * 2
def baseEnd_4228690 : Nat := 2171350508861165464627615

theorem tailTrace_4228690 : CollatzResearch.WordTrace tailWord_4228690 prefixEnd_4228690 2171350508861165464627615 := by
  unfold tailWord_4228690
  simp only [CollatzResearch.WordTrace]
  refine ⟨38558248762546451899902881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102821996700123871733074349 38558248762546451899902881)
  ·
    refine ⟨28918686571909838924927161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38558248762546451899902881 28918686571909838924927161)
    ·
      refine ⟨21689014928932379193695371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28918686571909838924927161 21689014928932379193695371)
      ·
        refine ⟨32533522393398568790543057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21689014928932379193695371 32533522393398568790543057)
        ·
          refine ⟨24400141795048926592907293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32533522393398568790543057 24400141795048926592907293)
          ·
            refine ⟨9150053173143347472340235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24400141795048926592907293 9150053173143347472340235)
            ·
              refine ⟨13725079759715021208510353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9150053173143347472340235 13725079759715021208510353)
              ·
                refine ⟨10293809819786265906382765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13725079759715021208510353 10293809819786265906382765)
                ·
                  refine ⟨3860178682419849714893537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10293809819786265906382765 3860178682419849714893537)
                  ·
                    refine ⟨2895134011814887286170153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3860178682419849714893537 2895134011814887286170153)
                    ·
                      refine ⟨2171350508861165464627615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895134011814887286170153 2171350508861165464627615)
                      ·
                        rfl

theorem cell23_4228690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_4228690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228690 prefixEnd_4228690 := by exact prefixLift 4228690
  have htrace : WordTrace (prefixWord ++ tailWord_4228690) baseStart_4228690 baseEnd_4228690 := by
    simpa [prefixWord, tailWord_4228690, baseEnd_4228690] using wordTrace_append hprefix tailTrace_4228690
  have hstable : (prefixWord ++ tailWord_4228690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228690).length < 2 ^ (prefixWord ++ tailWord_4228690).sum := by decide
  have hdescent : baseEnd_4228690 < baseStart_4228690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228707 : List Nat := [1, 1, 1, 5, 1, 4, 2, 3, 1, 2, 2]
def baseStart_4228707 : Nat := 118140960795 + 4228707 * 2 ^ 59
def prefixEnd_4228707 : Nat := 4983230072969 + 3 ^ 40 * 4228707 * 2
def baseEnd_4228707 : Nat := 2171359238032291898115037

theorem tailTrace_4228707 : CollatzResearch.WordTrace tailWord_4228707 prefixEnd_4228707 2171359238032291898115037 := by
  unfold tailWord_4228707
  simp only [CollatzResearch.WordTrace]
  refine ⟨154233615091124219502980375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102822410060749479668653583 154233615091124219502980375)
  ·
    refine ⟨231350422636686329254470563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154233615091124219502980375 231350422636686329254470563)
    ·
      refine ⟨347025633955029493881705845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231350422636686329254470563 347025633955029493881705845)
      ·
        refine ⟨32533653183284015051409923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 347025633955029493881705845 32533653183284015051409923)
        ·
          refine ⟨48800479774926022577114885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32533653183284015051409923 48800479774926022577114885)
          ·
            refine ⟨9150089957798629233209041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48800479774926022577114885 9150089957798629233209041)
            ·
              refine ⟨6862567468348971924906781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9150089957798629233209041 6862567468348971924906781)
              ·
                refine ⟨2573462800630864471840043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6862567468348971924906781 2573462800630864471840043)
                ·
                  refine ⟨3860194200946296707760065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573462800630864471840043 3860194200946296707760065)
                  ·
                    refine ⟨2895145650709722530820049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3860194200946296707760065 2895145650709722530820049)
                    ·
                      refine ⟨2171359238032291898115037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895145650709722530820049 2171359238032291898115037)
                      ·
                        rfl

theorem cell23_4228707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_4228707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228707 prefixEnd_4228707 := by exact prefixLift 4228707
  have htrace : WordTrace (prefixWord ++ tailWord_4228707) baseStart_4228707 baseEnd_4228707 := by
    simpa [prefixWord, tailWord_4228707, baseEnd_4228707] using wordTrace_append hprefix tailTrace_4228707
  have hstable : (prefixWord ++ tailWord_4228707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228707).length < 2 ^ (prefixWord ++ tailWord_4228707).sum := by decide
  have hdescent : baseEnd_4228707 < baseStart_4228707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228717 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_4228717 : Nat := 118140960795 + 4228717 * 2 ^ 59
def prefixEnd_4228717 : Nat := 4983230072969 + 3 ^ 40 * 4228717 * 2
def baseEnd_4228717 : Nat := 723788124279612286329997

theorem tailTrace_4228717 : CollatzResearch.WordTrace tailWord_4228717 prefixEnd_4228717 723788124279612286329997 := by
  unfold tailWord_4228717
  simp only [CollatzResearch.WordTrace]
  refine ⟨154233979821087991210844405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102822653214058660807229603 154233979821087991210844405)
  ·
    refine ⟨14459435608226999176016663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154233979821087991210844405 14459435608226999176016663)
    ·
      refine ⟨21689153412340498764024995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14459435608226999176016663 21689153412340498764024995)
      ·
        refine ⟨32533730118510748146037493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21689153412340498764024995 32533730118510748146037493)
        ·
          refine ⟨3050037198610382638691015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32533730118510748146037493 3050037198610382638691015)
          ·
            refine ⟨4575055797915573958036523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050037198610382638691015 4575055797915573958036523)
            ·
              refine ⟨6862583696873360937054785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575055797915573958036523 6862583696873360937054785)
              ·
                refine ⟨5146937772655020702791089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6862583696873360937054785 5146937772655020702791089)
                ·
                  refine ⟨3860203329491265527093317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5146937772655020702791089 3860203329491265527093317)
                  ·
                    refine ⟨723788124279612286329997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860203329491265527093317 723788124279612286329997)
                    ·
                      rfl

theorem cell23_4228717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_4228717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228717 prefixEnd_4228717 := by exact prefixLift 4228717
  have htrace : WordTrace (prefixWord ++ tailWord_4228717) baseStart_4228717 baseEnd_4228717 := by
    simpa [prefixWord, tailWord_4228717, baseEnd_4228717] using wordTrace_append hprefix tailTrace_4228717
  have hstable : (prefixWord ++ tailWord_4228717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228717).length < 2 ^ (prefixWord ++ tailWord_4228717).sum := by decide
  have hdescent : baseEnd_4228717 < baseStart_4228717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228740 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_4228740 : Nat := 118140960795 + 4228740 * 2 ^ 59
def prefixEnd_4228740 : Nat := 4983230072969 + 3 ^ 40 * 4228740 * 2
def baseEnd_4228740 : Nat := 2171376182893890269002385

theorem tailTrace_4228740 : CollatzResearch.WordTrace tailWord_4228740 prefixEnd_4228740 2171376182893890269002385 := by
  unfold tailWord_4228740
  simp only [CollatzResearch.WordTrace]
  refine ⟨77117409350002333069465837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102823212466669777425954449 77117409350002333069465837)
  ·
    refine ⟨28919028506250874901049689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77117409350002333069465837 28919028506250874901049689)
    ·
      refine ⟨21689271379688156175787267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28919028506250874901049689 21689271379688156175787267)
      ·
        refine ⟨32533907069532234263680901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21689271379688156175787267 32533907069532234263680901)
        ·
          refine ⟨6100107575537293924440169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32533907069532234263680901 6100107575537293924440169)
          ·
            refine ⟨4575080681652970443330127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6100107575537293924440169 4575080681652970443330127)
            ·
              refine ⟨6862621022479455664995191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575080681652970443330127 6862621022479455664995191)
              ·
                refine ⟨10293931533719183497492787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6862621022479455664995191 10293931533719183497492787)
                ·
                  refine ⟨15440897300578775246239181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10293931533719183497492787 15440897300578775246239181)
                  ·
                    refine ⟨5790336487717040717339693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15440897300578775246239181 5790336487717040717339693)
                    ·
                      refine ⟨2171376182893890269002385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790336487717040717339693 2171376182893890269002385)
                      ·
                        rfl

theorem cell23_4228740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_4228740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228740 prefixEnd_4228740 := by exact prefixLift 4228740
  have htrace : WordTrace (prefixWord ++ tailWord_4228740) baseStart_4228740 baseEnd_4228740 := by
    simpa [prefixWord, tailWord_4228740, baseEnd_4228740] using wordTrace_append hprefix tailTrace_4228740
  have hstable : (prefixWord ++ tailWord_4228740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228740).length < 2 ^ (prefixWord ++ tailWord_4228740).sum := by decide
  have hdescent : baseEnd_4228740 < baseStart_4228740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228750 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4228750 : Nat := 118140960795 + 4228750 * 2 ^ 59
def prefixEnd_4228750 : Nat := 4983230072969 + 3 ^ 40 * 4228750 * 2
def baseEnd_4228750 : Nat := 2171381317700435229877339

theorem tailTrace_4228750 : CollatzResearch.WordTrace tailWord_4228750 prefixEnd_4228750 2171381317700435229877339 := by
  unfold tailWord_4228750
  simp only [CollatzResearch.WordTrace]
  refine ⟨19279397928746054730849463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102823455619978958564530469 19279397928746054730849463)
  ·
    refine ⟨28919096893119082096274195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19279397928746054730849463 28919096893119082096274195)
    ·
      refine ⟨43378645339678623144411293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28919096893119082096274195 43378645339678623144411293)
      ·
        refine ⟨16266992002379483679154235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43378645339678623144411293 16266992002379483679154235)
        ·
          refine ⟨24400488003569225518731353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16266992002379483679154235 24400488003569225518731353)
          ·
            refine ⟨18300366002676919139048515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24400488003569225518731353 18300366002676919139048515)
            ·
              refine ⟨27450549004015378708572773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18300366002676919139048515 27450549004015378708572773)
              ·
                refine ⟨5146977938252883507857395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27450549004015378708572773 5146977938252883507857395)
                ·
                  refine ⟨7720466907379325261786093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5146977938252883507857395 7720466907379325261786093)
                  ·
                    refine ⟨2895175090267246973169785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7720466907379325261786093 2895175090267246973169785)
                    ·
                      refine ⟨2171381317700435229877339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895175090267246973169785 2171381317700435229877339)
                      ·
                        rfl

theorem cell23_4228750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4228750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228750 prefixEnd_4228750 := by exact prefixLift 4228750
  have htrace : WordTrace (prefixWord ++ tailWord_4228750) baseStart_4228750 baseEnd_4228750 := by
    simpa [prefixWord, tailWord_4228750, baseEnd_4228750] using wordTrace_append hprefix tailTrace_4228750
  have hstable : (prefixWord ++ tailWord_4228750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228750).length < 2 ^ (prefixWord ++ tailWord_4228750).sum := by decide
  have hdescent : baseEnd_4228750 < baseStart_4228750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228786 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 7]
def baseStart_4228786 : Nat := 118140960795 + 4228786 * 2 ^ 59
def prefixEnd_4228786 : Nat := 4983230072969 + 3 ^ 40 * 4228786 * 2
def baseEnd_4228786 : Nat := 241266644778221898780797

theorem tailTrace_4228786 : CollatzResearch.WordTrace tailWord_4228786 prefixEnd_4228786 241266644778221898780797 := by
  unfold tailWord_4228786
  simp only [CollatzResearch.WordTrace]
  refine ⟨38559124114459503998776553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102824330971892010663404141 38559124114459503998776553)
  ·
    refine ⟨28919343085844627999082415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38559124114459503998776553 28919343085844627999082415)
    ·
      refine ⟨43379014628766941998623623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28919343085844627999082415 43379014628766941998623623)
      ·
        refine ⟨65068521943150412997935435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43379014628766941998623623 65068521943150412997935435)
        ·
          refine ⟨97602782914725619496903153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65068521943150412997935435 97602782914725619496903153)
          ·
            refine ⟨73202087186044214622677365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97602782914725619496903153 73202087186044214622677365)
            ·
              refine ⟨6862695673691645120876003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73202087186044214622677365 6862695673691645120876003)
              ·
                refine ⟨10294043510537467681314005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6862695673691645120876003 10294043510537467681314005)
                ·
                  refine ⟨241266644778221898780797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10294043510537467681314005 241266644778221898780797)
                  ·
                    rfl

theorem cell23_4228786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_4228786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228786 prefixEnd_4228786 := by exact prefixLift 4228786
  have htrace : WordTrace (prefixWord ++ tailWord_4228786) baseStart_4228786 baseEnd_4228786 := by
    simpa [prefixWord, tailWord_4228786, baseEnd_4228786] using wordTrace_append hprefix tailTrace_4228786
  have hstable : (prefixWord ++ tailWord_4228786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228786).length < 2 ^ (prefixWord ++ tailWord_4228786).sum := by decide
  have hdescent : baseEnd_4228786 < baseStart_4228786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228826 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_4228826 : Nat := 118140960795 + 4228826 * 2 ^ 59
def prefixEnd_4228826 : Nat := 4983230072969 + 3 ^ 40 * 4228826 * 2
def baseEnd_4228826 : Nat := 2171420342230176932526989

theorem tailTrace_4228826 : CollatzResearch.WordTrace tailWord_4228826 prefixEnd_4228826 2171420342230176932526989 := by
  unfold tailWord_4228826
  simp only [CollatzResearch.WordTrace]
  refine ⟨38559488844423275706640583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102825303585128735217708221 38559488844423275706640583)
  ·
    refine ⟨57839233266634913559960875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38559488844423275706640583 57839233266634913559960875)
    ·
      refine ⟨86758849899952370339941313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57839233266634913559960875 86758849899952370339941313)
      ·
        refine ⟨65069137424964277754955985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86758849899952370339941313 65069137424964277754955985)
        ·
          refine ⟨48801853068723208316216989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65069137424964277754955985 48801853068723208316216989)
          ·
            refine ⟨18300694900771203118581371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48801853068723208316216989 18300694900771203118581371)
            ·
              refine ⟨27451042351156804677872057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18300694900771203118581371 27451042351156804677872057)
              ·
                refine ⟨20588281763367603508404043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27451042351156804677872057 20588281763367603508404043)
                ·
                  refine ⟨30882422645051405262606065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20588281763367603508404043 30882422645051405262606065)
                  ·
                    refine ⟨23161816983788553946954549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30882422645051405262606065 23161816983788553946954549)
                    ·
                      refine ⟨2171420342230176932526989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23161816983788553946954549 2171420342230176932526989)
                      ·
                        rfl

theorem cell23_4228826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_4228826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228826 prefixEnd_4228826 := by exact prefixLift 4228826
  have htrace : WordTrace (prefixWord ++ tailWord_4228826) baseStart_4228826 baseEnd_4228826 := by
    simpa [prefixWord, tailWord_4228826, baseEnd_4228826] using wordTrace_append hprefix tailTrace_4228826
  have hstable : (prefixWord ++ tailWord_4228826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228826).length < 2 ^ (prefixWord ++ tailWord_4228826).sum := by decide
  have hdescent : baseEnd_4228826 < baseStart_4228826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228896 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4228896 : Nat := 118140960795 + 4228896 * 2 ^ 59
def prefixEnd_4228896 : Nat := 4983230072969 + 3 ^ 40 * 4228896 * 2
def baseEnd_4228896 : Nat := 2171456285875991658651667

theorem tailTrace_4228896 : CollatzResearch.WordTrace tailWord_4228896 prefixEnd_4228896 2171456285875991658651667 := by
  unfold tailWord_4228896
  simp only [CollatzResearch.WordTrace]
  refine ⟨77120254243719752390805271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102827005658293003187740361 77120254243719752390805271)
  ·
    refine ⟨115680381365579628586207907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77120254243719752390805271 115680381365579628586207907)
    ·
      refine ⟨173520572048369442879311861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115680381365579628586207907 173520572048369442879311861)
      ·
        refine ⟨16267553629534635269935487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173520572048369442879311861 16267553629534635269935487)
        ·
          refine ⟨24401330444301952904903231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16267553629534635269935487 24401330444301952904903231)
          ·
            refine ⟨36601995666452929357354847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24401330444301952904903231 36601995666452929357354847)
            ·
              refine ⟨54902993499679394036032271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36601995666452929357354847 54902993499679394036032271)
              ·
                refine ⟨82354490249519091054048407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54902993499679394036032271 82354490249519091054048407)
                ·
                  refine ⟨123531735374278636581072611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82354490249519091054048407 123531735374278636581072611)
                  ·
                    refine ⟨185297603061417954871608917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123531735374278636581072611 185297603061417954871608917)
                    ·
                      refine ⟨2171456285875991658651667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 185297603061417954871608917 2171456285875991658651667)
                      ·
                        rfl

theorem cell23_4228896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4228896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228896 prefixEnd_4228896 := by exact prefixLift 4228896
  have htrace : WordTrace (prefixWord ++ tailWord_4228896) baseStart_4228896 baseEnd_4228896 := by
    simpa [prefixWord, tailWord_4228896, baseEnd_4228896] using wordTrace_append hprefix tailTrace_4228896
  have hstable : (prefixWord ++ tailWord_4228896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228896).length < 2 ^ (prefixWord ++ tailWord_4228896).sum := by decide
  have hdescent : baseEnd_4228896 < baseStart_4228896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228920 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_4228920 : Nat := 118140960795 + 4228920 * 2 ^ 59
def prefixEnd_4228920 : Nat := 4983230072969 + 3 ^ 40 * 4228920 * 2
def baseEnd_4228920 : Nat := 2171468609411699564751557

theorem tailTrace_4228920 : CollatzResearch.WordTrace tailWord_4228920 prefixEnd_4228920 2171468609411699564751557 := by
  unfold tailWord_4228920
  simp only [CollatzResearch.WordTrace]
  refine ⟨77120691919676278440242107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102827589226235037920322809 77120691919676278440242107)
  ·
    refine ⟨115681037879514417660363161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77120691919676278440242107 115681037879514417660363161)
    ·
      refine ⟨86760778409635813245272371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115681037879514417660363161 86760778409635813245272371)
      ·
        refine ⟨130141167614453719867908557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86760778409635813245272371 130141167614453719867908557)
        ·
          refine ⟨48802937855420144950465709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130141167614453719867908557 48802937855420144950465709)
          ·
            refine ⟨18301101695782554356424641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48802937855420144950465709 18301101695782554356424641)
            ·
              refine ⟨13725826271836915767318481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18301101695782554356424641 13725826271836915767318481)
              ·
                refine ⟨10294369703877686825488861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13725826271836915767318481 10294369703877686825488861)
                ·
                  refine ⟨3860388638954132559558323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10294369703877686825488861 3860388638954132559558323)
                  ·
                    refine ⟨5790582958431198839337485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3860388638954132559558323 5790582958431198839337485)
                    ·
                      refine ⟨2171468609411699564751557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790582958431198839337485 2171468609411699564751557)
                      ·
                        rfl

theorem cell23_4228920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_4228920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228920 prefixEnd_4228920 := by exact prefixLift 4228920
  have htrace : WordTrace (prefixWord ++ tailWord_4228920) baseStart_4228920 baseEnd_4228920 := by
    simpa [prefixWord, tailWord_4228920, baseEnd_4228920] using wordTrace_append hprefix tailTrace_4228920
  have hstable : (prefixWord ++ tailWord_4228920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228920).length < 2 ^ (prefixWord ++ tailWord_4228920).sum := by decide
  have hdescent : baseEnd_4228920 < baseStart_4228920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228953 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 4, 4]
def baseStart_4228953 : Nat := 118140960795 + 4228953 * 2 ^ 59
def prefixEnd_4228953 : Nat := 4983230072969 + 3 ^ 40 * 4228953 * 2
def baseEnd_4228953 : Nat := 723828518091099311879635

theorem tailTrace_4228953 : CollatzResearch.WordTrace tailWord_4228953 prefixEnd_4228953 723828518091099311879635 := by
  unfold tailWord_4228953
  simp only [CollatzResearch.WordTrace]
  refine ⟨154242587448233003516435513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102828391632155335677623675 154242587448233003516435513)
  ·
    refine ⟨115681940586174752637326635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154242587448233003516435513 115681940586174752637326635)
    ·
      refine ⟨173522910879262128955989953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115681940586174752637326635 173522910879262128955989953)
      ·
        refine ⟨130142183159446596716992465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173522910879262128955989953 130142183159446596716992465)
        ·
          refine ⟨97606637369584947537744349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130142183159446596716992465 97606637369584947537744349)
          ·
            refine ⟨36602489013594355326654131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97606637369584947537744349 36602489013594355326654131)
            ·
              refine ⟨54903733520391532989981197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36602489013594355326654131 54903733520391532989981197)
              ·
                refine ⟨20588900070146824871242949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54903733520391532989981197 20588900070146824871242949)
                ·
                  refine ⟨3860418763152529663358053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20588900070146824871242949 3860418763152529663358053)
                  ·
                    refine ⟨723828518091099311879635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860418763152529663358053 723828518091099311879635)
                    ·
                      rfl

theorem cell23_4228953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_4228953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228953 prefixEnd_4228953 := by exact prefixLift 4228953
  have htrace : WordTrace (prefixWord ++ tailWord_4228953) baseStart_4228953 baseEnd_4228953 := by
    simpa [prefixWord, tailWord_4228953, baseEnd_4228953] using wordTrace_append hprefix tailTrace_4228953
  have hstable : (prefixWord ++ tailWord_4228953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228953).length < 2 ^ (prefixWord ++ tailWord_4228953).sum := by decide
  have hdescent : baseEnd_4228953 < baseStart_4228953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228954 : List Nat := [3, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3]
def baseStart_4228954 : Nat := 118140960795 + 4228954 * 2 ^ 59
def prefixEnd_4228954 : Nat := 4983230072969 + 3 ^ 40 * 4228954 * 2
def baseEnd_4228954 : Nat := 2171486067753952431726401

theorem tailTrace_4228954 : CollatzResearch.WordTrace tailWord_4228954 prefixEnd_4228954 2171486067753952431726401 := by
  unfold tailWord_4228954
  simp only [CollatzResearch.WordTrace]
  refine ⟨38560655980307345171805479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102828415947486253791481277 38560655980307345171805479)
  ·
    refine ⟨57840983970461017757708219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38560655980307345171805479 57840983970461017757708219)
    ·
      refine ⟨86761475955691526636562329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57840983970461017757708219 86761475955691526636562329)
      ·
        refine ⟨65071106966768644977421747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86761475955691526636562329 65071106966768644977421747)
        ·
          refine ⟨97606660450152967466132621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65071106966768644977421747 97606660450152967466132621)
          ·
            refine ⟨36602497668807362799799733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97606660450152967466132621 36602497668807362799799733)
            ·
              refine ⟨3431484156450690262481225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36602497668807362799799733 3431484156450690262481225)
              ·
                refine ⟨2573613117338017696860919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3431484156450690262481225 2573613117338017696860919)
                ·
                  refine ⟨3860419676007026545291379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573613117338017696860919 3860419676007026545291379)
                  ·
                    refine ⟨5790629514010539817937069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3860419676007026545291379 5790629514010539817937069)
                    ·
                      refine ⟨2171486067753952431726401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790629514010539817937069 2171486067753952431726401)
                      ·
                        rfl

theorem cell23_4228954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_4228954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228954 prefixEnd_4228954 := by exact prefixLift 4228954
  have htrace : WordTrace (prefixWord ++ tailWord_4228954) baseStart_4228954 baseEnd_4228954 := by
    simpa [prefixWord, tailWord_4228954, baseEnd_4228954] using wordTrace_append hprefix tailTrace_4228954
  have hstable : (prefixWord ++ tailWord_4228954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228954).length < 2 ^ (prefixWord ++ tailWord_4228954).sum := by decide
  have hdescent : baseEnd_4228954 < baseStart_4228954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228973 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4228973 : Nat := 118140960795 + 4228973 * 2 ^ 59
def prefixEnd_4228973 : Nat := 4983230072969 + 3 ^ 40 * 4228973 * 2
def baseEnd_4228973 : Nat := 2171495823886387857388813

theorem tailTrace_4228973 : CollatzResearch.WordTrace tailWord_4228973 prefixEnd_4228973 2171495823886387857388813 := by
  unfold tailWord_4228973
  simp only [CollatzResearch.WordTrace]
  refine ⟨154243316908160546932163573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102828877938773697954775715 154243316908160546932163573)
  ·
    refine ⟨14460310960140051274890335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154243316908160546932163573 14460310960140051274890335)
    ·
      refine ⟨21690466440210076912335503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14460310960140051274890335 21690466440210076912335503)
      ·
        refine ⟨32535699660315115368503255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21690466440210076912335503 32535699660315115368503255)
        ·
          refine ⟨48803549490472673052754883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32535699660315115368503255 48803549490472673052754883)
          ·
            refine ⟨73205324235709009579132325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48803549490472673052754883 73205324235709009579132325)
            ·
              refine ⟨13725998294195439296087311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73205324235709009579132325 13725998294195439296087311)
              ·
                refine ⟨20588997441293158944130967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13725998294195439296087311 20588997441293158944130967)
                ·
                  refine ⟨30883496161939738416196451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20588997441293158944130967 30883496161939738416196451)
                  ·
                    refine ⟨46325244242909607624294677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30883496161939738416196451 46325244242909607624294677)
                    ·
                      refine ⟨2171495823886387857388813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46325244242909607624294677 2171495823886387857388813)
                      ·
                        rfl

theorem cell23_4228973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4228973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228973 prefixEnd_4228973 := by exact prefixLift 4228973
  have htrace : WordTrace (prefixWord ++ tailWord_4228973) baseStart_4228973 baseEnd_4228973 := by
    simpa [prefixWord, tailWord_4228973, baseEnd_4228973] using wordTrace_append hprefix tailTrace_4228973
  have hstable : (prefixWord ++ tailWord_4228973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228973).length < 2 ^ (prefixWord ++ tailWord_4228973).sum := by decide
  have hdescent : baseEnd_4228973 < baseStart_4228973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4228997 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 1, 2, 3]
def baseStart_4228997 : Nat := 118140960795 + 4228997 * 2 ^ 59
def prefixEnd_4228997 : Nat := 4983230072969 + 3 ^ 40 * 4228997 * 2
def baseEnd_4228997 : Nat := 2171508147422095763488703

theorem tailTrace_4228997 : CollatzResearch.WordTrace tailWord_4228997 prefixEnd_4228997 2171508147422095763488703 := by
  unfold tailWord_4228997
  simp only [CollatzResearch.WordTrace]
  refine ⟨154244192260073599031037245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102829461506715732687358163 154244192260073599031037245)
  ·
    refine ⟨57841572097527599636638967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154244192260073599031037245 57841572097527599636638967)
    ·
      refine ⟨86762358146291399454958451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57841572097527599636638967 86762358146291399454958451)
      ·
        refine ⟨130143537219437099182437677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86762358146291399454958451 130143537219437099182437677)
        ·
          refine ⟨48803826457288912193414129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130143537219437099182437677 48803826457288912193414129)
          ·
            refine ⟨36602869842966684145060597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48803826457288912193414129 36602869842966684145060597)
            ·
              refine ⟨3431519047778126638599431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36602869842966684145060597 3431519047778126638599431)
              ·
                refine ⟨5147278571667189957899147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431519047778126638599431 5147278571667189957899147)
                ·
                  refine ⟨7720917857500784936848721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5147278571667189957899147 7720917857500784936848721)
                  ·
                    refine ⟨5790688393125588702636541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7720917857500784936848721 5790688393125588702636541)
                    ·
                      refine ⟨2171508147422095763488703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790688393125588702636541 2171508147422095763488703)
                      ·
                        rfl

theorem cell23_4228997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_4228997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4228997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4228997 prefixEnd_4228997 := by exact prefixLift 4228997
  have htrace : WordTrace (prefixWord ++ tailWord_4228997) baseStart_4228997 baseEnd_4228997 := by
    simpa [prefixWord, tailWord_4228997, baseEnd_4228997] using wordTrace_append hprefix tailTrace_4228997
  have hstable : (prefixWord ++ tailWord_4228997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4228997).length < 2 ^ (prefixWord ++ tailWord_4228997).sum := by decide
  have hdescent : baseEnd_4228997 < baseStart_4228997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4228997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229050 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2]
def baseStart_4229050 : Nat := 118140960795 + 4229050 * 2 ^ 59
def prefixEnd_4229050 : Nat := 4983230072969 + 3 ^ 40 * 4229050 * 2
def baseEnd_4229050 : Nat := 2171535361896784056125959

theorem tailTrace_4229050 : CollatzResearch.WordTrace tailWord_4229050 prefixEnd_4229050 2171535361896784056125959 := by
  unfold tailWord_4229050
  simp only [CollatzResearch.WordTrace]
  refine ⟨38561531332220397270679151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102830750219254392721811069 38561531332220397270679151)
  ·
    refine ⟨57842296998330595906018727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38561531332220397270679151 57842296998330595906018727)
    ·
      refine ⟨86763445497495893859028091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57842296998330595906018727 86763445497495893859028091)
      ·
        refine ⟨130145168246243840788542137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86763445497495893859028091 130145168246243840788542137)
        ·
          refine ⟨97608876184682880591406603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130145168246243840788542137 97608876184682880591406603)
          ·
            refine ⟨146413314277024320887109905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97608876184682880591406603 146413314277024320887109905)
            ·
              refine ⟨109809985707768240665332429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146413314277024320887109905 109809985707768240665332429)
              ·
                refine ⟨41178744640413090249499661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109809985707768240665332429 41178744640413090249499661)
                ·
                  refine ⟨15442029240154908843562373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41178744640413090249499661 15442029240154908843562373)
                  ·
                    refine ⟨2895380482529045408167945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15442029240154908843562373 2895380482529045408167945)
                    ·
                      refine ⟨2171535361896784056125959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895380482529045408167945 2171535361896784056125959)
                      ·
                        rfl

theorem cell23_4229050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_4229050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229050 prefixEnd_4229050 := by exact prefixLift 4229050
  have htrace : WordTrace (prefixWord ++ tailWord_4229050) baseStart_4229050 baseEnd_4229050 := by
    simpa [prefixWord, tailWord_4229050, baseEnd_4229050] using wordTrace_append hprefix tailTrace_4229050
  have hstable : (prefixWord ++ tailWord_4229050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229050).length < 2 ^ (prefixWord ++ tailWord_4229050).sum := by decide
  have hdescent : baseEnd_4229050 < baseStart_4229050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229054 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_4229054 : Nat := 118140960795 + 4229054 * 2 ^ 59
def prefixEnd_4229054 : Nat := 4983230072969 + 3 ^ 40 * 4229054 * 2
def baseEnd_4229054 : Nat := 2171537415819402040475941

theorem tailTrace_4229054 : CollatzResearch.WordTrace tailWord_4229054 prefixEnd_4229054 2171537415819402040475941 := by
  unfold tailWord_4229054
  simp only [CollatzResearch.WordTrace]
  refine ⟨19280783902608387220732777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102830847480578065177241477 19280783902608387220732777)
  ·
    refine ⟨14460587926956290415549583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19280783902608387220732777 14460587926956290415549583)
    ·
      refine ⟨21690881890434435623324375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14460587926956290415549583 21690881890434435623324375)
      ·
        refine ⟨32536322835651653434986563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21690881890434435623324375 32536322835651653434986563)
        ·
          refine ⟨48804484253477480152479845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32536322835651653434986563 48804484253477480152479845)
          ·
            refine ⟨9150840797527027528589971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48804484253477480152479845 9150840797527027528589971)
            ·
              refine ⟨13726261196290541292884957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9150840797527027528589971 13726261196290541292884957)
              ·
                refine ⟨5147347948608952984831859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13726261196290541292884957 5147347948608952984831859)
                ·
                  refine ⟨7721021922913429477247789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5147347948608952984831859 7721021922913429477247789)
                  ·
                    refine ⟨2895383221092536053967921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7721021922913429477247789 2895383221092536053967921)
                    ·
                      refine ⟨2171537415819402040475941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895383221092536053967921 2171537415819402040475941)
                      ·
                        rfl

theorem cell23_4229054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_4229054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229054 prefixEnd_4229054 := by exact prefixLift 4229054
  have htrace : WordTrace (prefixWord ++ tailWord_4229054) baseStart_4229054 baseEnd_4229054 := by
    simpa [prefixWord, tailWord_4229054, baseEnd_4229054] using wordTrace_append hprefix tailTrace_4229054
  have hstable : (prefixWord ++ tailWord_4229054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229054).length < 2 ^ (prefixWord ++ tailWord_4229054).sum := by decide
  have hdescent : baseEnd_4229054 < baseStart_4229054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229067 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 4, 2, 2]
def baseStart_4229067 : Nat := 118140960795 + 4229067 * 2 ^ 59
def prefixEnd_4229067 : Nat := 4983230072969 + 3 ^ 40 * 4229067 * 2
def baseEnd_4229067 : Nat := 2171544091067910489613381

theorem tailTrace_4229067 : CollatzResearch.WordTrace tailWord_4229067 prefixEnd_4229067 2171544091067910489613381 := by
  unfold tailWord_4229067
  simp only [CollatzResearch.WordTrace]
  refine ⟨154246745369820000986085455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102831163579880000657390303 154246745369820000986085455)
  ·
    refine ⟨231370118054730001479128183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154246745369820000986085455 231370118054730001479128183)
    ·
      refine ⟨347055177082095002218692275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231370118054730001479128183 347055177082095002218692275)
      ·
        refine ⟨520582765623142503328038413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347055177082095002218692275 520582765623142503328038413)
        ·
          refine ⟨195218537108678438748014405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 520582765623142503328038413 195218537108678438748014405)
          ·
            refine ⟨36603475707877207265252701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195218537108678438748014405 36603475707877207265252701)
            ·
              refine ⟨13726303390453952724469763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36603475707877207265252701 13726303390453952724469763)
              ·
                refine ⟨20589455085680929086704645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13726303390453952724469763 20589455085680929086704645)
                ·
                  refine ⟨3860522828565174203757121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20589455085680929086704645 3860522828565174203757121)
                  ·
                    refine ⟨2895392121423880652817841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3860522828565174203757121 2895392121423880652817841)
                    ·
                      refine ⟨2171544091067910489613381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895392121423880652817841 2171544091067910489613381)
                      ·
                        rfl

theorem cell23_4229067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 2, 2].length) (baseStart_4229067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229067 prefixEnd_4229067 := by exact prefixLift 4229067
  have htrace : WordTrace (prefixWord ++ tailWord_4229067) baseStart_4229067 baseEnd_4229067 := by
    simpa [prefixWord, tailWord_4229067, baseEnd_4229067] using wordTrace_append hprefix tailTrace_4229067
  have hstable : (prefixWord ++ tailWord_4229067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229067).length < 2 ^ (prefixWord ++ tailWord_4229067).sum := by decide
  have hdescent : baseEnd_4229067 < baseStart_4229067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229078 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_4229078 : Nat := 118140960795 + 4229078 * 2 ^ 59
def prefixEnd_4229078 : Nat := 4983230072969 + 3 ^ 40 * 4229078 * 2
def baseEnd_4229078 : Nat := 2171549739355109946575831

theorem tailTrace_4229078 : CollatzResearch.WordTrace tailWord_4229078 prefixEnd_4229078 2171549739355109946575831 := by
  unfold tailWord_4229078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640446660798759366545993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102831431048520099909823925 9640446660798759366545993)
  ·
    refine ⟨7230334995599069524909495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9640446660798759366545993 7230334995599069524909495)
    ·
      refine ⟨10845502493398604287364243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230334995599069524909495 10845502493398604287364243)
      ·
        refine ⟨16268253740097906431046365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10845502493398604287364243 16268253740097906431046365)
        ·
          refine ⟨6100595152536714911642387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16268253740097906431046365 6100595152536714911642387)
          ·
            refine ⟨9150892728805072367463581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6100595152536714911642387 9150892728805072367463581)
            ·
              refine ⟨3431584773301902137798843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9150892728805072367463581 3431584773301902137798843)
              ·
                refine ⟨5147377159952853206698265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431584773301902137798843 5147377159952853206698265)
                ·
                  refine ⟨3860532869964639905023699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5147377159952853206698265 3860532869964639905023699)
                  ·
                    refine ⟨5790799304946959857535549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3860532869964639905023699 5790799304946959857535549)
                    ·
                      refine ⟨2171549739355109946575831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790799304946959857535549 2171549739355109946575831)
                      ·
                        rfl

theorem cell23_4229078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_4229078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229078 prefixEnd_4229078 := by exact prefixLift 4229078
  have htrace : WordTrace (prefixWord ++ tailWord_4229078) baseStart_4229078 baseEnd_4229078 := by
    simpa [prefixWord, tailWord_4229078, baseEnd_4229078] using wordTrace_append hprefix tailTrace_4229078
  have hstable : (prefixWord ++ tailWord_4229078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229078).length < 2 ^ (prefixWord ++ tailWord_4229078).sum := by decide
  have hdescent : baseEnd_4229078 < baseStart_4229078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229103 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 1, 7]
def baseStart_4229103 : Nat := 118140960795 + 4229103 * 2 ^ 59
def prefixEnd_4229103 : Nat := 4983230072969 + 3 ^ 40 * 4229103 * 2
def baseEnd_4229103 : Nat := 723854192123824116254405

theorem tailTrace_4229103 : CollatzResearch.WordTrace tailWord_4229103 prefixEnd_4229103 723854192123824116254405 := by
  unfold tailWord_4229103
  simp only [CollatzResearch.WordTrace]
  refine ⟨154248058397689579134395963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102832038931793052756263975 154248058397689579134395963)
  ·
    refine ⟨231372087596534368701593945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154248058397689579134395963 231372087596534368701593945)
    ·
      refine ⟨173529065697400776526195459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231372087596534368701593945 173529065697400776526195459)
      ·
        refine ⟨260293598546101164789293189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173529065697400776526195459 260293598546101164789293189)
        ·
          refine ⟨48805049727393968397992473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260293598546101164789293189 48805049727393968397992473)
          ·
            refine ⟨36603787295545476298494355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48805049727393968397992473 36603787295545476298494355)
            ·
              refine ⟨54905680943318214447741533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36603787295545476298494355 54905680943318214447741533)
              ·
                refine ⟨20589630353744330417903075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54905680943318214447741533 20589630353744330417903075)
                ·
                  refine ⟨30884445530616495626854613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20589630353744330417903075 30884445530616495626854613)
                  ·
                    refine ⟨723854192123824116254405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30884445530616495626854613 723854192123824116254405)
                    ·
                      rfl

theorem cell23_4229103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_4229103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229103 prefixEnd_4229103 := by exact prefixLift 4229103
  have htrace : WordTrace (prefixWord ++ tailWord_4229103) baseStart_4229103 baseEnd_4229103 := by
    simpa [prefixWord, tailWord_4229103, baseEnd_4229103] using wordTrace_append hprefix tailTrace_4229103
  have hstable : (prefixWord ++ tailWord_4229103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229103).length < 2 ^ (prefixWord ++ tailWord_4229103).sum := by decide
  have hdescent : baseEnd_4229103 < baseStart_4229103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229124 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 7]
def baseStart_4229124 : Nat := 118140960795 + 4229124 * 2 ^ 59
def prefixEnd_4229124 : Nat := 4983230072969 + 3 ^ 40 * 4229124 * 2
def baseEnd_4229124 : Nat := 241285928829468529622291

theorem tailTrace_4229124 : CollatzResearch.WordTrace tailWord_4229124 prefixEnd_4229124 241285928829468529622291 := by
  unfold tailWord_4229124
  simp only [CollatzResearch.WordTrace]
  refine ⟨77124412165306749860455213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102832549553742333147273617 77124412165306749860455213)
  ·
    refine ⟨28921654561990031197670705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77124412165306749860455213 28921654561990031197670705)
    ·
      refine ⟨21691240921492523398253029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28921654561990031197670705 21691240921492523398253029)
      ·
        refine ⟨4067107672779848137172443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21691240921492523398253029 4067107672779848137172443)
        ·
          refine ⟨6100661509169772205758665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067107672779848137172443 6100661509169772205758665)
          ·
            refine ⟨4575496131877329154318999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6100661509169772205758665 4575496131877329154318999)
            ·
              refine ⟨6863244197815993731478499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575496131877329154318999 6863244197815993731478499)
              ·
                refine ⟨10294866296723990597217749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6863244197815993731478499 10294866296723990597217749)
                ·
                  refine ⟨241285928829468529622291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10294866296723990597217749 241285928829468529622291)
                  ·
                    rfl

theorem cell23_4229124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_4229124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229124 prefixEnd_4229124 := by exact prefixLift 4229124
  have htrace : WordTrace (prefixWord ++ tailWord_4229124) baseStart_4229124 baseEnd_4229124 := by
    simpa [prefixWord, tailWord_4229124, baseEnd_4229124] using wordTrace_append hprefix tailTrace_4229124
  have hstable : (prefixWord ++ tailWord_4229124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229124).length < 2 ^ (prefixWord ++ tailWord_4229124).sum := by decide
  have hdescent : baseEnd_4229124 < baseStart_4229124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229157 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_4229157 : Nat := 118140960795 + 4229157 * 2 ^ 59
def prefixEnd_4229157 : Nat := 4983230072969 + 3 ^ 40 * 4229157 * 2
def baseEnd_4229157 : Nat := 2171590304326815137487967

theorem tailTrace_4229157 : CollatzResearch.WordTrace tailWord_4229157 prefixEnd_4229157 2171590304326815137487967 := by
  unfold tailWord_4229157
  simp only [CollatzResearch.WordTrace]
  refine ⟨154250027939493946356861725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102833351959662630904574483 154250027939493946356861725)
  ·
    refine ⟨57843760477310229883823147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154250027939493946356861725 57843760477310229883823147)
    ·
      refine ⟨86765640715965344825734721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57843760477310229883823147 86765640715965344825734721)
      ·
        refine ⟨65074230536974008619301041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86765640715965344825734721 65074230536974008619301041)
        ·
          refine ⟨48805672902730506464475781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65074230536974008619301041 48805672902730506464475781)
          ·
            refine ⟨9151063669261969962089209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48805672902730506464475781 9151063669261969962089209)
            ·
              refine ⟨6863297751946477471566907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9151063669261969962089209 6863297751946477471566907)
              ·
                refine ⟨10294946627919716207350361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6863297751946477471566907 10294946627919716207350361)
                ·
                  refine ⟨7721209970939787155512771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10294946627919716207350361 7721209970939787155512771)
                  ·
                    refine ⟨11581814956409680733269157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7721209970939787155512771 11581814956409680733269157)
                    ·
                      refine ⟨2171590304326815137487967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11581814956409680733269157 2171590304326815137487967)
                      ·
                        rfl

theorem cell23_4229157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_4229157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229157 prefixEnd_4229157 := by exact prefixLift 4229157
  have htrace : WordTrace (prefixWord ++ tailWord_4229157) baseStart_4229157 baseEnd_4229157 := by
    simpa [prefixWord, tailWord_4229157, baseEnd_4229157] using wordTrace_append hprefix tailTrace_4229157
  have hstable : (prefixWord ++ tailWord_4229157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229157).length < 2 ^ (prefixWord ++ tailWord_4229157).sum := by decide
  have hdescent : baseEnd_4229157 < baseStart_4229157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229163 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 8]
def baseStart_4229163 : Nat := 118140960795 + 4229163 * 2 ^ 59
def prefixEnd_4229163 : Nat := 4983230072969 + 3 ^ 40 * 4229163 * 2
def baseEnd_4229163 : Nat := 241288153912304679334771

theorem tailTrace_4229163 : CollatzResearch.WordTrace tailWord_4229163 prefixEnd_4229163 241288153912304679334771 := by
  unfold tailWord_4229163
  simp only [CollatzResearch.WordTrace]
  refine ⟨154250246777472209381580143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102833497851648139587720095 154250246777472209381580143)
  ·
    refine ⟨231375370166208314072370215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154250246777472209381580143 231375370166208314072370215)
    ·
      refine ⟨347063055249312471108555323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231375370166208314072370215 347063055249312471108555323)
      ·
        refine ⟨520594582873968706662832985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347063055249312471108555323 520594582873968706662832985)
        ·
          refine ⟨390445937155476529997124739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520594582873968706662832985 390445937155476529997124739)
          ·
            refine ⟨585668905733214794995687109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390445937155476529997124739 585668905733214794995687109)
            ·
              refine ⟨109812919824977774061691333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 585668905733214794995687109 109812919824977774061691333)
              ·
                refine ⟨20589922467183332636567125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109812919824977774061691333 20589922467183332636567125)
                ·
                  refine ⟨241288153912304679334771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20589922467183332636567125 241288153912304679334771)
                  ·
                    rfl

theorem cell23_4229163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 8].length) (baseStart_4229163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229163 prefixEnd_4229163 := by exact prefixLift 4229163
  have htrace : WordTrace (prefixWord ++ tailWord_4229163) baseStart_4229163 baseEnd_4229163 := by
    simpa [prefixWord, tailWord_4229163, baseEnd_4229163] using wordTrace_append hprefix tailTrace_4229163
  have hstable : (prefixWord ++ tailWord_4229163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229163).length < 2 ^ (prefixWord ++ tailWord_4229163).sum := by decide
  have hdescent : baseEnd_4229163 < baseStart_4229163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229174 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_4229174 : Nat := 118140960795 + 4229174 * 2 ^ 59
def prefixEnd_4229174 : Nat := 4983230072969 + 3 ^ 40 * 4229174 * 2
def baseEnd_4229174 : Nat := 2171599033497941570975389

theorem tailTrace_4229174 : CollatzResearch.WordTrace tailWord_4229174 prefixEnd_4229174 2171599033497941570975389 := by
  unfold tailWord_4229174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9640665498777022391264411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102833765320288238840153717 9640665498777022391264411)
  ·
    refine ⟨14460998248165533586896617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9640665498777022391264411 14460998248165533586896617)
    ·
      refine ⟨10845748686124150190172463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14460998248165533586896617 10845748686124150190172463)
      ·
        refine ⟨16268623029186225285258695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10845748686124150190172463 16268623029186225285258695)
        ·
          refine ⟨24402934543779337927888043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16268623029186225285258695 24402934543779337927888043)
          ·
            refine ⟨36604401815669006891832065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24402934543779337927888043 36604401815669006891832065)
            ·
              refine ⟨27453301361751755168874049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36604401815669006891832065 27453301361751755168874049)
              ·
                refine ⟨20589976021313816376655537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27453301361751755168874049 20589976021313816376655537)
                ·
                  refine ⟨15442482015985362282491653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20589976021313816376655537 15442482015985362282491653)
                  ·
                    refine ⟨2895465377997255427967185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15442482015985362282491653 2895465377997255427967185)
                    ·
                      refine ⟨2171599033497941570975389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895465377997255427967185 2171599033497941570975389)
                      ·
                        rfl

theorem cell23_4229174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_4229174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229174 prefixEnd_4229174 := by exact prefixLift 4229174
  have htrace : WordTrace (prefixWord ++ tailWord_4229174) baseStart_4229174 baseEnd_4229174 := by
    simpa [prefixWord, tailWord_4229174, baseEnd_4229174] using wordTrace_append hprefix tailTrace_4229174
  have hstable : (prefixWord ++ tailWord_4229174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229174).length < 2 ^ (prefixWord ++ tailWord_4229174).sum := by decide
  have hdescent : baseEnd_4229174 < baseStart_4229174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229184 : List Nat := [2, 1, 1, 2, 2, 5, 1, 4, 1, 4]
def baseStart_4229184 : Nat := 118140960795 + 4229184 * 2 ^ 59
def prefixEnd_4229184 : Nat := 4983230072969 + 3 ^ 40 * 4229184 * 2
def baseEnd_4229184 : Nat := 723868056101495510616781

theorem tailTrace_4229184 : CollatzResearch.WordTrace tailWord_4229184 prefixEnd_4229184 723868056101495510616781 := by
  unfold tailWord_4229184
  simp only [CollatzResearch.WordTrace]
  refine ⟨77125506355198064984047303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102834008473597419978729737 77125506355198064984047303)
  ·
    refine ⟨115688259532797097476070955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77125506355198064984047303 115688259532797097476070955)
    ·
      refine ⟨173532389299195646214106433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115688259532797097476070955 173532389299195646214106433)
      ·
        refine ⟨130149291974396734660579825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173532389299195646214106433 130149291974396734660579825)
        ·
          refine ⟨97611968980797550995434869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130149291974396734660579825 97611968980797550995434869)
          ·
            refine ⟨9151122091949770405822019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97611968980797550995434869 9151122091949770405822019)
            ·
              refine ⟨13726683137924655608733029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9151122091949770405822019 13726683137924655608733029)
              ·
                refine ⟨2573753088360872926637443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13726683137924655608733029 2573753088360872926637443)
                ·
                  refine ⟨3860629632541309389956165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573753088360872926637443 3860629632541309389956165)
                  ·
                    refine ⟨723868056101495510616781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860629632541309389956165 723868056101495510616781)
                    ·
                      rfl

theorem cell23_4229184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 1, 4].length) (baseStart_4229184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229184 prefixEnd_4229184 := by exact prefixLift 4229184
  have htrace : WordTrace (prefixWord ++ tailWord_4229184) baseStart_4229184 baseEnd_4229184 := by
    simpa [prefixWord, tailWord_4229184, baseEnd_4229184] using wordTrace_append hprefix tailTrace_4229184
  have hstable : (prefixWord ++ tailWord_4229184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229184).length < 2 ^ (prefixWord ++ tailWord_4229184).sum := by decide
  have hdescent : baseEnd_4229184 < baseStart_4229184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229197 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 6]
def baseStart_4229197 : Nat := 118140960795 + 4229197 * 2 ^ 59
def prefixEnd_4229197 : Nat := 4983230072969 + 3 ^ 40 * 4229197 * 2
def baseEnd_4229197 : Nat := 241290093728110553443087

theorem tailTrace_4229197 : CollatzResearch.WordTrace tailWord_4229197 prefixEnd_4229197 241290093728110553443087 := by
  unfold tailWord_4229197
  simp only [CollatzResearch.WordTrace]
  refine ⟨154251486859349033188317845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102834324572899355458878563 154251486859349033188317845)
  ·
    refine ⟨7230538446531985930702399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154251486859349033188317845 7230538446531985930702399)
    ·
      refine ⟨10845807669797978896053599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7230538446531985930702399 10845807669797978896053599)
      ·
        refine ⟨16268711504696968344080399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10845807669797978896053599 16268711504696968344080399)
        ·
          refine ⟨24403067257045452516120599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16268711504696968344080399 24403067257045452516120599)
          ·
            refine ⟨36604600885568178774180899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24403067257045452516120599 36604600885568178774180899)
            ·
              refine ⟨54906901328352268161271349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36604600885568178774180899 54906901328352268161271349)
              ·
                refine ⟨5147521999533025140119189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54906901328352268161271349 5147521999533025140119189)
                ·
                  refine ⟨241290093728110553443087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5147521999533025140119189 241290093728110553443087)
                  ·
                    rfl

theorem cell23_4229197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_4229197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229197 prefixEnd_4229197 := by exact prefixLift 4229197
  have htrace : WordTrace (prefixWord ++ tailWord_4229197) baseStart_4229197 baseEnd_4229197 := by
    simpa [prefixWord, tailWord_4229197, baseEnd_4229197] using wordTrace_append hprefix tailTrace_4229197
  have hstable : (prefixWord ++ tailWord_4229197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229197).length < 2 ^ (prefixWord ++ tailWord_4229197).sum := by decide
  have hdescent : baseEnd_4229197 < baseStart_4229197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229207 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_4229207 : Nat := 118140960795 + 4229207 * 2 ^ 59
def prefixEnd_4229207 : Nat := 4983230072969 + 3 ^ 40 * 4229207 * 2
def baseEnd_4229207 : Nat := 2171615978359539941862737

theorem tailTrace_4229207 : CollatzResearch.WordTrace tailWord_4229207 prefixEnd_4229207 2171615978359539941862737 := by
  unfold tailWord_4229207
  simp only [CollatzResearch.WordTrace]
  refine ⟨154251851589312804896181875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102834567726208536597454583 154251851589312804896181875)
  ·
    refine ⟨231377777383969207344272813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154251851589312804896181875 231377777383969207344272813)
    ·
      refine ⟨86766666518988452754102305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231377777383969207344272813 86766666518988452754102305)
      ·
        refine ⟨65074999889241339565576729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86766666518988452754102305 65074999889241339565576729)
        ·
          refine ⟨48806249916931004674182547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65074999889241339565576729 48806249916931004674182547)
          ·
            refine ⟨73209374875396507011273821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48806249916931004674182547 73209374875396507011273821)
            ·
              refine ⟨27453515578273690129227683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73209374875396507011273821 27453515578273690129227683)
              ·
                refine ⟨41180273367410535193841525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27453515578273690129227683 41180273367410535193841525)
                ·
                  refine ⟨3860650628194737674422643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41180273367410535193841525 3860650628194737674422643)
                  ·
                    refine ⟨5790975942292106511633965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3860650628194737674422643 5790975942292106511633965)
                    ·
                      refine ⟨2171615978359539941862737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5790975942292106511633965 2171615978359539941862737)
                      ·
                        rfl

theorem cell23_4229207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_4229207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229207 prefixEnd_4229207 := by exact prefixLift 4229207
  have htrace : WordTrace (prefixWord ++ tailWord_4229207) baseStart_4229207 baseEnd_4229207 := by
    simpa [prefixWord, tailWord_4229207, baseEnd_4229207] using wordTrace_append hprefix tailTrace_4229207
  have hstable : (prefixWord ++ tailWord_4229207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229207).length < 2 ^ (prefixWord ++ tailWord_4229207).sum := by decide
  have hdescent : baseEnd_4229207 < baseStart_4229207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229210 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_4229210 : Nat := 118140960795 + 4229210 * 2 ^ 59
def prefixEnd_4229210 : Nat := 4983230072969 + 3 ^ 40 * 4229210 * 2
def baseEnd_4229210 : Nat := 723872506267167810041741

theorem tailTrace_4229210 : CollatzResearch.WordTrace tailWord_4229210 prefixEnd_4229210 723872506267167810041741 := by
  unfold tailWord_4229210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38562990252075484102135271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102834640672201290939027389 38562990252075484102135271)
  ·
    refine ⟨57844485378113226153202907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38562990252075484102135271 57844485378113226153202907)
    ·
      refine ⟨86766728067169839229804361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57844485378113226153202907 86766728067169839229804361)
      ·
        refine ⟨65075046050377379422353271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86766728067169839229804361 65075046050377379422353271)
        ·
          refine ⟨97612569075566069133529907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65075046050377379422353271 97612569075566069133529907)
          ·
            refine ⟨146418853613349103700294861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97612569075566069133529907 146418853613349103700294861)
            ·
              refine ⟨54907070105005913887610573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146418853613349103700294861 54907070105005913887610573)
              ·
                refine ⟨20590151289377217707853965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54907070105005913887610573 20590151289377217707853965)
                ·
                  refine ⟨7721306733516456640445237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20590151289377217707853965 7721306733516456640445237)
                  ·
                    refine ⟨723872506267167810041741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7721306733516456640445237 723872506267167810041741)
                    ·
                      rfl

theorem cell23_4229210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_4229210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229210 prefixEnd_4229210 := by exact prefixLift 4229210
  have htrace : WordTrace (prefixWord ++ tailWord_4229210) baseStart_4229210 baseEnd_4229210 := by
    simpa [prefixWord, tailWord_4229210, baseEnd_4229210] using wordTrace_append hprefix tailTrace_4229210
  have hstable : (prefixWord ++ tailWord_4229210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229210).length < 2 ^ (prefixWord ++ tailWord_4229210).sum := by decide
  have hdescent : baseEnd_4229210 < baseStart_4229210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229218 : List Nat := [3, 3, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4229218 : Nat := 118140960795 + 4229218 * 2 ^ 59
def prefixEnd_4229218 : Nat := 4983230072969 + 3 ^ 40 * 4229218 * 2
def baseEnd_4229218 : Nat := 723873875548913132941729

theorem tailTrace_4229218 : CollatzResearch.WordTrace tailWord_4229218 prefixEnd_4229218 723873875548913132941729 := by
  unfold tailWord_4229218
  simp only [CollatzResearch.WordTrace]
  refine ⟨38563063198068238443708077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102834835194848635849888205 38563063198068238443708077)
  ·
    refine ⟨14461148699275589416390529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38563063198068238443708077 14461148699275589416390529)
    ·
      refine ⟨10845861524456692062292897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14461148699275589416390529 10845861524456692062292897)
      ·
        refine ⟨8134396143342519046719673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10845861524456692062292897 8134396143342519046719673)
        ·
          refine ⟨6100797107506889285039755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8134396143342519046719673 6100797107506889285039755)
          ·
            refine ⟨9151195661260333927559633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6100797107506889285039755 9151195661260333927559633)
            ·
              refine ⟨6863396745945250445669725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9151195661260333927559633 6863396745945250445669725)
              ·
                refine ⟨2573773779729468917126147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6863396745945250445669725 2573773779729468917126147)
                ·
                  refine ⟨3860660669594203375689221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573773779729468917126147 3860660669594203375689221)
                  ·
                    refine ⟨723873875548913132941729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860660669594203375689221 723873875548913132941729)
                    ·
                      rfl

theorem cell23_4229218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4229218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229218 prefixEnd_4229218 := by exact prefixLift 4229218
  have htrace : WordTrace (prefixWord ++ tailWord_4229218) baseStart_4229218 baseEnd_4229218 := by
    simpa [prefixWord, tailWord_4229218, baseEnd_4229218] using wordTrace_append hprefix tailTrace_4229218
  have hstable : (prefixWord ++ tailWord_4229218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229218).length < 2 ^ (prefixWord ++ tailWord_4229218).sum := by decide
  have hdescent : baseEnd_4229218 < baseStart_4229218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229241 : List Nat := [1, 2, 1, 3, 4, 1, 2, 4, 1, 1, 3]
def baseStart_4229241 : Nat := 118140960795 + 4229241 * 2 ^ 59
def prefixEnd_4229241 : Nat := 4983230072969 + 3 ^ 40 * 4229241 * 2
def baseEnd_4229241 : Nat := 2171633436701792808837581

theorem tailTrace_4229241 : CollatzResearch.WordTrace tailWord_4229241 prefixEnd_4229241 2171633436701792808837581 := by
  unfold tailWord_4229241
  simp only [CollatzResearch.WordTrace]
  refine ⟨154253091671189628702919577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102835394447459752468613051 154253091671189628702919577)
  ·
    refine ⟨115689818753392221527189683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154253091671189628702919577 115689818753392221527189683)
    ·
      refine ⟨173534728130088332290784525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115689818753392221527189683 173534728130088332290784525)
      ·
        refine ⟨65075523048783124609044197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173534728130088332290784525 65075523048783124609044197)
        ·
          refine ⟨12201660571646835864195787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65075523048783124609044197 12201660571646835864195787)
          ·
            refine ⟨18302490857470253796293681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12201660571646835864195787 18302490857470253796293681)
            ·
              refine ⟨13726868143102690347220261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18302490857470253796293681 13726868143102690347220261)
              ·
                refine ⟨2573787776831754440103799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13726868143102690347220261 2573787776831754440103799)
                ·
                  refine ⟨3860681665247631660155699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573787776831754440103799 3860681665247631660155699)
                  ·
                    refine ⟨5791022497871447490233549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3860681665247631660155699 5791022497871447490233549)
                    ·
                      refine ⟨2171633436701792808837581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5791022497871447490233549 2171633436701792808837581)
                      ·
                        rfl

theorem cell23_4229241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_4229241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229241 prefixEnd_4229241 := by exact prefixLift 4229241
  have htrace : WordTrace (prefixWord ++ tailWord_4229241) baseStart_4229241 baseEnd_4229241 := by
    simpa [prefixWord, tailWord_4229241, baseEnd_4229241] using wordTrace_append hprefix tailTrace_4229241
  have hstable : (prefixWord ++ tailWord_4229241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229241).length < 2 ^ (prefixWord ++ tailWord_4229241).sum := by decide
  have hdescent : baseEnd_4229241 < baseStart_4229241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229264 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 3, 2, 2]
def baseStart_4229264 : Nat := 118140960795 + 4229264 * 2 ^ 59
def prefixEnd_4229264 : Nat := 4983230072969 + 3 ^ 40 * 4229264 * 2
def baseEnd_4229264 : Nat := 2171645246756846218849975

theorem tailTrace_4229264 : CollatzResearch.WordTrace tailWord_4229264 prefixEnd_4229264 2171645246756846218849975 := by
  unfold tailWord_4229264
  simp only [CollatzResearch.WordTrace]
  refine ⟨77126965275053151815503423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102835953700070869087337897 77126965275053151815503423)
  ·
    refine ⟨115690447912579727723255135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77126965275053151815503423 115690447912579727723255135)
    ·
      refine ⟨173535671868869591584882703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115690447912579727723255135 173535671868869591584882703)
      ·
        refine ⟨260303507803304387377324055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173535671868869591584882703 260303507803304387377324055)
        ·
          refine ⟨390455261704956581065986083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260303507803304387377324055 390455261704956581065986083)
          ·
            refine ⟨585682892557434871598979125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390455261704956581065986083 585682892557434871598979125)
            ·
              refine ⟨54907771177259519212404293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 585682892557434871598979125 54907771177259519212404293)
              ·
                refine ⟨10295207095736159852325805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54907771177259519212404293 10295207095736159852325805)
                ·
                  refine ⟨3860702660901059944622177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10295207095736159852325805 3860702660901059944622177)
                  ·
                    refine ⟨2895526995675794958466633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3860702660901059944622177 2895526995675794958466633)
                    ·
                      refine ⟨2171645246756846218849975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895526995675794958466633 2171645246756846218849975)
                      ·
                        rfl

theorem cell23_4229264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3, 2, 2].length) (baseStart_4229264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229264 prefixEnd_4229264 := by exact prefixLift 4229264
  have htrace : WordTrace (prefixWord ++ tailWord_4229264) baseStart_4229264 baseEnd_4229264 := by
    simpa [prefixWord, tailWord_4229264, baseEnd_4229264] using wordTrace_append hprefix tailTrace_4229264
  have hstable : (prefixWord ++ tailWord_4229264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229264).length < 2 ^ (prefixWord ++ tailWord_4229264).sum := by decide
  have hdescent : baseEnd_4229264 < baseStart_4229264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229284 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_4229284 : Nat := 118140960795 + 4229284 * 2 ^ 59
def prefixEnd_4229284 : Nat := 4983230072969 + 3 ^ 40 * 4229284 * 2
def baseEnd_4229284 : Nat := 2171655516369936140599883

theorem tailTrace_4229284 : CollatzResearch.WordTrace tailWord_4229284 prefixEnd_4229284 2171655516369936140599883 := by
  unfold tailWord_4229284
  simp only [CollatzResearch.WordTrace]
  refine ⟨77127330005016923523367453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102836440006689231364489937 77127330005016923523367453)
  ·
    refine ⟨28922748751881346321262795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77127330005016923523367453 28922748751881346321262795)
    ·
      refine ⟨43384123127822019481894193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28922748751881346321262795 43384123127822019481894193)
      ·
        refine ⟨32538092345866514611420645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43384123127822019481894193 32538092345866514611420645)
        ·
          refine ⟨6100892314849971489641371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32538092345866514611420645 6100892314849971489641371)
          ·
            refine ⟨9151338472274957234462057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6100892314849971489641371 9151338472274957234462057)
            ·
              refine ⟨6863503854206217925846543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9151338472274957234462057 6863503854206217925846543)
              ·
                refine ⟨10295255781309326888769815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6863503854206217925846543 10295255781309326888769815)
                ·
                  refine ⟨15442883671963990333154723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10295255781309326888769815 15442883671963990333154723)
                  ·
                    refine ⟨23164325507945985499732085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15442883671963990333154723 23164325507945985499732085)
                    ·
                      refine ⟨2171655516369936140599883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23164325507945985499732085 2171655516369936140599883)
                      ·
                        rfl

theorem cell23_4229284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_4229284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229284 prefixEnd_4229284 := by exact prefixLift 4229284
  have htrace : WordTrace (prefixWord ++ tailWord_4229284) baseStart_4229284 baseEnd_4229284 := by
    simpa [prefixWord, tailWord_4229284, baseEnd_4229284] using wordTrace_append hprefix tailTrace_4229284
  have hstable : (prefixWord ++ tailWord_4229284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229284).length < 2 ^ (prefixWord ++ tailWord_4229284).sum := by decide
  have hdescent : baseEnd_4229284 < baseStart_4229284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229308 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_4229308 : Nat := 118140960795 + 4229308 * 2 ^ 59
def prefixEnd_4229308 : Nat := 4983230072969 + 3 ^ 40 * 4229308 * 2
def baseEnd_4229308 : Nat := 723889279968548015566591

theorem tailTrace_4229308 : CollatzResearch.WordTrace tailWord_4229308 prefixEnd_4229308 723889279968548015566591 := by
  unfold tailWord_4229308
  simp only [CollatzResearch.WordTrace]
  refine ⟨77127767680973449572804289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102837023574631266097072385 77127767680973449572804289)
  ·
    refine ⟨57845825760730087179603217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77127767680973449572804289 57845825760730087179603217)
    ·
      refine ⟨43384369320547565384702413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57845825760730087179603217 43384369320547565384702413)
      ·
        refine ⟨16269138495205337019263405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43384369320547565384702413 16269138495205337019263405)
        ·
          refine ⟨6100926935702001382223777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16269138495205337019263405 6100926935702001382223777)
          ·
            refine ⟨4575695201776501036667833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6100926935702001382223777 4575695201776501036667833)
            ·
              refine ⟨3431771401332375777500875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4575695201776501036667833 3431771401332375777500875)
              ·
                refine ⟨5147657101998563666251313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3431771401332375777500875 5147657101998563666251313)
                ·
                  refine ⟨3860742826498922749688485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5147657101998563666251313 3860742826498922749688485)
                  ·
                    refine ⟨723889279968548015566591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860742826498922749688485 723889279968548015566591)
                    ·
                      rfl

theorem cell23_4229308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_4229308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229308 prefixEnd_4229308 := by exact prefixLift 4229308
  have htrace : WordTrace (prefixWord ++ tailWord_4229308) baseStart_4229308 baseEnd_4229308 := by
    simpa [prefixWord, tailWord_4229308, baseEnd_4229308] using wordTrace_append hprefix tailTrace_4229308
  have hstable : (prefixWord ++ tailWord_4229308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229308).length < 2 ^ (prefixWord ++ tailWord_4229308).sum := by decide
  have hdescent : baseEnd_4229308 < baseStart_4229308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229320 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_4229320 : Nat := 118140960795 + 4229320 * 2 ^ 59
def prefixEnd_4229320 : Nat := 4983230072969 + 3 ^ 40 * 4229320 * 2
def baseEnd_4229320 : Nat := 2171674001673497999749717

theorem tailTrace_4229320 : CollatzResearch.WordTrace tailWord_4229320 prefixEnd_4229320 2171674001673497999749717 := by
  unfold tailWord_4229320
  simp only [CollatzResearch.WordTrace]
  refine ⟨77127986518951712597522707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102837315358602283463363609 77127986518951712597522707)
  ·
    refine ⟨115691979778427568896284061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77127986518951712597522707 115691979778427568896284061)
    ·
      refine ⟨43384492416910338336106523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115691979778427568896284061 43384492416910338336106523)
      ·
        refine ⟨65076738625365507504159785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43384492416910338336106523 65076738625365507504159785)
        ·
          refine ⟨48807553969024130628119839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65076738625365507504159785 48807553969024130628119839)
          ·
            refine ⟨73211330953536195942179759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48807553969024130628119839 73211330953536195942179759)
            ·
              refine ⟨109816996430304293913269639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73211330953536195942179759 109816996430304293913269639)
              ·
                refine ⟨164725494645456440869904459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109816996430304293913269639 164725494645456440869904459)
                ·
                  refine ⟨247088241968184661304856689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164725494645456440869904459 247088241968184661304856689)
                  ·
                    refine ⟨185316181476138495978642517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 247088241968184661304856689 185316181476138495978642517)
                    ·
                      refine ⟨2171674001673497999749717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 185316181476138495978642517 2171674001673497999749717)
                      ·
                        rfl

theorem cell23_4229320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_4229320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229320 prefixEnd_4229320 := by exact prefixLift 4229320
  have htrace : WordTrace (prefixWord ++ tailWord_4229320) baseStart_4229320 baseEnd_4229320 := by
    simpa [prefixWord, tailWord_4229320, baseEnd_4229320] using wordTrace_append hprefix tailTrace_4229320
  have hstable : (prefixWord ++ tailWord_4229320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229320).length < 2 ^ (prefixWord ++ tailWord_4229320).sum := by decide
  have hdescent : baseEnd_4229320 < baseStart_4229320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229354 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_4229354 : Nat := 118140960795 + 4229354 * 2 ^ 59
def prefixEnd_4229354 : Nat := 4983230072969 + 3 ^ 40 * 4229354 * 2
def baseEnd_4229354 : Nat := 2171691460015750866724561

theorem tailTrace_4229354 : CollatzResearch.WordTrace tailWord_4229354 prefixEnd_4229354 2171691460015750866724561 := by
  unfold tailWord_4229354
  simp only [CollatzResearch.WordTrace]
  refine ⟨38564303279945062250445779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102838142079853499334522077 38564303279945062250445779)
  ·
    refine ⟨57846454919917593375668669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38564303279945062250445779 57846454919917593375668669)
    ·
      refine ⟨21692420594969097515875751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57846454919917593375668669 21692420594969097515875751)
      ·
        refine ⟨32538630892453646273813627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21692420594969097515875751 32538630892453646273813627)
        ·
          refine ⟨48807946338680469410720441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32538630892453646273813627 48807946338680469410720441)
          ·
            refine ⟨36605959754010352058040331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48807946338680469410720441 36605959754010352058040331)
            ·
              refine ⟨54908939631015528087060497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36605959754010352058040331 54908939631015528087060497)
              ·
                refine ⟨41181704723261646065295373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54908939631015528087060497 41181704723261646065295373)
                ·
                  refine ⟨15443139271223117274485765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41181704723261646065295373 15443139271223117274485765)
                  ·
                    refine ⟨2895588613354334488966081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15443139271223117274485765 2895588613354334488966081)
                    ·
                      refine ⟨2171691460015750866724561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895588613354334488966081 2171691460015750866724561)
                      ·
                        rfl

theorem cell23_4229354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_4229354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229354 prefixEnd_4229354 := by exact prefixLift 4229354
  have htrace : WordTrace (prefixWord ++ tailWord_4229354) baseStart_4229354 baseEnd_4229354 := by
    simpa [prefixWord, tailWord_4229354, baseEnd_4229354] using wordTrace_append hprefix tailTrace_4229354
  have hstable : (prefixWord ++ tailWord_4229354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229354).length < 2 ^ (prefixWord ++ tailWord_4229354).sum := by decide
  have hdescent : baseEnd_4229354 < baseStart_4229354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229360 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 11]
def baseStart_4229360 : Nat := 118140960795 + 4229360 * 2 ^ 59
def prefixEnd_4229360 : Nat := 4983230072969 + 3 ^ 40 * 4229360 * 2
def baseEnd_4229360 : Nat := 241299393433297538138837

theorem tailTrace_4229360 : CollatzResearch.WordTrace tailWord_4229360 prefixEnd_4229360 241299393433297538138837 := by
  unfold tailWord_4229360
  simp only [CollatzResearch.WordTrace]
  refine ⟨77128715978879256013250767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102838287971839008017667689 77128715978879256013250767)
  ·
    refine ⟨115693073968318884019876151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77128715978879256013250767 115693073968318884019876151)
    ·
      refine ⟨173539610952478326029814227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115693073968318884019876151 173539610952478326029814227)
      ·
        refine ⟨260309416428717489044721341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173539610952478326029814227 260309416428717489044721341)
        ·
          refine ⟨97616031160769058391770503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260309416428717489044721341 97616031160769058391770503)
          ·
            refine ⟨146424046741153587587655755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97616031160769058391770503 146424046741153587587655755)
            ·
              refine ⟨219636070111730381381483633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146424046741153587587655755 219636070111730381381483633)
              ·
                refine ⟨164727052583797786036112725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219636070111730381381483633 164727052583797786036112725)
                ·
                  refine ⟨241299393433297538138837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 164727052583797786036112725 241299393433297538138837)
                  ·
                    rfl

theorem cell23_4229360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 11].length) (baseStart_4229360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229360 prefixEnd_4229360 := by exact prefixLift 4229360
  have htrace : WordTrace (prefixWord ++ tailWord_4229360) baseStart_4229360 baseEnd_4229360 := by
    simpa [prefixWord, tailWord_4229360, baseEnd_4229360] using wordTrace_append hprefix tailTrace_4229360
  have hstable : (prefixWord ++ tailWord_4229360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229360).length < 2 ^ (prefixWord ++ tailWord_4229360).sum := by decide
  have hdescent : baseEnd_4229360 < baseStart_4229360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229374 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_4229374 : Nat := 118140960795 + 4229374 * 2 ^ 59
def prefixEnd_4229374 : Nat := 4983230072969 + 3 ^ 40 * 4229374 * 2
def baseEnd_4229374 : Nat := 2171701729628840788474469

theorem tailTrace_4229374 : CollatzResearch.WordTrace tailWord_4229374 prefixEnd_4229374 2171701729628840788474469 := by
  unfold tailWord_4229374
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282242822463474052188897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102838628386471861611674117 19282242822463474052188897)
  ·
    refine ⟨14461682116847605539141673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19282242822463474052188897 14461682116847605539141673)
    ·
      refine ⟨10846261587635704154356255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14461682116847605539141673 10846261587635704154356255)
      ·
        refine ⟨16269392381453556231534383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10846261587635704154356255 16269392381453556231534383)
        ·
          refine ⟨24404088572180334347301575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16269392381453556231534383 24404088572180334347301575)
          ·
            refine ⟨36606132858270501520952363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24404088572180334347301575 36606132858270501520952363)
            ·
              refine ⟨54909199287405752281428545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36606132858270501520952363 54909199287405752281428545)
              ·
                refine ⟨41181899465554314211071409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54909199287405752281428545 41181899465554314211071409)
                ·
                  refine ⟨30886424599165735658303557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41181899465554314211071409 30886424599165735658303557)
                  ·
                    refine ⟨5791204612343575435931917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30886424599165735658303557 5791204612343575435931917)
                    ·
                      refine ⟨2171701729628840788474469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5791204612343575435931917 2171701729628840788474469)
                      ·
                        rfl

theorem cell23_4229374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_4229374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229374 prefixEnd_4229374 := by exact prefixLift 4229374
  have htrace : WordTrace (prefixWord ++ tailWord_4229374) baseStart_4229374 baseEnd_4229374 := by
    simpa [prefixWord, tailWord_4229374, baseEnd_4229374] using wordTrace_append hprefix tailTrace_4229374
  have hstable : (prefixWord ++ tailWord_4229374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229374).length < 2 ^ (prefixWord ++ tailWord_4229374).sum := by decide
  have hdescent : baseEnd_4229374 < baseStart_4229374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229377 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 7]
def baseStart_4229377 : Nat := 118140960795 + 4229377 * 2 ^ 59
def prefixEnd_4229377 : Nat := 4983230072969 + 3 ^ 40 * 4229377 * 2
def baseEnd_4229377 : Nat := 241300363341200475192995

theorem tailTrace_4229377 : CollatzResearch.WordTrace tailWord_4229377 prefixEnd_4229377 241300363341200475192995 := by
  unfold tailWord_4229377
  simp only [CollatzResearch.WordTrace]
  refine ⟨154258051998696923929870385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102838701332464615953246923 154258051998696923929870385)
  ·
    refine ⟨115693538999022692947402789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154258051998696923929870385 115693538999022692947402789)
    ·
      refine ⟨21692538562316754927638023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115693538999022692947402789 21692538562316754927638023)
      ·
        refine ⟨32538807843475132391457035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21692538562316754927638023 32538807843475132391457035)
        ·
          refine ⟨48808211765212698587185553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32538807843475132391457035 48808211765212698587185553)
          ·
            refine ⟨36606158823909523940389165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48808211765212698587185553 36606158823909523940389165)
            ·
              refine ⟨13727309558966071477645937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36606158823909523940389165 13727309558966071477645937)
              ·
                refine ⟨10295482169224553608234453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13727309558966071477645937 10295482169224553608234453)
                ·
                  refine ⟨241300363341200475192995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10295482169224553608234453 241300363341200475192995)
                  ·
                    rfl

theorem cell23_4229377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 7].length) (baseStart_4229377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229377 prefixEnd_4229377 := by exact prefixLift 4229377
  have htrace : WordTrace (prefixWord ++ tailWord_4229377) baseStart_4229377 baseEnd_4229377 := by
    simpa [prefixWord, tailWord_4229377, baseEnd_4229377] using wordTrace_append hprefix tailTrace_4229377
  have hstable : (prefixWord ++ tailWord_4229377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229377).length < 2 ^ (prefixWord ++ tailWord_4229377).sum := by decide
  have hdescent : baseEnd_4229377 < baseStart_4229377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229387 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 3]
def baseStart_4229387 : Nat := 118140960795 + 4229387 * 2 ^ 59
def prefixEnd_4229387 : Nat := 4983230072969 + 3 ^ 40 * 4229387 * 2
def baseEnd_4229387 : Nat := 2171708404877349237611909

theorem tailTrace_4229387 : CollatzResearch.WordTrace tailWord_4229387 prefixEnd_4229387 2171708404877349237611909 := by
  unfold tailWord_4229387
  simp only [CollatzResearch.WordTrace]
  refine ⟨154258416728660695637734415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102838944485773797091822943 154258416728660695637734415)
  ·
    refine ⟨231387625092991043456601623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154258416728660695637734415 231387625092991043456601623)
    ·
      refine ⟨347081437639486565184902435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231387625092991043456601623 347081437639486565184902435)
      ·
        refine ⟨520622156459229847777353653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347081437639486565184902435 520622156459229847777353653)
        ·
          refine ⟨48808327168052798229126905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 520622156459229847777353653 48808327168052798229126905)
          ·
            refine ⟨36606245376039598671845179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48808327168052798229126905 36606245376039598671845179)
            ·
              refine ⟨54909368064059398007767769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36606245376039598671845179 54909368064059398007767769)
              ·
                refine ⟨41182026048044548505825827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54909368064059398007767769 41182026048044548505825827)
                ·
                  refine ⟨61773039072066822758738741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41182026048044548505825827 61773039072066822758738741)
                  ·
                    refine ⟨5791222413006264633631757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61773039072066822758738741 5791222413006264633631757)
                    ·
                      refine ⟨2171708404877349237611909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5791222413006264633631757 2171708404877349237611909)
                      ·
                        rfl

theorem cell23_4229387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 3].length) (baseStart_4229387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229387 prefixEnd_4229387 := by exact prefixLift 4229387
  have htrace : WordTrace (prefixWord ++ tailWord_4229387) baseStart_4229387 baseEnd_4229387 := by
    simpa [prefixWord, tailWord_4229387, baseEnd_4229387] using wordTrace_append hprefix tailTrace_4229387
  have hstable : (prefixWord ++ tailWord_4229387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229387).length < 2 ^ (prefixWord ++ tailWord_4229387).sum := by decide
  have hdescent : baseEnd_4229387 < baseStart_4229387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229422 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4229422 : Nat := 118140960795 + 4229422 * 2 ^ 59
def prefixEnd_4229422 : Nat := 4983230072969 + 3 ^ 40 * 4229422 * 2
def baseEnd_4229422 : Nat := 2171726376700256600674249

theorem tailTrace_4229422 : CollatzResearch.WordTrace tailWord_4229422 prefixEnd_4229422 2171726376700256600674249 := by
  unfold tailWord_4229422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19282461660441737076907315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102839795522355931076839013 19282461660441737076907315)
  ·
    refine ⟨28923692490662605615360973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19282461660441737076907315 28923692490662605615360973)
    ·
      refine ⟨10846384683998477105760365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28923692490662605615360973 10846384683998477105760365)
      ·
        refine ⟨4067394256499428914660137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10846384683998477105760365 4067394256499428914660137)
        ·
          refine ⟨3050545692374571685995103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4067394256499428914660137 3050545692374571685995103)
          ·
            refine ⟨4575818538561857528992655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050545692374571685995103 4575818538561857528992655)
            ·
              refine ⟨6863727807842786293488983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4575818538561857528992655 6863727807842786293488983)
              ·
                refine ⟨10295591711764179440233475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6863727807842786293488983 10295591711764179440233475)
                ·
                  refine ⟨15443387567646269160350213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10295591711764179440233475 15443387567646269160350213)
                  ·
                    refine ⟨2895635168933675467565665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15443387567646269160350213 2895635168933675467565665)
                    ·
                      refine ⟨2171726376700256600674249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895635168933675467565665 2171726376700256600674249)
                      ·
                        rfl

theorem cell23_4229422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4229422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229422 prefixEnd_4229422 := by exact prefixLift 4229422
  have htrace : WordTrace (prefixWord ++ tailWord_4229422) baseStart_4229422 baseEnd_4229422 := by
    simpa [prefixWord, tailWord_4229422, baseEnd_4229422] using wordTrace_append hprefix tailTrace_4229422
  have hstable : (prefixWord ++ tailWord_4229422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229422).length < 2 ^ (prefixWord ++ tailWord_4229422).sum := by decide
  have hdescent : baseEnd_4229422 < baseStart_4229422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229427 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4]
def baseStart_4229427 : Nat := 118140960795 + 4229427 * 2 ^ 59
def prefixEnd_4229427 : Nat := 4983230072969 + 3 ^ 40 * 4229427 * 2
def baseEnd_4229427 : Nat := 2171728944103529081111725

theorem tailTrace_4229427 : CollatzResearch.WordTrace tailWord_4229427 prefixEnd_4229427 2171728944103529081111725 := by
  unfold tailWord_4229427
  simp only [CollatzResearch.WordTrace]
  refine ⟨154259875648515782469190535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102839917099010521646127023 154259875648515782469190535)
  ·
    refine ⟨231389813472773673703785803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154259875648515782469190535 231389813472773673703785803)
    ·
      refine ⟨347084720209160510555678705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231389813472773673703785803 347084720209160510555678705)
      ·
        refine ⟨260313540156870382916759029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347084720209160510555678705 260313540156870382916759029)
        ·
          refine ⟨24404394389706598398446159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260313540156870382916759029 24404394389706598398446159)
          ·
            refine ⟨36606591584559897597669239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24404394389706598398446159 36606591584559897597669239)
            ·
              refine ⟨54909887376839846396503859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36606591584559897597669239 54909887376839846396503859)
              ·
                refine ⟨82364831065259769594755789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54909887376839846396503859 82364831065259769594755789)
                ·
                  refine ⟨30886811649472413598033421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82364831065259769594755789 30886811649472413598033421)
                  ·
                    refine ⟨11582554368552155099262533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30886811649472413598033421 11582554368552155099262533)
                    ·
                      refine ⟨2171728944103529081111725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11582554368552155099262533 2171728944103529081111725)
                      ·
                        rfl

theorem cell23_4229427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_4229427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229427 prefixEnd_4229427 := by exact prefixLift 4229427
  have htrace : WordTrace (prefixWord ++ tailWord_4229427) baseStart_4229427 baseEnd_4229427 := by
    simpa [prefixWord, tailWord_4229427, baseEnd_4229427] using wordTrace_append hprefix tailTrace_4229427
  have hstable : (prefixWord ++ tailWord_4229427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229427).length < 2 ^ (prefixWord ++ tailWord_4229427).sum := by decide
  have hdescent : baseEnd_4229427 < baseStart_4229427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229461 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_4229461 : Nat := 118140960795 + 4229461 * 2 ^ 59
def prefixEnd_4229461 : Nat := 4983230072969 + 3 ^ 40 * 4229461 * 2
def baseEnd_4229461 : Nat := 2171746402445781948086569

theorem tailTrace_4229461 : CollatzResearch.WordTrace tailWord_4229461 prefixEnd_4229461 2171746402445781948086569 := by
  unfold tailWord_4229461
  simp only [CollatzResearch.WordTrace]
  refine ⟨154261115730392606275928237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102840743820261737517285491 154261115730392606275928237)
  ·
    refine ⟨57847918398897227353473089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154261115730392606275928237 57847918398897227353473089)
    ·
      refine ⟨43385938799172920515104817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57847918398897227353473089 43385938799172920515104817)
      ·
        refine ⟨32539454099379690386328613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43385938799172920515104817 32539454099379690386328613)
        ·
          refine ⟨6101147643633691947436615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32539454099379690386328613 6101147643633691947436615)
          ·
            refine ⟨9151721465450537921154923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6101147643633691947436615 9151721465450537921154923)
            ·
              refine ⟨13727582198175806881732385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9151721465450537921154923 13727582198175806881732385)
              ·
                refine ⟨10295686648631855161299289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13727582198175806881732385 10295686648631855161299289)
                ·
                  refine ⟨7721764986473891370974467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10295686648631855161299289 7721764986473891370974467)
                  ·
                    refine ⟨11582647479710837056461701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7721764986473891370974467 11582647479710837056461701)
                    ·
                      refine ⟨2171746402445781948086569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11582647479710837056461701 2171746402445781948086569)
                      ·
                        rfl

theorem cell23_4229461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_4229461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229461 prefixEnd_4229461 := by exact prefixLift 4229461
  have htrace : WordTrace (prefixWord ++ tailWord_4229461) baseStart_4229461 baseEnd_4229461 := by
    simpa [prefixWord, tailWord_4229461, baseEnd_4229461] using wordTrace_append hprefix tailTrace_4229461
  have hstable : (prefixWord ++ tailWord_4229461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229461).length < 2 ^ (prefixWord ++ tailWord_4229461).sum := by decide
  have hdescent : baseEnd_4229461 < baseStart_4229461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229471 : List Nat := [1, 1, 2, 3, 1, 2, 2, 6, 1, 4]
def baseStart_4229471 : Nat := 118140960795 + 4229471 * 2 ^ 59
def prefixEnd_4229471 : Nat := 4983230072969 + 3 ^ 40 * 4229471 * 2
def baseEnd_4229471 : Nat := 723917179084108969653841

theorem tailTrace_4229471 : CollatzResearch.WordTrace tailWord_4229471 prefixEnd_4229471 723917179084108969653841 := by
  unfold tailWord_4229471
  simp only [CollatzResearch.WordTrace]
  refine ⟨154261480460356377983792267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102840986973570918655861511 154261480460356377983792267)
  ·
    refine ⟨231392220690534566975688401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154261480460356377983792267 231392220690534566975688401)
    ·
      refine ⟨173544165517900925231766301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231392220690534566975688401 173544165517900925231766301)
      ·
        refine ⟨65079062069212846961912363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173544165517900925231766301 65079062069212846961912363)
        ·
          refine ⟨97618593103819270442868545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65079062069212846961912363 97618593103819270442868545)
          ·
            refine ⟨73213944827864452832151409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97618593103819270442868545 73213944827864452832151409)
            ·
              refine ⟨54910458620898339624113557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73213944827864452832151409 54910458620898339624113557)
              ·
                refine ⟨2573927747854609669880323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54910458620898339624113557 2573927747854609669880323)
                ·
                  refine ⟨3860891621781914504820485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2573927747854609669880323 3860891621781914504820485)
                  ·
                    refine ⟨723917179084108969653841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3860891621781914504820485 723917179084108969653841)
                    ·
                      rfl

theorem cell23_4229471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 4].length) (baseStart_4229471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229471 prefixEnd_4229471 := by exact prefixLift 4229471
  have htrace : WordTrace (prefixWord ++ tailWord_4229471) baseStart_4229471 baseEnd_4229471 := by
    simpa [prefixWord, tailWord_4229471, baseEnd_4229471] using wordTrace_append hprefix tailTrace_4229471
  have hstable : (prefixWord ++ tailWord_4229471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229471).length < 2 ^ (prefixWord ++ tailWord_4229471).sum := by decide
  have hdescent : baseEnd_4229471 < baseStart_4229471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229602 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4229602 : Nat := 118140960795 + 4229602 * 2 ^ 59
def prefixEnd_4229602 : Nat := 4983230072969 + 3 ^ 40 * 4229602 * 2
def baseEnd_4229602 : Nat := 2171818803218065896423421

theorem tailTrace_4229602 : CollatzResearch.WordTrace tailWord_4229602 prefixEnd_4229602 2171818803218065896423421 := by
  unfold tailWord_4229602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38566564605720446839202765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102844172281921191571207373 38566564605720446839202765)
  ·
    refine ⟨14462461727145167564701037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38566564605720446839202765 14462461727145167564701037)
    ·
      refine ⟨5423423147679437836762889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14462461727145167564701037 5423423147679437836762889)
      ·
        refine ⟨4067567360759578377572167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5423423147679437836762889 4067567360759578377572167)
        ·
          refine ⟨6101351041139367566358251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4067567360759578377572167 6101351041139367566358251)
          ·
            refine ⟨9152026561709051349537377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6101351041139367566358251 9152026561709051349537377)
            ·
              refine ⟨6864019921281788512153033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9152026561709051349537377 6864019921281788512153033)
              ·
                refine ⟨5148014940961341384114775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6864019921281788512153033 5148014940961341384114775)
                ·
                  refine ⟨7722022411442012076172163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148014940961341384114775 7722022411442012076172163)
                  ·
                    refine ⟨11583033617163018114258245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7722022411442012076172163 11583033617163018114258245)
                    ·
                      refine ⟨2171818803218065896423421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11583033617163018114258245 2171818803218065896423421)
                      ·
                        rfl

theorem cell23_4229602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4229602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229602 prefixEnd_4229602 := by exact prefixLift 4229602
  have htrace : WordTrace (prefixWord ++ tailWord_4229602) baseStart_4229602 baseEnd_4229602 := by
    simpa [prefixWord, tailWord_4229602, baseEnd_4229602] using wordTrace_append hprefix tailTrace_4229602
  have hstable : (prefixWord ++ tailWord_4229602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229602).length < 2 ^ (prefixWord ++ tailWord_4229602).sum := by decide
  have hdescent : baseEnd_4229602 < baseStart_4229602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229605 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4229605 : Nat := 118140960795 + 4229605 * 2 ^ 59
def prefixEnd_4229605 : Nat := 4983230072969 + 3 ^ 40 * 4229605 * 2
def baseEnd_4229605 : Nat := 2171820343660029384685907

theorem tailTrace_4229605 : CollatzResearch.WordTrace tailWord_4229605 prefixEnd_4229605 2171820343660029384685907 := by
  unfold tailWord_4229605
  simp only [CollatzResearch.WordTrace]
  refine ⟨154266367841870918869170269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102844245227913945912780179 154266367841870918869170269)
  ·
    refine ⟨57849887940701594575938851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154266367841870918869170269 57849887940701594575938851)
    ·
      refine ⟨86774831911052391863908277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57849887940701594575938851 86774831911052391863908277)
      ·
        refine ⟨8135140491661161737241401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86774831911052391863908277 8135140491661161737241401)
        ·
          refine ⟨6101355368745871302931051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8135140491661161737241401 6101355368745871302931051)
          ·
            refine ⟨9152033053118806954396577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6101355368745871302931051 9152033053118806954396577)
            ·
              refine ⟨6864024789839105215797433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9152033053118806954396577 6864024789839105215797433)
              ·
                refine ⟨5148018592379328911848075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6864024789839105215797433 5148018592379328911848075)
                ·
                  refine ⟨7722027888568993367772113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148018592379328911848075 7722027888568993367772113)
                  ·
                    refine ⟨5791520916426745025829085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7722027888568993367772113 5791520916426745025829085)
                    ·
                      refine ⟨2171820343660029384685907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5791520916426745025829085 2171820343660029384685907)
                      ·
                        rfl

theorem cell23_4229605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4229605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229605 prefixEnd_4229605 := by exact prefixLift 4229605
  have htrace : WordTrace (prefixWord ++ tailWord_4229605) baseStart_4229605 baseEnd_4229605 := by
    simpa [prefixWord, tailWord_4229605, baseEnd_4229605] using wordTrace_append hprefix tailTrace_4229605
  have hstable : (prefixWord ++ tailWord_4229605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229605).length < 2 ^ (prefixWord ++ tailWord_4229605).sum := by decide
  have hdescent : baseEnd_4229605 < baseStart_4229605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229641 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 5, 4, 2]
def baseStart_4229641 : Nat := 118140960795 + 4229641 * 2 ^ 59
def prefixEnd_4229641 : Nat := 4983230072969 + 3 ^ 40 * 4229641 * 2
def baseEnd_4229641 : Nat := 2171838828963591243835741

theorem tailTrace_4229641 : CollatzResearch.WordTrace tailWord_4229641 prefixEnd_4229641 2171838828963591243835741 := by
  unfold tailWord_4229641
  simp only [CollatzResearch.WordTrace]
  refine ⟨154267680869740497017480777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102845120579826998011653851 154267680869740497017480777)
  ·
    refine ⟨115700760652305372763110583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154267680869740497017480777 115700760652305372763110583)
    ·
      refine ⟨173551140978458059144665875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115700760652305372763110583 173551140978458059144665875)
      ·
        refine ⟨260326711467687088716998813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173551140978458059144665875 260326711467687088716998813)
        ·
          refine ⟨97622516800382658268874555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260326711467687088716998813 97622516800382658268874555)
          ·
            refine ⟨146433775200573987403311833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97622516800382658268874555 146433775200573987403311833)
            ·
              refine ⟨109825331400430490552483875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146433775200573987403311833 109825331400430490552483875)
              ·
                refine ⟨164737997100645735828725813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109825331400430490552483875 164737997100645735828725813)
                ·
                  refine ⟨15444187228185537733943045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164737997100645735828725813 15444187228185537733943045)
                  ·
                    refine ⟨2895785105284788325114321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15444187228185537733943045 2895785105284788325114321)
                    ·
                      refine ⟨2171838828963591243835741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895785105284788325114321 2171838828963591243835741)
                      ·
                        rfl

theorem cell23_4229641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 4, 2].length) (baseStart_4229641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229641 prefixEnd_4229641 := by exact prefixLift 4229641
  have htrace : WordTrace (prefixWord ++ tailWord_4229641) baseStart_4229641 baseEnd_4229641 := by
    simpa [prefixWord, tailWord_4229641, baseEnd_4229641] using wordTrace_append hprefix tailTrace_4229641
  have hstable : (prefixWord ++ tailWord_4229641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229641).length < 2 ^ (prefixWord ++ tailWord_4229641).sum := by decide
  have hdescent : baseEnd_4229641 < baseStart_4229641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229652 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4229652 : Nat := 118140960795 + 4229652 * 2 ^ 59
def prefixEnd_4229652 : Nat := 4983230072969 + 3 ^ 40 * 4229652 * 2
def baseEnd_4229652 : Nat := 2171844477250790700798191

theorem tailTrace_4229652 : CollatzResearch.WordTrace tailWord_4229652 prefixEnd_4229652 2171844477250790700798191 := by
  unfold tailWord_4229652
  simp only [CollatzResearch.WordTrace]
  refine ⟨77134041036350322948065605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102845388048467097264087473 77134041036350322948065605)
  ·
    refine ⟨14462632694315685552762301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77134041036350322948065605 14462632694315685552762301)
    ·
      refine ⟨5423487260368382082285863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14462632694315685552762301 5423487260368382082285863)
      ·
        refine ⟨8135230890552573123428795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5423487260368382082285863 8135230890552573123428795)
        ·
          refine ⟨12202846335828859685143193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8135230890552573123428795 12202846335828859685143193)
          ·
            refine ⟨9152134751871644763857395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12202846335828859685143193 9152134751871644763857395)
            ·
              refine ⟨13728202127807467145786093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9152134751871644763857395 13728202127807467145786093)
              ·
                refine ⟨5148075797927800179669785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13728202127807467145786093 5148075797927800179669785)
                ·
                  refine ⟨3861056848445850134752339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5148075797927800179669785 3861056848445850134752339)
                  ·
                    refine ⟨5791585272668775202128509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3861056848445850134752339 5791585272668775202128509)
                    ·
                      refine ⟨2171844477250790700798191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5791585272668775202128509 2171844477250790700798191)
                      ·
                        rfl

theorem cell23_4229652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4229652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229652 prefixEnd_4229652 := by exact prefixLift 4229652
  have htrace : WordTrace (prefixWord ++ tailWord_4229652) baseStart_4229652 baseEnd_4229652 := by
    simpa [prefixWord, tailWord_4229652, baseEnd_4229652] using wordTrace_append hprefix tailTrace_4229652
  have hstable : (prefixWord ++ tailWord_4229652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229652).length < 2 ^ (prefixWord ++ tailWord_4229652).sum := by decide
  have hdescent : baseEnd_4229652 < baseStart_4229652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229661 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4229661 : Nat := 118140960795 + 4229661 * 2 ^ 59
def prefixEnd_4229661 : Nat := 4983230072969 + 3 ^ 40 * 4229661 * 2
def baseEnd_4229661 : Nat := 2171849098576681165585649

theorem tailTrace_4229661 : CollatzResearch.WordTrace tailWord_4229661 prefixEnd_4229661 2171849098576681165585649 := by
  unfold tailWord_4229661
  simp only [CollatzResearch.WordTrace]
  refine ⟨154268410329668040433208837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102845606886445360288805891 154268410329668040433208837)
  ·
    refine ⟨28925326936812757581226657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154268410329668040433208837 28925326936812757581226657)
    ·
      refine ⟨21693995202609568185919993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28925326936812757581226657 21693995202609568185919993)
      ·
        refine ⟨16270496401957176139439995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21693995202609568185919993 16270496401957176139439995)
        ·
          refine ⟨24405744602935764209159993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16270496401957176139439995 24405744602935764209159993)
          ·
            refine ⟨18304308452201823156869995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24405744602935764209159993 18304308452201823156869995)
            ·
              refine ⟨27456462678302734735304993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18304308452201823156869995 27456462678302734735304993)
              ·
                refine ⟨20592347008727051051478745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27456462678302734735304993 20592347008727051051478745)
                ·
                  refine ⟨15444260256545288288609059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20592347008727051051478745 15444260256545288288609059)
                  ·
                    refine ⟨23166390384817932432913589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15444260256545288288609059 23166390384817932432913589)
                    ·
                      refine ⟨2171849098576681165585649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23166390384817932432913589 2171849098576681165585649)
                      ·
                        rfl

theorem cell23_4229661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4229661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229661 prefixEnd_4229661 := by exact prefixLift 4229661
  have htrace : WordTrace (prefixWord ++ tailWord_4229661) baseStart_4229661 baseEnd_4229661 := by
    simpa [prefixWord, tailWord_4229661, baseEnd_4229661] using wordTrace_append hprefix tailTrace_4229661
  have hstable : (prefixWord ++ tailWord_4229661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229661).length < 2 ^ (prefixWord ++ tailWord_4229661).sum := by decide
  have hdescent : baseEnd_4229661 < baseStart_4229661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229692 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2]
def baseStart_4229692 : Nat := 118140960795 + 4229692 * 2 ^ 59
def prefixEnd_4229692 : Nat := 4983230072969 + 3 ^ 40 * 4229692 * 2
def baseEnd_4229692 : Nat := 2171865016476970544298007

theorem tailTrace_4229692 : CollatzResearch.WordTrace tailWord_4229692 prefixEnd_4229692 2171865016476970544298007 := by
  unfold tailWord_4229692
  simp only [CollatzResearch.WordTrace]
  refine ⟨77134770496277866363793665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102846360661703821818391553 77134770496277866363793665)
  ·
    refine ⟨57851077872208399772845249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77134770496277866363793665 57851077872208399772845249)
    ·
      refine ⟨43388308404156299829633937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57851077872208399772845249 43388308404156299829633937)
      ·
        refine ⟨32541231303117224872225453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43388308404156299829633937 32541231303117224872225453)
        ·
          refine ⟨12202961738668959327084545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32541231303117224872225453 12202961738668959327084545)
          ·
            refine ⟨9152221304001719495313409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12202961738668959327084545 9152221304001719495313409)
            ·
              refine ⟨6864165978001289621485057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9152221304001719495313409 6864165978001289621485057)
              ·
                refine ⟨5148124483500967216113793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6864165978001289621485057 5148124483500967216113793)
                ·
                  refine ⟨3861093362625725412085345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5148124483500967216113793 3861093362625725412085345)
                  ·
                    refine ⟨2895820021969294059064009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3861093362625725412085345 2895820021969294059064009)
                    ·
                      refine ⟨2171865016476970544298007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2895820021969294059064009 2171865016476970544298007)
                      ·
                        rfl

theorem cell23_4229692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_4229692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229692 prefixEnd_4229692 := by exact prefixLift 4229692
  have htrace : WordTrace (prefixWord ++ tailWord_4229692) baseStart_4229692 baseEnd_4229692 := by
    simpa [prefixWord, tailWord_4229692, baseEnd_4229692] using wordTrace_append hprefix tailTrace_4229692
  have hstable : (prefixWord ++ tailWord_4229692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229692).length < 2 ^ (prefixWord ++ tailWord_4229692).sum := by decide
  have hdescent : baseEnd_4229692 < baseStart_4229692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229731 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4]
def baseStart_4229731 : Nat := 118140960795 + 4229731 * 2 ^ 59
def prefixEnd_4229731 : Nat := 4983230072969 + 3 ^ 40 * 4229731 * 2
def baseEnd_4229731 : Nat := 2171885042222495891710327

theorem tailTrace_4229731 : CollatzResearch.WordTrace tailWord_4229731 prefixEnd_4229731 2171885042222495891710327 := by
  unfold tailWord_4229731
  simp only [CollatzResearch.WordTrace]
  refine ⟨154270963439414442388257047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102847308959609628258838031 154270963439414442388257047)
  ·
    refine ⟨231406445159121663582385571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154270963439414442388257047 231406445159121663582385571)
    ·
      refine ⟨347109667738682495373578357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231406445159121663582385571 347109667738682495373578357)
      ·
        refine ⟨32541531350501483941272971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 347109667738682495373578357 32541531350501483941272971)
        ·
          refine ⟨48812297025752225911909457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32541531350501483941272971 48812297025752225911909457)
          ·
            refine ⟨36609222769314169433932093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48812297025752225911909457 36609222769314169433932093)
            ·
              refine ⟨13728458538492813537724535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36609222769314169433932093 13728458538492813537724535)
              ·
                refine ⟨20592687807739220306586803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13728458538492813537724535 20592687807739220306586803)
                ·
                  refine ⟨30889031711608830459880205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20592687807739220306586803 30889031711608830459880205)
                  ·
                    refine ⟨11583386891853311422455077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30889031711608830459880205 11583386891853311422455077)
                    ·
                      refine ⟨2171885042222495891710327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11583386891853311422455077 2171885042222495891710327)
                      ·
                        rfl

theorem cell23_4229731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_4229731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229731 prefixEnd_4229731 := by exact prefixLift 4229731
  have htrace : WordTrace (prefixWord ++ tailWord_4229731) baseStart_4229731 baseEnd_4229731 := by
    simpa [prefixWord, tailWord_4229731, baseEnd_4229731] using wordTrace_append hprefix tailTrace_4229731
  have hstable : (prefixWord ++ tailWord_4229731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229731).length < 2 ^ (prefixWord ++ tailWord_4229731).sum := by decide
  have hdescent : baseEnd_4229731 < baseStart_4229731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229761 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4229761 : Nat := 118140960795 + 4229761 * 2 ^ 59
def prefixEnd_4229761 : Nat := 4983230072969 + 3 ^ 40 * 4229761 * 2
def baseEnd_4229761 : Nat := 2171900446642130774335189

theorem tailTrace_4229761 : CollatzResearch.WordTrace tailWord_4229761 prefixEnd_4229761 2171900446642130774335189 := by
  unfold tailWord_4229761
  simp only [CollatzResearch.WordTrace]
  refine ⟨154272057629305757511849137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102848038419537171674566091 154272057629305757511849137)
  ·
    refine ⟨115704043221979318133886853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154272057629305757511849137 115704043221979318133886853)
    ·
      refine ⟨21694508104121122150103785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115704043221979318133886853 21694508104121122150103785)
      ·
        refine ⟨16270881078090841612577839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21694508104121122150103785 16270881078090841612577839)
        ·
          refine ⟨24406321617136262418866759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16270881078090841612577839 24406321617136262418866759)
          ·
            refine ⟨36609482425704393628300139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24406321617136262418866759 36609482425704393628300139)
            ·
              refine ⟨54914223638556590442450209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36609482425704393628300139 54914223638556590442450209)
              ·
                refine ⟨41185667728917442831837657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54914223638556590442450209 41185667728917442831837657)
                ·
                  refine ⟨30889250796688082123878243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41185667728917442831837657 30889250796688082123878243)
                  ·
                    refine ⟨46333876195032123185817365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30889250796688082123878243 46333876195032123185817365)
                    ·
                      refine ⟨2171900446642130774335189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46333876195032123185817365 2171900446642130774335189)
                      ·
                        rfl

theorem cell23_4229761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4229761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229761 prefixEnd_4229761 := by exact prefixLift 4229761
  have htrace : WordTrace (prefixWord ++ tailWord_4229761) baseStart_4229761 baseEnd_4229761 := by
    simpa [prefixWord, tailWord_4229761, baseEnd_4229761] using wordTrace_append hprefix tailTrace_4229761
  have hstable : (prefixWord ++ tailWord_4229761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229761).length < 2 ^ (prefixWord ++ tailWord_4229761).sum := by decide
  have hdescent : baseEnd_4229761 < baseStart_4229761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229809 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 3, 4]
def baseStart_4229809 : Nat := 118140960795 + 4229809 * 2 ^ 59
def prefixEnd_4229809 : Nat := 4983230072969 + 3 ^ 40 * 4229809 * 2
def baseEnd_4229809 : Nat := 723975031237848862178323

theorem tailTrace_4229809 : CollatzResearch.WordTrace tailWord_4229809 prefixEnd_4229809 723975031237848862178323 := by
  unfold tailWord_4229809
  simp only [CollatzResearch.WordTrace]
  refine ⟨154273808333131861709596481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102849205555421241139730987 154273808333131861709596481)
  ·
    refine ⟨115705356249848896282197361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154273808333131861709596481 115705356249848896282197361)
    ·
      refine ⟨86779017187386672211648021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115705356249848896282197361 86779017187386672211648021)
      ·
        refine ⟨4067766430658750259921001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86779017187386672211648021 4067766430658750259921001)
        ·
          refine ⟨3050824822994062694940751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4067766430658750259921001 3050824822994062694940751)
          ·
            refine ⟨4576237234491094042411127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3050824822994062694940751 4576237234491094042411127)
            ·
              refine ⟨6864355851736641063616691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4576237234491094042411127 6864355851736641063616691)
              ·
                refine ⟨10296533777604961595425037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6864355851736641063616691 10296533777604961595425037)
                ·
                  refine ⟨3861200166601860598284389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10296533777604961595425037 3861200166601860598284389)
                  ·
                    refine ⟨723975031237848862178323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3861200166601860598284389 723975031237848862178323)
                    ·
                      rfl

theorem cell23_4229809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_4229809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229809 prefixEnd_4229809 := by exact prefixLift 4229809
  have htrace : WordTrace (prefixWord ++ tailWord_4229809) baseStart_4229809 baseEnd_4229809 := by
    simpa [prefixWord, tailWord_4229809, baseEnd_4229809] using wordTrace_append hprefix tailTrace_4229809
  have hstable : (prefixWord ++ tailWord_4229809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229809).length < 2 ^ (prefixWord ++ tailWord_4229809).sum := by decide
  have hdescent : baseEnd_4229809 < baseStart_4229809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229848 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 1, 6]
def baseStart_4229848 : Nat := 118140960795 + 4229848 * 2 ^ 59
def prefixEnd_4229848 : Nat := 4983230072969 + 3 ^ 40 * 4229848 * 2
def baseEnd_4229848 : Nat := 723981706486357311315763

theorem tailTrace_4229848 : CollatzResearch.WordTrace tailWord_4229848 prefixEnd_4229848 723981706486357311315763 := by
  unfold tailWord_4229848
  simp only [CollatzResearch.WordTrace]
  refine ⟨77137615389995285685133099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102850153853327047580177465 77137615389995285685133099)
  ·
    refine ⟨115706423084992928527699649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77137615389995285685133099 115706423084992928527699649)
    ·
      refine ⟨86779817313744696395774737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115706423084992928527699649 86779817313744696395774737)
      ·
        refine ⟨65084862985308522296831053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86779817313744696395774737 65084862985308522296831053)
        ·
          refine ⟨24406823619490695861311645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65084862985308522296831053 24406823619490695861311645)
          ·
            refine ⟨9152558857309010947991867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24406823619490695861311645 9152558857309010947991867)
            ·
              refine ⟨13728838285963516421987801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9152558857309010947991867 13728838285963516421987801)
              ·
                refine ⟨10296628714472637316490851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13728838285963516421987801 10296628714472637316490851)
                ·
                  refine ⟨15444943071708955974736277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10296628714472637316490851 15444943071708955974736277)
                  ·
                    refine ⟨723981706486357311315763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15444943071708955974736277 723981706486357311315763)
                    ·
                      rfl

theorem cell23_4229848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_4229848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229848 prefixEnd_4229848 := by exact prefixLift 4229848
  have htrace : WordTrace (prefixWord ++ tailWord_4229848) baseStart_4229848 baseEnd_4229848 := by
    simpa [prefixWord, tailWord_4229848, baseEnd_4229848] using wordTrace_append hprefix tailTrace_4229848
  have hstable : (prefixWord ++ tailWord_4229848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229848).length < 2 ^ (prefixWord ++ tailWord_4229848).sum := by decide
  have hdescent : baseEnd_4229848 < baseStart_4229848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229861 : List Nat := [1, 3, 1, 4, 1, 13]
def baseStart_4229861 : Nat := 118140960795 + 4229861 * 2 ^ 59
def prefixEnd_4229861 : Nat := 4983230072969 + 3 ^ 40 * 4229861 * 2
def baseEnd_4229861 : Nat := 8938073229249301988003

theorem tailTrace_4229861 : CollatzResearch.WordTrace tailWord_4229861 prefixEnd_4229861 8938073229249301988003 := by
  unfold tailWord_4229861
  simp only [CollatzResearch.WordTrace]
  refine ⟨154275704928943474590489437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102850469952628983060326291 154275704928943474590489437)
  ·
    refine ⟨57853389348353802971433539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154275704928943474590489437 57853389348353802971433539)
    ·
      refine ⟨86780084022530704457150309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57853389348353802971433539 86780084022530704457150309)
      ·
        refine ⟨16271265754224507085715683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86780084022530704457150309 16271265754224507085715683)
        ·
          refine ⟨24406898631336760628573525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16271265754224507085715683 24406898631336760628573525)
          ·
            refine ⟨8938073229249301988003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 24406898631336760628573525 8938073229249301988003)
            ·
              rfl

theorem cell23_4229861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 13].length) (baseStart_4229861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229861 prefixEnd_4229861 := by exact prefixLift 4229861
  have htrace : WordTrace (prefixWord ++ tailWord_4229861) baseStart_4229861 baseEnd_4229861 := by
    simpa [prefixWord, tailWord_4229861, baseEnd_4229861] using wordTrace_append hprefix tailTrace_4229861
  have hstable : (prefixWord ++ tailWord_4229861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229861).length < 2 ^ (prefixWord ++ tailWord_4229861).sum := by decide
  have hdescent : baseEnd_4229861 < baseStart_4229861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229881 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_4229881 : Nat := 118140960795 + 4229881 * 2 ^ 59
def prefixEnd_4229881 : Nat := 4983230072969 + 3 ^ 40 * 4229881 * 2
def baseEnd_4229881 : Nat := 2171962064320670304834637

theorem tailTrace_4229881 : CollatzResearch.WordTrace tailWord_4229881 prefixEnd_4229881 2171962064320670304834637 := by
  unfold tailWord_4229881
  simp only [CollatzResearch.WordTrace]
  refine ⟨154276434388871018006217497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102850956259247345337478331 154276434388871018006217497)
  ·
    refine ⟨115707325791653263504663123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154276434388871018006217497 115707325791653263504663123)
    ·
      refine ⟨173560988687479895256994685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115707325791653263504663123 173560988687479895256994685)
      ·
        refine ⟨65085370757804960721373007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173560988687479895256994685 65085370757804960721373007)
        ·
          refine ⟨97628056136707441082059511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65085370757804960721373007 97628056136707441082059511)
          ·
            refine ⟨146442084205061161623089267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97628056136707441082059511 146442084205061161623089267)
            ·
              refine ⟨219663126307591742434633901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146442084205061161623089267 219663126307591742434633901)
              ·
                refine ⟨82373672365346903412987713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219663126307591742434633901 82373672365346903412987713)
                ·
                  refine ⟨61780254274010177559740785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82373672365346903412987713 61780254274010177559740785)
                  ·
                    refine ⟨46335190705507633169805589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61780254274010177559740785 46335190705507633169805589)
                    ·
                      refine ⟨2171962064320670304834637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46335190705507633169805589 2171962064320670304834637)
                      ·
                        rfl

theorem cell23_4229881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_4229881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229881 prefixEnd_4229881 := by exact prefixLift 4229881
  have htrace : WordTrace (prefixWord ++ tailWord_4229881) baseStart_4229881 baseEnd_4229881 := by
    simpa [prefixWord, tailWord_4229881, baseEnd_4229881] using wordTrace_append hprefix tailTrace_4229881
  have hstable : (prefixWord ++ tailWord_4229881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229881).length < 2 ^ (prefixWord ++ tailWord_4229881).sum := by decide
  have hdescent : baseEnd_4229881 < baseStart_4229881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229891 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 4, 7]
def baseStart_4229891 : Nat := 118140960795 + 4229891 * 2 ^ 59
def prefixEnd_4229891 : Nat := 4983230072969 + 3 ^ 40 * 4229891 * 2
def baseEnd_4229891 : Nat := 723989066375738421903197

theorem tailTrace_4229891 : CollatzResearch.WordTrace tailWord_4229891 prefixEnd_4229891 723989066375738421903197 := by
  unfold tailWord_4229891
  simp only [CollatzResearch.WordTrace]
  refine ⟨154276799118834789714081527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102851199412556526476054351 154276799118834789714081527)
  ·
    refine ⟨231415198678252184571122291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154276799118834789714081527 231415198678252184571122291)
    ·
      refine ⟨347122798017378276856683437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231415198678252184571122291 347122798017378276856683437)
      ·
        refine ⟨130171049256516853821256289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347122798017378276856683437 130171049256516853821256289)
        ·
          refine ⟨97628286942387640365942217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130171049256516853821256289 97628286942387640365942217)
          ·
            refine ⟨73221215206790730274456663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97628286942387640365942217 73221215206790730274456663)
            ·
              refine ⟨109831822810186095411684995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73221215206790730274456663 109831822810186095411684995)
              ·
                refine ⟨164747734215279143117527493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109831822810186095411684995 164747734215279143117527493)
                ·
                  refine ⟨30890200165364839334536405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164747734215279143117527493 30890200165364839334536405)
                  ·
                    refine ⟨723989066375738421903197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30890200165364839334536405 723989066375738421903197)
                    ·
                      rfl

theorem cell23_4229891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 7].length) (baseStart_4229891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229891 prefixEnd_4229891 := by exact prefixLift 4229891
  have htrace : WordTrace (prefixWord ++ tailWord_4229891) baseStart_4229891 baseEnd_4229891 := by
    simpa [prefixWord, tailWord_4229891, baseEnd_4229891] using wordTrace_append hprefix tailTrace_4229891
  have hstable : (prefixWord ++ tailWord_4229891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229891).length < 2 ^ (prefixWord ++ tailWord_4229891).sum := by decide
  have hdescent : baseEnd_4229891 < baseStart_4229891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229895 : List Nat := [1, 1, 4, 4, 1, 2, 3, 7]
def baseStart_4229895 : Nat := 118140960795 + 4229895 * 2 ^ 59
def prefixEnd_4229895 : Nat := 4983230072969 + 3 ^ 40 * 4229895 * 2
def baseEnd_4229895 : Nat := 80443305668512342594799

theorem tailTrace_4229895 : CollatzResearch.WordTrace tailWord_4229895 prefixEnd_4229895 80443305668512342594799 := by
  unfold tailWord_4229895
  simp only [CollatzResearch.WordTrace]
  refine ⟨154276945010820298397227139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102851296673880198931484759 154276945010820298397227139)
  ·
    refine ⟨231415417516230447595840709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154276945010820298397227139 231415417516230447595840709)
    ·
      refine ⟨43390390784293208924220133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231415417516230447595840709 43390390784293208924220133)
      ·
        refine ⟨8135698272054976673291275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43390390784293208924220133 8135698272054976673291275)
        ·
          refine ⟨12203547408082465009936913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8135698272054976673291275 12203547408082465009936913)
          ·
            refine ⟨9152660556061848757452685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12203547408082465009936913 9152660556061848757452685)
            ·
              refine ⟨3432247708523193284044757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9152660556061848757452685 3432247708523193284044757)
              ·
                refine ⟨80443305668512342594799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3432247708523193284044757 80443305668512342594799)
                ·
                  rfl

theorem cell23_4229895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 7].length) (baseStart_4229895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229895 prefixEnd_4229895 := by exact prefixLift 4229895
  have htrace : WordTrace (prefixWord ++ tailWord_4229895) baseStart_4229895 baseEnd_4229895 := by
    simpa [prefixWord, tailWord_4229895, baseEnd_4229895] using wordTrace_append hprefix tailTrace_4229895
  have hstable : (prefixWord ++ tailWord_4229895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229895).length < 2 ^ (prefixWord ++ tailWord_4229895).sum := by decide
  have hdescent : baseEnd_4229895 < baseStart_4229895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229906 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4229906 : Nat := 118140960795 + 4229906 * 2 ^ 59
def prefixEnd_4229906 : Nat := 4983230072969 + 3 ^ 40 * 4229906 * 2
def baseEnd_4229906 : Nat := 2171974901337032707022023

theorem tailTrace_4229906 : CollatzResearch.WordTrace tailWord_4229906 prefixEnd_4229906 2171974901337032707022023 := by
  unfold tailWord_4229906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38569336553445111818969393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102851564142520298183918381 38569336553445111818969393)
  ·
    refine ⟨28927002415083833864227045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38569336553445111818969393 28927002415083833864227045)
    ·
      refine ⟨5423812952828218849542571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28927002415083833864227045 5423812952828218849542571)
      ·
        refine ⟨8135719429242328274313857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5423812952828218849542571 8135719429242328274313857)
        ·
          refine ⟨6101789571931746205735393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8135719429242328274313857 6101789571931746205735393)
          ·
            refine ⟨4576342178948809654301545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6101789571931746205735393 4576342178948809654301545)
            ·
              refine ⟨3432256634211607240726159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4576342178948809654301545 3432256634211607240726159)
              ·
                refine ⟨5148384951317410861089239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432256634211607240726159 5148384951317410861089239)
                ·
                  refine ⟨7722577426976116291633859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148384951317410861089239 7722577426976116291633859)
                  ·
                    refine ⟨11583866140464174437450789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7722577426976116291633859 11583866140464174437450789)
                    ·
                      refine ⟨2171974901337032707022023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11583866140464174437450789 2171974901337032707022023)
                      ·
                        rfl

theorem cell23_4229906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4229906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229906 prefixEnd_4229906 := by exact prefixLift 4229906
  have htrace : WordTrace (prefixWord ++ tailWord_4229906) baseStart_4229906 baseEnd_4229906 := by
    simpa [prefixWord, tailWord_4229906, baseEnd_4229906] using wordTrace_append hprefix tailTrace_4229906
  have hstable : (prefixWord ++ tailWord_4229906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229906).length < 2 ^ (prefixWord ++ tailWord_4229906).sum := by decide
  have hdescent : baseEnd_4229906 < baseStart_4229906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229922 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_4229922 : Nat := 118140960795 + 4229922 * 2 ^ 59
def prefixEnd_4229922 : Nat := 4983230072969 + 3 ^ 40 * 4229922 * 2
def baseEnd_4229922 : Nat := 2171983117027504644421949

theorem tailTrace_4229922 : CollatzResearch.WordTrace tailWord_4229922 prefixEnd_4229922 2171983117027504644421949 := by
  unfold tailWord_4229922
  simp only [CollatzResearch.WordTrace]
  refine ⟨38569482445430620502115005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102851953187814988005640013 38569482445430620502115005)
  ·
    refine ⟨14463555917036482688293127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38569482445430620502115005 14463555917036482688293127)
    ·
      refine ⟨21695333875554724032439691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14463555917036482688293127 21695333875554724032439691)
      ·
        refine ⟨32543000813332086048659537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21695333875554724032439691 32543000813332086048659537)
        ·
          refine ⟨24407250609999064536494653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32543000813332086048659537 24407250609999064536494653)
          ·
            refine ⟨9152718978749649201185495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24407250609999064536494653 9152718978749649201185495)
            ·
              refine ⟨13729078468124473801778243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9152718978749649201185495 13729078468124473801778243)
              ·
                refine ⟨20593617702186710702667365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13729078468124473801778243 20593617702186710702667365)
                ·
                  refine ⟨3861303319160008256750131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20593617702186710702667365 3861303319160008256750131)
                  ·
                    refine ⟨5791954978740012385125197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3861303319160008256750131 5791954978740012385125197)
                    ·
                      refine ⟨2171983117027504644421949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5791954978740012385125197 2171983117027504644421949)
                      ·
                        rfl

theorem cell23_4229922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_4229922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229922 prefixEnd_4229922 := by exact prefixLift 4229922
  have htrace : WordTrace (prefixWord ++ tailWord_4229922) baseStart_4229922 baseEnd_4229922 := by
    simpa [prefixWord, tailWord_4229922, baseEnd_4229922] using wordTrace_append hprefix tailTrace_4229922
  have hstable : (prefixWord ++ tailWord_4229922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229922).length < 2 ^ (prefixWord ++ tailWord_4229922).sum := by decide
  have hdescent : baseEnd_4229922 < baseStart_4229922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229938 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_4229938 : Nat := 118140960795 + 4229938 * 2 ^ 59
def prefixEnd_4229938 : Nat := 4983230072969 + 3 ^ 40 * 4229938 * 2
def baseEnd_4229938 : Nat := 723997110905992193940625

theorem tailTrace_4229938 : CollatzResearch.WordTrace tailWord_4229938 prefixEnd_4229938 723997110905992193940625 := by
  unfold tailWord_4229938
  simp only [CollatzResearch.WordTrace]
  refine ⟨38569628337416129185260617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102852342233109677827361645 38569628337416129185260617)
  ·
    refine ⟨28927221253062096888945463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38569628337416129185260617 28927221253062096888945463)
    ·
      refine ⟨43390831879593145333418195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28927221253062096888945463 43390831879593145333418195)
      ·
        refine ⟨65086247819389718000127293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43390831879593145333418195 65086247819389718000127293)
        ·
          refine ⟨24407342932271144250047735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65086247819389718000127293 24407342932271144250047735)
          ·
            refine ⟨36611014398406716375071603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24407342932271144250047735 36611014398406716375071603)
            ·
              refine ⟨54916521597610074562607405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36611014398406716375071603 54916521597610074562607405)
              ·
                refine ⟨20593695599103777960977777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54916521597610074562607405 20593695599103777960977777)
                ·
                  refine ⟨15445271699327833470733333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20593695599103777960977777 15445271699327833470733333)
                  ·
                    refine ⟨723997110905992193940625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15445271699327833470733333 723997110905992193940625)
                    ·
                      rfl

theorem cell23_4229938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_4229938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229938 prefixEnd_4229938 := by exact prefixLift 4229938
  have htrace : WordTrace (prefixWord ++ tailWord_4229938) baseStart_4229938 baseEnd_4229938 := by
    simpa [prefixWord, tailWord_4229938, baseEnd_4229938] using wordTrace_append hprefix tailTrace_4229938
  have hstable : (prefixWord ++ tailWord_4229938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229938).length < 2 ^ (prefixWord ++ tailWord_4229938).sum := by decide
  have hdescent : baseEnd_4229938 < baseStart_4229938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229939 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 2, 1, 3]
def baseStart_4229939 : Nat := 118140960795 + 4229939 * 2 ^ 59
def prefixEnd_4229939 : Nat := 4983230072969 + 3 ^ 40 * 4229939 * 2
def baseEnd_4229939 : Nat := 2171991846198631077909371

theorem tailTrace_4229939 : CollatzResearch.WordTrace tailWord_4229939 prefixEnd_4229939 2171991846198631077909371 := by
  unfold tailWord_4229939
  simp only [CollatzResearch.WordTrace]
  refine ⟨154278549822660893911828871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102852366548440595941219247 154278549822660893911828871)
  ·
    refine ⟨231417824733991340867743307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154278549822660893911828871 231417824733991340867743307)
    ·
      refine ⟨347126737100987011301614961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231417824733991340867743307 347126737100987011301614961)
      ·
        refine ⟨260345052825740258476211221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347126737100987011301614961 260345052825740258476211221)
        ·
          refine ⟨12203674351206574616072401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 260345052825740258476211221 12203674351206574616072401)
          ·
            refine ⟨9152755763404930962054301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12203674351206574616072401 9152755763404930962054301)
            ·
              refine ⟨3432283411276849110770363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9152755763404930962054301 3432283411276849110770363)
              ·
                refine ⟨5148425116915273666155545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432283411276849110770363 5148425116915273666155545)
                ·
                  refine ⟨3861318837686455249616659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5148425116915273666155545 3861318837686455249616659)
                  ·
                    refine ⟨5791978256529682874424989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3861318837686455249616659 5791978256529682874424989)
                    ·
                      refine ⟨2171991846198631077909371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5791978256529682874424989 2171991846198631077909371)
                      ·
                        rfl

theorem cell23_4229939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 2, 1, 3].length) (baseStart_4229939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229939 prefixEnd_4229939 := by exact prefixLift 4229939
  have htrace : WordTrace (prefixWord ++ tailWord_4229939) baseStart_4229939 baseEnd_4229939 := by
    simpa [prefixWord, tailWord_4229939, baseEnd_4229939] using wordTrace_append hprefix tailTrace_4229939
  have hstable : (prefixWord ++ tailWord_4229939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229939).length < 2 ^ (prefixWord ++ tailWord_4229939).sum := by decide
  have hdescent : baseEnd_4229939 < baseStart_4229939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4229948 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_4229948 : Nat := 118140960795 + 4229948 * 2 ^ 59
def prefixEnd_4229948 : Nat := 4983230072969 + 3 ^ 40 * 4229948 * 2
def baseEnd_4229948 : Nat := 2171996467524521542696829

theorem tailTrace_4229948 : CollatzResearch.WordTrace tailWord_4229948 prefixEnd_4229948 2171996467524521542696829 := by
  unfold tailWord_4229948
  simp only [CollatzResearch.WordTrace]
  refine ⟨77139439039814144224453249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102852585386418858965937665 77139439039814144224453249)
  ·
    refine ⟨57854579279860608168339937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77139439039814144224453249 57854579279860608168339937)
    ·
      refine ⟨43390934459895456126254953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57854579279860608168339937 43390934459895456126254953)
      ·
        refine ⟨32543200844921592094691215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43390934459895456126254953 32543200844921592094691215)
        ·
          refine ⟨48814801267382388142036823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32543200844921592094691215 48814801267382388142036823)
          ·
            refine ⟨73222201901073582213055235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48814801267382388142036823 73222201901073582213055235)
            ·
              refine ⟨109833302851610373319582853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73222201901073582213055235 109833302851610373319582853)
              ·
                refine ⟨20593744284676944997421785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109833302851610373319582853 20593744284676944997421785)
                ·
                  refine ⟨15445308213507708748066339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20593744284676944997421785 15445308213507708748066339)
                  ·
                    refine ⟨23167962320261563122099509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15445308213507708748066339 23167962320261563122099509)
                    ·
                      refine ⟨2171996467524521542696829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23167962320261563122099509 2171996467524521542696829)
                      ·
                        rfl

theorem cell23_4229948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_4229948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4229948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4229948 prefixEnd_4229948 := by exact prefixLift 4229948
  have htrace : WordTrace (prefixWord ++ tailWord_4229948) baseStart_4229948 baseEnd_4229948 := by
    simpa [prefixWord, tailWord_4229948, baseEnd_4229948] using wordTrace_append hprefix tailTrace_4229948
  have hstable : (prefixWord ++ tailWord_4229948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4229948).length < 2 ^ (prefixWord ++ tailWord_4229948).sum := by decide
  have hdescent : baseEnd_4229948 < baseStart_4229948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4229948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230052 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_4230052 : Nat := 118140960795 + 4230052 * 2 ^ 59
def prefixEnd_4230052 : Nat := 4983230072969 + 3 ^ 40 * 4230052 * 2
def baseEnd_4230052 : Nat := 2172049869512589135796351

theorem tailTrace_4230052 : CollatzResearch.WordTrace tailWord_4230052 prefixEnd_4230052 2172049869512589135796351 := by
  unfold tailWord_4230052
  simp only [CollatzResearch.WordTrace]
  refine ⟨77141335635625757105346205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102855114180834342807128273 77141335635625757105346205)
  ·
    refine ⟨28928000863359658914504827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77141335635625757105346205 28928000863359658914504827)
    ·
      refine ⟨43392001295039488371757241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28928000863359658914504827 43392001295039488371757241)
      ·
        refine ⟨32544000971279616278817931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43392001295039488371757241 32544000971279616278817931)
        ·
          refine ⟨48816001456919424418226897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32544000971279616278817931 48816001456919424418226897)
          ·
            refine ⟨36612001092689568313670173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48816001456919424418226897 36612001092689568313670173)
            ·
              refine ⟨13729500409758588117626315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36612001092689568313670173 13729500409758588117626315)
              ·
                refine ⟨20594250614637882176439473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13729500409758588117626315 20594250614637882176439473)
                ·
                  refine ⟨15445687960978411632329605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20594250614637882176439473 15445687960978411632329605)
                  ·
                    refine ⟨2896066492683452181061801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15445687960978411632329605 2896066492683452181061801)
                    ·
                      refine ⟨2172049869512589135796351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896066492683452181061801 2172049869512589135796351)
                      ·
                        rfl

theorem cell23_4230052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_4230052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230052 prefixEnd_4230052 := by exact prefixLift 4230052
  have htrace : WordTrace (prefixWord ++ tailWord_4230052) baseStart_4230052 baseEnd_4230052 := by
    simpa [prefixWord, tailWord_4230052, baseEnd_4230052] using wordTrace_append hprefix tailTrace_4230052
  have hstable : (prefixWord ++ tailWord_4230052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230052).length < 2 ^ (prefixWord ++ tailWord_4230052).sum := by decide
  have hdescent : baseEnd_4230052 < baseStart_4230052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230072 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_4230072 : Nat := 118140960795 + 4230072 * 2 ^ 59
def prefixEnd_4230072 : Nat := 4983230072969 + 3 ^ 40 * 4230072 * 2
def baseEnd_4230072 : Nat := 2172060139125679057546259

theorem tailTrace_4230072 : CollatzResearch.WordTrace tailWord_4230072 prefixEnd_4230072 2172060139125679057546259 := by
  unfold tailWord_4230072
  simp only [CollatzResearch.WordTrace]
  refine ⟨77141700365589528813210235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102855600487452705084280313 77141700365589528813210235)
  ·
    refine ⟨115712550548384293219815353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77141700365589528813210235 115712550548384293219815353)
    ·
      refine ⟨86784412911288219914861515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115712550548384293219815353 86784412911288219914861515)
      ·
        refine ⟨130176619366932329872292273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86784412911288219914861515 130176619366932329872292273)
        ·
          refine ⟨97632464525199247404219205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130176619366932329872292273 97632464525199247404219205)
          ·
            refine ⟨18306087098474858888291101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97632464525199247404219205 18306087098474858888291101)
            ·
              refine ⟨6864782661928072083109163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18306087098474858888291101 6864782661928072083109163)
              ·
                refine ⟨10297173992892108124663745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6864782661928072083109163 10297173992892108124663745)
                ·
                  refine ⟨7722880494669081093497809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10297173992892108124663745 7722880494669081093497809)
                  ·
                    refine ⟨5792160371001810820123357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7722880494669081093497809 5792160371001810820123357)
                    ·
                      refine ⟨2172060139125679057546259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792160371001810820123357 2172060139125679057546259)
                      ·
                        rfl

theorem cell23_4230072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_4230072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230072 prefixEnd_4230072 := by exact prefixLift 4230072
  have htrace : WordTrace (prefixWord ++ tailWord_4230072) baseStart_4230072 baseEnd_4230072 := by
    simpa [prefixWord, tailWord_4230072, baseEnd_4230072] using wordTrace_append hprefix tailTrace_4230072
  have hstable : (prefixWord ++ tailWord_4230072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230072).length < 2 ^ (prefixWord ++ tailWord_4230072).sum := by decide
  have hdescent : baseEnd_4230072 < baseStart_4230072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230109 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 6]
def baseStart_4230109 : Nat := 118140960795 + 4230109 * 2 ^ 59
def prefixEnd_4230109 : Nat := 4983230072969 + 3 ^ 40 * 4230109 * 2
def baseEnd_4230109 : Nat := 241342126434432823642621

theorem tailTrace_4230109 : CollatzResearch.WordTrace tailWord_4230109 prefixEnd_4230109 241342126434432823642621 := by
  unfold tailWord_4230109
  simp only [CollatzResearch.WordTrace]
  refine ⟨154284750232045012945517381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102856500154696675297011587 154284750232045012945517381)
  ·
    refine ⟨28928390668508439927284509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154284750232045012945517381 28928390668508439927284509)
    ·
      refine ⟨10848146500690664972731691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28928390668508439927284509 10848146500690664972731691)
      ·
        refine ⟨16272219751035997459097537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10848146500690664972731691 16272219751035997459097537)
        ·
          refine ⟨12204164813276998094323153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16272219751035997459097537 12204164813276998094323153)
          ·
            refine ⟨9153123609957748570742365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12204164813276998094323153 9153123609957748570742365)
            ·
              refine ⟨3432421353734155714028387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9153123609957748570742365 3432421353734155714028387)
              ·
                refine ⟨5148632030601233571042581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432421353734155714028387 5148632030601233571042581)
                ·
                  refine ⟨241342126434432823642621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5148632030601233571042581 241342126434432823642621)
                  ·
                    rfl

theorem cell23_4230109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_4230109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230109 prefixEnd_4230109 := by exact prefixLift 4230109
  have htrace : WordTrace (prefixWord ++ tailWord_4230109) baseStart_4230109 baseEnd_4230109 := by
    simpa [prefixWord, tailWord_4230109, baseEnd_4230109] using wordTrace_append hprefix tailTrace_4230109
  have hstable : (prefixWord ++ tailWord_4230109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230109).length < 2 ^ (prefixWord ++ tailWord_4230109).sum := by decide
  have hdescent : baseEnd_4230109 < baseStart_4230109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230119 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4230119 : Nat := 118140960795 + 4230119 * 2 ^ 59
def prefixEnd_4230119 : Nat := 4983230072969 + 3 ^ 40 * 4230119 * 2
def baseEnd_4230119 : Nat := 2172084272716440373658543

theorem tailTrace_4230119 : CollatzResearch.WordTrace tailWord_4230119 prefixEnd_4230119 2172084272716440373658543 := by
  unfold tailWord_4230119
  simp only [CollatzResearch.WordTrace]
  refine ⟨154285114962008784653381411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102856743308005856435587607 154285114962008784653381411)
  ·
    refine ⟨231427672443013176980072117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154285114962008784653381411 231427672443013176980072117)
    ·
      refine ⟨21696344291532485341881761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 231427672443013176980072117 21696344291532485341881761)
      ·
        refine ⟨16272258218649364006411321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21696344291532485341881761 16272258218649364006411321)
        ·
          refine ⟨12204193663987023004808491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16272258218649364006411321 12204193663987023004808491)
          ·
            refine ⟨18306290495980534507212737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12204193663987023004808491 18306290495980534507212737)
            ·
              refine ⟨13729717871985400880409553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18306290495980534507212737 13729717871985400880409553)
              ·
                refine ⟨10297288403989050660307165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13729717871985400880409553 10297288403989050660307165)
                ·
                  refine ⟨3861483151495893997615187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10297288403989050660307165 3861483151495893997615187)
                  ·
                    refine ⟨5792224727243840996422781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3861483151495893997615187 5792224727243840996422781)
                    ·
                      refine ⟨2172084272716440373658543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792224727243840996422781 2172084272716440373658543)
                      ·
                        rfl

theorem cell23_4230119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4230119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230119 prefixEnd_4230119 := by exact prefixLift 4230119
  have htrace : WordTrace (prefixWord ++ tailWord_4230119) baseStart_4230119 baseEnd_4230119 := by
    simpa [prefixWord, tailWord_4230119, baseEnd_4230119] using wordTrace_append hprefix tailTrace_4230119
  have hstable : (prefixWord ++ tailWord_4230119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230119).length < 2 ^ (prefixWord ++ tailWord_4230119).sum := by decide
  have hdescent : baseEnd_4230119 < baseStart_4230119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230122 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_4230122 : Nat := 118140960795 + 4230122 * 2 ^ 59
def prefixEnd_4230122 : Nat := 4983230072969 + 3 ^ 40 * 4230122 * 2
def baseEnd_4230122 : Nat := 724028604386134620640343

theorem tailTrace_4230122 : CollatzResearch.WordTrace tailWord_4230122 prefixEnd_4230122 724028604386134620640343 := by
  unfold tailWord_4230122
  simp only [CollatzResearch.WordTrace]
  refine ⟨38571306095249479041435155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102856816253998610777160413 38571306095249479041435155)
  ·
    refine ⟨57856959142874218562152733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38571306095249479041435155 57856959142874218562152733)
    ·
      refine ⟨21696359678577831960807275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57856959142874218562152733 21696359678577831960807275)
      ·
        refine ⟨32544539517866747941210913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21696359678577831960807275 32544539517866747941210913)
        ·
          refine ⟨24408404638400060955908185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32544539517866747941210913 24408404638400060955908185)
          ·
            refine ⟨18306303478800045716931139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24408404638400060955908185 18306303478800045716931139)
            ·
              refine ⟨27459455218200068575396709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18306303478800045716931139 27459455218200068575396709)
              ·
                refine ⟨5148647853412512857886883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27459455218200068575396709 5148647853412512857886883)
                ·
                  refine ⟨7722971780118769286830325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148647853412512857886883 7722971780118769286830325)
                  ·
                    refine ⟨724028604386134620640343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7722971780118769286830325 724028604386134620640343)
                    ·
                      rfl

theorem cell23_4230122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_4230122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230122 prefixEnd_4230122 := by exact prefixLift 4230122
  have htrace : WordTrace (prefixWord ++ tailWord_4230122) baseStart_4230122 baseEnd_4230122 := by
    simpa [prefixWord, tailWord_4230122, baseEnd_4230122] using wordTrace_append hprefix tailTrace_4230122
  have hstable : (prefixWord ++ tailWord_4230122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230122).length < 2 ^ (prefixWord ++ tailWord_4230122).sum := by decide
  have hdescent : baseEnd_4230122 < baseStart_4230122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230130 : List Nat := [3, 2, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_4230130 : Nat := 118140960795 + 4230130 * 2 ^ 59
def prefixEnd_4230130 : Nat := 4983230072969 + 3 ^ 40 * 4230130 * 2
def baseEnd_4230130 : Nat := 724029973667879943540331

theorem tailTrace_4230130 : CollatzResearch.WordTrace tailWord_4230130 prefixEnd_4230130 724029973667879943540331 := by
  unfold tailWord_4230130
  simp only [CollatzResearch.WordTrace]
  refine ⟨38571379041242233383007961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102857010776645955688021229 38571379041242233383007961)
  ·
    refine ⟨28928534280931675037255971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38571379041242233383007961 28928534280931675037255971)
    ·
      refine ⟨43392801421397512555883957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28928534280931675037255971 43392801421397512555883957)
      ·
        refine ⟨4068075133256016802114121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43392801421397512555883957 4068075133256016802114121)
        ·
          refine ⟨3051056349942012601585591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4068075133256016802114121 3051056349942012601585591)
          ·
            refine ⟨4576584524913018902378387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051056349942012601585591 4576584524913018902378387)
            ·
              refine ⟨6864876787369528353567581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4576584524913018902378387 6864876787369528353567581)
              ·
                refine ⟨2574328795263573132587843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6864876787369528353567581 2574328795263573132587843)
                ·
                  refine ⟨3861493192895359698881765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574328795263573132587843 3861493192895359698881765)
                  ·
                    refine ⟨724029973667879943540331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3861493192895359698881765 724029973667879943540331)
                    ·
                      rfl

theorem cell23_4230130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_4230130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230130 prefixEnd_4230130 := by exact prefixLift 4230130
  have htrace : WordTrace (prefixWord ++ tailWord_4230130) baseStart_4230130 baseEnd_4230130 := by
    simpa [prefixWord, tailWord_4230130, baseEnd_4230130] using wordTrace_append hprefix tailTrace_4230130
  have hstable : (prefixWord ++ tailWord_4230130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230130).length < 2 ^ (prefixWord ++ tailWord_4230130).sum := by decide
  have hdescent : baseEnd_4230130 < baseStart_4230130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230152 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 4, 4]
def baseStart_4230152 : Nat := 118140960795 + 4230152 * 2 ^ 59
def prefixEnd_4230152 : Nat := 4983230072969 + 3 ^ 40 * 4230152 * 2
def baseEnd_4230152 : Nat := 724033739192679581515297

theorem tailTrace_4230152 : CollatzResearch.WordTrace tailWord_4230152 prefixEnd_4230152 724033739192679581515297 := by
  unfold tailWord_4230152
  simp only [CollatzResearch.WordTrace]
  refine ⟨77143159285444615644666355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102857545713926154192888473 77143159285444615644666355)
  ·
    refine ⟨115714738928166923466999533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77143159285444615644666355 115714738928166923466999533)
    ·
      refine ⟨43393027098062596300124825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115714738928166923466999533 43393027098062596300124825)
      ·
        refine ⟨32544770323546947225093619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43393027098062596300124825 32544770323546947225093619)
        ·
          refine ⟨48817155485320420837640429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32544770323546947225093619 48817155485320420837640429)
          ·
            refine ⟨18306433306995157814115161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48817155485320420837640429 18306433306995157814115161)
            ·
              refine ⟨13729824980246368360586371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18306433306995157814115161 13729824980246368360586371)
              ·
                refine ⟨20594737470369552540879557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13729824980246368360586371 20594737470369552540879557)
                ·
                  refine ⟨3861513275694291101414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20594737470369552540879557 3861513275694291101414917)
                  ·
                    refine ⟨724033739192679581515297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3861513275694291101414917 724033739192679581515297)
                    ·
                      rfl

theorem cell23_4230152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_4230152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230152 prefixEnd_4230152 := by exact prefixLift 4230152
  have htrace : WordTrace (prefixWord ++ tailWord_4230152) baseStart_4230152 baseEnd_4230152 := by
    simpa [prefixWord, tailWord_4230152, baseEnd_4230152] using wordTrace_append hprefix tailTrace_4230152
  have hstable : (prefixWord ++ tailWord_4230152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230152).length < 2 ^ (prefixWord ++ tailWord_4230152).sum := by decide
  have hdescent : baseEnd_4230152 < baseStart_4230152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230155 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6]
def baseStart_4230155 : Nat := 118140960795 + 4230155 * 2 ^ 59
def prefixEnd_4230155 : Nat := 4983230072969 + 3 ^ 40 * 4230155 * 2
def baseEnd_4230155 : Nat := 2172102758020002232808377

theorem tailTrace_4230155 : CollatzResearch.WordTrace tailWord_4230155 prefixEnd_4230155 2172102758020002232808377 := by
  unfold tailWord_4230155
  simp only [CollatzResearch.WordTrace]
  refine ⟨154286427989878362801691919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102857618659918908534461279 154286427989878362801691919)
  ·
    refine ⟨231429641984817544202537879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154286427989878362801691919 231429641984817544202537879)
    ·
      refine ⟨347144462977226316303806819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231429641984817544202537879 347144462977226316303806819)
      ·
        refine ⟨520716694465839474455710229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347144462977226316303806819 520716694465839474455710229)
        ·
          refine ⟨24408595053086225365111417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 520716694465839474455710229 24408595053086225365111417)
          ·
            refine ⟨18306446289814669023833563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24408595053086225365111417 18306446289814669023833563)
            ·
              refine ⟨27459669434722003535750345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18306446289814669023833563 27459669434722003535750345)
              ·
                refine ⟨20594752076041502651812759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27459669434722003535750345 20594752076041502651812759)
                ·
                  refine ⟨30892128114062253977719139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20594752076041502651812759 30892128114062253977719139)
                  ·
                    refine ⟨46338192171093380966578709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30892128114062253977719139 46338192171093380966578709)
                    ·
                      refine ⟨2172102758020002232808377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46338192171093380966578709 2172102758020002232808377)
                      ·
                        rfl

theorem cell23_4230155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_4230155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230155 prefixEnd_4230155 := by exact prefixLift 4230155
  have htrace : WordTrace (prefixWord ++ tailWord_4230155) baseStart_4230155 baseEnd_4230155 := by
    simpa [prefixWord, tailWord_4230155, baseEnd_4230155] using wordTrace_append hprefix tailTrace_4230155
  have hstable : (prefixWord ++ tailWord_4230155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230155).length < 2 ^ (prefixWord ++ tailWord_4230155).sum := by decide
  have hdescent : baseEnd_4230155 < baseStart_4230155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230165 : List Nat := [1, 3, 2, 1, 4, 1, 1, 10]
def baseStart_4230165 : Nat := 118140960795 + 4230165 * 2 ^ 59
def prefixEnd_4230165 : Nat := 4983230072969 + 3 ^ 40 * 4230165 * 2
def baseEnd_4230165 : Nat := 80448440475057303469753

theorem tailTrace_4230165 : CollatzResearch.WordTrace tailWord_4230165 prefixEnd_4230165 80448440475057303469753 := by
  unfold tailWord_4230165
  simp only [CollatzResearch.WordTrace]
  refine ⟨154286792719842134509555949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102857861813228089673037299 154286792719842134509555949)
  ·
    refine ⟨57857547269940800441083481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154286792719842134509555949 57857547269940800441083481)
    ·
      refine ⟨43393160452455600330812611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57857547269940800441083481 43393160452455600330812611)
      ·
        refine ⟨65089740678683400496218917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43393160452455600330812611 65089740678683400496218917)
        ·
          refine ⟨12204326377253137593041047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65089740678683400496218917 12204326377253137593041047)
          ·
            refine ⟨18306489565879706389561571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12204326377253137593041047 18306489565879706389561571)
            ·
              refine ⟨27459734348819559584342357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18306489565879706389561571 27459734348819559584342357)
              ·
                refine ⟨80448440475057303469753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27459734348819559584342357 80448440475057303469753)
                ·
                  rfl

theorem cell23_4230165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 10].length) (baseStart_4230165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230165 prefixEnd_4230165 := by exact prefixLift 4230165
  have htrace : WordTrace (prefixWord ++ tailWord_4230165) baseStart_4230165 baseEnd_4230165 := by
    simpa [prefixWord, tailWord_4230165, baseEnd_4230165] using wordTrace_append hprefix tailTrace_4230165
  have hstable : (prefixWord ++ tailWord_4230165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230165).length < 2 ^ (prefixWord ++ tailWord_4230165).sum := by decide
  have hdescent : baseEnd_4230165 < baseStart_4230165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230169 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 2, 4]
def baseStart_4230169 : Nat := 118140960795 + 4230169 * 2 ^ 59
def prefixEnd_4230169 : Nat := 4983230072969 + 3 ^ 40 * 4230169 * 2
def baseEnd_4230169 : Nat := 724036648916388392677771

theorem tailTrace_4230169 : CollatzResearch.WordTrace tailWord_4230169 prefixEnd_4230169 724036648916388392677771 := by
  unfold tailWord_4230169
  simp only [CollatzResearch.WordTrace]
  refine ⟨154286938611827643192701561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102857959074551762128467707 154286938611827643192701561)
  ·
    refine ⟨115715203958870732394526171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154286938611827643192701561 115715203958870732394526171)
    ·
      refine ⟨173572805938306098591789257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115715203958870732394526171 173572805938306098591789257)
      ·
        refine ⟨130179604453729573943841943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173572805938306098591789257 130179604453729573943841943)
        ·
          refine ⟨195269406680594360915762915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130179604453729573943841943 195269406680594360915762915)
          ·
            refine ⟨292904110020891541373644373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195269406680594360915762915 292904110020891541373644373)
            ·
              refine ⟨3432470039307322750472395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 292904110020891541373644373 3432470039307322750472395)
              ·
                refine ⟨5148705058960984125708593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432470039307322750472395 5148705058960984125708593)
                ·
                  refine ⟨3861528794220738094281445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5148705058960984125708593 3861528794220738094281445)
                  ·
                    refine ⟨724036648916388392677771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3861528794220738094281445 724036648916388392677771)
                    ·
                      rfl

theorem cell23_4230169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 4].length) (baseStart_4230169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230169 prefixEnd_4230169 := by exact prefixLift 4230169
  have htrace : WordTrace (prefixWord ++ tailWord_4230169) baseStart_4230169 baseEnd_4230169 := by
    simpa [prefixWord, tailWord_4230169, baseEnd_4230169] using wordTrace_append hprefix tailTrace_4230169
  have hstable : (prefixWord ++ tailWord_4230169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230169).length < 2 ^ (prefixWord ++ tailWord_4230169).sum := by decide
  have hdescent : baseEnd_4230169 < baseStart_4230169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230179 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 3]
def baseStart_4230179 : Nat := 118140960795 + 4230179 * 2 ^ 59
def prefixEnd_4230179 : Nat := 4983230072969 + 3 ^ 40 * 4230179 * 2
def baseEnd_4230179 : Nat := 2172115081555710138908267

theorem tailTrace_4230179 : CollatzResearch.WordTrace tailWord_4230179 prefixEnd_4230179 2172115081555710138908267 := by
  unfold tailWord_4230179
  simp only [CollatzResearch.WordTrace]
  refine ⟨154287303341791414900565591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102858202227860943267043727 154287303341791414900565591)
  ·
    refine ⟨231430955012687122350848387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154287303341791414900565591 231430955012687122350848387)
    ·
      refine ⟨347146432519030683526272581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231430955012687122350848387 347146432519030683526272581)
      ·
        refine ⟨65089956097318253161176109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 347146432519030683526272581 65089956097318253161176109)
        ·
          refine ⟨24408733536494344935441041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65089956097318253161176109 24408733536494344935441041)
          ·
            refine ⟨18306550152370758701580781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24408733536494344935441041 18306550152370758701580781)
            ·
              refine ⟨6864956307139034513092793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18306550152370758701580781 6864956307139034513092793)
              ·
                refine ⟨5148717230354275884819595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6864956307139034513092793 5148717230354275884819595)
                ·
                  refine ⟨7723075845531413827229393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148717230354275884819595 7723075845531413827229393)
                  ·
                    refine ⟨5792306884148560370422045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7723075845531413827229393 5792306884148560370422045)
                    ·
                      refine ⟨2172115081555710138908267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792306884148560370422045 2172115081555710138908267)
                      ·
                        rfl

theorem cell23_4230179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_4230179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230179 prefixEnd_4230179 := by exact prefixLift 4230179
  have htrace : WordTrace (prefixWord ++ tailWord_4230179) baseStart_4230179 baseEnd_4230179 := by
    simpa [prefixWord, tailWord_4230179, baseEnd_4230179] using wordTrace_append hprefix tailTrace_4230179
  have hstable : (prefixWord ++ tailWord_4230179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230179).length < 2 ^ (prefixWord ++ tailWord_4230179).sum := by decide
  have hdescent : baseEnd_4230179 < baseStart_4230179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230192 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3]
def baseStart_4230192 : Nat := 118140960795 + 4230192 * 2 ^ 59
def prefixEnd_4230192 : Nat := 4983230072969 + 3 ^ 40 * 4230192 * 2
def baseEnd_4230192 : Nat := 2172121756804218588045707

theorem tailTrace_4230192 : CollatzResearch.WordTrace tailWord_4230192 prefixEnd_4230192 2172121756804218588045707 := by
  unfold tailWord_4230192
  simp only [CollatzResearch.WordTrace]
  refine ⟨77143888745372159060394415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102858518327162878747192553 77143888745372159060394415)
  ·
    refine ⟨115715833118058238590591623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77143888745372159060394415 115715833118058238590591623)
    ·
      refine ⟨173573749677087357885887435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115715833118058238590591623 173573749677087357885887435)
      ·
        refine ⟨260360624515631036828831153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173573749677087357885887435 260360624515631036828831153)
        ·
          refine ⟨195270468386723277621623365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260360624515631036828831153 195270468386723277621623365)
          ·
            refine ⟨36613212822510614554054381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195270468386723277621623365 36613212822510614554054381)
            ·
              refine ⟨13729954808441480457770393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36613212822510614554054381 13729954808441480457770393)
              ·
                refine ⟨10297466106331110343327795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13729954808441480457770393 10297466106331110343327795)
                ·
                  refine ⟨15446199159496665514991693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10297466106331110343327795 15446199159496665514991693)
                  ·
                    refine ⟨5792324684811249568121885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15446199159496665514991693 5792324684811249568121885)
                    ·
                      refine ⟨2172121756804218588045707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792324684811249568121885 2172121756804218588045707)
                      ·
                        rfl

theorem cell23_4230192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_4230192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230192 prefixEnd_4230192 := by exact prefixLift 4230192
  have htrace : WordTrace (prefixWord ++ tailWord_4230192) baseStart_4230192 baseEnd_4230192 := by
    simpa [prefixWord, tailWord_4230192, baseEnd_4230192] using wordTrace_append hprefix tailTrace_4230192
  have hstable : (prefixWord ++ tailWord_4230192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230192).length < 2 ^ (prefixWord ++ tailWord_4230192).sum := by decide
  have hdescent : baseEnd_4230192 < baseStart_4230192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230196 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4230196 : Nat := 118140960795 + 4230196 * 2 ^ 59
def prefixEnd_4230196 : Nat := 4983230072969 + 3 ^ 40 * 4230196 * 2
def baseEnd_4230196 : Nat := 2172123810726836572395689

theorem tailTrace_4230196 : CollatzResearch.WordTrace tailWord_4230196 prefixEnd_4230196 2172123810726836572395689 := by
  unfold tailWord_4230196
  simp only [CollatzResearch.WordTrace]
  refine ⟨77143961691364913401967221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102858615588486551202622961 77143961691364913401967221)
  ·
    refine ⟨7232246408565460631434427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77143961691364913401967221 7232246408565460631434427)
    ·
      refine ⟨10848369612848190947151641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7232246408565460631434427 10848369612848190947151641)
      ·
        refine ⟨8136277209636143210363731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10848369612848190947151641 8136277209636143210363731)
        ·
          refine ⟨12204415814454214815545597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8136277209636143210363731 12204415814454214815545597)
          ·
            refine ⟨4576655930420330555829599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12204415814454214815545597 4576655930420330555829599)
            ·
              refine ⟨6864983895630495833744399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4576655930420330555829599 6864983895630495833744399)
              ·
                refine ⟨10297475843445743750616599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6864983895630495833744399 10297475843445743750616599)
                ·
                  refine ⟨15446213765168615625924899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10297475843445743750616599 15446213765168615625924899)
                  ·
                    refine ⟨23169320647752923438887349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15446213765168615625924899 23169320647752923438887349)
                    ·
                      refine ⟨2172123810726836572395689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23169320647752923438887349 2172123810726836572395689)
                      ·
                        rfl

theorem cell23_4230196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4230196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230196 prefixEnd_4230196 := by exact prefixLift 4230196
  have htrace : WordTrace (prefixWord ++ tailWord_4230196) baseStart_4230196 baseEnd_4230196 := by
    simpa [prefixWord, tailWord_4230196, baseEnd_4230196] using wordTrace_append hprefix tailTrace_4230196
  have hstable : (prefixWord ++ tailWord_4230196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230196).length < 2 ^ (prefixWord ++ tailWord_4230196).sum := by decide
  have hdescent : baseEnd_4230196 < baseStart_4230196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230225 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 1, 8]
def baseStart_4230225 : Nat := 118140960795 + 4230225 * 2 ^ 59
def prefixEnd_4230225 : Nat := 4983230072969 + 3 ^ 40 * 4230225 * 2
def baseEnd_4230225 : Nat := 724046233888605652977685

theorem tailTrace_4230225 : CollatzResearch.WordTrace tailWord_4230225 prefixEnd_4230225 724046233888605652977685 := by
  unfold tailWord_4230225
  simp only [CollatzResearch.WordTrace]
  refine ⟨154288981099624764756740129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102859320733083176504493419 154288981099624764756740129)
  ·
    refine ⟨115716735824718573567555097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154288981099624764756740129 115716735824718573567555097)
    ·
      refine ⟨86787551868538930175666323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115716735824718573567555097 86787551868538930175666323)
      ·
        refine ⟨130181327802808395263499485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86787551868538930175666323 130181327802808395263499485)
        ·
          refine ⟨48817997926053148223812307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130181327802808395263499485 48817997926053148223812307)
          ·
            refine ⟨73226996889079722335718461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48817997926053148223812307 73226996889079722335718461)
            ·
              refine ⟨27460123833404895875894423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73226996889079722335718461 27460123833404895875894423)
              ·
                refine ⟨41190185750107343813841635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27460123833404895875894423 41190185750107343813841635)
                ·
                  refine ⟨61785278625161015720762453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41190185750107343813841635 61785278625161015720762453)
                  ·
                    refine ⟨724046233888605652977685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61785278625161015720762453 724046233888605652977685)
                    ·
                      rfl

theorem cell23_4230225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_4230225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230225 prefixEnd_4230225 := by exact prefixLift 4230225
  have htrace : WordTrace (prefixWord ++ tailWord_4230225) baseStart_4230225 baseEnd_4230225 := by
    simpa [prefixWord, tailWord_4230225, baseEnd_4230225] using wordTrace_append hprefix tailTrace_4230225
  have hstable : (prefixWord ++ tailWord_4230225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230225).length < 2 ^ (prefixWord ++ tailWord_4230225).sum := by decide
  have hdescent : baseEnd_4230225 < baseStart_4230225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230226 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_4230226 : Nat := 118140960795 + 4230226 * 2 ^ 59
def prefixEnd_4230226 : Nat := 4983230072969 + 3 ^ 40 * 4230226 * 2
def baseEnd_4230226 : Nat := 2172139215146471455020551

theorem tailTrace_4230226 : CollatzResearch.WordTrace tailWord_4230226 prefixEnd_4230226 2172139215146471455020551 := by
  unfold tailWord_4230226
  simp only [CollatzResearch.WordTrace]
  refine ⟨38572254393155285481881633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102859345048414094618351021 38572254393155285481881633)
  ·
    refine ⟨28929190794866464111411225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38572254393155285481881633 28929190794866464111411225)
    ·
      refine ⟨21696893096149848083558419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28929190794866464111411225 21696893096149848083558419)
      ·
        refine ⟨32545339644224772125337629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21696893096149848083558419 32545339644224772125337629)
        ·
          refine ⟨12204502366584289547001611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32545339644224772125337629 12204502366584289547001611)
          ·
            refine ⟨18306753549876434320502417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12204502366584289547001611 18306753549876434320502417)
            ·
              refine ⟨13730065162407325740376813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18306753549876434320502417 13730065162407325740376813)
              ·
                refine ⟨5148774435902747152641305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13730065162407325740376813 5148774435902747152641305)
                ·
                  refine ⟨3861580826927060364480979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5148774435902747152641305 3861580826927060364480979)
                  ·
                    refine ⟨5792371240390590546721469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3861580826927060364480979 5792371240390590546721469)
                    ·
                      refine ⟨2172139215146471455020551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792371240390590546721469 2172139215146471455020551)
                      ·
                        rfl

theorem cell23_4230226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_4230226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230226 prefixEnd_4230226 := by exact prefixLift 4230226
  have htrace : WordTrace (prefixWord ++ tailWord_4230226) baseStart_4230226 baseEnd_4230226 := by
    simpa [prefixWord, tailWord_4230226, baseEnd_4230226] using wordTrace_append hprefix tailTrace_4230226
  have hstable : (prefixWord ++ tailWord_4230226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230226).length < 2 ^ (prefixWord ++ tailWord_4230226).sum := by decide
  have hdescent : baseEnd_4230226 < baseStart_4230226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230236 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_4230236 : Nat := 118140960795 + 4230236 * 2 ^ 59
def prefixEnd_4230236 : Nat := 4983230072969 + 3 ^ 40 * 4230236 * 2
def baseEnd_4230236 : Nat := 2172144349953016415895505

theorem tailTrace_4230236 : CollatzResearch.WordTrace tailWord_4230236 prefixEnd_4230236 2172144349953016415895505 := by
  unfold tailWord_4230236
  simp only [CollatzResearch.WordTrace]
  refine ⟨77144691151292456817695281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102859588201723275756927041 77144691151292456817695281)
  ·
    refine ⟨57858518363469342613271461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77144691151292456817695281 57858518363469342613271461)
    ·
      refine ⟨10848472193150501739988399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57858518363469342613271461 10848472193150501739988399)
      ·
        refine ⟨16272708289725752609982599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10848472193150501739988399 16272708289725752609982599)
        ·
          refine ⟨24409062434588628914973899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16272708289725752609982599 24409062434588628914973899)
          ·
            refine ⟨36613593651882943372460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24409062434588628914973899 36613593651882943372460849)
            ·
              refine ⟨27460195238912207529345637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36613593651882943372460849 27460195238912207529345637)
              ·
                refine ⟨5148786607296038911752307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27460195238912207529345637 5148786607296038911752307)
                ·
                  refine ⟨7723179910944058367628461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148786607296038911752307 7723179910944058367628461)
                  ·
                    refine ⟨2896192466604021887860673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7723179910944058367628461 2896192466604021887860673)
                    ·
                      refine ⟨2172144349953016415895505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896192466604021887860673 2172144349953016415895505)
                      ·
                        rfl

theorem cell23_4230236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_4230236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230236 prefixEnd_4230236 := by exact prefixLift 4230236
  have htrace : WordTrace (prefixWord ++ tailWord_4230236) baseStart_4230236 baseEnd_4230236 := by
    simpa [prefixWord, tailWord_4230236, baseEnd_4230236] using wordTrace_append hprefix tailTrace_4230236
  have hstable : (prefixWord ++ tailWord_4230236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230236).length < 2 ^ (prefixWord ++ tailWord_4230236).sum := by decide
  have hdescent : baseEnd_4230236 < baseStart_4230236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230249 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 1, 4, 2]
def baseStart_4230249 : Nat := 118140960795 + 4230249 * 2 ^ 59
def prefixEnd_4230249 : Nat := 4983230072969 + 3 ^ 40 * 4230249 * 2
def baseEnd_4230249 : Nat := 2172151025201524865032945

theorem tailTrace_4230249 : CollatzResearch.WordTrace tailWord_4230249 prefixEnd_4230249 2172151025201524865032945 := by
  unfold tailWord_4230249
  simp only [CollatzResearch.WordTrace]
  refine ⟨154289856451537816855613801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102859904301025211237075867 154289856451537816855613801)
  ·
    refine ⟨115717392338653362641710351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154289856451537816855613801 115717392338653362641710351)
    ·
      refine ⟨173576088507980043962565527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115717392338653362641710351 173576088507980043962565527)
      ·
        refine ⟨260364132761970065943848291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173576088507980043962565527 260364132761970065943848291)
        ·
          refine ⟨390546199142955098915772437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260364132761970065943848291 390546199142955098915772437)
          ·
            refine ⟨18306853084826020261676833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 390546199142955098915772437 18306853084826020261676833)
            ·
              refine ⟨13730139813619515196257625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18306853084826020261676833 13730139813619515196257625)
              ·
                refine ⟨10297604860214636397193219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13730139813619515196257625 10297604860214636397193219)
                ·
                  refine ⟨15446407290321954595789829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10297604860214636397193219 15446407290321954595789829)
                  ·
                    refine ⟨2896201366935366486710593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15446407290321954595789829 2896201366935366486710593)
                    ·
                      refine ⟨2172151025201524865032945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896201366935366486710593 2172151025201524865032945)
                      ·
                        rfl

theorem cell23_4230249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 4, 2].length) (baseStart_4230249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230249 prefixEnd_4230249 := by exact prefixLift 4230249
  have htrace : WordTrace (prefixWord ++ tailWord_4230249) baseStart_4230249 baseEnd_4230249 := by
    simpa [prefixWord, tailWord_4230249, baseEnd_4230249] using wordTrace_append hprefix tailTrace_4230249
  have hstable : (prefixWord ++ tailWord_4230249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230249).length < 2 ^ (prefixWord ++ tailWord_4230249).sum := by decide
  have hdescent : baseEnd_4230249 < baseStart_4230249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230253 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_4230253 : Nat := 118140960795 + 4230253 * 2 ^ 59
def prefixEnd_4230253 : Nat := 4983230072969 + 3 ^ 40 * 4230253 * 2
def baseEnd_4230253 : Nat := 2172153079124142849382927

theorem tailTrace_4230253 : CollatzResearch.WordTrace tailWord_4230253 prefixEnd_4230253 2172153079124142849382927 := by
  unfold tailWord_4230253
  simp only [CollatzResearch.WordTrace]
  refine ⟨154290002343523325538759413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102860001562348883692506275 154290002343523325538759413)
  ·
    refine ⟨14464687719705311769258695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154290002343523325538759413 14464687719705311769258695)
    ·
      refine ⟨21697031579557967653888043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14464687719705311769258695 21697031579557967653888043)
      ·
        refine ⟨32545547369336951480832065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21697031579557967653888043 32545547369336951480832065)
        ·
          refine ⟨24409160527002713610624049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32545547369336951480832065 24409160527002713610624049)
          ·
            refine ⟨18306870395252035207968037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24409160527002713610624049 18306870395252035207968037)
            ·
              refine ⟨3432538199109756601494007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18306870395252035207968037 3432538199109756601494007)
              ·
                refine ⟨5148807298664634902241011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432538199109756601494007 5148807298664634902241011)
                ·
                  refine ⟨7723210947996952353361517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148807298664634902241011 7723210947996952353361517)
                  ·
                    refine ⟨2896204105498857132510569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7723210947996952353361517 2896204105498857132510569)
                    ·
                      refine ⟨2172153079124142849382927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896204105498857132510569 2172153079124142849382927)
                      ·
                        rfl

theorem cell23_4230253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_4230253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230253 prefixEnd_4230253 := by exact prefixLift 4230253
  have htrace : WordTrace (prefixWord ++ tailWord_4230253) baseStart_4230253 baseEnd_4230253 := by
    simpa [prefixWord, tailWord_4230253, baseEnd_4230253] using wordTrace_append hprefix tailTrace_4230253
  have hstable : (prefixWord ++ tailWord_4230253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230253).length < 2 ^ (prefixWord ++ tailWord_4230253).sum := by decide
  have hdescent : baseEnd_4230253 < baseStart_4230253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230255 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 9]
def baseStart_4230255 : Nat := 118140960795 + 4230255 * 2 ^ 59
def prefixEnd_4230255 : Nat := 4983230072969 + 3 ^ 40 * 4230255 * 2
def baseEnd_4230255 : Nat := 241350456231716871284213

theorem tailTrace_4230255 : CollatzResearch.WordTrace tailWord_4230255 prefixEnd_4230255 241350456231716871284213 := by
  unfold tailWord_4230255
  simp only [CollatzResearch.WordTrace]
  refine ⟨154290075289516079880332219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102860050193010719920221479 154290075289516079880332219)
  ·
    refine ⟨231435112934274119820498329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154290075289516079880332219 231435112934274119820498329)
    ·
      refine ⟨173576334700705589865373747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231435112934274119820498329 173576334700705589865373747)
      ·
        refine ⟨260364502051058384798060621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173576334700705589865373747 260364502051058384798060621)
        ·
          refine ⟨97636688269146894299272733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260364502051058384798060621 97636688269146894299272733)
          ·
            refine ⟨36613758100930085362227275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97636688269146894299272733 36613758100930085362227275)
            ·
              refine ⟨54920637151395128043340913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36613758100930085362227275 54920637151395128043340913)
              ·
                refine ⟨41190477863546346032505685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54920637151395128043340913 41190477863546346032505685)
                ·
                  refine ⟨241350456231716871284213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41190477863546346032505685 241350456231716871284213)
                  ·
                    rfl

theorem cell23_4230255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 9].length) (baseStart_4230255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230255 prefixEnd_4230255 := by exact prefixLift 4230255
  have htrace : WordTrace (prefixWord ++ tailWord_4230255) baseStart_4230255 baseEnd_4230255 := by
    simpa [prefixWord, tailWord_4230255, baseEnd_4230255] using wordTrace_append hprefix tailTrace_4230255
  have hstable : (prefixWord ++ tailWord_4230255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230255).length < 2 ^ (prefixWord ++ tailWord_4230255).sum := by decide
  have hdescent : baseEnd_4230255 < baseStart_4230255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230359 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_4230359 : Nat := 118140960795 + 4230359 * 2 ^ 59
def prefixEnd_4230359 : Nat := 4983230072969 + 3 ^ 40 * 4230359 * 2
def baseEnd_4230359 : Nat := 2172207508073519434657439

theorem tailTrace_4230359 : CollatzResearch.WordTrace tailWord_4230359 prefixEnd_4230359 2172207508073519434657439 := by
  unfold tailWord_4230359
  simp only [CollatzResearch.WordTrace]
  refine ⟨154293868481139305642118131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102862578987426203761412087 154293868481139305642118131)
  ·
    refine ⟨231440802721708958463177197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154293868481139305642118131 231440802721708958463177197)
    ·
      refine ⟨86790301020640859423691449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231440802721708958463177197 86790301020640859423691449)
      ·
        refine ⟨65092725765480644567768587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86790301020640859423691449 65092725765480644567768587)
        ·
          refine ⟨97639088648220966851652881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65092725765480644567768587 97639088648220966851652881)
          ·
            refine ⟨73229316486165725138739661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97639088648220966851652881 73229316486165725138739661)
            ·
              refine ⟨27460993682312146927027373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73229316486165725138739661 27460993682312146927027373)
              ·
                refine ⟨10297872630867055097635265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27460993682312146927027373 10297872630867055097635265)
                ·
                  refine ⟨7723404473150291323226449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10297872630867055097635265 7723404473150291323226449)
                  ·
                    refine ⟨5792553354862718492419837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7723404473150291323226449 5792553354862718492419837)
                    ·
                      refine ⟨2172207508073519434657439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792553354862718492419837 2172207508073519434657439)
                      ·
                        rfl

theorem cell23_4230359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_4230359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230359 prefixEnd_4230359 := by exact prefixLift 4230359
  have htrace : WordTrace (prefixWord ++ tailWord_4230359) baseStart_4230359 baseEnd_4230359 := by
    simpa [prefixWord, tailWord_4230359, baseEnd_4230359] using wordTrace_append hprefix tailTrace_4230359
  have hstable : (prefixWord ++ tailWord_4230359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230359).length < 2 ^ (prefixWord ++ tailWord_4230359).sum := by decide
  have hdescent : baseEnd_4230359 < baseStart_4230359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230379 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 6]
def baseStart_4230379 : Nat := 118140960795 + 4230379 * 2 ^ 59
def prefixEnd_4230379 : Nat := 4983230072969 + 3 ^ 40 * 4230379 * 2
def baseEnd_4230379 : Nat := 241357530854067706267483

theorem tailTrace_4230379 : CollatzResearch.WordTrace tailWord_4230379 prefixEnd_4230379 241357530854067706267483 := by
  unfold tailWord_4230379
  simp only [CollatzResearch.WordTrace]
  refine ⟨154294597941066849057846191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102863065294044566038564127 154294597941066849057846191)
  ·
    refine ⟨231441896911600273586769287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154294597941066849057846191 231441896911600273586769287)
    ·
      refine ⟨347162845367400410380153931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231441896911600273586769287 347162845367400410380153931)
      ·
        refine ⟨520744268051100615570230897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347162845367400410380153931 520744268051100615570230897)
        ·
          refine ⟨390558201038325461677673173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520744268051100615570230897 390558201038325461677673173)
          ·
            refine ⟨9153707836835753008070465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 390558201038325461677673173 9153707836835753008070465)
            ·
              refine ⟨6865280877626814756052849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9153707836835753008070465 6865280877626814756052849)
              ·
                refine ⟨5148960658220111067039637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6865280877626814756052849 5148960658220111067039637)
                ·
                  refine ⟨241357530854067706267483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5148960658220111067039637 241357530854067706267483)
                  ·
                    rfl

theorem cell23_4230379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 6].length) (baseStart_4230379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230379 prefixEnd_4230379 := by exact prefixLift 4230379
  have htrace : WordTrace (prefixWord ++ tailWord_4230379) baseStart_4230379 baseEnd_4230379 := by
    simpa [prefixWord, tailWord_4230379, baseEnd_4230379] using wordTrace_append hprefix tailTrace_4230379
  have hstable : (prefixWord ++ tailWord_4230379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230379).length < 2 ^ (prefixWord ++ tailWord_4230379).sum := by decide
  have hdescent : baseEnd_4230379 < baseStart_4230379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230383 : List Nat := [1, 1, 2, 1, 7, 1, 1, 4, 1, 4]
def baseStart_4230383 : Nat := 118140960795 + 4230383 * 2 ^ 59
def prefixEnd_4230383 : Nat := 4983230072969 + 3 ^ 40 * 4230383 * 2
def baseEnd_4230383 : Nat := 724073277203075780252443

theorem tailTrace_4230383 : CollatzResearch.WordTrace tailWord_4230383 prefixEnd_4230383 724073277203075780252443 := by
  unfold tailWord_4230383
  simp only [CollatzResearch.WordTrace]
  refine ⟨154294743833052357740991803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102863162555368238493994535 154294743833052357740991803)
  ·
    refine ⟨231442115749578536611487705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154294743833052357740991803 231442115749578536611487705)
    ·
      refine ⟨173581586812183902458615779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231442115749578536611487705 173581586812183902458615779)
      ·
        refine ⟨260372380218275853687923669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173581586812183902458615779 260372380218275853687923669)
        ·
          refine ⟨6102477661365840320810711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 260372380218275853687923669 6102477661365840320810711)
          ·
            refine ⟨9153716492048760481216067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6102477661365840320810711 9153716492048760481216067)
            ·
              refine ⟨13730574738073140721824101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9153716492048760481216067 13730574738073140721824101)
              ·
                refine ⟨2574482763388713885342019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13730574738073140721824101 2574482763388713885342019)
                ·
                  refine ⟨3861724145083070828013029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574482763388713885342019 3861724145083070828013029)
                  ·
                    refine ⟨724073277203075780252443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3861724145083070828013029 724073277203075780252443)
                    ·
                      rfl

theorem cell23_4230383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 4].length) (baseStart_4230383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230383 prefixEnd_4230383 := by exact prefixLift 4230383
  have htrace : WordTrace (prefixWord ++ tailWord_4230383) baseStart_4230383 baseEnd_4230383 := by
    simpa [prefixWord, tailWord_4230383, baseEnd_4230383] using wordTrace_append hprefix tailTrace_4230383
  have hstable : (prefixWord ++ tailWord_4230383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230383).length < 2 ^ (prefixWord ++ tailWord_4230383).sum := by decide
  have hdescent : baseEnd_4230383 < baseStart_4230383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230409 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 1, 5]
def baseStart_4230409 : Nat := 118140960795 + 4230409 * 2 ^ 59
def prefixEnd_4230409 : Nat := 4983230072969 + 3 ^ 40 * 4230409 * 2
def baseEnd_4230409 : Nat := 724077727368748079677403

theorem tailTrace_4230409 : CollatzResearch.WordTrace tailWord_4230409 prefixEnd_4230409 724077727368748079677403 := by
  unfold tailWord_4230409
  simp only [CollatzResearch.WordTrace]
  refine ⟨154295692130958164181438281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102863794753972109454292187 154295692130958164181438281)
  ·
    refine ⟨115721769098218623136078711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154295692130958164181438281 115721769098218623136078711)
    ·
      refine ⟨173582653647327934704118067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115721769098218623136078711 173582653647327934704118067)
      ·
        refine ⟨260373980470991902056177101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173582653647327934704118067 260373980470991902056177101)
        ·
          refine ⟨97640242676621963271066413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260373980470991902056177101 97640242676621963271066413)
          ·
            refine ⟨36615091003733236226649905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97640242676621963271066413 36615091003733236226649905)
            ·
              refine ⟨27461318252799927169987429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36615091003733236226649905 27461318252799927169987429)
              ·
                refine ⟨5148997172399986344372643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27461318252799927169987429 5148997172399986344372643)
                ·
                  refine ⟨7723495758599979516558965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5148997172399986344372643 7723495758599979516558965)
                  ·
                    refine ⟨724077727368748079677403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7723495758599979516558965 724077727368748079677403)
                    ·
                      rfl

theorem cell23_4230409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_4230409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230409 prefixEnd_4230409 := by exact prefixLift 4230409
  have htrace : WordTrace (prefixWord ++ tailWord_4230409) baseStart_4230409 baseEnd_4230409 := by
    simpa [prefixWord, tailWord_4230409, baseEnd_4230409] using wordTrace_append hprefix tailTrace_4230409
  have hstable : (prefixWord ++ tailWord_4230409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230409).length < 2 ^ (prefixWord ++ tailWord_4230409).sum := by decide
  have hdescent : baseEnd_4230409 < baseStart_4230409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230426 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_4230426 : Nat := 118140960795 + 4230426 * 2 ^ 59
def prefixEnd_4230426 : Nat := 4983230072969 + 3 ^ 40 * 4230426 * 2
def baseEnd_4230426 : Nat := 724080637092456890839877

theorem tailTrace_4230426 : CollatzResearch.WordTrace tailWord_4230426 prefixEnd_4230426 724080637092456890839877 := by
  unfold tailWord_4230426
  simp only [CollatzResearch.WordTrace]
  refine ⟨38574078042974144021201783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102864208114597717389871421 38574078042974144021201783)
  ·
    refine ⟨57861117064461216031802675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38574078042974144021201783 57861117064461216031802675)
    ·
      refine ⟨86791675596691824047704013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57861117064461216031802675 86791675596691824047704013)
      ·
        refine ⟨32546878348759434017889005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86791675596691824047704013 32546878348759434017889005)
        ·
          refine ⟨12205079380784787756708377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32546878348759434017889005 12205079380784787756708377)
          ·
            refine ⟨9153809535588590817531283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12205079380784787756708377 9153809535588590817531283)
            ·
              refine ⟨13730714303382886226296925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9153809535588590817531283 13730714303382886226296925)
              ·
                refine ⟨5149017863768582334861347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13730714303382886226296925 5149017863768582334861347)
                ·
                  refine ⟨7723526795652873502292021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149017863768582334861347 7723526795652873502292021)
                  ·
                    refine ⟨724080637092456890839877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7723526795652873502292021 724080637092456890839877)
                    ·
                      rfl

theorem cell23_4230426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_4230426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230426 prefixEnd_4230426 := by exact prefixLift 4230426
  have htrace : WordTrace (prefixWord ++ tailWord_4230426) baseStart_4230426 baseEnd_4230426 := by
    simpa [prefixWord, tailWord_4230426, baseEnd_4230426] using wordTrace_append hprefix tailTrace_4230426
  have hstable : (prefixWord ++ tailWord_4230426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230426).length < 2 ^ (prefixWord ++ tailWord_4230426).sum := by decide
  have hdescent : baseEnd_4230426 < baseStart_4230426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230430 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_4230430 : Nat := 118140960795 + 4230430 * 2 ^ 59
def prefixEnd_4230430 : Nat := 4983230072969 + 3 ^ 40 * 4230430 * 2
def baseEnd_4230430 : Nat := 241360440577776517429957

theorem tailTrace_4230430 : CollatzResearch.WordTrace tailWord_4230430 prefixEnd_4230430 241360440577776517429957 := by
  unfold tailWord_4230430
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287057257985260595994093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102864305375921389845301829 19287057257985260595994093)
  ·
    refine ⟨7232646471744472723497785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19287057257985260595994093 7232646471744472723497785)
    ·
      refine ⟨5424484853808354542623339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7232646471744472723497785 5424484853808354542623339)
      ·
        refine ⟨8136727280712531813935009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5424484853808354542623339 8136727280712531813935009)
        ·
          refine ⟨6102545460534398860451257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8136727280712531813935009 6102545460534398860451257)
          ·
            refine ⟨4576909095400799145338443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6102545460534398860451257 4576909095400799145338443)
            ·
              refine ⟨6865363643101198718007665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4576909095400799145338443 6865363643101198718007665)
              ·
                refine ⟨5149022732325899038505749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6865363643101198718007665 5149022732325899038505749)
                ·
                  refine ⟨241360440577776517429957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5149022732325899038505749 241360440577776517429957)
                  ·
                    rfl

theorem cell23_4230430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_4230430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230430 prefixEnd_4230430 := by exact prefixLift 4230430
  have htrace : WordTrace (prefixWord ++ tailWord_4230430) baseStart_4230430 baseEnd_4230430 := by
    simpa [prefixWord, tailWord_4230430, baseEnd_4230430] using wordTrace_append hprefix tailTrace_4230430
  have hstable : (prefixWord ++ tailWord_4230430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230430).length < 2 ^ (prefixWord ++ tailWord_4230430).sum := by decide
  have hdescent : baseEnd_4230430 < baseStart_4230430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230440 : List Nat := [2, 1, 5, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_4230440 : Nat := 118140960795 + 4230440 * 2 ^ 59
def prefixEnd_4230440 : Nat := 4983230072969 + 3 ^ 40 * 4230440 * 2
def baseEnd_4230440 : Nat := 2172249100006533617744567

theorem tailTrace_4230440 : CollatzResearch.WordTrace tailWord_4230440 prefixEnd_4230440 2172249100006533617744567 := by
  unfold tailWord_4230440
  simp only [CollatzResearch.WordTrace]
  refine ⟨77148411396922928237908387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102864548529230570983877849 77148411396922928237908387)
  ·
    refine ⟨115722617095384392356862581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77148411396922928237908387 115722617095384392356862581)
    ·
      refine ⟨10848995352692286783455867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115722617095384392356862581 10848995352692286783455867)
      ·
        refine ⟨16273493029038430175183801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10848995352692286783455867 16273493029038430175183801)
        ·
          refine ⟨12205119771778822631387851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16273493029038430175183801 12205119771778822631387851)
          ·
            refine ⟨18307679657668233947081777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12205119771778822631387851 18307679657668233947081777)
            ·
              refine ⟨13730759743251175460311333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18307679657668233947081777 13730759743251175460311333)
              ·
                refine ⟨2574517451859595398808375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13730759743251175460311333 2574517451859595398808375)
                ·
                  refine ⟨3861776177789393098212563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2574517451859595398808375 3861776177789393098212563)
                  ·
                    refine ⟨5792664266684089647318845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3861776177789393098212563 5792664266684089647318845)
                    ·
                      refine ⟨2172249100006533617744567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792664266684089647318845 2172249100006533617744567)
                      ·
                        rfl

theorem cell23_4230440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_4230440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230440 prefixEnd_4230440 := by exact prefixLift 4230440
  have htrace : WordTrace (prefixWord ++ tailWord_4230440) baseStart_4230440 baseEnd_4230440 := by
    simpa [prefixWord, tailWord_4230440, baseEnd_4230440] using wordTrace_append hprefix tailTrace_4230440
  have hstable : (prefixWord ++ tailWord_4230440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230440).length < 2 ^ (prefixWord ++ tailWord_4230440).sum := by decide
  have hdescent : baseEnd_4230440 < baseStart_4230440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230449 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_4230449 : Nat := 118140960795 + 4230449 * 2 ^ 59
def prefixEnd_4230449 : Nat := 4983230072969 + 3 ^ 40 * 4230449 * 2
def baseEnd_4230449 : Nat := 2172253721332424082532025

theorem tailTrace_4230449 : CollatzResearch.WordTrace tailWord_4230449 prefixEnd_4230449 2172253721332424082532025 := by
  unfold tailWord_4230449
  simp only [CollatzResearch.WordTrace]
  refine ⟨154297151050813251012894401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102864767367208834008596267 154297151050813251012894401)
  ·
    refine ⟨115722863288109938259670801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154297151050813251012894401 115722863288109938259670801)
    ·
      refine ⟨86792147466082453694753101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115722863288109938259670801 86792147466082453694753101)
      ·
        refine ⟨32547055299780920135532413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86792147466082453694753101 32547055299780920135532413)
        ·
          refine ⟨12205145737417845050824655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32547055299780920135532413 12205145737417845050824655)
          ·
            refine ⟨18307718606126767576236983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12205145737417845050824655 18307718606126767576236983)
            ·
              refine ⟨27461577909190151364355475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18307718606126767576236983 27461577909190151364355475)
              ·
                refine ⟨41192366863785227046533213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27461577909190151364355475 41192366863785227046533213)
                ·
                  refine ⟨15447137573919460142449955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41192366863785227046533213 15447137573919460142449955)
                  ·
                    refine ⟨23170706360879190213674933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15447137573919460142449955 23170706360879190213674933)
                    ·
                      refine ⟨2172253721332424082532025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23170706360879190213674933 2172253721332424082532025)
                      ·
                        rfl

theorem cell23_4230449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_4230449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230449 prefixEnd_4230449 := by exact prefixLift 4230449
  have htrace : WordTrace (prefixWord ++ tailWord_4230449) baseStart_4230449 baseEnd_4230449 := by
    simpa [prefixWord, tailWord_4230449, baseEnd_4230449] using wordTrace_append hprefix tailTrace_4230449
  have hstable : (prefixWord ++ tailWord_4230449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230449).length < 2 ^ (prefixWord ++ tailWord_4230449).sum := by decide
  have hdescent : baseEnd_4230449 < baseStart_4230449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230463 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 3, 2, 2]
def baseStart_4230463 : Nat := 118140960795 + 4230463 * 2 ^ 59
def prefixEnd_4230463 : Nat := 4983230072969 + 3 ^ 40 * 4230463 * 2
def baseEnd_4230463 : Nat := 2172260910061587027756961

theorem tailTrace_4230463 : CollatzResearch.WordTrace tailWord_4230463 prefixEnd_4230463 2172260910061587027756961 := by
  unfold tailWord_4230463
  simp only [CollatzResearch.WordTrace]
  refine ⟨154297661672762531403904043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102865107781841687602602695 154297661672762531403904043)
  ·
    refine ⟨231446492509143797105856065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154297661672762531403904043 231446492509143797105856065)
    ·
      refine ⟨173584869381857847829392049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231446492509143797105856065 173584869381857847829392049)
      ·
        refine ⟨130188652036393385872044037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173584869381857847829392049 130188652036393385872044037)
        ·
          refine ⟨24410372256823759851008257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130188652036393385872044037 24410372256823759851008257)
          ·
            refine ⟨18307779192617819888256193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24410372256823759851008257 18307779192617819888256193)
            ·
              refine ⟨13730834394463364916192145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18307779192617819888256193 13730834394463364916192145)
              ·
                refine ⟨10298125795847523687144109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13730834394463364916192145 10298125795847523687144109)
                ·
                  refine ⟨3861797173442821382679041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10298125795847523687144109 3861797173442821382679041)
                  ·
                    refine ⟨2896347880082116037009281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3861797173442821382679041 2896347880082116037009281)
                    ·
                      refine ⟨2172260910061587027756961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896347880082116037009281 2172260910061587027756961)
                      ·
                        rfl

theorem cell23_4230463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 2, 2].length) (baseStart_4230463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230463 prefixEnd_4230463 := by exact prefixLift 4230463
  have htrace : WordTrace (prefixWord ++ tailWord_4230463) baseStart_4230463 baseEnd_4230463 := by
    simpa [prefixWord, tailWord_4230463, baseEnd_4230463] using wordTrace_append hprefix tailTrace_4230463
  have hstable : (prefixWord ++ tailWord_4230463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230463).length < 2 ^ (prefixWord ++ tailWord_4230463).sum := by decide
  have hdescent : baseEnd_4230463 < baseStart_4230463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230517 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_4230517 : Nat := 118140960795 + 4230517 * 2 ^ 59
def prefixEnd_4230517 : Nat := 4983230072969 + 3 ^ 40 * 4230517 * 2
def baseEnd_4230517 : Nat := 2172288638016929816481713

theorem tailTrace_4230517 : CollatzResearch.WordTrace tailWord_4230517 prefixEnd_4230517 2172288638016929816481713 := by
  unfold tailWord_4230517
  simp only [CollatzResearch.WordTrace]
  refine ⟨154299631214566898626369805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102866420809711265750913203 154299631214566898626369805)
  ·
    refine ⟨57862361705462586984888677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154299631214566898626369805 57862361705462586984888677)
    ·
      refine ⟨10849192819774235059666627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57862361705462586984888677 10849192819774235059666627)
      ·
        refine ⟨16273789229661352589499941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10849192819774235059666627 16273789229661352589499941)
        ·
          refine ⟨3051335480561503610531239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16273789229661352589499941 3051335480561503610531239)
          ·
            refine ⟨4577003220842255415796859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051335480561503610531239 4577003220842255415796859)
            ·
              refine ⟨6865504831263383123695289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577003220842255415796859 6865504831263383123695289)
              ·
                refine ⟨5149128623447537342771467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6865504831263383123695289 5149128623447537342771467)
                ·
                  refine ⟨7723692935171306014157201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149128623447537342771467 7723692935171306014157201)
                  ·
                    refine ⟨5792769701378479510617901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7723692935171306014157201 5792769701378479510617901)
                    ·
                      refine ⟨2172288638016929816481713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792769701378479510617901 2172288638016929816481713)
                      ·
                        rfl

theorem cell23_4230517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_4230517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230517 prefixEnd_4230517 := by exact prefixLift 4230517
  have htrace : WordTrace (prefixWord ++ tailWord_4230517) baseStart_4230517 baseEnd_4230517 := by
    simpa [prefixWord, tailWord_4230517, baseEnd_4230517] using wordTrace_append hprefix tailTrace_4230517
  have hstable : (prefixWord ++ tailWord_4230517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230517).length < 2 ^ (prefixWord ++ tailWord_4230517).sum := by decide
  have hdescent : baseEnd_4230517 < baseStart_4230517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230530 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4230530 : Nat := 118140960795 + 4230530 * 2 ^ 59
def prefixEnd_4230530 : Nat := 4983230072969 + 3 ^ 40 * 4230530 * 2
def baseEnd_4230530 : Nat := 2172295313265438265619153

theorem tailTrace_4230530 : CollatzResearch.WordTrace tailWord_4230530 prefixEnd_4230530 2172295313265438265619153 := by
  unfold tailWord_4230530
  simp only [CollatzResearch.WordTrace]
  refine ⟨38575026340879950461648261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102866736909013201231062029 38575026340879950461648261)
  ·
    refine ⟨7232817438914990711559049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38575026340879950461648261 7232817438914990711559049)
    ·
      refine ⟨5424613079186243033669287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7232817438914990711559049 5424613079186243033669287)
      ·
        refine ⟨8136919618779364550503931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5424613079186243033669287 8136919618779364550503931)
        ·
          refine ⟨12205379428169046825755897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8136919618779364550503931 12205379428169046825755897)
          ·
            refine ⟨9154034571126785119316923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12205379428169046825755897 9154034571126785119316923)
            ·
              refine ⟨13731051856690177678975385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9154034571126785119316923 13731051856690177678975385)
              ·
                refine ⟨10298288892517633259231539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13731051856690177678975385 10298288892517633259231539)
                ·
                  refine ⟨15447433338776449888847309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10298288892517633259231539 15447433338776449888847309)
                  ·
                    refine ⟨5792787502041168708317741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15447433338776449888847309 5792787502041168708317741)
                    ·
                      refine ⟨2172295313265438265619153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792787502041168708317741 2172295313265438265619153)
                      ·
                        rfl

theorem cell23_4230530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4230530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230530 prefixEnd_4230530 := by exact prefixLift 4230530
  have htrace : WordTrace (prefixWord ++ tailWord_4230530) baseStart_4230530 baseEnd_4230530 := by
    simpa [prefixWord, tailWord_4230530, baseEnd_4230530] using wordTrace_append hprefix tailTrace_4230530
  have hstable : (prefixWord ++ tailWord_4230530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230530).length < 2 ^ (prefixWord ++ tailWord_4230530).sum := by decide
  have hdescent : baseEnd_4230530 < baseStart_4230530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230539 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5]
def baseStart_4230539 : Nat := 118140960795 + 4230539 * 2 ^ 59
def prefixEnd_4230539 : Nat := 4983230072969 + 3 ^ 40 * 4230539 * 2
def baseEnd_4230539 : Nat := 2172299934591328730406611

theorem tailTrace_4230539 : CollatzResearch.WordTrace tailWord_4230539 prefixEnd_4230539 2172299934591328730406611 := by
  unfold tailWord_4230539
  simp only [CollatzResearch.WordTrace]
  refine ⟨154300433620487196383670671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102866955746991464255780447 154300433620487196383670671)
  ·
    refine ⟨231450650430730794575506007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154300433620487196383670671 231450650430730794575506007)
    ·
      refine ⟨347175975646096191863259011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231450650430730794575506007 347175975646096191863259011)
      ·
        refine ⟨520763963469144287794888517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347175975646096191863259011 520763963469144287794888517)
        ·
          refine ⟨97643243150464553961541597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 520763963469144287794888517 97643243150464553961541597)
          ·
            refine ⟨36616216181424207735578099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97643243150464553961541597 36616216181424207735578099)
            ·
              refine ⟨54924324272136311603367149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36616216181424207735578099 54924324272136311603367149)
              ·
                refine ⟨20596621602051116851262681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54924324272136311603367149 20596621602051116851262681)
                ·
                  refine ⟨15447466201538337638447011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20596621602051116851262681 15447466201538337638447011)
                  ·
                    refine ⟨23171199302307506457670517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15447466201538337638447011 23171199302307506457670517)
                    ·
                      refine ⟨2172299934591328730406611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23171199302307506457670517 2172299934591328730406611)
                      ·
                        rfl

theorem cell23_4230539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_4230539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230539 prefixEnd_4230539 := by exact prefixLift 4230539
  have htrace : WordTrace (prefixWord ++ tailWord_4230539) baseStart_4230539 baseEnd_4230539 := by
    simpa [prefixWord, tailWord_4230539, baseEnd_4230539] using wordTrace_append hprefix tailTrace_4230539
  have hstable : (prefixWord ++ tailWord_4230539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230539).length < 2 ^ (prefixWord ++ tailWord_4230539).sum := by decide
  have hdescent : baseEnd_4230539 < baseStart_4230539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230540 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 1, 3, 2]
def baseStart_4230540 : Nat := 118140960795 + 4230540 * 2 ^ 59
def prefixEnd_4230540 : Nat := 4983230072969 + 3 ^ 40 * 4230540 * 2
def baseEnd_4230540 : Nat := 2172300448071983226494107

theorem tailTrace_4230540 : CollatzResearch.WordTrace tailWord_4230540 prefixEnd_4230540 2172300448071983226494107 := by
  unfold tailWord_4230540
  simp only [CollatzResearch.WordTrace]
  refine ⟨77150235046741786777228537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102866980062322382369638049 77150235046741786777228537)
  ·
    refine ⟨57862676285056340082921403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77150235046741786777228537 57862676285056340082921403)
    ·
      refine ⟨86794014427584510124382105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57862676285056340082921403 86794014427584510124382105)
      ·
        refine ⟨65095510820688382593286579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86794014427584510124382105 65095510820688382593286579)
        ·
          refine ⟨97643266231032573889929869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65095510820688382593286579 97643266231032573889929869)
          ·
            refine ⟨36616224836637215208723701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97643266231032573889929869 36616224836637215208723701)
            ·
              refine ⟨3432771078434738925817847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36616224836637215208723701 3432771078434738925817847)
              ·
                refine ⟨5149156617652108388726771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3432771078434738925817847 5149156617652108388726771)
                ·
                  refine ⟨7723734926478162583090157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149156617652108388726771 7723734926478162583090157)
                  ·
                    refine ⟨2896400597429310968658809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7723734926478162583090157 2896400597429310968658809)
                    ·
                      refine ⟨2172300448071983226494107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896400597429310968658809 2172300448071983226494107)
                      ·
                        rfl

theorem cell23_4230540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_4230540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230540 prefixEnd_4230540 := by exact prefixLift 4230540
  have htrace : WordTrace (prefixWord ++ tailWord_4230540) baseStart_4230540 baseEnd_4230540 := by
    simpa [prefixWord, tailWord_4230540, baseEnd_4230540] using wordTrace_append hprefix tailTrace_4230540
  have hstable : (prefixWord ++ tailWord_4230540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230540).length < 2 ^ (prefixWord ++ tailWord_4230540).sum := by decide
  have hdescent : baseEnd_4230540 < baseStart_4230540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230606 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_4230606 : Nat := 118140960795 + 4230606 * 2 ^ 59
def prefixEnd_4230606 : Nat := 4983230072969 + 3 ^ 40 * 4230606 * 2
def baseEnd_4230606 : Nat := 724111445931726656089601

theorem tailTrace_4230606 : CollatzResearch.WordTrace tailWord_4230606 prefixEnd_4230606 724111445931726656089601 := by
  unfold tailWord_4230606
  simp only [CollatzResearch.WordTrace]
  refine ⟨19287859663905558353294959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102868584874162977884239781 19287859663905558353294959)
  ·
    refine ⟨28931789495858337529942439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19287859663905558353294959 28931789495858337529942439)
    ·
      refine ⟨43397684243787506294913659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28931789495858337529942439 43397684243787506294913659)
      ·
        refine ⟨65096526365681259442370489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43397684243787506294913659 65096526365681259442370489)
        ·
          refine ⟨48822394774260944581777867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65096526365681259442370489 48822394774260944581777867)
          ·
            refine ⟨73233592161391416872666801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48822394774260944581777867 73233592161391416872666801)
            ·
              refine ⟨54925194121043562654500101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73233592161391416872666801 54925194121043562654500101)
              ·
                refine ⟨10298473897695667997718769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54925194121043562654500101 10298473897695667997718769)
                ·
                  refine ⟨7723855423271750998289077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10298473897695667997718769 7723855423271750998289077)
                  ·
                    refine ⟨724111445931726656089601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7723855423271750998289077 724111445931726656089601)
                    ·
                      rfl

theorem cell23_4230606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_4230606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230606 prefixEnd_4230606 := by exact prefixLift 4230606
  have htrace : WordTrace (prefixWord ++ tailWord_4230606) baseStart_4230606 baseEnd_4230606 := by
    simpa [prefixWord, tailWord_4230606, baseEnd_4230606] using wordTrace_append hprefix tailTrace_4230606
  have hstable : (prefixWord ++ tailWord_4230606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230606).length < 2 ^ (prefixWord ++ tailWord_4230606).sum := by decide
  have hdescent : baseEnd_4230606 < baseStart_4230606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230636 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_4230636 : Nat := 118140960795 + 4230636 * 2 ^ 59
def prefixEnd_4230636 : Nat := 4983230072969 + 3 ^ 40 * 4230636 * 2
def baseEnd_4230636 : Nat := 724116580738271616964555

theorem tailTrace_4230636 : CollatzResearch.WordTrace tailWord_4230636 prefixEnd_4230636 724116580738271616964555 := by
  unfold tailWord_4230636
  simp only [CollatzResearch.WordTrace]
  refine ⟨77151985750567890974975881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102869314334090521299967841 77151985750567890974975881)
  ·
    refine ⟨57863989312925918231231911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77151985750567890974975881 57863989312925918231231911)
    ·
      refine ⟨86795983969388877346847867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57863989312925918231231911 86795983969388877346847867)
      ·
        refine ⟨130193975954083316020271801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86795983969388877346847867 130193975954083316020271801)
        ·
          refine ⟨97645481965562487015203851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130193975954083316020271801 97645481965562487015203851)
          ·
            refine ⟨146468222948343730522805777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97645481965562487015203851 146468222948343730522805777)
            ·
              refine ⟨109851167211257797892104333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146468222948343730522805777 109851167211257797892104333)
              ·
                refine ⟨41194187704221674209539125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109851167211257797892104333 41194187704221674209539125)
                ·
                  refine ⟨3861955097270781957144293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41194187704221674209539125 3861955097270781957144293)
                  ·
                    refine ⟨724116580738271616964555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3861955097270781957144293 724116580738271616964555)
                    ·
                      rfl

theorem cell23_4230636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_4230636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230636 prefixEnd_4230636 := by exact prefixLift 4230636
  have htrace : WordTrace (prefixWord ++ tailWord_4230636) baseStart_4230636 baseEnd_4230636 := by
    simpa [prefixWord, tailWord_4230636, baseEnd_4230636] using wordTrace_append hprefix tailTrace_4230636
  have hstable : (prefixWord ++ tailWord_4230636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230636).length < 2 ^ (prefixWord ++ tailWord_4230636).sum := by decide
  have hdescent : baseEnd_4230636 < baseStart_4230636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230660 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4230660 : Nat := 118140960795 + 4230660 * 2 ^ 59
def prefixEnd_4230660 : Nat := 4983230072969 + 3 ^ 40 * 4230660 * 2
def baseEnd_4230660 : Nat := 2172362065750522756993555

theorem tailTrace_4230660 : CollatzResearch.WordTrace tailWord_4230660 prefixEnd_4230660 2172362065750522756993555 := by
  unfold tailWord_4230660
  simp only [CollatzResearch.WordTrace]
  refine ⟨77152423426524417024412717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102869897902032556032550289 77152423426524417024412717)
  ·
    refine ⟨28932158784946656384154769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77152423426524417024412717 28932158784946656384154769)
    ·
      refine ⟨21699119088709992288116077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28932158784946656384154769 21699119088709992288116077)
      ·
        refine ⟨8137169658266247108043529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21699119088709992288116077 8137169658266247108043529)
        ·
          refine ⟨6102877243699685331032647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8137169658266247108043529 6102877243699685331032647)
          ·
            refine ⟨9154315865549527996548971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6102877243699685331032647 9154315865549527996548971)
            ·
              refine ⟨13731473798324291994823457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9154315865549527996548971 13731473798324291994823457)
              ·
                refine ⟨10298605348743218996117593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13731473798324291994823457 10298605348743218996117593)
                ·
                  refine ⟨7723954011557414247088195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10298605348743218996117593 7723954011557414247088195)
                  ·
                    refine ⟨11585931017336121370632293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7723954011557414247088195 11585931017336121370632293)
                    ·
                      refine ⟨2172362065750522756993555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11585931017336121370632293 2172362065750522756993555)
                      ·
                        rfl

theorem cell23_4230660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4230660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230660 prefixEnd_4230660 := by exact prefixLift 4230660
  have htrace : WordTrace (prefixWord ++ tailWord_4230660) baseStart_4230660 baseEnd_4230660 := by
    simpa [prefixWord, tailWord_4230660, baseEnd_4230660] using wordTrace_append hprefix tailTrace_4230660
  have hstable : (prefixWord ++ tailWord_4230660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230660).length < 2 ^ (prefixWord ++ tailWord_4230660).sum := by decide
  have hdescent : baseEnd_4230660 < baseStart_4230660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230663 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_4230663 : Nat := 118140960795 + 4230663 * 2 ^ 59
def prefixEnd_4230663 : Nat := 4983230072969 + 3 ^ 40 * 4230663 * 2
def baseEnd_4230663 : Nat := 2172363606192486245256041

theorem tailTrace_4230663 : CollatzResearch.WordTrace tailWord_4230663 prefixEnd_4230663 2172363606192486245256041 := by
  unfold tailWord_4230663
  simp only [CollatzResearch.WordTrace]
  refine ⟨154304956272037965561184643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102869970848025310374123095 154304956272037965561184643)
  ·
    refine ⟨231457434408056948341776965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154304956272037965561184643 231457434408056948341776965)
    ·
      refine ⟨43398268951510677814083181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231457434408056948341776965 43398268951510677814083181)
      ·
        refine ⟨16274350856816504180281193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43398268951510677814083181 16274350856816504180281193)
        ·
          refine ⟨12205763142612378135210895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16274350856816504180281193 12205763142612378135210895)
          ·
            refine ⟨18308644713918567202816343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12205763142612378135210895 18308644713918567202816343)
            ·
              refine ⟨27462967070877850804224515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18308644713918567202816343 27462967070877850804224515)
              ·
                refine ⟨41194450606316776206336773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27462967070877850804224515 41194450606316776206336773)
                ·
                  refine ⟨7723959488684395538688145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41194450606316776206336773 7723959488684395538688145)
                  ·
                    refine ⟨5792969616513296654016109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7723959488684395538688145 5792969616513296654016109)
                    ·
                      refine ⟨2172363606192486245256041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5792969616513296654016109 2172363606192486245256041)
                      ·
                        rfl

theorem cell23_4230663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_4230663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230663 prefixEnd_4230663 := by exact prefixLift 4230663
  have htrace : WordTrace (prefixWord ++ tailWord_4230663) baseStart_4230663 baseEnd_4230663 := by
    simpa [prefixWord, tailWord_4230663, baseEnd_4230663] using wordTrace_append hprefix tailTrace_4230663
  have hstable : (prefixWord ++ tailWord_4230663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230663).length < 2 ^ (prefixWord ++ tailWord_4230663).sum := by decide
  have hdescent : baseEnd_4230663 < baseStart_4230663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230666 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 8]
def baseStart_4230666 : Nat := 118140960795 + 4230666 * 2 ^ 59
def prefixEnd_4230666 : Nat := 4983230072969 + 3 ^ 40 * 4230666 * 2
def baseEnd_4230666 : Nat := 241373905181605525946503

theorem tailTrace_4230666 : CollatzResearch.WordTrace tailWord_4230666 prefixEnd_4230666 241373905181605525946503 := by
  unfold tailWord_4230666
  simp only [CollatzResearch.WordTrace]
  refine ⟨38576266422756774268385963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102870043794018064715695901 38576266422756774268385963)
  ·
    refine ⟨57864399634135161402578945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38576266422756774268385963 57864399634135161402578945)
    ·
      refine ⟨43398299725601371051934209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57864399634135161402578945 43398299725601371051934209)
      ·
        refine ⟨32548724794201028288950657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43398299725601371051934209 32548724794201028288950657)
        ·
          refine ⟨24411543595650771216712993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32548724794201028288950657 24411543595650771216712993)
          ·
            refine ⟨18308657696738078412534745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24411543595650771216712993 18308657696738078412534745)
            ·
              refine ⟨13731493272553558809401059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18308657696738078412534745 13731493272553558809401059)
              ·
                refine ⟨20597239908830338214101589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13731493272553558809401059 20597239908830338214101589)
                ·
                  refine ⟨241373905181605525946503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20597239908830338214101589 241373905181605525946503)
                  ·
                    rfl

theorem cell23_4230666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_4230666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230666 prefixEnd_4230666 := by exact prefixLift 4230666
  have htrace : WordTrace (prefixWord ++ tailWord_4230666) baseStart_4230666 baseEnd_4230666 := by
    simpa [prefixWord, tailWord_4230666, baseEnd_4230666] using wordTrace_append hprefix tailTrace_4230666
  have hstable : (prefixWord ++ tailWord_4230666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230666).length < 2 ^ (prefixWord ++ tailWord_4230666).sum := by decide
  have hdescent : baseEnd_4230666 < baseStart_4230666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230693 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_4230693 : Nat := 118140960795 + 4230693 * 2 ^ 59
def prefixEnd_4230693 : Nat := 4983230072969 + 3 ^ 40 * 4230693 * 2
def baseEnd_4230693 : Nat := 2172379010612121127880903

theorem tailTrace_4230693 : CollatzResearch.WordTrace tailWord_4230693 prefixEnd_4230693 2172379010612121127880903 := by
  unfold tailWord_4230693
  simp only [CollatzResearch.WordTrace]
  refine ⟨154306050461929280684776733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102870700307952853789851155 154306050461929280684776733)
  ·
    refine ⟨57864768923223480256791275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154306050461929280684776733 57864768923223480256791275)
    ·
      refine ⟨86797153384835220385186913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57864768923223480256791275 86797153384835220385186913)
      ·
        refine ⟨65097865038626415288890185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86797153384835220385186913 65097865038626415288890185)
        ·
          refine ⟨48823398778969811466667639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65097865038626415288890185 48823398778969811466667639)
          ·
            refine ⟨73235098168454717200001459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48823398778969811466667639 73235098168454717200001459)
            ·
              refine ⟨109852647252682075800002189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73235098168454717200001459 109852647252682075800002189)
              ·
                refine ⟨41194742719755778425000821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109852647252682075800002189 41194742719755778425000821)
                ·
                  refine ⟨3862007129977104227343827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41194742719755778425000821 3862007129977104227343827)
                  ·
                    refine ⟨5793010694965656341015741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3862007129977104227343827 5793010694965656341015741)
                    ·
                      refine ⟨2172379010612121127880903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793010694965656341015741 2172379010612121127880903)
                      ·
                        rfl

theorem cell23_4230693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_4230693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230693 prefixEnd_4230693 := by exact prefixLift 4230693
  have htrace : WordTrace (prefixWord ++ tailWord_4230693) baseStart_4230693 baseEnd_4230693 := by
    simpa [prefixWord, tailWord_4230693, baseEnd_4230693] using wordTrace_append hprefix tailTrace_4230693
  have hstable : (prefixWord ++ tailWord_4230693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230693).length < 2 ^ (prefixWord ++ tailWord_4230693).sum := by decide
  have hdescent : baseEnd_4230693 < baseStart_4230693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230736 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_4230736 : Nat := 118140960795 + 4230736 * 2 ^ 59
def prefixEnd_4230736 : Nat := 4983230072969 + 3 ^ 40 * 4230736 * 2
def baseEnd_4230736 : Nat := 2172401090280264459643205

theorem tailTrace_4230736 : CollatzResearch.WordTrace tailWord_4230736 prefixEnd_4230736 2172401090280264459643205 := by
  unfold tailWord_4230736
  simp only [CollatzResearch.WordTrace]
  refine ⟨77153809400386749514296031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102871745867182332685728041 77153809400386749514296031)
  ·
    refine ⟨115730714100580124271444047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77153809400386749514296031 115730714100580124271444047)
    ·
      refine ⟨173596071150870186407166071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115730714100580124271444047 173596071150870186407166071)
      ·
        refine ⟨260394106726305279610749107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173596071150870186407166071 260394106726305279610749107)
        ·
          refine ⟨390591160089457919416123661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260394106726305279610749107 390591160089457919416123661)
          ·
            refine ⟨146471685033546719781046373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 390591160089457919416123661 146471685033546719781046373)
            ·
              refine ⟨27463440943790009958946195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146471685033546719781046373 27463440943790009958946195)
              ·
                refine ⟨41195161415685014938419293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27463440943790009958946195 41195161415685014938419293)
                ·
                  refine ⟨15448185530881880601907235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41195161415685014938419293 15448185530881880601907235)
                  ·
                    refine ⟨23172278296322820902860853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15448185530881880601907235 23172278296322820902860853)
                    ·
                      refine ⟨2172401090280264459643205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23172278296322820902860853 2172401090280264459643205)
                      ·
                        rfl

theorem cell23_4230736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_4230736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230736 prefixEnd_4230736 := by exact prefixLift 4230736
  have htrace : WordTrace (prefixWord ++ tailWord_4230736) baseStart_4230736 baseEnd_4230736 := by
    simpa [prefixWord, tailWord_4230736, baseEnd_4230736] using wordTrace_append hprefix tailTrace_4230736
  have hstable : (prefixWord ++ tailWord_4230736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230736).length < 2 ^ (prefixWord ++ tailWord_4230736).sum := by decide
  have hdescent : baseEnd_4230736 < baseStart_4230736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230743 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 1, 6]
def baseStart_4230743 : Nat := 118140960795 + 4230743 * 2 ^ 59
def prefixEnd_4230743 : Nat := 4983230072969 + 3 ^ 40 * 4230743 * 2
def baseEnd_4230743 : Nat := 724134894881615310751891

theorem tailTrace_4230743 : CollatzResearch.WordTrace tailWord_4230743 prefixEnd_4230743 724134894881615310751891 := by
  unfold tailWord_4230743
  simp only [CollatzResearch.WordTrace]
  refine ⟨154307874111748139224096883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102871916074498759482731255 154307874111748139224096883)
  ·
    refine ⟨231461811167622208836145325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154307874111748139224096883 231461811167622208836145325)
    ·
      refine ⟨86798179187858328313554497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231461811167622208836145325 86798179187858328313554497)
      ·
        refine ⟨65098634390893746235165873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86798179187858328313554497 65098634390893746235165873)
        ·
          refine ⟨48823975793170309676374405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65098634390893746235165873 48823975793170309676374405)
          ·
            refine ⟨9154495461219433064320201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48823975793170309676374405 9154495461219433064320201)
            ·
              refine ⟨6865871595914574798240151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9154495461219433064320201 6865871595914574798240151)
              ·
                refine ⟨10298807393871862197360227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6865871595914574798240151 10298807393871862197360227)
                ·
                  refine ⟨15448211090807793296040341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10298807393871862197360227 15448211090807793296040341)
                  ·
                    refine ⟨724134894881615310751891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15448211090807793296040341 724134894881615310751891)
                    ·
                      rfl

theorem cell23_4230743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_4230743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230743 prefixEnd_4230743 := by exact prefixLift 4230743
  have htrace : WordTrace (prefixWord ++ tailWord_4230743) baseStart_4230743 baseEnd_4230743 := by
    simpa [prefixWord, tailWord_4230743, baseEnd_4230743] using wordTrace_append hprefix tailTrace_4230743
  have hstable : (prefixWord ++ tailWord_4230743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230743).length < 2 ^ (prefixWord ++ tailWord_4230743).sum := by decide
  have hdescent : baseEnd_4230743 < baseStart_4230743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230746 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_4230746 : Nat := 118140960795 + 4230746 * 2 ^ 59
def prefixEnd_4230746 : Nat := 4983230072969 + 3 ^ 40 * 4230746 * 2
def baseEnd_4230746 : Nat := 2172406225086809420518159

theorem tailTrace_4230746 : CollatzResearch.WordTrace tailWord_4230746 prefixEnd_4230746 2172406225086809420518159 := by
  unfold tailWord_4230746
  simp only [CollatzResearch.WordTrace]
  refine ⟨38576995882684317684114023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102871989020491513824304061 38576995882684317684114023)
  ·
    refine ⟨57865493824026476526171035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38576995882684317684114023 57865493824026476526171035)
    ·
      refine ⟨86798240736039714789256553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57865493824026476526171035 86798240736039714789256553)
      ·
        refine ⟨65098680552029786091942415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86798240736039714789256553 65098680552029786091942415)
        ·
          refine ⟨97648020828044679137913623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65098680552029786091942415 97648020828044679137913623)
          ·
            refine ⟨146472031242067018706870435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97648020828044679137913623 146472031242067018706870435)
            ·
              refine ⟨219708046863100528060305653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146472031242067018706870435 219708046863100528060305653)
              ·
                refine ⟨20597629393415674505653655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 219708046863100528060305653 20597629393415674505653655)
                ·
                  refine ⟨30896444090123511758480483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20597629393415674505653655 30896444090123511758480483)
                  ·
                    refine ⟨46344666135185267637720725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30896444090123511758480483 46344666135185267637720725)
                    ·
                      refine ⟨2172406225086809420518159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46344666135185267637720725 2172406225086809420518159)
                      ·
                        rfl

theorem cell23_4230746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_4230746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230746 prefixEnd_4230746 := by exact prefixLift 4230746
  have htrace : WordTrace (prefixWord ++ tailWord_4230746) baseStart_4230746 baseEnd_4230746 := by
    simpa [prefixWord, tailWord_4230746, baseEnd_4230746] using wordTrace_append hprefix tailTrace_4230746
  have hstable : (prefixWord ++ tailWord_4230746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230746).length < 2 ^ (prefixWord ++ tailWord_4230746).sum := by decide
  have hdescent : baseEnd_4230746 < baseStart_4230746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230753 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_4230753 : Nat := 118140960795 + 4230753 * 2 ^ 59
def prefixEnd_4230753 : Nat := 4983230072969 + 3 ^ 40 * 4230753 * 2
def baseEnd_4230753 : Nat := 2172409819451390893130627

theorem tailTrace_4230753 : CollatzResearch.WordTrace tailWord_4230753 prefixEnd_4230753 2172409819451390893130627 := by
  unfold tailWord_4230753
  simp only [CollatzResearch.WordTrace]
  refine ⟨154308238841711910931960913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102872159227807940621307275 154308238841711910931960913)
  ·
    refine ⟨115731179131283933198970685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154308238841711910931960913 115731179131283933198970685)
    ·
      refine ⟨43399192174231474949614007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115731179131283933198970685 43399192174231474949614007)
      ·
        refine ⟨65098788261347212424421011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43399192174231474949614007 65098788261347212424421011)
        ·
          refine ⟨97648182392020818636631517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65098788261347212424421011 97648182392020818636631517)
          ·
            refine ⟨36618068397007806988736819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97648182392020818636631517 36618068397007806988736819)
            ·
              refine ⟨54927102595511710483105229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36618068397007806988736819 54927102595511710483105229)
              ·
                refine ⟨20597663473316891431164461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54927102595511710483105229 20597663473316891431164461)
                ·
                  refine ⟨7724123802493834286686673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20597663473316891431164461 7724123802493834286686673)
                  ·
                    refine ⟨5793092851870375715015005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7724123802493834286686673 5793092851870375715015005)
                    ·
                      refine ⟨2172409819451390893130627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793092851870375715015005 2172409819451390893130627)
                      ·
                        rfl

theorem cell23_4230753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_4230753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230753 prefixEnd_4230753 := by exact prefixLift 4230753
  have htrace : WordTrace (prefixWord ++ tailWord_4230753) baseStart_4230753 baseEnd_4230753 := by
    simpa [prefixWord, tailWord_4230753, baseEnd_4230753] using wordTrace_append hprefix tailTrace_4230753
  have hstable : (prefixWord ++ tailWord_4230753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230753).length < 2 ^ (prefixWord ++ tailWord_4230753).sum := by decide
  have hdescent : baseEnd_4230753 < baseStart_4230753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230773 : List Nat := [1, 3, 4, 2, 1, 2, 10]
def baseStart_4230773 : Nat := 118140960795 + 4230773 * 2 ^ 59
def prefixEnd_4230773 : Nat := 4983230072969 + 3 ^ 40 * 4230773 * 2
def baseEnd_4230773 : Nat := 26820001099561491541735

theorem tailTrace_4230773 : CollatzResearch.WordTrace tailWord_4230773 prefixEnd_4230773 26820001099561491541735 := by
  unfold tailWord_4230773
  simp only [CollatzResearch.WordTrace]
  refine ⟨154308968301639454347688973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102872645534426302898459315 154308968301639454347688973)
  ·
    refine ⟨57865863113114795380383365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154308968301639454347688973 57865863113114795380383365)
    ·
      refine ⟨10849849333709024133821881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57865863113114795380383365 10849849333709024133821881)
      ·
        refine ⟨8137387000281768100366411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10849849333709024133821881 8137387000281768100366411)
        ·
          refine ⟨12206080500422652150549617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8137387000281768100366411 12206080500422652150549617)
          ·
            refine ⟨9154560375316989112912213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12206080500422652150549617 9154560375316989112912213)
            ·
              refine ⟨26820001099561491541735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9154560375316989112912213 26820001099561491541735)
              ·
                rfl

theorem cell23_4230773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 10].length) (baseStart_4230773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230773 prefixEnd_4230773 := by exact prefixLift 4230773
  have htrace : WordTrace (prefixWord ++ tailWord_4230773) baseStart_4230773 baseEnd_4230773 := by
    simpa [prefixWord, tailWord_4230773, baseEnd_4230773] using wordTrace_append hprefix tailTrace_4230773
  have hstable : (prefixWord ++ tailWord_4230773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230773).length < 2 ^ (prefixWord ++ tailWord_4230773).sum := by decide
  have hdescent : baseEnd_4230773 < baseStart_4230773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230800 : List Nat := [2, 1, 1, 1, 1, 1, 3, 7, 2, 1, 3]
def baseStart_4230800 : Nat := 118140960795 + 4230800 * 2 ^ 59
def prefixEnd_4230800 : Nat := 4983230072969 + 3 ^ 40 * 4230800 * 2
def baseEnd_4230800 : Nat := 2172433953042152209242911

theorem tailTrace_4230800 : CollatzResearch.WordTrace tailWord_4230800 prefixEnd_4230800 2172433953042152209242911 := by
  unfold tailWord_4230800
  simp only [CollatzResearch.WordTrace]
  refine ⟨77154976536270818979460927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102873302048361091972614569 77154976536270818979460927)
  ·
    refine ⟨115732464804406228469191391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77154976536270818979460927 115732464804406228469191391)
    ·
      refine ⟨173598697206609342703787087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115732464804406228469191391 173598697206609342703787087)
      ·
        refine ⟨260398045809914014055680631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173598697206609342703787087 260398045809914014055680631)
        ·
          refine ⟨390597068714871021083520947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260398045809914014055680631 390597068714871021083520947)
          ·
            refine ⟨585895603072306531625281421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390597068714871021083520947 585895603072306531625281421)
            ·
              refine ⟨219710851152114949359480533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 585895603072306531625281421 219710851152114949359480533)
              ·
                refine ⟨5149473073877694125612825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 219710851152114949359480533 5149473073877694125612825)
                ·
                  refine ⟨3862104805408270594209619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5149473073877694125612825 3862104805408270594209619)
                  ·
                    refine ⟨5793157208112405891314429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3862104805408270594209619 5793157208112405891314429)
                    ·
                      refine ⟨2172433953042152209242911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793157208112405891314429 2172433953042152209242911)
                      ·
                        rfl

theorem cell23_4230800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 2, 1, 3].length) (baseStart_4230800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230800 prefixEnd_4230800 := by exact prefixLift 4230800
  have htrace : WordTrace (prefixWord ++ tailWord_4230800) baseStart_4230800 baseEnd_4230800 := by
    simpa [prefixWord, tailWord_4230800, baseEnd_4230800] using wordTrace_append hprefix tailTrace_4230800
  have hstable : (prefixWord ++ tailWord_4230800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230800).length < 2 ^ (prefixWord ++ tailWord_4230800).sum := by decide
  have hdescent : baseEnd_4230800 < baseStart_4230800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230804 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4230804 : Nat := 118140960795 + 4230804 * 2 ^ 59
def prefixEnd_4230804 : Nat := 4983230072969 + 3 ^ 40 * 4230804 * 2
def baseEnd_4230804 : Nat := 2172436006964770193592893

theorem tailTrace_4230804 : CollatzResearch.WordTrace tailWord_4230804 prefixEnd_4230804 2172436006964770193592893 := by
  unfold tailWord_4230804
  simp only [CollatzResearch.WordTrace]
  refine ⟨77155049482263573321033733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102873399309684764428044977 77155049482263573321033733)
  ·
    refine ⟨14466571777924419997693825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77155049482263573321033733 14466571777924419997693825)
    ·
      refine ⟨10849928833443314998270369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14466571777924419997693825 10849928833443314998270369)
      ·
        refine ⟨8137446625082486248702777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10849928833443314998270369 8137446625082486248702777)
        ·
          refine ⟨6103084968811864686527083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8137446625082486248702777 6103084968811864686527083)
          ·
            refine ⟨9154627453217797029790625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6103084968811864686527083 9154627453217797029790625)
            ·
              refine ⟨6865970589913347772342969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9154627453217797029790625 6865970589913347772342969)
              ·
                refine ⟨5149477942435010829257227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6865970589913347772342969 5149477942435010829257227)
                ·
                  refine ⟨7724216913652516243885841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149477942435010829257227 7724216913652516243885841)
                  ·
                    refine ⟨5793162685239387182914381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7724216913652516243885841 5793162685239387182914381)
                    ·
                      refine ⟨2172436006964770193592893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793162685239387182914381 2172436006964770193592893)
                      ·
                        rfl

theorem cell23_4230804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4230804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230804 prefixEnd_4230804 := by exact prefixLift 4230804
  have htrace : WordTrace (prefixWord ++ tailWord_4230804) baseStart_4230804 baseEnd_4230804 := by
    simpa [prefixWord, tailWord_4230804, baseEnd_4230804] using wordTrace_append hprefix tailTrace_4230804
  have hstable : (prefixWord ++ tailWord_4230804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230804).length < 2 ^ (prefixWord ++ tailWord_4230804).sum := by decide
  have hdescent : baseEnd_4230804 < baseStart_4230804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230824 : List Nat := [2, 1, 7, 1, 2, 1, 9]
def baseStart_4230824 : Nat := 118140960795 + 4230824 * 2 ^ 59
def prefixEnd_4230824 : Nat := 4983230072969 + 3 ^ 40 * 4230824 * 2
def baseEnd_4230824 : Nat := 26820324402195803893121

theorem tailTrace_4230824 : CollatzResearch.WordTrace tailWord_4230824 prefixEnd_4230824 26820324402195803893121 := by
  unfold tailWord_4230824
  simp only [CollatzResearch.WordTrace]
  refine ⟨77155414212227345028897763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102873885616303126705197017 77155414212227345028897763)
  ·
    refine ⟨115733121318341017543346645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77155414212227345028897763 115733121318341017543346645)
    ·
      refine ⟨2712495030898617598672187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 115733121318341017543346645 2712495030898617598672187)
      ·
        refine ⟨4068742546347926398008281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2712495030898617598672187 4068742546347926398008281)
        ·
          refine ⟨3051556909760944798506211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4068742546347926398008281 3051556909760944798506211)
          ·
            refine ⟨4577335364641417197759317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051556909760944798506211 4577335364641417197759317)
            ·
              refine ⟨26820324402195803893121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4577335364641417197759317 26820324402195803893121)
              ·
                rfl

theorem cell23_4230824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 9].length) (baseStart_4230824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230824 prefixEnd_4230824 := by exact prefixLift 4230824
  have htrace : WordTrace (prefixWord ++ tailWord_4230824) baseStart_4230824 baseEnd_4230824 := by
    simpa [prefixWord, tailWord_4230824, baseEnd_4230824] using wordTrace_append hprefix tailTrace_4230824
  have hstable : (prefixWord ++ tailWord_4230824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230824).length < 2 ^ (prefixWord ++ tailWord_4230824).sum := by decide
  have hdescent : baseEnd_4230824 < baseStart_4230824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230861 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_4230861 : Nat := 118140960795 + 4230861 * 2 ^ 59
def prefixEnd_4230861 : Nat := 4983230072969 + 3 ^ 40 * 4230861 * 2
def baseEnd_4230861 : Nat := 2172465275362076470580131

theorem tailTrace_4230861 : CollatzResearch.WordTrace tailWord_4230861 prefixEnd_4230861 2172465275362076470580131 := by
  unfold tailWord_4230861
  simp only [CollatzResearch.WordTrace]
  refine ⟨154312177925320645376892437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102874785283547096917928291 154312177925320645376892437)
  ·
    refine ⟨7233383340249405252041833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154312177925320645376892437 7233383340249405252041833)
    ·
      refine ⟨5425037505187053939031375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7233383340249405252041833 5425037505187053939031375)
      ·
        refine ⟨8137556257780580908547063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425037505187053939031375 8137556257780580908547063)
        ·
          refine ⟨12206334386670871362820595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8137556257780580908547063 12206334386670871362820595)
          ·
            refine ⟨18309501580006307044230893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12206334386670871362820595 18309501580006307044230893)
            ·
              refine ⟨6866063092502365141586585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18309501580006307044230893 6866063092502365141586585)
              ·
                refine ⟨5149547319376773856189939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6866063092502365141586585 5149547319376773856189939)
                ·
                  refine ⟨7724320979065160784284909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149547319376773856189939 7724320979065160784284909)
                  ·
                    refine ⟨2896620367149435294106841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7724320979065160784284909 2896620367149435294106841)
                    ·
                      refine ⟨2172465275362076470580131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896620367149435294106841 2172465275362076470580131)
                      ·
                        rfl

theorem cell23_4230861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_4230861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230861 prefixEnd_4230861 := by exact prefixLift 4230861
  have htrace : WordTrace (prefixWord ++ tailWord_4230861) baseStart_4230861 baseEnd_4230861 := by
    simpa [prefixWord, tailWord_4230861, baseEnd_4230861] using wordTrace_append hprefix tailTrace_4230861
  have hstable : (prefixWord ++ tailWord_4230861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230861).length < 2 ^ (prefixWord ++ tailWord_4230861).sum := by decide
  have hdescent : baseEnd_4230861 < baseStart_4230861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230897 : List Nat := [1, 2, 2, 2, 2, 3, 4, 2, 5]
def baseStart_4230897 : Nat := 118140960795 + 4230897 * 2 ^ 59
def prefixEnd_4230897 : Nat := 4983230072969 + 3 ^ 40 * 4230897 * 2
def baseEnd_4230897 : Nat := 241387084518404258858885

theorem tailTrace_4230897 : CollatzResearch.WordTrace tailWord_4230897 prefixEnd_4230897 241387084518404258858885 := by
  unfold tailWord_4230897
  simp only [CollatzResearch.WordTrace]
  refine ⟨154313490953190223525202945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102875660635460149016801963 154313490953190223525202945)
  ·
    refine ⟨115735118214892667643902209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154313490953190223525202945 115735118214892667643902209)
    ·
      refine ⟨86801338661169500732926657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115735118214892667643902209 86801338661169500732926657)
      ·
        refine ⟨65101003995877125549694993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86801338661169500732926657 65101003995877125549694993)
        ·
          refine ⟨48825752996907844162271245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65101003995877125549694993 48825752996907844162271245)
          ·
            refine ⟨18309657373840441560851717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48825752996907844162271245 18309657373840441560851717)
            ·
              refine ⟨3433060757595082792659697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18309657373840441560851717 3433060757595082792659697)
              ·
                refine ⟨2574795568196312094494773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3433060757595082792659697 2574795568196312094494773)
                ·
                  refine ⟨241387084518404258858885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2574795568196312094494773 241387084518404258858885)
                  ·
                    rfl

theorem cell23_4230897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 5].length) (baseStart_4230897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230897 prefixEnd_4230897 := by exact prefixLift 4230897
  have htrace : WordTrace (prefixWord ++ tailWord_4230897) baseStart_4230897 baseEnd_4230897 := by
    simpa [prefixWord, tailWord_4230897, baseEnd_4230897] using wordTrace_append hprefix tailTrace_4230897
  have hstable : (prefixWord ++ tailWord_4230897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230897).length < 2 ^ (prefixWord ++ tailWord_4230897).sum := by decide
  have hdescent : baseEnd_4230897 < baseStart_4230897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230903 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_4230903 : Nat := 118140960795 + 4230903 * 2 ^ 59
def prefixEnd_4230903 : Nat := 4983230072969 + 3 ^ 40 * 4230903 * 2
def baseEnd_4230903 : Nat := 2172486841549565306254937

theorem tailTrace_4230903 : CollatzResearch.WordTrace tailWord_4230903 prefixEnd_4230903 2172486841549565306254937 := by
  unfold tailWord_4230903
  simp only [CollatzResearch.WordTrace]
  refine ⟨154313709791168486549921363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102875806527445657699947575 154313709791168486549921363)
  ·
    refine ⟨231470564686752729824882045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154313709791168486549921363 231470564686752729824882045)
    ·
      refine ⟨86801461757532273684330767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231470564686752729824882045 86801461757532273684330767)
      ·
        refine ⟨130202192636298410526496151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86801461757532273684330767 130202192636298410526496151)
        ·
          refine ⟨195303288954447615789744227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130202192636298410526496151 195303288954447615789744227)
          ·
            refine ⟨292954933431671423684616341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195303288954447615789744227 292954933431671423684616341)
            ·
              refine ⟨13732262504609597985216391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 292954933431671423684616341 13732262504609597985216391)
              ·
                refine ⟨20598393756914396977824587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13732262504609597985216391 20598393756914396977824587)
                ·
                  refine ⟨30897590635371595466736881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20598393756914396977824587 30897590635371595466736881)
                  ·
                    refine ⟨23173192976528696600052661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30897590635371595466736881 23173192976528696600052661)
                    ·
                      refine ⟨2172486841549565306254937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23173192976528696600052661 2172486841549565306254937)
                      ·
                        rfl

theorem cell23_4230903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_4230903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230903 prefixEnd_4230903 := by exact prefixLift 4230903
  have htrace : WordTrace (prefixWord ++ tailWord_4230903) baseStart_4230903 baseEnd_4230903 := by
    simpa [prefixWord, tailWord_4230903, baseEnd_4230903] using wordTrace_append hprefix tailTrace_4230903
  have hstable : (prefixWord ++ tailWord_4230903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230903).length < 2 ^ (prefixWord ++ tailWord_4230903).sum := by decide
  have hdescent : baseEnd_4230903 < baseStart_4230903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230940 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_4230940 : Nat := 118140960795 + 4230940 * 2 ^ 59
def prefixEnd_4230940 : Nat := 4983230072969 + 3 ^ 40 * 4230940 * 2
def baseEnd_4230940 : Nat := 724168613444593887164089

theorem tailTrace_4230940 : CollatzResearch.WordTrace tailWord_4230940 prefixEnd_4230940 724168613444593887164089 := by
  unfold tailWord_4230940
  simp only [CollatzResearch.WordTrace]
  refine ⟨77157529646017220934509137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102876706194689627912678849 77157529646017220934509137)
  ·
    refine ⟨57868147234512915700881853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77157529646017220934509137 57868147234512915700881853)
    ·
      refine ⟨21700555212942343387830695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57868147234512915700881853 21700555212942343387830695)
      ·
        refine ⟨32550832819413515081746043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21700555212942343387830695 32550832819413515081746043)
        ·
          refine ⟨48826249229120272622619065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32550832819413515081746043 48826249229120272622619065)
          ·
            refine ⟨36619686921840204466964299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48826249229120272622619065 36619686921840204466964299)
            ·
              refine ⟨54929530382760306700446449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36619686921840204466964299 54929530382760306700446449)
              ·
                refine ⟨41197147787070230025334837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54929530382760306700446449 41197147787070230025334837)
                ·
                  refine ⟨3862232605037834064875141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41197147787070230025334837 3862232605037834064875141)
                  ·
                    refine ⟨724168613444593887164089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3862232605037834064875141 724168613444593887164089)
                    ·
                      rfl

theorem cell23_4230940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_4230940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230940 prefixEnd_4230940 := by exact prefixLift 4230940
  have htrace : WordTrace (prefixWord ++ tailWord_4230940) baseStart_4230940 baseEnd_4230940 := by
    simpa [prefixWord, tailWord_4230940, baseEnd_4230940] using wordTrace_append hprefix tailTrace_4230940
  have hstable : (prefixWord ++ tailWord_4230940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230940).length < 2 ^ (prefixWord ++ tailWord_4230940).sum := by decide
  have hdescent : baseEnd_4230940 < baseStart_4230940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230942 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4230942 : Nat := 118140960795 + 4230942 * 2 ^ 59
def prefixEnd_4230942 : Nat := 4983230072969 + 3 ^ 40 * 4230942 * 2
def baseEnd_4230942 : Nat := 2172506867295090653667259

theorem tailTrace_4230942 : CollatzResearch.WordTrace tailWord_4230942 prefixEnd_4230942 2172506867295090653667259 := by
  unfold tailWord_4230942
  simp only [CollatzResearch.WordTrace]
  refine ⟨19289391529753399526323885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102876754825351464140394053 19289391529753399526323885)
  ·
    refine ⟨7233521823657524822371457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19289391529753399526323885 7233521823657524822371457)
    ·
      refine ⟨5425141367743143616778593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7233521823657524822371457 5425141367743143616778593)
      ·
        refine ⟨4068856025807357712583945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5425141367743143616778593 4068856025807357712583945)
        ·
          refine ⟨3051642019355518284437959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4068856025807357712583945 3051642019355518284437959)
          ·
            refine ⟨4577463029033277426656939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051642019355518284437959 4577463029033277426656939)
            ·
              refine ⟨6866194543549916139985409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577463029033277426656939 6866194543549916139985409)
              ·
                refine ⟨5149645907662437104989057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6866194543549916139985409 5149645907662437104989057)
                ·
                  refine ⟨3862234430746827828741793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5149645907662437104989057 3862234430746827828741793)
                  ·
                    refine ⟨2896675823060120871556345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3862234430746827828741793 2896675823060120871556345)
                    ·
                      refine ⟨2172506867295090653667259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896675823060120871556345 2172506867295090653667259)
                      ·
                        rfl

theorem cell23_4230942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4230942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230942 prefixEnd_4230942 := by exact prefixLift 4230942
  have htrace : WordTrace (prefixWord ++ tailWord_4230942) baseStart_4230942 baseEnd_4230942 := by
    simpa [prefixWord, tailWord_4230942, baseEnd_4230942] using wordTrace_append hprefix tailTrace_4230942
  have hstable : (prefixWord ++ tailWord_4230942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230942).length < 2 ^ (prefixWord ++ tailWord_4230942).sum := by decide
  have hdescent : baseEnd_4230942 < baseStart_4230942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230943 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4230943 : Nat := 118140960795 + 4230943 * 2 ^ 59
def prefixEnd_4230943 : Nat := 4983230072969 + 3 ^ 40 * 4230943 * 2
def baseEnd_4230943 : Nat := 2172507380775745149754753

theorem tailTrace_4230943 : CollatzResearch.WordTrace tailWord_4230943 prefixEnd_4230943 2172507380775745149754753 := by
  unfold tailWord_4230943
  simp only [CollatzResearch.WordTrace]
  refine ⟨154315168711023573381377483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102876779140682382254251655 154315168711023573381377483)
  ·
    refine ⟨231472753066535360072066225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154315168711023573381377483 231472753066535360072066225)
    ·
      refine ⟨173604564799901520054049669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231472753066535360072066225 173604564799901520054049669)
      ·
        refine ⟨32550855899981535010134313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173604564799901520054049669 32550855899981535010134313)
        ·
          refine ⟨24413141924986151257600735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32550855899981535010134313 24413141924986151257600735)
          ·
            refine ⟨36619712887479226886401103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24413141924986151257600735 36619712887479226886401103)
            ·
              refine ⟨54929569331218840329601655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36619712887479226886401103 54929569331218840329601655)
              ·
                refine ⟨82394353996828260494402483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54929569331218840329601655 82394353996828260494402483)
                ·
                  refine ⟨123591530995242390741603725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82394353996828260494402483 123591530995242390741603725)
                  ·
                    refine ⟨46346824123215896528101397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123591530995242390741603725 46346824123215896528101397)
                    ·
                      refine ⟨2172507380775745149754753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46346824123215896528101397 2172507380775745149754753)
                      ·
                        rfl

theorem cell23_4230943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4230943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230943 prefixEnd_4230943 := by exact prefixLift 4230943
  have htrace : WordTrace (prefixWord ++ tailWord_4230943) baseStart_4230943 baseEnd_4230943 := by
    simpa [prefixWord, tailWord_4230943, baseEnd_4230943] using wordTrace_append hprefix tailTrace_4230943
  have hstable : (prefixWord ++ tailWord_4230943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230943).length < 2 ^ (prefixWord ++ tailWord_4230943).sum := by decide
  have hdescent : baseEnd_4230943 < baseStart_4230943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4230964 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_4230964 : Nat := 118140960795 + 4230964 * 2 ^ 59
def prefixEnd_4230964 : Nat := 4983230072969 + 3 ^ 40 * 4230964 * 2
def baseEnd_4230964 : Nat := 2172518163869489567592157

theorem tailTrace_4230964 : CollatzResearch.WordTrace tailWord_4230964 prefixEnd_4230964 2172518163869489567592157 := by
  unfold tailWord_4230964
  simp only [CollatzResearch.WordTrace]
  refine ⟨77157967321973746983945973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102877289762631662645261297 77157967321973746983945973)
  ·
    refine ⟨7233559436435038779744935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77157967321973746983945973 7233559436435038779744935)
    ·
      refine ⟨10850339154652558169617403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7233559436435038779744935 10850339154652558169617403)
      ·
        refine ⟨16275508731978837254426105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10850339154652558169617403 16275508731978837254426105)
        ·
          refine ⟨12206631548984127940819579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16275508731978837254426105 12206631548984127940819579)
          ·
            refine ⟨18309947323476191911229369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12206631548984127940819579 18309947323476191911229369)
            ·
              refine ⟨13732460492607143933422027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18309947323476191911229369 13732460492607143933422027)
              ·
                refine ⟨20598690738910715900133041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13732460492607143933422027 20598690738910715900133041)
                ·
                  refine ⟨15449018054183036925099781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20598690738910715900133041 15449018054183036925099781)
                  ·
                    refine ⟨2896690885159319423456209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15449018054183036925099781 2896690885159319423456209)
                    ·
                      refine ⟨2172518163869489567592157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896690885159319423456209 2172518163869489567592157)
                      ·
                        rfl

theorem cell23_4230964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_4230964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4230964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4230964 prefixEnd_4230964 := by exact prefixLift 4230964
  have htrace : WordTrace (prefixWord ++ tailWord_4230964) baseStart_4230964 baseEnd_4230964 := by
    simpa [prefixWord, tailWord_4230964, baseEnd_4230964] using wordTrace_append hprefix tailTrace_4230964
  have hstable : (prefixWord ++ tailWord_4230964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4230964).length < 2 ^ (prefixWord ++ tailWord_4230964).sum := by decide
  have hdescent : baseEnd_4230964 < baseStart_4230964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4230964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231007 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 4, 3, 2]
def baseStart_4231007 : Nat := 118140960795 + 4231007 * 2 ^ 59
def prefixEnd_4231007 : Nat := 4983230072969 + 3 ^ 40 * 4231007 * 2
def baseEnd_4231007 : Nat := 2172540243537632899354459

theorem tailTrace_4231007 : CollatzResearch.WordTrace tailWord_4231007 prefixEnd_4231007 2172540243537632899354459 := by
  unfold tailWord_4231007
  simp only [CollatzResearch.WordTrace]
  refine ⟨154317502982791712311707275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102878335321861141541138183 154317502982791712311707275)
  ·
    refine ⟨231476254474187568467560913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154317502982791712311707275 231476254474187568467560913)
    ·
      refine ⟨173607190855640676350670685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231476254474187568467560913 173607190855640676350670685)
      ·
        refine ⟨65102696570865253631501507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173607190855640676350670685 65102696570865253631501507)
        ·
          refine ⟨97654044856297880447252261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65102696570865253631501507 97654044856297880447252261)
          ·
            refine ⟨18310133410555852583859799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97654044856297880447252261 18310133410555852583859799)
            ·
              refine ⟨27465200115833778875789699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18310133410555852583859799 27465200115833778875789699)
              ·
                refine ⟨41197800173750668313684549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27465200115833778875789699 41197800173750668313684549)
                ·
                  refine ⟨7724587532578250308815853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41197800173750668313684549 7724587532578250308815853)
                  ·
                    refine ⟨2896720324716843865805945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7724587532578250308815853 2896720324716843865805945)
                    ·
                      refine ⟨2172540243537632899354459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2896720324716843865805945 2172540243537632899354459)
                      ·
                        rfl

theorem cell23_4231007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_4231007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231007 prefixEnd_4231007 := by exact prefixLift 4231007
  have htrace : WordTrace (prefixWord ++ tailWord_4231007) baseStart_4231007 baseEnd_4231007 := by
    simpa [prefixWord, tailWord_4231007, baseEnd_4231007] using wordTrace_append hprefix tailTrace_4231007
  have hstable : (prefixWord ++ tailWord_4231007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231007).length < 2 ^ (prefixWord ++ tailWord_4231007).sum := by decide
  have hdescent : baseEnd_4231007 < baseStart_4231007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231047 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 1, 6]
def baseStart_4231047 : Nat := 118140960795 + 4231047 * 2 ^ 59
def prefixEnd_4231047 : Nat := 4983230072969 + 3 ^ 40 * 4231047 * 2
def baseEnd_4231047 : Nat := 724186927587937580951425

theorem tailTrace_4231047 : CollatzResearch.WordTrace tailWord_4231047 prefixEnd_4231047 724186927587937580951425 := by
  unfold tailWord_4231047
  simp only [CollatzResearch.WordTrace]
  refine ⟨154318961902646799143163395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102879307935097866095442263 154318961902646799143163395)
  ·
    refine ⟨231478442853970198714745093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154318961902646799143163395 231478442853970198714745093)
    ·
      refine ⟨43402208035119412259014705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231478442853970198714745093 43402208035119412259014705)
      ·
        refine ⟨32551656026339559194261029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43402208035119412259014705 32551656026339559194261029)
        ·
          refine ⟨6103435504938667348923943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32551656026339559194261029 6103435504938667348923943)
          ·
            refine ⟨9155153257408001023385915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6103435504938667348923943 9155153257408001023385915)
            ·
              refine ⟨13732729886112001535078873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9155153257408001023385915 13732729886112001535078873)
              ·
                refine ⟨10299547414584001151309155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13732729886112001535078873 10299547414584001151309155)
                ·
                  refine ⟨15449321121876001726963733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10299547414584001151309155 15449321121876001726963733)
                  ·
                    refine ⟨724186927587937580951425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15449321121876001726963733 724186927587937580951425)
                    ·
                      rfl

theorem cell23_4231047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_4231047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231047 prefixEnd_4231047 := by exact prefixLift 4231047
  have htrace : WordTrace (prefixWord ++ tailWord_4231047) baseStart_4231047 baseEnd_4231047 := by
    simpa [prefixWord, tailWord_4231047, baseEnd_4231047] using wordTrace_append hprefix tailTrace_4231047
  have hstable : (prefixWord ++ tailWord_4231047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231047).length < 2 ^ (prefixWord ++ tailWord_4231047).sum := by decide
  have hdescent : baseEnd_4231047 < baseStart_4231047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231057 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_4231057 : Nat := 118140960795 + 4231057 * 2 ^ 59
def prefixEnd_4231057 : Nat := 4983230072969 + 3 ^ 40 * 4231057 * 2
def baseEnd_4231057 : Nat := 2172565917570357703729229

theorem tailTrace_4231057 : CollatzResearch.WordTrace tailWord_4231057 prefixEnd_4231057 2172565917570357703729229 := by
  unfold tailWord_4231057
  simp only [CollatzResearch.WordTrace]
  refine ⟨154319326632610570851027425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102879551088407047234018283 154319326632610570851027425)
  ·
    refine ⟨115739494974457928138270569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154319326632610570851027425 115739494974457928138270569)
    ·
      refine ⟨86804621230843446103702927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115739494974457928138270569 86804621230843446103702927)
      ·
        refine ⟨130206931846265169155554391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86804621230843446103702927 130206931846265169155554391)
        ·
          refine ⟨195310397769397753733331587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130206931846265169155554391 195310397769397753733331587)
          ·
            refine ⟨292965596654096630599997381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195310397769397753733331587 292965596654096630599997381)
            ·
              refine ⟨54931049372643118237499509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 292965596654096630599997381 54931049372643118237499509)
              ·
                refine ⟨5149785878685292334765579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54931049372643118237499509 5149785878685292334765579)
                ·
                  refine ⟨7724678818027938502148369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5149785878685292334765579 7724678818027938502148369)
                  ·
                    refine ⟨5793509113520953876611277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7724678818027938502148369 5793509113520953876611277)
                    ·
                      refine ⟨2172565917570357703729229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793509113520953876611277 2172565917570357703729229)
                      ·
                        rfl

theorem cell23_4231057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_4231057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231057 prefixEnd_4231057 := by exact prefixLift 4231057
  have htrace : WordTrace (prefixWord ++ tailWord_4231057) baseStart_4231057 baseEnd_4231057 := by
    simpa [prefixWord, tailWord_4231057, baseEnd_4231057] using wordTrace_append hprefix tailTrace_4231057
  have hstable : (prefixWord ++ tailWord_4231057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231057).length < 2 ^ (prefixWord ++ tailWord_4231057).sum := by decide
  have hdescent : baseEnd_4231057 < baseStart_4231057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231060 : List Nat := [2, 4, 2, 1, 1, 13]
def baseStart_4231060 : Nat := 118140960795 + 4231060 * 2 ^ 59
def prefixEnd_4231060 : Nat := 4983230072969 + 3 ^ 40 * 4231060 * 2
def baseEnd_4231060 : Nat := 8940606823095971983505

theorem tailTrace_4231060 : CollatzResearch.WordTrace tailWord_4231060 prefixEnd_4231060 8940606823095971983505 := by
  unfold tailWord_4231060
  simp only [CollatzResearch.WordTrace]
  refine ⟨77159718025799851181693317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102879624034399801575591089 77159718025799851181693317)
  ·
    refine ⟨14467447129837472096567497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77159718025799851181693317 14467447129837472096567497)
    ·
      refine ⟨10850585347378104072425623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14467447129837472096567497 10850585347378104072425623)
      ·
        refine ⟨16275878021067156108638435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10850585347378104072425623 16275878021067156108638435)
        ·
          refine ⟨24413817031600734162957653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16275878021067156108638435 24413817031600734162957653)
          ·
            refine ⟨8940606823095971983505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 24413817031600734162957653 8940606823095971983505)
            ·
              rfl

theorem cell23_4231060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 13].length) (baseStart_4231060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231060 prefixEnd_4231060 := by exact prefixLift 4231060
  have htrace : WordTrace (prefixWord ++ tailWord_4231060) baseStart_4231060 baseEnd_4231060 := by
    simpa [prefixWord, tailWord_4231060, baseEnd_4231060] using wordTrace_append hprefix tailTrace_4231060
  have hstable : (prefixWord ++ tailWord_4231060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231060).length < 2 ^ (prefixWord ++ tailWord_4231060).sum := by decide
  have hdescent : baseEnd_4231060 < baseStart_4231060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231087 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 3]
def baseStart_4231087 : Nat := 118140960795 + 4231087 * 2 ^ 59
def prefixEnd_4231087 : Nat := 4983230072969 + 3 ^ 40 * 4231087 * 2
def baseEnd_4231087 : Nat := 2172581321989992586354091

theorem tailTrace_4231087 : CollatzResearch.WordTrace tailWord_4231087 prefixEnd_4231087 2172581321989992586354091 := by
  unfold tailWord_4231087
  simp only [CollatzResearch.WordTrace]
  refine ⟨154320420822501885974619515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102880280548334590649746343 154320420822501885974619515)
  ·
    refine ⟨231480631233752828961929273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154320420822501885974619515 231480631233752828961929273)
    ·
      refine ⟨173610473425314621721446955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231480631233752828961929273 173610473425314621721446955)
      ·
        refine ⟨260415710137971932582170433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173610473425314621721446955 260415710137971932582170433)
        ·
          refine ⟨195311782603478949436627825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260415710137971932582170433 195311782603478949436627825)
          ·
            refine ⟨146483836952609212077470869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195311782603478949436627825 146483836952609212077470869)
            ·
              refine ⟨6866429857153556816131447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146483836952609212077470869 6866429857153556816131447)
              ·
                refine ⟨10299644785730335224197171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6866429857153556816131447 10299644785730335224197171)
                ·
                  refine ⟨15449467178595502836295757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10299644785730335224197171 15449467178595502836295757)
                  ·
                    refine ⟨5793550191973313563610909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15449467178595502836295757 5793550191973313563610909)
                    ·
                      refine ⟨2172581321989992586354091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793550191973313563610909 2172581321989992586354091)
                      ·
                        rfl

theorem cell23_4231087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_4231087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231087 prefixEnd_4231087 := by exact prefixLift 4231087
  have htrace : WordTrace (prefixWord ++ tailWord_4231087) baseStart_4231087 baseEnd_4231087 := by
    simpa [prefixWord, tailWord_4231087, baseEnd_4231087] using wordTrace_append hprefix tailTrace_4231087
  have hstable : (prefixWord ++ tailWord_4231087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231087).length < 2 ^ (prefixWord ++ tailWord_4231087).sum := by decide
  have hdescent : baseEnd_4231087 < baseStart_4231087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231120 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 2, 6]
def baseStart_4231120 : Nat := 118140960795 + 4231120 * 2 ^ 59
def prefixEnd_4231120 : Nat := 4983230072969 + 3 ^ 40 * 4231120 * 2
def baseEnd_4231120 : Nat := 724199422283863652413813

theorem tailTrace_4231120 : CollatzResearch.WordTrace tailWord_4231120 prefixEnd_4231120 724199422283863652413813 := by
  unfold tailWord_4231120
  simp only [CollatzResearch.WordTrace]
  refine ⟨77160812215691166305285407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102881082954254888407047209 77160812215691166305285407)
  ·
    refine ⟨115741218323536749457928111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77160812215691166305285407 115741218323536749457928111)
    ·
      refine ⟨173611827485305124186892167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115741218323536749457928111 173611827485305124186892167)
      ·
        refine ⟨260417741227957686280338251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173611827485305124186892167 260417741227957686280338251)
        ·
          refine ⟨390626611841936529420507377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260417741227957686280338251 390626611841936529420507377)
          ·
            refine ⟨292969958881452397065380533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390626611841936529420507377 292969958881452397065380533)
            ·
              refine ⟨27465933645136162224879425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 292969958881452397065380533 27465933645136162224879425)
              ·
                refine ⟨20599450233852121668659569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27465933645136162224879425 20599450233852121668659569)
                ·
                  refine ⟨15449587675389091251494677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20599450233852121668659569 15449587675389091251494677)
                  ·
                    refine ⟨724199422283863652413813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15449587675389091251494677 724199422283863652413813)
                    ·
                      rfl

theorem cell23_4231120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_4231120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231120 prefixEnd_4231120 := by exact prefixLift 4231120
  have htrace : WordTrace (prefixWord ++ tailWord_4231120) baseStart_4231120 baseEnd_4231120 := by
    simpa [prefixWord, tailWord_4231120, baseEnd_4231120] using wordTrace_append hprefix tailTrace_4231120
  have hstable : (prefixWord ++ tailWord_4231120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231120).length < 2 ^ (prefixWord ++ tailWord_4231120).sum := by decide
  have hdescent : baseEnd_4231120 < baseStart_4231120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231138 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4231138 : Nat := 118140960795 + 4231138 * 2 ^ 59
def prefixEnd_4231138 : Nat := 4983230072969 + 3 ^ 40 * 4231138 * 2
def baseEnd_4231138 : Nat := 2172607509503371886816357

theorem tailTrace_4231138 : CollatzResearch.WordTrace tailWord_4231138 prefixEnd_4231138 2172607509503371886816357 := by
  unfold tailWord_4231138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38580570236329280421181517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102881520630211414456484045 38580570236329280421181517)
  ·
    refine ⟨14467713838623480157943069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38580570236329280421181517 14467713838623480157943069)
    ·
      refine ⟨5425392689483805059228651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14467713838623480157943069 5425392689483805059228651)
      ·
        refine ⟨8138089034225707588842977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425392689483805059228651 8138089034225707588842977)
        ·
          refine ⟨6103566775669280691632233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8138089034225707588842977 6103566775669280691632233)
          ·
            refine ⟨4577675081751960518724175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6103566775669280691632233 4577675081751960518724175)
            ·
              refine ⟨6866512622627940778086263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577675081751960518724175 6866512622627940778086263)
              ·
                refine ⟨10299768933941911167129395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6866512622627940778086263 10299768933941911167129395)
                ·
                  refine ⟨15449653400912866750694093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10299768933941911167129395 15449653400912866750694093)
                  ·
                    refine ⟨5793620025342325031510285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15449653400912866750694093 5793620025342325031510285)
                    ·
                      refine ⟨2172607509503371886816357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793620025342325031510285 2172607509503371886816357)
                      ·
                        rfl

theorem cell23_4231138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4231138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231138 prefixEnd_4231138 := by exact prefixLift 4231138
  have htrace : WordTrace (prefixWord ++ tailWord_4231138) baseStart_4231138 baseEnd_4231138 := by
    simpa [prefixWord, tailWord_4231138, baseEnd_4231138] using wordTrace_append hprefix tailTrace_4231138
  have hstable : (prefixWord ++ tailWord_4231138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231138).length < 2 ^ (prefixWord ++ tailWord_4231138).sum := by decide
  have hdescent : baseEnd_4231138 < baseStart_4231138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231214 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_4231214 : Nat := 118140960795 + 4231214 * 2 ^ 59
def prefixEnd_4231214 : Nat := 4983230072969 + 3 ^ 40 * 4231214 * 2
def baseEnd_4231214 : Nat := 724215511344371196488669

theorem tailTrace_4231214 : CollatzResearch.WordTrace tailWord_4231214 prefixEnd_4231214 724215511344371196488669 := by
  unfold tailWord_4231214
  simp only [CollatzResearch.WordTrace]
  refine ⟨19290631611630223333061587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102883368595361191109661797 19290631611630223333061587)
  ·
    refine ⟨28935947417445334999592381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19290631611630223333061587 28935947417445334999592381)
    ·
      refine ⟨10850980281542000624847143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28935947417445334999592381 10850980281542000624847143)
      ·
        refine ⟨16276470422313000937270715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10850980281542000624847143 16276470422313000937270715)
        ·
          refine ⟨24414705633469501405906073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16276470422313000937270715 24414705633469501405906073)
          ·
            refine ⟨18311029225102126054429555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24414705633469501405906073 18311029225102126054429555)
            ·
              refine ⟨27466543837653189081644333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18311029225102126054429555 27466543837653189081644333)
              ·
                refine ⟨10299953939119945905616625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27466543837653189081644333 10299953939119945905616625)
                ·
                  refine ⟨7724965454339959429212469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10299953939119945905616625 7724965454339959429212469)
                  ·
                    refine ⟨724215511344371196488669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7724965454339959429212469 724215511344371196488669)
                    ·
                      rfl

theorem cell23_4231214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_4231214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231214 prefixEnd_4231214 := by exact prefixLift 4231214
  have htrace : WordTrace (prefixWord ++ tailWord_4231214) baseStart_4231214 baseEnd_4231214 := by
    simpa [prefixWord, tailWord_4231214, baseEnd_4231214] using wordTrace_append hprefix tailTrace_4231214
  have hstable : (prefixWord ++ tailWord_4231214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231214).length < 2 ^ (prefixWord ++ tailWord_4231214).sum := by decide
  have hdescent : baseEnd_4231214 < baseStart_4231214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231227 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 5, 4]
def baseStart_4231227 : Nat := 118140960795 + 4231227 * 2 ^ 59
def prefixEnd_4231227 : Nat := 4983230072969 + 3 ^ 40 * 4231227 * 2
def baseEnd_4231227 : Nat := 724217736427207346201149

theorem tailTrace_4231227 : CollatzResearch.WordTrace tailWord_4231227 prefixEnd_4231227 724217736427207346201149 := by
  unfold tailWord_4231227
  simp only [CollatzResearch.WordTrace]
  refine ⟨154325527041994689884715935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102883684694663126589810623 154325527041994689884715935)
  ·
    refine ⟨231488290562992034827073903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154325527041994689884715935 231488290562992034827073903)
    ·
      refine ⟨347232435844488052240610855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231488290562992034827073903 347232435844488052240610855)
      ·
        refine ⟨520848653766732078360916283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347232435844488052240610855 520848653766732078360916283)
        ·
          refine ⟨781272980650098117541374425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520848653766732078360916283 781272980650098117541374425)
          ·
            refine ⟨585954735487573588156030819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 781272980650098117541374425 585954735487573588156030819)
            ·
              refine ⟨878932103231360382234046229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585954735487573588156030819 878932103231360382234046229)
              ·
                refine ⟨41199942338970017917220917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 878932103231360382234046229 41199942338970017917220917)
                ·
                  refine ⟨3862494594278439179739461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41199942338970017917220917 3862494594278439179739461)
                  ·
                    refine ⟨724217736427207346201149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3862494594278439179739461 724217736427207346201149)
                    ·
                      rfl

theorem cell23_4231227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 4].length) (baseStart_4231227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231227 prefixEnd_4231227 := by exact prefixLift 4231227
  have htrace : WordTrace (prefixWord ++ tailWord_4231227) baseStart_4231227 baseEnd_4231227 := by
    simpa [prefixWord, tailWord_4231227, baseEnd_4231227] using wordTrace_append hprefix tailTrace_4231227
  have hstable : (prefixWord ++ tailWord_4231227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231227).length < 2 ^ (prefixWord ++ tailWord_4231227).sum := by decide
  have hdescent : baseEnd_4231227 < baseStart_4231227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231237 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_4231237 : Nat := 118140960795 + 4231237 * 2 ^ 59
def prefixEnd_4231237 : Nat := 4983230072969 + 3 ^ 40 * 4231237 * 2
def baseEnd_4231237 : Nat := 2172658344088166999478401

theorem tailTrace_4231237 : CollatzResearch.WordTrace tailWord_4231237 prefixEnd_4231237 2172658344088166999478401 := by
  unfold tailWord_4231237
  simp only [CollatzResearch.WordTrace]
  refine ⟨154325891771958461592579965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102883927847972307728386643 154325891771958461592579965)
  ·
    refine ⟨57872209414484423097217487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154325891771958461592579965 57872209414484423097217487)
    ·
      refine ⟨86808314121726634645826231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57872209414484423097217487 86808314121726634645826231)
      ·
        refine ⟨130212471182589951968739347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86808314121726634645826231 130212471182589951968739347)
        ·
          refine ⟨195318706773884927953109021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130212471182589951968739347 195318706773884927953109021)
          ·
            refine ⟨73244515040206847982415883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195318706773884927953109021 73244515040206847982415883)
            ·
              refine ⟨109866772560310271973623825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73244515040206847982415883 109866772560310271973623825)
              ·
                refine ⟨82400079420232703980217869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109866772560310271973623825 82400079420232703980217869)
                ·
                  refine ⟨30900029782587263992581701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82400079420232703980217869 30900029782587263992581701)
                  ·
                    refine ⟨5793755584235111998609069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30900029782587263992581701 5793755584235111998609069)
                    ·
                      refine ⟨2172658344088166999478401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793755584235111998609069 2172658344088166999478401)
                      ·
                        rfl

theorem cell23_4231237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_4231237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231237 prefixEnd_4231237 := by exact prefixLift 4231237
  have htrace : WordTrace (prefixWord ++ tailWord_4231237) baseStart_4231237 baseEnd_4231237 := by
    simpa [prefixWord, tailWord_4231237, baseEnd_4231237] using wordTrace_append hprefix tailTrace_4231237
  have hstable : (prefixWord ++ tailWord_4231237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231237).length < 2 ^ (prefixWord ++ tailWord_4231237).sum := by decide
  have hdescent : baseEnd_4231237 < baseStart_4231237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231257 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 6]
def baseStart_4231257 : Nat := 118140960795 + 4231257 * 2 ^ 59
def prefixEnd_4231257 : Nat := 4983230072969 + 3 ^ 40 * 4231257 * 2
def baseEnd_4231257 : Nat := 241407623744584102358701

theorem tailTrace_4231257 : CollatzResearch.WordTrace tailWord_4231257 prefixEnd_4231257 241407623744584102358701 := by
  unfold tailWord_4231257
  simp only [CollatzResearch.WordTrace]
  refine ⟨154326621231886005008308025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102884414154590670005538683 154326621231886005008308025)
  ·
    refine ⟨115744965923914503756231019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154326621231886005008308025 115744965923914503756231019)
    ·
      refine ⟨173617448885871755634346529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115744965923914503756231019 173617448885871755634346529)
      ·
        refine ⟨130213086664403816725759897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173617448885871755634346529 130213086664403816725759897)
        ·
          refine ⟨97659814998302862544319923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130213086664403816725759897 97659814998302862544319923)
          ·
            refine ⟨146489722497454293816479885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97659814998302862544319923 146489722497454293816479885)
            ·
              refine ⟨54933645936545360181179957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146489722497454293816479885 54933645936545360181179957)
              ·
                refine ⟨5150029306551127516985621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54933645936545360181179957 5150029306551127516985621)
                ·
                  refine ⟨241407623744584102358701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5150029306551127516985621 241407623744584102358701)
                  ·
                    rfl

theorem cell23_4231257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 6].length) (baseStart_4231257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231257 prefixEnd_4231257 := by exact prefixLift 4231257
  have htrace : WordTrace (prefixWord ++ tailWord_4231257) baseStart_4231257 baseEnd_4231257 := by
    simpa [prefixWord, tailWord_4231257, baseEnd_4231257] using wordTrace_append hprefix tailTrace_4231257
  have hstable : (prefixWord ++ tailWord_4231257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231257).length < 2 ^ (prefixWord ++ tailWord_4231257).sum := by decide
  have hdescent : baseEnd_4231257 < baseStart_4231257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231261 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4231261 : Nat := 118140960795 + 4231261 * 2 ^ 59
def prefixEnd_4231261 : Nat := 4983230072969 + 3 ^ 40 * 4231261 * 2
def baseEnd_4231261 : Nat := 724223555874624968526097

theorem tailTrace_4231261 : CollatzResearch.WordTrace tailWord_4231261 prefixEnd_4231261 724223555874624968526097 := by
  unfold tailWord_4231261
  simp only [CollatzResearch.WordTrace]
  refine ⟨154326767123871513691453637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102884511415914342460969091 154326767123871513691453637)
  ·
    refine ⟨28936268835725908817147557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154326767123871513691453637 28936268835725908817147557)
    ·
      refine ⟨5425550406698607903215167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28936268835725908817147557 5425550406698607903215167)
      ·
        refine ⟨8138325610047911854822751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5425550406698607903215167 8138325610047911854822751)
        ·
          refine ⟨12207488415071867782234127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8138325610047911854822751 12207488415071867782234127)
          ·
            refine ⟨18311232622607801673351191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12207488415071867782234127 18311232622607801673351191)
            ·
              refine ⟨27466848933911702510026787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18311232622607801673351191 27466848933911702510026787)
              ·
                refine ⟨41200273400867553765040181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27466848933911702510026787 41200273400867553765040181)
                ·
                  refine ⟨3862525631331333165472517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41200273400867553765040181 3862525631331333165472517)
                  ·
                    refine ⟨724223555874624968526097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3862525631331333165472517 724223555874624968526097)
                    ·
                      rfl

theorem cell23_4231261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4231261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231261 prefixEnd_4231261 := by exact prefixLift 4231261
  have htrace : WordTrace (prefixWord ++ tailWord_4231261) baseStart_4231261 baseEnd_4231261 := by
    simpa [prefixWord, tailWord_4231261, baseEnd_4231261] using wordTrace_append hprefix tailTrace_4231261
  have hstable : (prefixWord ++ tailWord_4231261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231261).length < 2 ^ (prefixWord ++ tailWord_4231261).sum := by decide
  have hdescent : baseEnd_4231261 < baseStart_4231261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231278 : List Nat := [4, 1, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_4231278 : Nat := 118140960795 + 4231278 * 2 ^ 59
def prefixEnd_4231278 : Nat := 4983230072969 + 3 ^ 40 * 4231278 * 2
def baseEnd_4231278 : Nat := 724226465598333779688571

theorem tailTrace_4231278 : CollatzResearch.WordTrace tailWord_4231278 prefixEnd_4231278 724226465598333779688571 := by
  unfold tailWord_4231278
  simp only [CollatzResearch.WordTrace]
  refine ⟨19290923395601240699352811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102884924776539950396548325 19290923395601240699352811)
  ·
    refine ⟨28936385093401861049029217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19290923395601240699352811 28936385093401861049029217)
    ·
      refine ⟨21702288820051395786771913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28936385093401861049029217 21702288820051395786771913)
      ·
        refine ⟨16276716615038546840078935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21702288820051395786771913 16276716615038546840078935)
        ·
          refine ⟨24415074922557820260118403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16276716615038546840078935 24415074922557820260118403)
          ·
            refine ⟨36622612383836730390177605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24415074922557820260118403 36622612383836730390177605)
            ·
              refine ⟨6866739821969386948158301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36622612383836730390177605 6866739821969386948158301)
              ·
                refine ⟨2575027433238520105559363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6866739821969386948158301 2575027433238520105559363)
                ·
                  refine ⟨3862541149857780158339045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575027433238520105559363 3862541149857780158339045)
                  ·
                    refine ⟨724226465598333779688571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3862541149857780158339045 724226465598333779688571)
                    ·
                      rfl

theorem cell23_4231278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_4231278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231278 prefixEnd_4231278 := by exact prefixLift 4231278
  have htrace : WordTrace (prefixWord ++ tailWord_4231278) baseStart_4231278 baseEnd_4231278 := by
    simpa [prefixWord, tailWord_4231278, baseEnd_4231278] using wordTrace_append hprefix tailTrace_4231278
  have hstable : (prefixWord ++ tailWord_4231278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231278).length < 2 ^ (prefixWord ++ tailWord_4231278).sum := by decide
  have hdescent : baseEnd_4231278 < baseStart_4231278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231301 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_4231301 : Nat := 118140960795 + 4231301 * 2 ^ 59
def prefixEnd_4231301 : Nat := 4983230072969 + 3 ^ 40 * 4231301 * 2
def baseEnd_4231301 : Nat := 2172691206850054749078107

theorem tailTrace_4231301 : CollatzResearch.WordTrace tailWord_4231301 prefixEnd_4231301 2172691206850054749078107 := by
  unfold tailWord_4231301
  simp only [CollatzResearch.WordTrace]
  refine ⟨154328226043726600522909757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102885484029151067015273171 154328226043726600522909757)
  ·
    refine ⟨57873084766397475196091159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154328226043726600522909757 57873084766397475196091159)
    ·
      refine ⟨86809627149596212794136739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57873084766397475196091159 86809627149596212794136739)
      ·
        refine ⟨130214440724394319191205109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86809627149596212794136739 130214440724394319191205109)
        ·
          refine ⟨12207603817911967424175479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130214440724394319191205109 12207603817911967424175479)
          ·
            refine ⟨18311405726867951136263219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12207603817911967424175479 18311405726867951136263219)
            ·
              refine ⟨27467108590301926704394829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18311405726867951136263219 27467108590301926704394829)
              ·
                refine ⟨10300165721363222514148061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27467108590301926704394829 10300165721363222514148061)
                ·
                  refine ⟨3862562145511208442805523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10300165721363222514148061 3862562145511208442805523)
                  ·
                    refine ⟨5793843218266812664208285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3862562145511208442805523 5793843218266812664208285)
                    ·
                      refine ⟨2172691206850054749078107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793843218266812664208285 2172691206850054749078107)
                      ·
                        rfl

theorem cell23_4231301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_4231301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231301 prefixEnd_4231301 := by exact prefixLift 4231301
  have htrace : WordTrace (prefixWord ++ tailWord_4231301) baseStart_4231301 baseEnd_4231301 := by
    simpa [prefixWord, tailWord_4231301, baseEnd_4231301] using wordTrace_append hprefix tailTrace_4231301
  have hstable : (prefixWord ++ tailWord_4231301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231301).length < 2 ^ (prefixWord ++ tailWord_4231301).sum := by decide
  have hdescent : baseEnd_4231301 < baseStart_4231301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231364 : List Nat := [2, 3, 3, 1, 2, 1, 1, 10]
def baseStart_4231364 : Nat := 118140960795 + 4231364 * 2 ^ 59
def prefixEnd_4231364 : Nat := 4983230072969 + 3 ^ 40 * 4231364 * 2
def baseEnd_4231364 : Nat := 80471242819677333429271

theorem tailTrace_4231364 : CollatzResearch.WordTrace tailWord_4231364 prefixEnd_4231364 80471242819677333429271 := by
  unfold tailWord_4231364
  simp only [CollatzResearch.WordTrace]
  refine ⟨77165261921249181141226573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102887015894998908188302097 77165261921249181141226573)
  ·
    refine ⟨28936973220468442927959965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77165261921249181141226573 28936973220468442927959965)
    ·
      refine ⟨10851364957675666097984987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28936973220468442927959965 10851364957675666097984987)
      ·
        refine ⟨16277047436513499146977481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10851364957675666097984987 16277047436513499146977481)
        ·
          refine ⟨12207785577385124360233111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16277047436513499146977481 12207785577385124360233111)
          ·
            refine ⟨18311678366077686540349667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12207785577385124360233111 18311678366077686540349667)
            ·
              refine ⟨27467517549116529810524501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18311678366077686540349667 27467517549116529810524501)
              ·
                refine ⟨80471242819677333429271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27467517549116529810524501 80471242819677333429271)
                ·
                  rfl

theorem cell23_4231364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 10].length) (baseStart_4231364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231364 prefixEnd_4231364 := by exact prefixLift 4231364
  have htrace : WordTrace (prefixWord ++ tailWord_4231364) baseStart_4231364 baseEnd_4231364 := by
    simpa [prefixWord, tailWord_4231364, baseEnd_4231364] using wordTrace_append hprefix tailTrace_4231364
  have hstable : (prefixWord ++ tailWord_4231364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231364).length < 2 ^ (prefixWord ++ tailWord_4231364).sum := by decide
  have hdescent : baseEnd_4231364 < baseStart_4231364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231378 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4231378 : Nat := 118140960795 + 4231378 * 2 ^ 59
def prefixEnd_4231378 : Nat := 4983230072969 + 3 ^ 40 * 4231378 * 2
def baseEnd_4231378 : Nat := 2172730744860450947815253

theorem tailTrace_4231378 : CollatzResearch.WordTrace tailWord_4231378 prefixEnd_4231378 2172730744860450947815253 := by
  unfold tailWord_4231378
  simp only [CollatzResearch.WordTrace]
  refine ⟨38582758616111910668365697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102887356309631761782308525 38582758616111910668365697)
  ·
    refine ⟨28937068962083933001274273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38582758616111910668365697 28937068962083933001274273)
    ·
      refine ⟨21702801721562949750955705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28937068962083933001274273 21702801721562949750955705)
      ·
        refine ⟨16277101291172212313216779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21702801721562949750955705 16277101291172212313216779)
        ·
          refine ⟨24415651936758318469825169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16277101291172212313216779 24415651936758318469825169)
          ·
            refine ⟨18311738952568738852368877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24415651936758318469825169 18311738952568738852368877)
            ·
              refine ⟨6866902107213277069638329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18311738952568738852368877 6866902107213277069638329)
              ·
                refine ⟨5150176580409957802228747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6866902107213277069638329 5150176580409957802228747)
                ·
                  refine ⟨7725264870614936703343121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150176580409957802228747 7725264870614936703343121)
                  ·
                    refine ⟨5793948652961202527507341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7725264870614936703343121 5793948652961202527507341)
                    ·
                      refine ⟨2172730744860450947815253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5793948652961202527507341 2172730744860450947815253)
                      ·
                        rfl

theorem cell23_4231378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4231378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231378 prefixEnd_4231378 := by exact prefixLift 4231378
  have htrace : WordTrace (prefixWord ++ tailWord_4231378) baseStart_4231378 baseEnd_4231378 := by
    simpa [prefixWord, tailWord_4231378, baseEnd_4231378] using wordTrace_append hprefix tailTrace_4231378
  have hstable : (prefixWord ++ tailWord_4231378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231378).length < 2 ^ (prefixWord ++ tailWord_4231378).sum := by decide
  have hdescent : baseEnd_4231378 < baseStart_4231378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231395 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4231395 : Nat := 118140960795 + 4231395 * 2 ^ 59
def prefixEnd_4231395 : Nat := 4983230072969 + 3 ^ 40 * 4231395 * 2
def baseEnd_4231395 : Nat := 2172739474031577381302675

theorem tailTrace_4231395 : CollatzResearch.WordTrace tailWord_4231395 prefixEnd_4231395 2172739474031577381302675 := by
  unfold tailWord_4231395
  simp only [CollatzResearch.WordTrace]
  refine ⟨154331654505386054576831639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102887769670257369717887759 154331654505386054576831639)
  ·
    refine ⟨231497481758079081865247459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154331654505386054576831639 231497481758079081865247459)
    ·
      refine ⟨347246222637118622797871189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231497481758079081865247459 347246222637118622797871189)
      ·
        refine ⟨4069291671528733860912553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 347246222637118622797871189 4069291671528733860912553)
        ·
          refine ⟨3051968753646550395684415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4069291671528733860912553 3051968753646550395684415)
          ·
            refine ⟨4577953130469825593526623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3051968753646550395684415 4577953130469825593526623)
            ·
              refine ⟨6866929695704738390289935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4577953130469825593526623 6866929695704738390289935)
              ·
                refine ⟨10300394543557107585434903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6866929695704738390289935 10300394543557107585434903)
                ·
                  refine ⟨15450591815335661378152355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10300394543557107585434903 15450591815335661378152355)
                  ·
                    refine ⟨23175887723003492067228533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15450591815335661378152355 23175887723003492067228533)
                    ·
                      refine ⟨2172739474031577381302675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23175887723003492067228533 2172739474031577381302675)
                      ·
                        rfl

theorem cell23_4231395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4231395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231395 prefixEnd_4231395 := by exact prefixLift 4231395
  have htrace : WordTrace (prefixWord ++ tailWord_4231395) baseStart_4231395 baseEnd_4231395 := by
    simpa [prefixWord, tailWord_4231395, baseEnd_4231395] using wordTrace_append hprefix tailTrace_4231395
  have hstable : (prefixWord ++ tailWord_4231395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231395).length < 2 ^ (prefixWord ++ tailWord_4231395).sum := by decide
  have hdescent : baseEnd_4231395 < baseStart_4231395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231434 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_4231434 : Nat := 118140960795 + 4231434 * 2 ^ 59
def prefixEnd_4231434 : Nat := 4983230072969 + 3 ^ 40 * 4231434 * 2
def baseEnd_4231434 : Nat := 2172759499777102728714995

theorem tailTrace_4231434 : CollatzResearch.WordTrace tailWord_4231434 prefixEnd_4231434 2172759499777102728714995 := by
  unfold tailWord_4231434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38583269238061191059375339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102888717968163176158334237 38583269238061191059375339)
  ·
    refine ⟨57874903857091786589063009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38583269238061191059375339 57874903857091786589063009)
    ·
      refine ⟨43406177892818839941797257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57874903857091786589063009 43406177892818839941797257)
      ·
        refine ⟨32554633419614129956347943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43406177892818839941797257 32554633419614129956347943)
        ·
          refine ⟨48831950129421194934521915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32554633419614129956347943 48831950129421194934521915)
          ·
            refine ⟨73247925194131792401782873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48831950129421194934521915 73247925194131792401782873)
            ·
              refine ⟨54935943895598844301337155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73247925194131792401782873 54935943895598844301337155)
              ·
                refine ⟨82403915843398266452005733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54935943895598844301337155 82403915843398266452005733)
                ·
                  refine ⟨15450734220637174959751075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82403915843398266452005733 15450734220637174959751075)
                  ·
                    refine ⟨23176101330955762439626613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15450734220637174959751075 23176101330955762439626613)
                    ·
                      refine ⟨2172759499777102728714995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23176101330955762439626613 2172759499777102728714995)
                      ·
                        rfl

theorem cell23_4231434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_4231434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231434 prefixEnd_4231434 := by exact prefixLift 4231434
  have htrace : WordTrace (prefixWord ++ tailWord_4231434) baseStart_4231434 baseEnd_4231434 := by
    simpa [prefixWord, tailWord_4231434, baseEnd_4231434] using wordTrace_append hprefix tailTrace_4231434
  have hstable : (prefixWord ++ tailWord_4231434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231434).length < 2 ^ (prefixWord ++ tailWord_4231434).sum := by decide
  have hdescent : baseEnd_4231434 < baseStart_4231434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231448 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 4, 2, 2]
def baseStart_4231448 : Nat := 118140960795 + 4231448 * 2 ^ 59
def prefixEnd_4231448 : Nat := 4983230072969 + 3 ^ 40 * 4231448 * 2
def baseEnd_4231448 : Nat := 2172766688506265673939931

theorem tailTrace_4231448 : CollatzResearch.WordTrace tailWord_4231448 prefixEnd_4231448 2172766688506265673939931 := by
  unfold tailWord_4231448
  simp only [CollatzResearch.WordTrace]
  refine ⟨77166793787097022314255499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102889058382796029752340665 77166793787097022314255499)
  ·
    refine ⟨115750190680645533471383249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77166793787097022314255499 115750190680645533471383249)
    ·
      refine ⟨86812643010484150103537437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115750190680645533471383249 86812643010484150103537437)
      ·
        refine ⟨32554741128931556288826539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86812643010484150103537437 32554741128931556288826539)
        ·
          refine ⟨48832111693397334433239809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32554741128931556288826539 48832111693397334433239809)
          ·
            refine ⟨36624083770048000824929857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48832111693397334433239809 36624083770048000824929857)
            ·
              refine ⟨27468062827536000618697393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36624083770048000824929857 27468062827536000618697393)
              ·
                refine ⟨20601047120652000464023045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27468062827536000618697393 20601047120652000464023045)
                ·
                  refine ⟨3862696335122250087004321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20601047120652000464023045 3862696335122250087004321)
                  ·
                    refine ⟨2897022251341687565253241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3862696335122250087004321 2897022251341687565253241)
                    ·
                      refine ⟨2172766688506265673939931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897022251341687565253241 2172766688506265673939931)
                      ·
                        rfl

theorem cell23_4231448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_4231448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231448 prefixEnd_4231448 := by exact prefixLift 4231448
  have htrace : WordTrace (prefixWord ++ tailWord_4231448) baseStart_4231448 baseEnd_4231448 := by
    simpa [prefixWord, tailWord_4231448, baseEnd_4231448] using wordTrace_append hprefix tailTrace_4231448
  have hstable : (prefixWord ++ tailWord_4231448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231448).length < 2 ^ (prefixWord ++ tailWord_4231448).sum := by decide
  have hdescent : baseEnd_4231448 < baseStart_4231448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231471 : List Nat := [1, 1, 2, 1, 2, 1, 6, 4, 5]
def baseStart_4231471 : Nat := 118140960795 + 4231471 * 2 ^ 59
def prefixEnd_4231471 : Nat := 4983230072969 + 3 ^ 40 * 4231471 * 2
def baseEnd_4231471 : Nat := 241419833173479898216925

theorem tailTrace_4231471 : CollatzResearch.WordTrace tailWord_4231471 prefixEnd_4231471 241419833173479898216925 := by
  unfold tailWord_4231471
  simp only [CollatzResearch.WordTrace]
  refine ⟨154334426453110719556598267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102889617635407146371065511 154334426453110719556598267)
  ·
    refine ⟨231501639679666079334897401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154334426453110719556598267 231501639679666079334897401)
    ·
      refine ⟨173626229759749559501173051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231501639679666079334897401 173626229759749559501173051)
      ·
        refine ⟨260439344639624339251759577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173626229759749559501173051 260439344639624339251759577)
        ·
          refine ⟨195329508479718254438819683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260439344639624339251759577 195329508479718254438819683)
          ·
            refine ⟨292994262719577381658229525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195329508479718254438819683 292994262719577381658229525)
            ·
              refine ⟨13734106064980189765229509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 292994262719577381658229525 13734106064980189765229509)
              ·
                refine ⟨2575144887183785580980533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13734106064980189765229509 2575144887183785580980533)
                ·
                  refine ⟨241419833173479898216925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2575144887183785580980533 241419833173479898216925)
                  ·
                    rfl

theorem cell23_4231471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 5].length) (baseStart_4231471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231471 prefixEnd_4231471 := by exact prefixLift 4231471
  have htrace : WordTrace (prefixWord ++ tailWord_4231471) baseStart_4231471 baseEnd_4231471 := by
    simpa [prefixWord, tailWord_4231471, baseEnd_4231471] using wordTrace_append hprefix tailTrace_4231471
  have hstable : (prefixWord ++ tailWord_4231471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231471).length < 2 ^ (prefixWord ++ tailWord_4231471).sum := by decide
  have hdescent : baseEnd_4231471 < baseStart_4231471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231482 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2]
def baseStart_4231482 : Nat := 118140960795 + 4231482 * 2 ^ 59
def prefixEnd_4231482 : Nat := 4983230072969 + 3 ^ 40 * 4231482 * 2
def baseEnd_4231482 : Nat := 2172784146848518540914775

theorem tailTrace_4231482 : CollatzResearch.WordTrace tailWord_4231482 prefixEnd_4231482 2172784146848518540914775 := by
  unfold tailWord_4231482
  simp only [CollatzResearch.WordTrace]
  refine ⟨38583706914017717108812175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102889885104047245623499133 38583706914017717108812175)
  ·
    refine ⟨57875560371026575663218263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38583706914017717108812175 57875560371026575663218263)
    ·
      refine ⟨86813340556539863494827395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57875560371026575663218263 86813340556539863494827395)
      ·
        refine ⟨130220010834809795242241093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86813340556539863494827395 130220010834809795242241093)
        ·
          refine ⟨24416252031526836607920205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130220010834809795242241093 24416252031526836607920205)
          ·
            refine ⟨9156094511822563727970077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24416252031526836607920205 9156094511822563727970077)
            ·
              refine ⟨3433535441933461397988779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9156094511822563727970077 3433535441933461397988779)
              ·
                refine ⟨5150303162900192096983169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433535441933461397988779 5150303162900192096983169)
                ·
                  refine ⟨3862727372175144072737377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5150303162900192096983169 3862727372175144072737377)
                  ·
                    refine ⟨2897045529131358054553033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3862727372175144072737377 2897045529131358054553033)
                    ·
                      refine ⟨2172784146848518540914775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897045529131358054553033 2172784146848518540914775)
                      ·
                        rfl

theorem cell23_4231482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_4231482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231482 prefixEnd_4231482 := by exact prefixLift 4231482
  have htrace : WordTrace (prefixWord ++ tailWord_4231482) baseStart_4231482 baseEnd_4231482 := by
    simpa [prefixWord, tailWord_4231482, baseEnd_4231482] using wordTrace_append hprefix tailTrace_4231482
  have hstable : (prefixWord ++ tailWord_4231482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231482).length < 2 ^ (prefixWord ++ tailWord_4231482).sum := by decide
  have hdescent : baseEnd_4231482 < baseStart_4231482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231484 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_4231484 : Nat := 118140960795 + 4231484 * 2 ^ 59
def prefixEnd_4231484 : Nat := 4983230072969 + 3 ^ 40 * 4231484 * 2
def baseEnd_4231484 : Nat := 724261724603275844363255

theorem tailTrace_4231484 : CollatzResearch.WordTrace tailWord_4231484 prefixEnd_4231484 724261724603275844363255 := by
  unfold tailWord_4231484
  simp only [CollatzResearch.WordTrace]
  refine ⟨77167450301031811388410753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102889933734709081851214337 77167450301031811388410753)
  ·
    refine ⟨57875587725773858541308065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77167450301031811388410753 57875587725773858541308065)
    ·
      refine ⟨43406690794330393905981049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57875587725773858541308065 43406690794330393905981049)
      ·
        refine ⟨32555018095747795429485787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43406690794330393905981049 32555018095747795429485787)
        ·
          refine ⟨48832527143621693144228681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32555018095747795429485787 48832527143621693144228681)
          ·
            refine ⟨36624395357716269858171511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48832527143621693144228681 36624395357716269858171511)
            ·
              refine ⟨54936593036574404787257267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36624395357716269858171511 54936593036574404787257267)
              ·
                refine ⟨82404889554861607180885901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54936593036574404787257267 82404889554861607180885901)
                ·
                  refine ⟨30901833583073102692832213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82404889554861607180885901 30901833583073102692832213)
                  ·
                    refine ⟨724261724603275844363255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30901833583073102692832213 724261724603275844363255)
                    ·
                      rfl

theorem cell23_4231484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_4231484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231484 prefixEnd_4231484 := by exact prefixLift 4231484
  have htrace : WordTrace (prefixWord ++ tailWord_4231484) baseStart_4231484 baseEnd_4231484 := by
    simpa [prefixWord, tailWord_4231484, baseEnd_4231484] using wordTrace_append hprefix tailTrace_4231484
  have hstable : (prefixWord ++ tailWord_4231484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231484).length < 2 ^ (prefixWord ++ tailWord_4231484).sum := by decide
  have hdescent : baseEnd_4231484 < baseStart_4231484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231491 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 2, 5, 2]
def baseStart_4231491 : Nat := 118140960795 + 4231491 * 2 ^ 59
def prefixEnd_4231491 : Nat := 4983230072969 + 3 ^ 40 * 4231491 * 2
def baseEnd_4231491 : Nat := 2172788768174409005702233

theorem tailTrace_4231491 : CollatzResearch.WordTrace tailWord_4231491 prefixEnd_4231491 2172788768174409005702233 := by
  unfold tailWord_4231491
  simp only [CollatzResearch.WordTrace]
  refine ⟨154335155913038262972326327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102890103942025508648217551 154335155913038262972326327)
  ·
    refine ⟨231502733869557394458489491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154335155913038262972326327 231502733869557394458489491)
    ·
      refine ⟨347254100804336091687734237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231502733869557394458489491 347254100804336091687734237)
      ·
        refine ⟨130220287801626034382900339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347254100804336091687734237 130220287801626034382900339)
        ·
          refine ⟨195330431702439051574350509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130220287801626034382900339 195330431702439051574350509)
          ·
            refine ⟨73248911888414644340381441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195330431702439051574350509 73248911888414644340381441)
            ·
              refine ⟨54936683916310983255286081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73248911888414644340381441 54936683916310983255286081)
              ·
                refine ⟨41202512937233237441464561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54936683916310983255286081 41202512937233237441464561)
                ·
                  refine ⟨30901884702924928081098421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41202512937233237441464561 30901884702924928081098421)
                  ·
                    refine ⟨2897051690899212007602977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30901884702924928081098421 2897051690899212007602977)
                    ·
                      refine ⟨2172788768174409005702233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897051690899212007602977 2172788768174409005702233)
                      ·
                        rfl

theorem cell23_4231491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_4231491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231491 prefixEnd_4231491 := by exact prefixLift 4231491
  have htrace : WordTrace (prefixWord ++ tailWord_4231491) baseStart_4231491 baseEnd_4231491 := by
    simpa [prefixWord, tailWord_4231491, baseEnd_4231491] using wordTrace_append hprefix tailTrace_4231491
  have hstable : (prefixWord ++ tailWord_4231491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231491).length < 2 ^ (prefixWord ++ tailWord_4231491).sum := by decide
  have hdescent : baseEnd_4231491 < baseStart_4231491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231578 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 6]
def baseStart_4231578 : Nat := 118140960795 + 4231578 * 2 ^ 59
def prefixEnd_4231578 : Nat := 4983230072969 + 3 ^ 40 * 4231578 * 2
def baseEnd_4231578 : Nat := 241425937887927796146037

theorem tailTrace_4231578 : CollatzResearch.WordTrace tailWord_4231578 prefixEnd_4231578 241425937887927796146037 := by
  unfold tailWord_4231578
  simp only [CollatzResearch.WordTrace]
  refine ⟨38584582265930769207685847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102892219375815384553828925 38584582265930769207685847)
  ·
    refine ⟨57876873398896153811528771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38584582265930769207685847 57876873398896153811528771)
    ·
      refine ⟨86815310098344230717293157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57876873398896153811528771 86815310098344230717293157)
      ·
        refine ⟨16277870643439543259492467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86815310098344230717293157 16277870643439543259492467)
        ·
          refine ⟨24416805965159314889238701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16277870643439543259492467 24416805965159314889238701)
          ·
            refine ⟨9156302236934743083464513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24416805965159314889238701 9156302236934743083464513)
            ·
              refine ⟨6867226677701057312598385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9156302236934743083464513 6867226677701057312598385)
              ·
                refine ⟨5150420008275792984448789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6867226677701057312598385 5150420008275792984448789)
                ·
                  refine ⟨241425937887927796146037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5150420008275792984448789 241425937887927796146037)
                  ·
                    rfl

theorem cell23_4231578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_4231578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231578 prefixEnd_4231578 := by exact prefixLift 4231578
  have htrace : WordTrace (prefixWord ++ tailWord_4231578) baseStart_4231578 baseEnd_4231578 := by
    simpa [prefixWord, tailWord_4231578, baseEnd_4231578] using wordTrace_append hprefix tailTrace_4231578
  have hstable : (prefixWord ++ tailWord_4231578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231578).length < 2 ^ (prefixWord ++ tailWord_4231578).sum := by decide
  have hdescent : baseEnd_4231578 < baseStart_4231578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231631 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_4231631 : Nat := 118140960795 + 4231631 * 2 ^ 59
def prefixEnd_4231631 : Nat := 4983230072969 + 3 ^ 40 * 4231631 * 2
def baseEnd_4231631 : Nat := 2172860655466038457951589

theorem tailTrace_4231631 : CollatzResearch.WordTrace tailWord_4231631 prefixEnd_4231631 2172860655466038457951589 := by
  unfold tailWord_4231631
  simp only [CollatzResearch.WordTrace]
  refine ⟨154340262132531066882422747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102893508088354044588281831 154340262132531066882422747)
  ·
    refine ⟨231510393198796600323634121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154340262132531066882422747 231510393198796600323634121)
    ·
      refine ⟨173632794899097450242725591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231510393198796600323634121 173632794899097450242725591)
      ·
        refine ⟨260449192348646175364088387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173632794899097450242725591 260449192348646175364088387)
        ·
          refine ⟨390673788522969263046132581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260449192348646175364088387 390673788522969263046132581)
          ·
            refine ⟨73251335348056736821149859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 390673788522969263046132581 73251335348056736821149859)
            ·
              refine ⟨109877003022085105231724789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73251335348056736821149859 109877003022085105231724789)
              ·
                refine ⟨10300969033320478615474199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109877003022085105231724789 10300969033320478615474199)
                ·
                  refine ⟨15451453549980717923211299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10300969033320478615474199 15451453549980717923211299)
                  ·
                    refine ⟨23177180324971076884816949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15451453549980717923211299 23177180324971076884816949)
                    ·
                      refine ⟨2172860655466038457951589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23177180324971076884816949 2172860655466038457951589)
                      ·
                        rfl

theorem cell23_4231631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_4231631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231631 prefixEnd_4231631 := by exact prefixLift 4231631
  have htrace : WordTrace (prefixWord ++ tailWord_4231631) baseStart_4231631 baseEnd_4231631 := by
    simpa [prefixWord, tailWord_4231631, baseEnd_4231631] using wordTrace_append hprefix tailTrace_4231631
  have hstable : (prefixWord ++ tailWord_4231631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231631).length < 2 ^ (prefixWord ++ tailWord_4231631).sum := by decide
  have hdescent : baseEnd_4231631 < baseStart_4231631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231641 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_4231641 : Nat := 118140960795 + 4231641 * 2 ^ 59
def prefixEnd_4231641 : Nat := 4983230072969 + 3 ^ 40 * 4231641 * 2
def baseEnd_4231641 : Nat := 2172865790272583418826543

theorem tailTrace_4231641 : CollatzResearch.WordTrace tailWord_4231641 prefixEnd_4231641 2172865790272583418826543 := by
  unfold tailWord_4231641
  simp only [CollatzResearch.WordTrace]
  refine ⟨154340626862494838590286777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102893751241663225726857851 154340626862494838590286777)
  ·
    refine ⟨115755470146871128942715083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154340626862494838590286777 115755470146871128942715083)
    ·
      refine ⟨173633205220306693414072625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115755470146871128942715083 173633205220306693414072625)
      ·
        refine ⟨130224903915230020060554469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173633205220306693414072625 130224903915230020060554469)
        ·
          refine ⟨24417169484105628761353963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130224903915230020060554469 24417169484105628761353963)
          ·
            refine ⟨36625754226158443142030945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24417169484105628761353963 36625754226158443142030945)
            ·
              refine ⟨27469315669618832356523209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36625754226158443142030945 27469315669618832356523209)
              ·
                refine ⟨20601986752214124267392407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27469315669618832356523209 20601986752214124267392407)
                ·
                  refine ⟨30902980128321186401088611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20601986752214124267392407 30902980128321186401088611)
                  ·
                    refine ⟨46354470192481779601632917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30902980128321186401088611 46354470192481779601632917)
                    ·
                      refine ⟨2172865790272583418826543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46354470192481779601632917 2172865790272583418826543)
                      ·
                        rfl

theorem cell23_4231641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_4231641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231641 prefixEnd_4231641 := by exact prefixLift 4231641
  have htrace : WordTrace (prefixWord ++ tailWord_4231641) baseStart_4231641 baseEnd_4231641 := by
    simpa [prefixWord, tailWord_4231641, baseEnd_4231641] using wordTrace_append hprefix tailTrace_4231641
  have hstable : (prefixWord ++ tailWord_4231641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231641).length < 2 ^ (prefixWord ++ tailWord_4231641).sum := by decide
  have hdescent : baseEnd_4231641 < baseStart_4231641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231658 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_4231658 : Nat := 118140960795 + 4231658 * 2 ^ 59
def prefixEnd_4231658 : Nat := 4983230072969 + 3 ^ 40 * 4231658 * 2
def baseEnd_4231658 : Nat := 2172874519443709852313965

theorem tailTrace_4231658 : CollatzResearch.WordTrace tailWord_4231658 prefixEnd_4231658 2172874519443709852313965 := by
  unfold tailWord_4231658
  simp only [CollatzResearch.WordTrace]
  refine ⟨38585311725858312623413907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102894164602288833662437085 38585311725858312623413907)
  ·
    refine ⟨57877967588787468935120861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38585311725858312623413907 57877967588787468935120861)
    ·
      refine ⟨21704237845795300850670323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57877967588787468935120861 21704237845795300850670323)
      ·
        refine ⟨32556356768692951276005485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21704237845795300850670323 32556356768692951276005485)
        ·
          refine ⟨12208633788259856728502057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32556356768692951276005485 12208633788259856728502057)
          ·
            refine ⟨9156475341194892546376543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12208633788259856728502057 9156475341194892546376543)
            ·
              refine ⟨13734713011792338819564815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9156475341194892546376543 13734713011792338819564815)
              ·
                refine ⟨20602069517688508229347223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13734713011792338819564815 20602069517688508229347223)
                ·
                  refine ⟨30903104276532762344020835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20602069517688508229347223 30903104276532762344020835)
                  ·
                    refine ⟨46354656414799143516031253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30903104276532762344020835 46354656414799143516031253)
                    ·
                      refine ⟨2172874519443709852313965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46354656414799143516031253 2172874519443709852313965)
                      ·
                        rfl

theorem cell23_4231658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_4231658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231658 prefixEnd_4231658 := by exact prefixLift 4231658
  have htrace : WordTrace (prefixWord ++ tailWord_4231658) baseStart_4231658 baseEnd_4231658 := by
    simpa [prefixWord, tailWord_4231658, baseEnd_4231658] using wordTrace_append hprefix tailTrace_4231658
  have hstable : (prefixWord ++ tailWord_4231658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231658).length < 2 ^ (prefixWord ++ tailWord_4231658).sum := by decide
  have hdescent : baseEnd_4231658 < baseStart_4231658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231662 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_4231662 : Nat := 118140960795 + 4231662 * 2 ^ 59
def prefixEnd_4231662 : Nat := 4983230072969 + 3 ^ 40 * 4231662 * 2
def baseEnd_4231662 : Nat := 2172876573366327836663947

theorem tailTrace_4231662 : CollatzResearch.WordTrace tailWord_4231662 prefixEnd_4231662 2172876573366327836663947 := by
  unfold tailWord_4231662
  simp only [CollatzResearch.WordTrace]
  refine ⟨19292674099427344897100155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102894261863612506117867493 19292674099427344897100155)
  ·
    refine ⟨28939011149141017345650233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19292674099427344897100155 28939011149141017345650233)
    ·
      refine ⟨21704258361855763009237675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28939011149141017345650233 21704258361855763009237675)
      ·
        refine ⟨32556387542783644513856513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21704258361855763009237675 32556387542783644513856513)
        ·
          refine ⟨24417290657087733385392385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32556387542783644513856513 24417290657087733385392385)
          ·
            refine ⟨18312967992815800039044289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24417290657087733385392385 18312967992815800039044289)
            ·
              refine ⟨13734725994611850029283217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18312967992815800039044289 13734725994611850029283217)
              ·
                refine ⟨10301044495958887521962413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13734725994611850029283217 10301044495958887521962413)
                ·
                  refine ⟨3862891685984582820735905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10301044495958887521962413 3862891685984582820735905)
                  ·
                    refine ⟨2897168764488437115551929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3862891685984582820735905 2897168764488437115551929)
                    ·
                      refine ⟨2172876573366327836663947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897168764488437115551929 2172876573366327836663947)
                      ·
                        rfl

theorem cell23_4231662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_4231662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231662 prefixEnd_4231662 := by exact prefixLift 4231662
  have htrace : WordTrace (prefixWord ++ tailWord_4231662) baseStart_4231662 baseEnd_4231662 := by
    simpa [prefixWord, tailWord_4231662, baseEnd_4231662] using wordTrace_append hprefix tailTrace_4231662
  have hstable : (prefixWord ++ tailWord_4231662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231662).length < 2 ^ (prefixWord ++ tailWord_4231662).sum := by decide
  have hdescent : baseEnd_4231662 < baseStart_4231662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231665 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_4231665 : Nat := 118140960795 + 4231665 * 2 ^ 59
def prefixEnd_4231665 : Nat := 4983230072969 + 3 ^ 40 * 4231665 * 2
def baseEnd_4231665 : Nat := 2172878113808291324926433

theorem tailTrace_4231665 : CollatzResearch.WordTrace tailWord_4231665 prefixEnd_4231665 2172878113808291324926433 := by
  unfold tailWord_4231665
  simp only [CollatzResearch.WordTrace]
  refine ⟨154341502214407890689160449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102894334809605260459440299 154341502214407890689160449)
  ·
    refine ⟨115756126660805918016870337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154341502214407890689160449 115756126660805918016870337)
    ·
      refine ⟨86817094995604438512652753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115756126660805918016870337 86817094995604438512652753)
      ·
        refine ⟨65112821246703328884489565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86817094995604438512652753 65112821246703328884489565)
        ·
          refine ⟨24417307967513748331683587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65112821246703328884489565 24417307967513748331683587)
          ·
            refine ⟨36625961951270622497525381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24417307967513748331683587 36625961951270622497525381)
            ·
              refine ⟨6867367865863241718286009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36625961951270622497525381 6867367865863241718286009)
              ·
                refine ⟨5150525899397431288714507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6867367865863241718286009 5150525899397431288714507)
                ·
                  refine ⟨7725788849096146933071761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150525899397431288714507 7725788849096146933071761)
                  ·
                    refine ⟨5794341636822110199803821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7725788849096146933071761 5794341636822110199803821)
                    ·
                      refine ⟨2172878113808291324926433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5794341636822110199803821 2172878113808291324926433)
                      ·
                        rfl

theorem cell23_4231665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_4231665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231665 prefixEnd_4231665 := by exact prefixLift 4231665
  have htrace : WordTrace (prefixWord ++ tailWord_4231665) baseStart_4231665 baseEnd_4231665 := by
    simpa [prefixWord, tailWord_4231665, baseEnd_4231665] using wordTrace_append hprefix tailTrace_4231665
  have hstable : (prefixWord ++ tailWord_4231665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231665).length < 2 ^ (prefixWord ++ tailWord_4231665).sum := by decide
  have hdescent : baseEnd_4231665 < baseStart_4231665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231682 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_4231682 : Nat := 118140960795 + 4231682 * 2 ^ 59
def prefixEnd_4231682 : Nat := 4983230072969 + 3 ^ 40 * 4231682 * 2
def baseEnd_4231682 : Nat := 2172886842979417758413855

theorem tailTrace_4231682 : CollatzResearch.WordTrace tailWord_4231682 prefixEnd_4231682 2172886842979417758413855 := by
  unfold tailWord_4231682
  simp only [CollatzResearch.WordTrace]
  refine ⟨38585530563836575648132325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102894748170230868395019533 38585530563836575648132325)
  ·
    refine ⟨7234786980719357934024811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38585530563836575648132325 7234786980719357934024811)
    ·
      refine ⟨10852180471079036901037217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7234786980719357934024811 10852180471079036901037217)
      ·
        refine ⟨8139135353309277675777913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10852180471079036901037217 8139135353309277675777913)
        ·
          refine ⟨6104351514981958256833435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8139135353309277675777913 6104351514981958256833435)
          ·
            refine ⟨9156527272472937385250153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6104351514981958256833435 9156527272472937385250153)
            ·
              refine ⟨6867395454354703038937615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9156527272472937385250153 6867395454354703038937615)
              ·
                refine ⟨10301093181532054558406423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6867395454354703038937615 10301093181532054558406423)
                ·
                  refine ⟨15451639772298081837609635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10301093181532054558406423 15451639772298081837609635)
                  ·
                    refine ⟨23177459658447122756414453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15451639772298081837609635 23177459658447122756414453)
                    ·
                      refine ⟨2172886842979417758413855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23177459658447122756414453 2172886842979417758413855)
                      ·
                        rfl

theorem cell23_4231682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_4231682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231682 prefixEnd_4231682 := by exact prefixLift 4231682
  have htrace : WordTrace (prefixWord ++ tailWord_4231682) baseStart_4231682 baseEnd_4231682 := by
    simpa [prefixWord, tailWord_4231682, baseEnd_4231682] using wordTrace_append hprefix tailTrace_4231682
  have hstable : (prefixWord ++ tailWord_4231682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231682).length < 2 ^ (prefixWord ++ tailWord_4231682).sum := by decide
  have hdescent : baseEnd_4231682 < baseStart_4231682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231711 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 1, 8]
def baseStart_4231711 : Nat := 118140960795 + 4231711 * 2 ^ 59
def prefixEnd_4231711 : Nat := 4983230072969 + 3 ^ 40 * 4231711 * 2
def baseEnd_4231711 : Nat := 724300577972799381650407

theorem tailTrace_4231711 : CollatzResearch.WordTrace tailWord_4231711 prefixEnd_4231711 724300577972799381650407 := by
  unfold tailWord_4231711
  simp only [CollatzResearch.WordTrace]
  refine ⟨154343179972241240545334987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102895453314827493696889991 154343179972241240545334987)
  ·
    refine ⟨231514769958361860818002481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154343179972241240545334987 231514769958361860818002481)
    ·
      refine ⟨173636077468771395613501861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231514769958361860818002481 173636077468771395613501861)
      ·
        refine ⟨32556764525394636677531599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173636077468771395613501861 32556764525394636677531599)
        ·
          refine ⟨48835146788091955016297399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32556764525394636677531599 48835146788091955016297399)
          ·
            refine ⟨73252720182137932524446099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48835146788091955016297399 73252720182137932524446099)
            ·
              refine ⟨109879080273206898786669149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73252720182137932524446099 109879080273206898786669149)
              ·
                refine ⟨41204655102452587045000931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109879080273206898786669149 41204655102452587045000931)
                ·
                  refine ⟨61806982653678880567501397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41204655102452587045000931 61806982653678880567501397)
                  ·
                    refine ⟨724300577972799381650407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61806982653678880567501397 724300577972799381650407)
                    ·
                      rfl

theorem cell23_4231711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_4231711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231711 prefixEnd_4231711 := by exact prefixLift 4231711
  have htrace : WordTrace (prefixWord ++ tailWord_4231711) baseStart_4231711 baseEnd_4231711 := by
    simpa [prefixWord, tailWord_4231711, baseEnd_4231711] using wordTrace_append hprefix tailTrace_4231711
  have hstable : (prefixWord ++ tailWord_4231711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231711).length < 2 ^ (prefixWord ++ tailWord_4231711).sum := by decide
  have hdescent : baseEnd_4231711 < baseStart_4231711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231716 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4231716 : Nat := 118140960795 + 4231716 * 2 ^ 59
def prefixEnd_4231716 : Nat := 4983230072969 + 3 ^ 40 * 4231716 * 2
def baseEnd_4231716 : Nat := 2172904301321670625388699

theorem tailTrace_4231716 : CollatzResearch.WordTrace tailWord_4231716 prefixEnd_4231716 2172904301321670625388699 := by
  unfold tailWord_4231716
  simp only [CollatzResearch.WordTrace]
  refine ⟨77171681168611563199633501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102895574891482084266178001 77171681168611563199633501)
  ·
    refine ⟨28939380438229336199862563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77171681168611563199633501 28939380438229336199862563)
    ·
      refine ⟨43409070657344004299793845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28939380438229336199862563 43409070657344004299793845)
      ·
        refine ⟨4069600374126000403105673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43409070657344004299793845 4069600374126000403105673)
        ·
          refine ⟨3052200280594500302329255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4069600374126000403105673 3052200280594500302329255)
          ·
            refine ⟨4578300420891750453493883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052200280594500302329255 4578300420891750453493883)
            ·
              refine ⟨6867450631337625680240825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578300420891750453493883 6867450631337625680240825)
              ·
                refine ⟨5150587973503219260180619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6867450631337625680240825 5150587973503219260180619)
                ·
                  refine ⟨7725881960254828890270929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150587973503219260180619 7725881960254828890270929)
                  ·
                    refine ⟨5794411470191121667703197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7725881960254828890270929 5794411470191121667703197)
                    ·
                      refine ⟨2172904301321670625388699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5794411470191121667703197 2172904301321670625388699)
                      ·
                        rfl

theorem cell23_4231716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4231716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231716 prefixEnd_4231716 := by exact prefixLift 4231716
  have htrace : WordTrace (prefixWord ++ tailWord_4231716) baseStart_4231716 baseEnd_4231716 := by
    simpa [prefixWord, tailWord_4231716, baseEnd_4231716] using wordTrace_append hprefix tailTrace_4231716
  have hstable : (prefixWord ++ tailWord_4231716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231716).length < 2 ^ (prefixWord ++ tailWord_4231716).sum := by decide
  have hdescent : baseEnd_4231716 < baseStart_4231716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231722 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_4231722 : Nat := 118140960795 + 4231722 * 2 ^ 59
def prefixEnd_4231722 : Nat := 4983230072969 + 3 ^ 40 * 4231722 * 2
def baseEnd_4231722 : Nat := 2172907382205597601913671

theorem tailTrace_4231722 : CollatzResearch.WordTrace tailWord_4231722 prefixEnd_4231722 2172907382205597601913671 := by
  unfold tailWord_4231722
  simp only [CollatzResearch.WordTrace]
  refine ⟨38585895293800347355996355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102895720783467592949323613 38585895293800347355996355)
  ·
    refine ⟨57878842940700521033994533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38585895293800347355996355 57878842940700521033994533)
    ·
      refine ⟨10852283051381347693873975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57878842940700521033994533 10852283051381347693873975)
      ·
        refine ⟨16278424577072021540810963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10852283051381347693873975 16278424577072021540810963)
        ·
          refine ⟨24417636865608032311216445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16278424577072021540810963 24417636865608032311216445)
          ·
            refine ⟨9156613824603012116706167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24417636865608032311216445 9156613824603012116706167)
            ·
              refine ⟨13734920736904518175059251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9156613824603012116706167 13734920736904518175059251)
              ·
                refine ⟨20602381105356777262588877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13734920736904518175059251 20602381105356777262588877)
                ·
                  refine ⟨7725892914508791473470829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20602381105356777262588877 7725892914508791473470829)
                  ·
                    refine ⟨2897209842940796802551561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7725892914508791473470829 2897209842940796802551561)
                    ·
                      refine ⟨2172907382205597601913671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897209842940796802551561 2172907382205597601913671)
                      ·
                        rfl

theorem cell23_4231722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_4231722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231722 prefixEnd_4231722 := by exact prefixLift 4231722
  have htrace : WordTrace (prefixWord ++ tailWord_4231722) baseStart_4231722 baseEnd_4231722 := by
    simpa [prefixWord, tailWord_4231722, baseEnd_4231722] using wordTrace_append hprefix tailTrace_4231722
  have hstable : (prefixWord ++ tailWord_4231722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231722).length < 2 ^ (prefixWord ++ tailWord_4231722).sum := by decide
  have hdescent : baseEnd_4231722 < baseStart_4231722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231735 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 1, 4, 2]
def baseStart_4231735 : Nat := 118140960795 + 4231735 * 2 ^ 59
def prefixEnd_4231735 : Nat := 4983230072969 + 3 ^ 40 * 4231735 * 2
def baseEnd_4231735 : Nat := 2172914057454106051051111

theorem tailTrace_4231735 : CollatzResearch.WordTrace tailWord_4231735 prefixEnd_4231735 2172914057454106051051111 := by
  unfold tailWord_4231735
  simp only [CollatzResearch.WordTrace]
  refine ⟨154344055324154292644208659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102896036882769528429472439 154344055324154292644208659)
  ·
    refine ⟨231516082986231438966312989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154344055324154292644208659 231516082986231438966312989)
    ·
      refine ⟨86818531119836789612367371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231516082986231438966312989 86818531119836789612367371)
      ·
        refine ⟨130227796679755184418551057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86818531119836789612367371 130227796679755184418551057)
        ·
          refine ⟨97670847509816388313913293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130227796679755184418551057 97670847509816388313913293)
          ·
            refine ⟨36626567816181145617717485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97670847509816388313913293 36626567816181145617717485)
            ·
              refine ⟨13734962931067929606644057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36626567816181145617717485 13734962931067929606644057)
              ·
                refine ⟨10301222198300947204983043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13734962931067929606644057 10301222198300947204983043)
                ·
                  refine ⟨15451833297451420807474565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10301222198300947204983043 15451833297451420807474565)
                  ·
                    refine ⟨2897218743272141401401481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15451833297451420807474565 2897218743272141401401481)
                    ·
                      refine ⟨2172914057454106051051111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897218743272141401401481 2172914057454106051051111)
                      ·
                        rfl

theorem cell23_4231735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_4231735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231735 prefixEnd_4231735 := by exact prefixLift 4231735
  have htrace : WordTrace (prefixWord ++ tailWord_4231735) baseStart_4231735 baseEnd_4231735 := by
    simpa [prefixWord, tailWord_4231735, baseEnd_4231735] using wordTrace_append hprefix tailTrace_4231735
  have hstable : (prefixWord ++ tailWord_4231735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231735).length < 2 ^ (prefixWord ++ tailWord_4231735).sum := by decide
  have hdescent : baseEnd_4231735 < baseStart_4231735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231738 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_4231738 : Nat := 118140960795 + 4231738 * 2 ^ 59
def prefixEnd_4231738 : Nat := 4983230072969 + 3 ^ 40 * 4231738 * 2
def baseEnd_4231738 : Nat := 2172915597896069539313597

theorem tailTrace_4231738 : CollatzResearch.WordTrace tailWord_4231738 prefixEnd_4231738 2172915597896069539313597 := by
  unfold tailWord_4231738
  simp only [CollatzResearch.WordTrace]
  refine ⟨38586041185785856039141967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102896109828762282771045245 38586041185785856039141967)
  ·
    refine ⟨57879061778678784058712951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38586041185785856039141967 57879061778678784058712951)
    ·
      refine ⟨86818592668018176088069427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57879061778678784058712951 86818592668018176088069427)
      ·
        refine ⟨130227889002027264132104141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86818592668018176088069427 130227889002027264132104141)
        ·
          refine ⟨48835458375760224049539053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130227889002027264132104141 48835458375760224049539053)
          ·
            refine ⟨18313296890910084018577145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48835458375760224049539053 18313296890910084018577145)
            ·
              refine ⟨13734972668182563013932859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18313296890910084018577145 13734972668182563013932859)
              ·
                refine ⟨20602459002273844520899289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13734972668182563013932859 20602459002273844520899289)
                ·
                  refine ⟨15451844251705383390674467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20602459002273844520899289 15451844251705383390674467)
                  ·
                    refine ⟨23177766377558075086011701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15451844251705383390674467 23177766377558075086011701)
                    ·
                      refine ⟨2172915597896069539313597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23177766377558075086011701 2172915597896069539313597)
                      ·
                        rfl

theorem cell23_4231738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_4231738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231738 prefixEnd_4231738 := by exact prefixLift 4231738
  have htrace : WordTrace (prefixWord ++ tailWord_4231738) baseStart_4231738 baseEnd_4231738 := by
    simpa [prefixWord, tailWord_4231738, baseEnd_4231738] using wordTrace_append hprefix tailTrace_4231738
  have hstable : (prefixWord ++ tailWord_4231738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231738).length < 2 ^ (prefixWord ++ tailWord_4231738).sum := by decide
  have hdescent : baseEnd_4231738 < baseStart_4231738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231768 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_4231768 : Nat := 118140960795 + 4231768 * 2 ^ 59
def prefixEnd_4231768 : Nat := 4983230072969 + 3 ^ 40 * 4231768 * 2
def baseEnd_4231768 : Nat := 2172931002315704421938459

theorem tailTrace_4231768 : CollatzResearch.WordTrace tailWord_4231768 prefixEnd_4231768 2172931002315704421938459 := by
  unfold tailWord_4231768
  simp only [CollatzResearch.WordTrace]
  refine ⟨77172629466517369640079979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102896839288689826186773305 77172629466517369640079979)
  ·
    refine ⟨115758944199776054460119969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77172629466517369640079979 115758944199776054460119969)
    ·
      refine ⟨86819208149832040845089977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115758944199776054460119969 86819208149832040845089977)
      ·
        refine ⟨65114406112374030633817483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86819208149832040845089977 65114406112374030633817483)
        ·
          refine ⟨97671609168561045950726225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65114406112374030633817483 97671609168561045950726225)
          ·
            refine ⟨73253706876420784463044669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97671609168561045950726225 73253706876420784463044669)
            ·
              refine ⟨27470140078657794173641751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73253706876420784463044669 27470140078657794173641751)
              ·
                refine ⟨41205210117986691260462627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27470140078657794173641751 41205210117986691260462627)
                ·
                  refine ⟨61807815176980036890693941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41205210117986691260462627 61807815176980036890693941)
                  ·
                    refine ⟨5794482672841878458502557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61807815176980036890693941 5794482672841878458502557)
                    ·
                      refine ⟨2172931002315704421938459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5794482672841878458502557 2172931002315704421938459)
                      ·
                        rfl

theorem cell23_4231768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_4231768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231768 prefixEnd_4231768 := by exact prefixLift 4231768
  have htrace : WordTrace (prefixWord ++ tailWord_4231768) baseStart_4231768 baseEnd_4231768 := by
    simpa [prefixWord, tailWord_4231768, baseEnd_4231768] using wordTrace_append hprefix tailTrace_4231768
  have hstable : (prefixWord ++ tailWord_4231768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231768).length < 2 ^ (prefixWord ++ tailWord_4231768).sum := by decide
  have hdescent : baseEnd_4231768 < baseStart_4231768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231792 : List Nat := [2, 1, 1, 1, 7, 1, 2, 3, 5]
def baseStart_4231792 : Nat := 118140960795 + 4231792 * 2 ^ 59
def prefixEnd_4231792 : Nat := 4983230072969 + 3 ^ 40 * 4231792 * 2
def baseEnd_4231792 : Nat := 241438147316823592004261

theorem tailTrace_4231792 : CollatzResearch.WordTrace tailWord_4231792 prefixEnd_4231792 241438147316823592004261 := by
  unfold tailWord_4231792
  simp only [CollatzResearch.WordTrace]
  refine ⟨77173067142473895689516815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102897422856631860919355753 77173067142473895689516815)
  ·
    refine ⟨115759600713710843534275223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77173067142473895689516815 115759600713710843534275223)
    ·
      refine ⟨173639401070566265301412835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115759600713710843534275223 173639401070566265301412835)
      ·
        refine ⟨260459101605849397952119253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173639401070566265301412835 260459101605849397952119253)
        ·
          refine ⟨6104510193887095264502795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 260459101605849397952119253 6104510193887095264502795)
          ·
            refine ⟨9156765290830642896754193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6104510193887095264502795 9156765290830642896754193)
            ·
              refine ⟨6867573968122982172565645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9156765290830642896754193 6867573968122982172565645)
              ·
                refine ⟨2575340238046118314712117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6867573968122982172565645 2575340238046118314712117)
                ·
                  refine ⟨241438147316823592004261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2575340238046118314712117 241438147316823592004261)
                  ·
                    rfl

theorem cell23_4231792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 5].length) (baseStart_4231792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231792 prefixEnd_4231792 := by exact prefixLift 4231792
  have htrace : WordTrace (prefixWord ++ tailWord_4231792) baseStart_4231792 baseEnd_4231792 := by
    simpa [prefixWord, tailWord_4231792, baseEnd_4231792] using wordTrace_append hprefix tailTrace_4231792
  have hstable : (prefixWord ++ tailWord_4231792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231792).length < 2 ^ (prefixWord ++ tailWord_4231792).sum := by decide
  have hdescent : baseEnd_4231792 < baseStart_4231792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231845 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_4231845 : Nat := 118140960795 + 4231845 * 2 ^ 59
def prefixEnd_4231845 : Nat := 4983230072969 + 3 ^ 40 * 4231845 * 2
def baseEnd_4231845 : Nat := 2172970540326100620675605

theorem tailTrace_4231845 : CollatzResearch.WordTrace tailWord_4231845 prefixEnd_4231845 2172970540326100620675605 := by
  unfold tailWord_4231845
  simp only [CollatzResearch.WordTrace]
  refine ⟨154348067353755781430712989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102898711569170520953808659 154348067353755781430712989)
  ·
    refine ⟨57880525257658418036517371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154348067353755781430712989 57880525257658418036517371)
    ·
      refine ⟨86820787886487627054776057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57880525257658418036517371 86820787886487627054776057)
      ·
        refine ⟨65115590914865720291082043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86820787886487627054776057 65115590914865720291082043)
        ·
          refine ⟨97673386372298580436623065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65115590914865720291082043 97673386372298580436623065)
          ·
            refine ⟨73255039779223935327467299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97673386372298580436623065 73255039779223935327467299)
            ·
              refine ⟨109882559668835902991200949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73255039779223935327467299 109882559668835902991200949)
              ·
                refine ⟨10301489968953365905425089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109882559668835902991200949 10301489968953365905425089)
                ·
                  refine ⟨7726117476715024429068817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10301489968953365905425089 7726117476715024429068817)
                  ·
                    refine ⟨5794588107536268321801613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7726117476715024429068817 5794588107536268321801613)
                    ·
                      refine ⟨2172970540326100620675605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5794588107536268321801613 2172970540326100620675605)
                      ·
                        rfl

theorem cell23_4231845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_4231845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231845 prefixEnd_4231845 := by exact prefixLift 4231845
  have htrace : WordTrace (prefixWord ++ tailWord_4231845) baseStart_4231845 baseEnd_4231845 := by
    simpa [prefixWord, tailWord_4231845, baseEnd_4231845] using wordTrace_append hprefix tailTrace_4231845
  have hstable : (prefixWord ++ tailWord_4231845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231845).length < 2 ^ (prefixWord ++ tailWord_4231845).sum := by decide
  have hdescent : baseEnd_4231845 < baseStart_4231845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231882 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 6]
def baseStart_4231882 : Nat := 118140960795 + 4231882 * 2 ^ 59
def prefixEnd_4231882 : Nat := 4983230072969 + 3 ^ 40 * 4231882 * 2
def baseEnd_4231882 : Nat := 241443282123368552879215

theorem tailTrace_4231882 : CollatzResearch.WordTrace tailWord_4231882 prefixEnd_4231882 241443282123368552879215 := by
  unfold tailWord_4231882
  simp only [CollatzResearch.WordTrace]
  refine ⟨38587354213655434187452475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102899611236414491166539933 38587354213655434187452475)
  ·
    refine ⟨57881031320483151281178713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38587354213655434187452475 57881031320483151281178713)
    ·
      refine ⟨43410773490362363460884035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57881031320483151281178713 43410773490362363460884035)
      ·
        refine ⟨65116160235543545191326053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43410773490362363460884035 65116160235543545191326053)
        ·
          refine ⟨12209280044164414723373635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65116160235543545191326053 12209280044164414723373635)
          ·
            refine ⟨18313920066246622085060453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12209280044164414723373635 18313920066246622085060453)
            ·
              refine ⟨3433860012421241640948835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18313920066246622085060453 3433860012421241640948835)
              ·
                refine ⟨5150790018631862461423253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3433860012421241640948835 5150790018631862461423253)
                ·
                  refine ⟨241443282123368552879215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5150790018631862461423253 241443282123368552879215)
                  ·
                    rfl

theorem cell23_4231882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_4231882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231882 prefixEnd_4231882 := by exact prefixLift 4231882
  have htrace : WordTrace (prefixWord ++ tailWord_4231882) baseStart_4231882 baseEnd_4231882 := by
    simpa [prefixWord, tailWord_4231882, baseEnd_4231882] using wordTrace_append hprefix tailTrace_4231882
  have hstable : (prefixWord ++ tailWord_4231882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231882).length < 2 ^ (prefixWord ++ tailWord_4231882).sum := by decide
  have hdescent : baseEnd_4231882 < baseStart_4231882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231895 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 3, 5]
def baseStart_4231895 : Nat := 118140960795 + 4231895 * 2 ^ 59
def prefixEnd_4231895 : Nat := 4983230072969 + 3 ^ 40 * 4231895 * 2
def baseEnd_4231895 : Nat := 724332071452941808350125

theorem tailTrace_4231895 : CollatzResearch.WordTrace tailWord_4231895 prefixEnd_4231895 724332071452941808350125 := by
  unfold tailWord_4231895
  simp only [CollatzResearch.WordTrace]
  refine ⟨154349891003574639970033139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102899927335716426646688759 154349891003574639970033139)
  ·
    refine ⟨231524836505361959955049709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154349891003574639970033139 231524836505361959955049709)
    ·
      refine ⟨86821813689510734983143641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231524836505361959955049709 86821813689510734983143641)
      ·
        refine ⟨65116360267133051237357731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86821813689510734983143641 65116360267133051237357731)
        ·
          refine ⟨97674540400699576856036597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65116360267133051237357731 97674540400699576856036597)
          ·
            refine ⟨9156988162565585330253431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97674540400699576856036597 9156988162565585330253431)
            ·
              refine ⟨13735482243848377995380147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9156988162565585330253431 13735482243848377995380147)
              ·
                refine ⟨20603223365772566993070221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13735482243848377995380147 20603223365772566993070221)
                ·
                  refine ⟨7726208762164712622401333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20603223365772566993070221 7726208762164712622401333)
                  ·
                    refine ⟨724332071452941808350125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7726208762164712622401333 724332071452941808350125)
                    ·
                      rfl

theorem cell23_4231895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_4231895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231895 prefixEnd_4231895 := by exact prefixLift 4231895
  have htrace : WordTrace (prefixWord ++ tailWord_4231895) baseStart_4231895 baseEnd_4231895 := by
    simpa [prefixWord, tailWord_4231895, baseEnd_4231895] using wordTrace_append hprefix tailTrace_4231895
  have hstable : (prefixWord ++ tailWord_4231895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231895).length < 2 ^ (prefixWord ++ tailWord_4231895).sum := by decide
  have hdescent : baseEnd_4231895 < baseStart_4231895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231926 : List Nat := [5, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_4231926 : Nat := 118140960795 + 4231926 * 2 ^ 59
def prefixEnd_4231926 : Nat := 4983230072969 + 3 ^ 40 * 4231926 * 2
def baseEnd_4231926 : Nat := 2173012132259114803762733

theorem tailTrace_4231926 : CollatzResearch.WordTrace tailWord_4231926 prefixEnd_4231926 2173012132259114803762733 := by
  unfold tailWord_4231926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9646938854153895766525727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102900681110974888176274421 9646938854153895766525727)
  ·
    refine ⟨14470408281230843649788591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9646938854153895766525727 14470408281230843649788591)
    ·
      refine ⟨21705612421846265474682887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14470408281230843649788591 21705612421846265474682887)
      ·
        refine ⟨32558418632769398212024331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21705612421846265474682887 32558418632769398212024331)
        ·
          refine ⟨48837627949154097318036497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32558418632769398212024331 48837627949154097318036497)
          ·
            refine ⟨36628220961865572988527373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48837627949154097318036497 36628220961865572988527373)
            ·
              refine ⟨13735582860699589870697765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36628220961865572988527373 13735582860699589870697765)
              ·
                refine ⟨2575421786381173100755831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13735582860699589870697765 2575421786381173100755831)
                ·
                  refine ⟨3863132679571759651133747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575421786381173100755831 3863132679571759651133747)
                  ·
                    refine ⟨5794699019357639476700621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3863132679571759651133747 5794699019357639476700621)
                    ·
                      refine ⟨2173012132259114803762733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5794699019357639476700621 2173012132259114803762733)
                      ·
                        rfl

theorem cell23_4231926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_4231926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231926 prefixEnd_4231926 := by exact prefixLift 4231926
  have htrace : WordTrace (prefixWord ++ tailWord_4231926) baseStart_4231926 baseEnd_4231926 := by
    simpa [prefixWord, tailWord_4231926, baseEnd_4231926] using wordTrace_append hprefix tailTrace_4231926
  have hstable : (prefixWord ++ tailWord_4231926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231926).length < 2 ^ (prefixWord ++ tailWord_4231926).sum := by decide
  have hdescent : baseEnd_4231926 < baseStart_4231926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231945 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_4231945 : Nat := 118140960795 + 4231945 * 2 ^ 59
def prefixEnd_4231945 : Nat := 4983230072969 + 3 ^ 40 * 4231945 * 2
def baseEnd_4231945 : Nat := 2173021888391550229425145

theorem tailTrace_4231945 : CollatzResearch.WordTrace tailWord_4231945 prefixEnd_4231945 2173021888391550229425145 := by
  unfold tailWord_4231945
  simp only [CollatzResearch.WordTrace]
  refine ⟨154351714653393498509353289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102901143102262332339568859 154351714653393498509353289)
  ·
    refine ⟨115763785990045123882014967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154351714653393498509353289 115763785990045123882014967)
    ·
      refine ⟨173645678985067685823022451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115763785990045123882014967 173645678985067685823022451)
      ·
        refine ⟨260468518477601528734533677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173645678985067685823022451 260468518477601528734533677)
        ·
          refine ⟨97675694429100573275450129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260468518477601528734533677 97675694429100573275450129)
          ·
            refine ⟨73256770821825429956587597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97675694429100573275450129 73256770821825429956587597)
            ·
              refine ⟨27471289058184536233720349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73256770821825429956587597 27471289058184536233720349)
              ·
                refine ⟨10301733396819201087645131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27471289058184536233720349 10301733396819201087645131)
                ·
                  refine ⟨15452600095228801631467697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10301733396819201087645131 15452600095228801631467697)
                  ·
                    refine ⟨11589450071421601223600773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15452600095228801631467697 11589450071421601223600773)
                    ·
                      refine ⟨2173021888391550229425145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11589450071421601223600773 2173021888391550229425145)
                      ·
                        rfl

theorem cell23_4231945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_4231945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231945 prefixEnd_4231945 := by exact prefixLift 4231945
  have htrace : WordTrace (prefixWord ++ tailWord_4231945) baseStart_4231945 baseEnd_4231945 := by
    simpa [prefixWord, tailWord_4231945, baseEnd_4231945] using wordTrace_append hprefix tailTrace_4231945
  have hstable : (prefixWord ++ tailWord_4231945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231945).length < 2 ^ (prefixWord ++ tailWord_4231945).sum := by decide
  have hdescent : baseEnd_4231945 < baseStart_4231945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231955 : List Nat := [1, 1, 1, 2, 1, 3, 7, 7]
def baseStart_4231955 : Nat := 118140960795 + 4231955 * 2 ^ 59
def prefixEnd_4231955 : Nat := 4983230072969 + 3 ^ 40 * 4231955 * 2
def baseEnd_4231955 : Nat := 80482482340670192233337

theorem tailTrace_4231955 : CollatzResearch.WordTrace tailWord_4231955 prefixEnd_4231955 80482482340670192233337 := by
  unfold tailWord_4231955
  simp only [CollatzResearch.WordTrace]
  refine ⟨154352079383357270217217319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102901386255571513478144879 154352079383357270217217319)
  ·
    refine ⟨231528119075035905325825979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154352079383357270217217319 231528119075035905325825979)
    ·
      refine ⟨347292178612553857988738969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231528119075035905325825979 347292178612553857988738969)
      ·
        refine ⟨260469133959415393491554227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347292178612553857988738969 260469133959415393491554227)
        ·
          refine ⟨390703700939123090237331341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260469133959415393491554227 390703700939123090237331341)
          ·
            refine ⟨146513887852171158838999253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 390703700939123090237331341 146513887852171158838999253)
            ·
              refine ⟨3433919246535261535289045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 146513887852171158838999253 3433919246535261535289045)
              ·
                refine ⟨80482482340670192233337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3433919246535261535289045 80482482340670192233337)
                ·
                  rfl

theorem cell23_4231955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 7].length) (baseStart_4231955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231955 prefixEnd_4231955 := by exact prefixLift 4231955
  have htrace : WordTrace (prefixWord ++ tailWord_4231955) baseStart_4231955 baseEnd_4231955 := by
    simpa [prefixWord, tailWord_4231955, baseEnd_4231955] using wordTrace_append hprefix tailTrace_4231955
  have hstable : (prefixWord ++ tailWord_4231955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231955).length < 2 ^ (prefixWord ++ tailWord_4231955).sum := by decide
  have hdescent : baseEnd_4231955 < baseStart_4231955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4231999 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 3]
def baseStart_4231999 : Nat := 118140960795 + 4231999 * 2 ^ 59
def prefixEnd_4231999 : Nat := 4983230072969 + 3 ^ 40 * 4231999 * 2
def baseEnd_4231999 : Nat := 2173049616346893018149897

theorem tailTrace_4231999 : CollatzResearch.WordTrace tailWord_4231999 prefixEnd_4231999 2173049616346893018149897 := by
  unfold tailWord_4231999
  simp only [CollatzResearch.WordTrace]
  refine ⟨154353684195197865731819051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102902456130131910487879367 154353684195197865731819051)
  ·
    refine ⟨231530526292796798597728577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154353684195197865731819051 231530526292796798597728577)
    ·
      refine ⟨173647894719597598948296433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231530526292796798597728577 173647894719597598948296433)
      ·
        refine ⟨130235921039698199211222325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173647894719597598948296433 130235921039698199211222325)
        ·
          refine ⟨12209617597471706176052093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130235921039698199211222325 12209617597471706176052093)
          ·
            refine ⟨4578606599051889816019535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12209617597471706176052093 4578606599051889816019535)
            ·
              refine ⟨6867909898577834724029303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578606599051889816019535 6867909898577834724029303)
              ·
                refine ⟨10301864847866752086043955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6867909898577834724029303 10301864847866752086043955)
                ·
                  refine ⟨15452797271800128129065933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10301864847866752086043955 15452797271800128129065933)
                  ·
                    refine ⟨5794798976925048048399725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15452797271800128129065933 5794798976925048048399725)
                    ·
                      refine ⟨2173049616346893018149897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5794798976925048048399725 2173049616346893018149897)
                      ·
                        rfl

theorem cell23_4231999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_4231999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4231999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4231999 prefixEnd_4231999 := by exact prefixLift 4231999
  have htrace : WordTrace (prefixWord ++ tailWord_4231999) baseStart_4231999 baseEnd_4231999 := by
    simpa [prefixWord, tailWord_4231999, baseEnd_4231999] using wordTrace_append hprefix tailTrace_4231999
  have hstable : (prefixWord ++ tailWord_4231999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4231999).length < 2 ^ (prefixWord ++ tailWord_4231999).sum := by decide
  have hdescent : baseEnd_4231999 < baseStart_4231999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4231999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232009 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 1, 3, 2]
def baseStart_4232009 : Nat := 118140960795 + 4232009 * 2 ^ 59
def prefixEnd_4232009 : Nat := 4983230072969 + 3 ^ 40 * 4232009 * 2
def baseEnd_4232009 : Nat := 2173054751153437979024851

theorem tailTrace_4232009 : CollatzResearch.WordTrace tailWord_4232009 prefixEnd_4232009 2173054751153437979024851 := by
  unfold tailWord_4232009
  simp only [CollatzResearch.WordTrace]
  refine ⟨154354048925161637439683081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102902699283441091626455387 154354048925161637439683081)
  ·
    refine ⟨115765536693871228079762311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154354048925161637439683081 115765536693871228079762311)
    ·
      refine ⟨173648305040806842119643467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115765536693871228079762311 173648305040806842119643467)
      ·
        refine ⟨260472457561210263179465201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173648305040806842119643467 260472457561210263179465201)
        ·
          refine ⟨195354343170907697384598901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260472457561210263179465201 195354343170907697384598901)
          ·
            refine ⟨18314469672272596629806147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 195354343170907697384598901 18314469672272596629806147)
            ·
              refine ⟨27471704508408894944709221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18314469672272596629806147 27471704508408894944709221)
              ·
                refine ⟨5150944595326667802132979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27471704508408894944709221 5150944595326667802132979)
                ·
                  refine ⟨7726416892990001703199469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5150944595326667802132979 7726416892990001703199469)
                  ·
                    refine ⟨2897406334871250638699801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7726416892990001703199469 2897406334871250638699801)
                    ·
                      refine ⟨2173054751153437979024851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897406334871250638699801 2173054751153437979024851)
                      ·
                        rfl

theorem cell23_4232009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 3, 2].length) (baseStart_4232009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232009 prefixEnd_4232009 := by exact prefixLift 4232009
  have htrace : WordTrace (prefixWord ++ tailWord_4232009) baseStart_4232009 baseEnd_4232009 := by
    simpa [prefixWord, tailWord_4232009, baseEnd_4232009] using wordTrace_append hprefix tailTrace_4232009
  have hstable : (prefixWord ++ tailWord_4232009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232009).length < 2 ^ (prefixWord ++ tailWord_4232009).sum := by decide
  have hdescent : baseEnd_4232009 < baseStart_4232009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232025 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_4232025 : Nat := 118140960795 + 4232025 * 2 ^ 59
def prefixEnd_4232025 : Nat := 4983230072969 + 3 ^ 40 * 4232025 * 2
def baseEnd_4232025 : Nat := 2173062966843909916424777

theorem tailTrace_4232025 : CollatzResearch.WordTrace tailWord_4232025 prefixEnd_4232025 2173062966843909916424777 := by
  unfold tailWord_4232025
  simp only [CollatzResearch.WordTrace]
  refine ⟨154354632493103672172265529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102903088328735781448177019 154354632493103672172265529)
  ·
    refine ⟨115765974369827754129199147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154354632493103672172265529 115765974369827754129199147)
    ·
      refine ⟨173648961554741631193798721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115765974369827754129199147 173648961554741631193798721)
      ·
        refine ⟨130236721166056223395349041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173648961554741631193798721 130236721166056223395349041)
        ·
          refine ⟨97677540874542167546511781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130236721166056223395349041 97677540874542167546511781)
          ·
            refine ⟨18314538913976656414970959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97677540874542167546511781 18314538913976656414970959)
            ·
              refine ⟨27471808370964984622456439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18314538913976656414970959 27471808370964984622456439)
              ·
                refine ⟨41207712556447476933684659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27471808370964984622456439 41207712556447476933684659)
                ·
                  refine ⟨61811568834671215400526989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41207712556447476933684659 61811568834671215400526989)
                  ·
                    refine ⟨23179338313001705775197621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61811568834671215400526989 23179338313001705775197621)
                    ·
                      refine ⟨2173062966843909916424777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23179338313001705775197621 2173062966843909916424777)
                      ·
                        rfl

theorem cell23_4232025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_4232025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232025 prefixEnd_4232025 := by exact prefixLift 4232025
  have htrace : WordTrace (prefixWord ++ tailWord_4232025) baseStart_4232025 baseEnd_4232025 := by
    simpa [prefixWord, tailWord_4232025, baseEnd_4232025] using wordTrace_append hprefix tailTrace_4232025
  have hstable : (prefixWord ++ tailWord_4232025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232025).length < 2 ^ (prefixWord ++ tailWord_4232025).sum := by decide
  have hdescent : baseEnd_4232025 < baseStart_4232025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232075 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 1, 7]
def baseStart_4232075 : Nat := 118140960795 + 4232075 * 2 ^ 59
def prefixEnd_4232075 : Nat := 4983230072969 + 3 ^ 40 * 4232075 * 2
def baseEnd_4232075 : Nat := 724362880292211573599849

theorem tailTrace_4232075 : CollatzResearch.WordTrace tailWord_4232075 prefixEnd_4232075 724362880292211573599849 := by
  unfold tailWord_4232075
  simp only [CollatzResearch.WordTrace]
  refine ⟨154356456142922530711585679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102904304095281687141057119 154356456142922530711585679)
  ·
    refine ⟨231534684214383796067378519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154356456142922530711585679 231534684214383796067378519)
    ·
      refine ⟨347302026321575694101067779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231534684214383796067378519 347302026321575694101067779)
      ·
        refine ⟨520953039482363541151601669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347302026321575694101067779 520953039482363541151601669)
        ·
          refine ⟨97678694902943163965925313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 520953039482363541151601669 97678694902943163965925313)
          ·
            refine ⟨73259021177207372974443985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97678694902943163965925313 73259021177207372974443985)
            ·
              refine ⟨54944265882905529730832989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73259021177207372974443985 54944265882905529730832989)
              ·
                refine ⟨20604099706089573649062371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54944265882905529730832989 20604099706089573649062371)
                ·
                  refine ⟨30906149559134360473593557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20604099706089573649062371 30906149559134360473593557)
                  ·
                    refine ⟨724362880292211573599849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30906149559134360473593557 724362880292211573599849)
                    ·
                      rfl

theorem cell23_4232075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 7].length) (baseStart_4232075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232075 prefixEnd_4232075 := by exact prefixLift 4232075
  have htrace : WordTrace (prefixWord ++ tailWord_4232075) baseStart_4232075 baseEnd_4232075 := by
    simpa [prefixWord, tailWord_4232075, baseEnd_4232075] using wordTrace_append hprefix tailTrace_4232075
  have hstable : (prefixWord ++ tailWord_4232075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232075).length < 2 ^ (prefixWord ++ tailWord_4232075).sum := by decide
  have hdescent : baseEnd_4232075 < baseStart_4232075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232141 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4232141 : Nat := 118140960795 + 4232141 * 2 ^ 59
def prefixEnd_4232141 : Nat := 4983230072969 + 3 ^ 40 * 4232141 * 2
def baseEnd_4232141 : Nat := 2173122530599831462574245

theorem tailTrace_4232141 : CollatzResearch.WordTrace tailWord_4232141 prefixEnd_4232141 2173122530599831462574245 := by
  unfold tailWord_4232141
  simp only [CollatzResearch.WordTrace]
  refine ⟨154358863360683423983488277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102905908907122282655658851 154358863360683423983488277)
  ·
    refine ⟨7235571720032035499226013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154358863360683423983488277 7235571720032035499226013)
    ·
      refine ⟨2713339395012013312209755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7235571720032035499226013 2713339395012013312209755)
      ·
        refine ⟨4070009092518019968314633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713339395012013312209755 4070009092518019968314633)
        ·
          refine ⟨3052506819388514976235975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070009092518019968314633 3052506819388514976235975)
          ·
            refine ⟨4578760229082772464353963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052506819388514976235975 4578760229082772464353963)
            ·
              refine ⟨6868140343624158696530945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578760229082772464353963 6868140343624158696530945)
              ·
                refine ⟨5151105257718119022398209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6868140343624158696530945 5151105257718119022398209)
                ·
                  refine ⟨3863328943288589266798657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5151105257718119022398209 3863328943288589266798657)
                  ·
                    refine ⟨2897496707466441950098993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3863328943288589266798657 2897496707466441950098993)
                    ·
                      refine ⟨2173122530599831462574245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897496707466441950098993 2173122530599831462574245)
                      ·
                        rfl

theorem cell23_4232141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4232141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232141 prefixEnd_4232141 := by exact prefixLift 4232141
  have htrace : WordTrace (prefixWord ++ tailWord_4232141) baseStart_4232141 baseEnd_4232141 := by
    simpa [prefixWord, tailWord_4232141, baseEnd_4232141] using wordTrace_append hprefix tailTrace_4232141
  have hstable : (prefixWord ++ tailWord_4232141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232141).length < 2 ^ (prefixWord ++ tailWord_4232141).sum := by decide
  have hdescent : baseEnd_4232141 < baseStart_4232141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232142 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_4232142 : Nat := 118140960795 + 4232142 * 2 ^ 59
def prefixEnd_4232142 : Nat := 4983230072969 + 3 ^ 40 * 4232142 * 2
def baseEnd_4232142 : Nat := 2173123044080485958661739

theorem tailTrace_4232142 : CollatzResearch.WordTrace tailWord_4232142 prefixEnd_4232142 2173123044080485958661739 := by
  unfold tailWord_4232142
  simp only [CollatzResearch.WordTrace]
  refine ⟨19294862479209975144284335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102905933222453200769516453 19294862479209975144284335)
  ·
    refine ⟨28942293718814962716426503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19294862479209975144284335 28942293718814962716426503)
    ·
      refine ⟨43413440578222444074639755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28942293718814962716426503 43413440578222444074639755)
      ·
        refine ⟨65120160867333666111959633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43413440578222444074639755 65120160867333666111959633)
        ·
          refine ⟨48840120650500249583969725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65120160867333666111959633 48840120650500249583969725)
          ·
            refine ⟨18315045243937593593988647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48840120650500249583969725 18315045243937593593988647)
            ·
              refine ⟨27472567865906390390982971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18315045243937593593988647 27472567865906390390982971)
              ·
                refine ⟨41208851798859585586474457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27472567865906390390982971 41208851798859585586474457)
                ·
                  refine ⟨30906638849144689189855843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41208851798859585586474457 30906638849144689189855843)
                  ·
                    refine ⟨46359958273717033784783765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30906638849144689189855843 46359958273717033784783765)
                    ·
                      refine ⟨2173123044080485958661739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46359958273717033784783765 2173123044080485958661739)
                      ·
                        rfl

theorem cell23_4232142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_4232142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232142 prefixEnd_4232142 := by exact prefixLift 4232142
  have htrace : WordTrace (prefixWord ++ tailWord_4232142) baseStart_4232142 baseEnd_4232142 := by
    simpa [prefixWord, tailWord_4232142, baseEnd_4232142] using wordTrace_append hprefix tailTrace_4232142
  have hstable : (prefixWord ++ tailWord_4232142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232142).length < 2 ^ (prefixWord ++ tailWord_4232142).sum := by decide
  have hdescent : baseEnd_4232142 < baseStart_4232142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232146 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4232146 : Nat := 118140960795 + 4232146 * 2 ^ 59
def prefixEnd_4232146 : Nat := 4983230072969 + 3 ^ 40 * 4232146 * 2
def baseEnd_4232146 : Nat := 2173125098003103943011721

theorem tailTrace_4232146 : CollatzResearch.WordTrace tailWord_4232146 prefixEnd_4232146 2173125098003103943011721 := by
  unfold tailWord_4232146
  simp only [CollatzResearch.WordTrace]
  refine ⟨38589761431416327459355073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102906030483776873224946861 38589761431416327459355073)
  ·
    refine ⟨28942321073562245594516305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38589761431416327459355073 28942321073562245594516305)
    ·
      refine ⟨21706740805171684195887229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28942321073562245594516305 21706740805171684195887229)
      ·
        refine ⟨8140027801939381573457711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21706740805171684195887229 8140027801939381573457711)
        ·
          refine ⟨12210041702909072360186567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140027801939381573457711 12210041702909072360186567)
          ·
            refine ⟨18315062554363608540279851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12210041702909072360186567 18315062554363608540279851)
            ·
              refine ⟨27472593831545412810419777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18315062554363608540279851 27472593831545412810419777)
              ·
                refine ⟨20604445373659059607814833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27472593831545412810419777 20604445373659059607814833)
                ·
                  refine ⟨15453334030244294705861125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20604445373659059607814833 15453334030244294705861125)
                  ·
                    refine ⟨2897500130670805257348961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15453334030244294705861125 2897500130670805257348961)
                    ·
                      refine ⟨2173125098003103943011721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897500130670805257348961 2173125098003103943011721)
                      ·
                        rfl

theorem cell23_4232146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4232146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232146 prefixEnd_4232146 := by exact prefixLift 4232146
  have htrace : WordTrace (prefixWord ++ tailWord_4232146) baseStart_4232146 baseEnd_4232146 := by
    simpa [prefixWord, tailWord_4232146, baseEnd_4232146] using wordTrace_append hprefix tailTrace_4232146
  have hstable : (prefixWord ++ tailWord_4232146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232146).length < 2 ^ (prefixWord ++ tailWord_4232146).sum := by decide
  have hdescent : baseEnd_4232146 < baseStart_4232146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232152 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 8]
def baseStart_4232152 : Nat := 118140960795 + 4232152 * 2 ^ 59
def prefixEnd_4232152 : Nat := 4983230072969 + 3 ^ 40 * 4232152 * 2
def baseEnd_4232152 : Nat := 241458686543003435504077

theorem tailTrace_4232152 : CollatzResearch.WordTrace tailWord_4232152 prefixEnd_4232152 241458686543003435504077 := by
  unfold tailWord_4232152
  simp only [CollatzResearch.WordTrace]
  refine ⟨77179632281821786431069355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102906176375762381908092473 77179632281821786431069355)
  ·
    refine ⟨115769448422732679646604033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77179632281821786431069355 115769448422732679646604033)
    ·
      refine ⟨86827086317049509734953025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115769448422732679646604033 86827086317049509734953025)
      ·
        refine ⟨65120314737787132301214769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86827086317049509734953025 65120314737787132301214769)
        ·
          refine ⟨48840236053340349225911077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65120314737787132301214769 48840236053340349225911077)
          ·
            refine ⟨9157544260001315479858327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48840236053340349225911077 9157544260001315479858327)
            ·
              refine ⟨13736316390001973219787491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9157544260001315479858327 13736316390001973219787491)
              ·
                refine ⟨20604474585002959829681237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13736316390001973219787491 20604474585002959829681237)
                ·
                  refine ⟨241458686543003435504077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20604474585002959829681237 241458686543003435504077)
                  ·
                    rfl

theorem cell23_4232152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 8].length) (baseStart_4232152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232152 prefixEnd_4232152 := by exact prefixLift 4232152
  have htrace : WordTrace (prefixWord ++ tailWord_4232152) baseStart_4232152 baseEnd_4232152 := by
    simpa [prefixWord, tailWord_4232152, baseEnd_4232152] using wordTrace_append hprefix tailTrace_4232152
  have hstable : (prefixWord ++ tailWord_4232152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232152).length < 2 ^ (prefixWord ++ tailWord_4232152).sum := by decide
  have hdescent : baseEnd_4232152 < baseStart_4232152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232199 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 1, 5]
def baseStart_4232199 : Nat := 118140960795 + 4232199 * 2 ^ 59
def prefixEnd_4232199 : Nat := 4983230072969 + 3 ^ 40 * 4232199 * 2
def baseEnd_4232199 : Nat := 724384104159264078549659

theorem tailTrace_4232199 : CollatzResearch.WordTrace tailWord_4232199 prefixEnd_4232199 724384104159264078549659 := by
  unfold tailWord_4232199
  simp only [CollatzResearch.WordTrace]
  refine ⟨154360978794473299889099651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102907319196315533259399767 154360978794473299889099651)
  ·
    refine ⟨231541468191709949833649477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154360978794473299889099651 231541468191709949833649477)
    ·
      refine ⟨43414025285945615593809277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231541468191709949833649477 43414025285945615593809277)
      ·
        refine ⟨16280259482229605847678479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43414025285945615593809277 16280259482229605847678479)
        ·
          refine ⟨24420389223344408771517719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16280259482229605847678479 24420389223344408771517719)
          ·
            refine ⟨36630583835016613157276579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24420389223344408771517719 36630583835016613157276579)
            ·
              refine ⟨54945875752524919735914869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36630583835016613157276579 54945875752524919735914869)
              ·
                refine ⟨5151175851799211225242019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54945875752524919735914869 5151175851799211225242019)
                ·
                  refine ⟨7726763777698816837863029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5151175851799211225242019 7726763777698816837863029)
                  ·
                    refine ⟨724384104159264078549659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7726763777698816837863029 724384104159264078549659)
                    ·
                      rfl

theorem cell23_4232199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_4232199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232199 prefixEnd_4232199 := by exact prefixLift 4232199
  have htrace : WordTrace (prefixWord ++ tailWord_4232199) baseStart_4232199 baseEnd_4232199 := by
    simpa [prefixWord, tailWord_4232199, baseEnd_4232199] using wordTrace_append hprefix tailTrace_4232199
  have hstable : (prefixWord ++ tailWord_4232199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232199).length < 2 ^ (prefixWord ++ tailWord_4232199).sum := by decide
  have hdescent : baseEnd_4232199 < baseStart_4232199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232206 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_4232206 : Nat := 118140960795 + 4232206 * 2 ^ 59
def prefixEnd_4232206 : Nat := 4983230072969 + 3 ^ 40 * 4232206 * 2
def baseEnd_4232206 : Nat := 2173155906842373708261445

theorem tailTrace_4232206 : CollatzResearch.WordTrace tailWord_4232206 prefixEnd_4232206 2173155906842373708261445 := by
  unfold tailWord_4232206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295154263180992510575559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102907489403631960056402981 19295154263180992510575559)
  ·
    refine ⟨28942731394771488765863339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19295154263180992510575559 28942731394771488765863339)
    ·
      refine ⟨43414097092157233148795009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28942731394771488765863339 43414097092157233148795009)
      ·
        refine ⟨32560572819117924861596257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43414097092157233148795009 32560572819117924861596257)
        ·
          refine ⟨24420429614338443646197193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32560572819117924861596257 24420429614338443646197193)
          ·
            refine ⟨18315322210753832734647895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24420429614338443646197193 18315322210753832734647895)
            ·
              refine ⟨27472983316130749101971843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18315322210753832734647895 27472983316130749101971843)
              ·
                refine ⟨41209474974196123652957765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27472983316130749101971843 41209474974196123652957765)
                ·
                  refine ⟨7726776557661773184929581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41209474974196123652957765 7726776557661773184929581)
                  ·
                    refine ⟨2897541209123164944348593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7726776557661773184929581 2897541209123164944348593)
                    ·
                      refine ⟨2173155906842373708261445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897541209123164944348593 2173155906842373708261445)
                      ·
                        rfl

theorem cell23_4232206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_4232206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232206 prefixEnd_4232206 := by exact prefixLift 4232206
  have htrace : WordTrace (prefixWord ++ tailWord_4232206) baseStart_4232206 baseEnd_4232206 := by
    simpa [prefixWord, tailWord_4232206, baseEnd_4232206] using wordTrace_append hprefix tailTrace_4232206
  have hstable : (prefixWord ++ tailWord_4232206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232206).length < 2 ^ (prefixWord ++ tailWord_4232206).sum := by decide
  have hdescent : baseEnd_4232206 < baseStart_4232206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232213 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_4232213 : Nat := 118140960795 + 4232213 * 2 ^ 59
def prefixEnd_4232213 : Nat := 4983230072969 + 3 ^ 40 * 4232213 * 2
def baseEnd_4232213 : Nat := 2173159501206955180873913

theorem tailTrace_4232213 : CollatzResearch.WordTrace tailWord_4232213 prefixEnd_4232213 2173159501206955180873913 := by
  unfold tailWord_4232213
  simp only [CollatzResearch.WordTrace]
  refine ⟨154361489416422580280109293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102907659610948386853406195 154361489416422580280109293)
  ·
    refine ⟨57885558531158467605040985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154361489416422580280109293 57885558531158467605040985)
    ·
      refine ⟨43414168898368850703780739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57885558531158467605040985 43414168898368850703780739)
      ·
        refine ⟨65121253347553276055671109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43414168898368850703780739 65121253347553276055671109)
        ·
          refine ⟨12210235002666239260438333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65121253347553276055671109 12210235002666239260438333)
          ·
            refine ⟨4578838125999839722664375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12210235002666239260438333 4578838125999839722664375)
            ·
              refine ⟨6868257188999759583996563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4578838125999839722664375 6868257188999759583996563)
              ·
                refine ⟨10302385783499639375994845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6868257188999759583996563 10302385783499639375994845)
                ·
                  refine ⟨3863394668812364765998067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10302385783499639375994845 3863394668812364765998067)
                  ·
                    refine ⟨5795092003218547148997101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3863394668812364765998067 5795092003218547148997101)
                    ·
                      refine ⟨2173159501206955180873913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5795092003218547148997101 2173159501206955180873913)
                      ·
                        rfl

theorem cell23_4232213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_4232213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232213 prefixEnd_4232213 := by exact prefixLift 4232213
  have htrace : WordTrace (prefixWord ++ tailWord_4232213) baseStart_4232213 baseEnd_4232213 := by
    simpa [prefixWord, tailWord_4232213, baseEnd_4232213] using wordTrace_append hprefix tailTrace_4232213
  have hstable : (prefixWord ++ tailWord_4232213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232213).length < 2 ^ (prefixWord ++ tailWord_4232213).sum := by decide
  have hdescent : baseEnd_4232213 < baseStart_4232213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232236 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 5, 2, 2]
def baseStart_4232236 : Nat := 118140960795 + 4232236 * 2 ^ 59
def prefixEnd_4232236 : Nat := 4983230072969 + 3 ^ 40 * 4232236 * 2
def baseEnd_4232236 : Nat := 2173171311262008590886307

theorem tailTrace_4232236 : CollatzResearch.WordTrace tailWord_4232236 prefixEnd_4232236 2173171311262008590886307 := by
  unfold tailWord_4232236
  simp only [CollatzResearch.WordTrace]
  refine ⟨77181164147669627604098281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102908218863559503472131041 77181164147669627604098281)
  ·
    refine ⟨57885873110752220703073711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77181164147669627604098281 57885873110752220703073711)
    ·
      refine ⟨86828809666128331054610567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57885873110752220703073711 86828809666128331054610567)
      ·
        refine ⟨130243214499192496581915851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86828809666128331054610567 130243214499192496581915851)
        ·
          refine ⟨195364821748788744872873777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130243214499192496581915851 195364821748788744872873777)
          ·
            refine ⟨146523616311591558654655333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195364821748788744872873777 146523616311591558654655333)
            ·
              refine ⟨27473178058423417247747875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146523616311591558654655333 27473178058423417247747875)
              ·
                refine ⟨41209767087635125871621813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27473178058423417247747875 41209767087635125871621813)
                ·
                  refine ⟨3863415664465793050464545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41209767087635125871621813 3863415664465793050464545)
                  ·
                    refine ⟨2897561748349344787848409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3863415664465793050464545 2897561748349344787848409)
                    ·
                      refine ⟨2173171311262008590886307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897561748349344787848409 2173171311262008590886307)
                      ·
                        rfl

theorem cell23_4232236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_4232236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232236 prefixEnd_4232236 := by exact prefixLift 4232236
  have htrace : WordTrace (prefixWord ++ tailWord_4232236) baseStart_4232236 baseEnd_4232236 := by
    simpa [prefixWord, tailWord_4232236, baseEnd_4232236] using wordTrace_append hprefix tailTrace_4232236
  have hstable : (prefixWord ++ tailWord_4232236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232236).length < 2 ^ (prefixWord ++ tailWord_4232236).sum := by decide
  have hdescent : baseEnd_4232236 < baseStart_4232236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232242 : List Nat := [3, 2, 1, 1, 2, 2, 1, 11]
def baseStart_4232242 : Nat := 118140960795 + 4232242 * 2 ^ 59
def prefixEnd_4232242 : Nat := 4983230072969 + 3 ^ 40 * 4232242 * 2
def baseEnd_4232242 : Nat := 80487940449849465459677

theorem tailTrace_4232242 : CollatzResearch.WordTrace tailWord_4232242 prefixEnd_4232242 80487940449849465459677 := by
  unfold tailWord_4232242
  simp only [CollatzResearch.WordTrace]
  refine ⟨38590636783329379558228745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102908364755545012155276653 38590636783329379558228745)
  ·
    refine ⟨28942977587497034668671559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38590636783329379558228745 28942977587497034668671559)
    ·
      refine ⟨43414466381245552003007339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28942977587497034668671559 43414466381245552003007339)
      ·
        refine ⟨65121699571868328004511009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43414466381245552003007339 65121699571868328004511009)
        ·
          refine ⟨48841274678901246003383257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65121699571868328004511009 48841274678901246003383257)
          ·
            refine ⟨36630956009175934502537443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48841274678901246003383257 36630956009175934502537443)
            ·
              refine ⟨54946434013763901753806165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36630956009175934502537443 54946434013763901753806165)
              ·
                refine ⟨80487940449849465459677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 54946434013763901753806165 80487940449849465459677)
                ·
                  rfl

theorem cell23_4232242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 11].length) (baseStart_4232242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232242 prefixEnd_4232242 := by exact prefixLift 4232242
  have htrace : WordTrace (prefixWord ++ tailWord_4232242) baseStart_4232242 baseEnd_4232242 := by
    simpa [prefixWord, tailWord_4232242, baseEnd_4232242] using wordTrace_append hprefix tailTrace_4232242
  have hstable : (prefixWord ++ tailWord_4232242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232242).length < 2 ^ (prefixWord ++ tailWord_4232242).sum := by decide
  have hdescent : baseEnd_4232242 < baseStart_4232242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232246 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4232246 : Nat := 118140960795 + 4232246 * 2 ^ 59
def prefixEnd_4232246 : Nat := 4983230072969 + 3 ^ 40 * 4232246 * 2
def baseEnd_4232246 : Nat := 724392148689517850587087

theorem tailTrace_4232246 : CollatzResearch.WordTrace tailWord_4232246 prefixEnd_4232246 724392148689517850587087 := by
  unfold tailWord_4232246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9647668314081439182253787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102908462016868684610707061 9647668314081439182253787)
  ·
    refine ⟨14471502471122158773380681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9647668314081439182253787 14471502471122158773380681)
    ·
      refine ⟨10853626853341619080035511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14471502471122158773380681 10853626853341619080035511)
      ·
        refine ⟨16280440280012428620053267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10853626853341619080035511 16280440280012428620053267)
        ·
          refine ⟨24420660420018642930079901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16280440280012428620053267 24420660420018642930079901)
          ·
            refine ⟨9157747657506991098779963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24420660420018642930079901 9157747657506991098779963)
            ·
              refine ⟨13736621486260486648169945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9157747657506991098779963 13736621486260486648169945)
              ·
                refine ⟨10302466114695364986127459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13736621486260486648169945 10302466114695364986127459)
                ·
                  refine ⟨15453699172043047479191189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10302466114695364986127459 15453699172043047479191189)
                  ·
                    refine ⟨724392148689517850587087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15453699172043047479191189 724392148689517850587087)
                    ·
                      rfl

theorem cell23_4232246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4232246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232246 prefixEnd_4232246 := by exact prefixLift 4232246
  have htrace : WordTrace (prefixWord ++ tailWord_4232246) baseStart_4232246 baseEnd_4232246 := by
    simpa [prefixWord, tailWord_4232246, baseEnd_4232246] using wordTrace_append hprefix tailTrace_4232246
  have hstable : (prefixWord ++ tailWord_4232246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232246).length < 2 ^ (prefixWord ++ tailWord_4232246).sum := by decide
  have hdescent : baseEnd_4232246 < baseStart_4232246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232249 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4232249 : Nat := 118140960795 + 4232249 * 2 ^ 59
def prefixEnd_4232249 : Nat := 4983230072969 + 3 ^ 40 * 4232249 * 2
def baseEnd_4232249 : Nat := 2173177986510517040023747

theorem tailTrace_4232249 : CollatzResearch.WordTrace tailWord_4232249 prefixEnd_4232249 2173177986510517040023747 := by
  unfold tailWord_4232249
  simp only [CollatzResearch.WordTrace]
  refine ⟨154362802444292158428419801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102908534962861438952279867 154362802444292158428419801)
  ·
    refine ⟨115772101833219118821314851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154362802444292158428419801 115772101833219118821314851)
    ·
      refine ⟨173658152749828678231972277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115772101833219118821314851 173658152749828678231972277)
      ·
        refine ⟨16280451820296438584247401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173658152749828678231972277 16280451820296438584247401)
        ·
          refine ⟨12210338865222328938185551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16280451820296438584247401 12210338865222328938185551)
          ·
            refine ⟨18315508297833493407278327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12210338865222328938185551 18315508297833493407278327)
            ·
              refine ⟨27473262446750240110917491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18315508297833493407278327 27473262446750240110917491)
              ·
                refine ⟨41209893670125360166376237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27473262446750240110917491 41209893670125360166376237)
                ·
                  refine ⟨15453710126297010062391089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41209893670125360166376237 15453710126297010062391089)
                  ·
                    refine ⟨11590282594722757546793317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15453710126297010062391089 11590282594722757546793317)
                    ·
                      refine ⟨2173177986510517040023747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11590282594722757546793317 2173177986510517040023747)
                      ·
                        rfl

theorem cell23_4232249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4232249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232249 prefixEnd_4232249 := by exact prefixLift 4232249
  have htrace : WordTrace (prefixWord ++ tailWord_4232249) baseStart_4232249 baseEnd_4232249 := by
    simpa [prefixWord, tailWord_4232249, baseEnd_4232249] using wordTrace_append hprefix tailTrace_4232249
  have hstable : (prefixWord ++ tailWord_4232249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232249).length < 2 ^ (prefixWord ++ tailWord_4232249).sum := by decide
  have hdescent : baseEnd_4232249 < baseStart_4232249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232253 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_4232253 : Nat := 118140960795 + 4232253 * 2 ^ 59
def prefixEnd_4232253 : Nat := 4983230072969 + 3 ^ 40 * 4232253 * 2
def baseEnd_4232253 : Nat := 2173180040433135024373729

theorem tailTrace_4232253 : CollatzResearch.WordTrace tailWord_4232253 prefixEnd_4232253 2173180040433135024373729 := by
  unfold tailWord_4232253
  simp only [CollatzResearch.WordTrace]
  refine ⟨154362948336277667111565413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102908632224185111407710275 154362948336277667111565413)
  ·
    refine ⟨28943052813052062583418515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154362948336277667111565413 28943052813052062583418515)
    ·
      refine ⟨43414579219578093875127773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28943052813052062583418515 43414579219578093875127773)
      ·
        refine ⟨16280467207341785203172915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43414579219578093875127773 16280467207341785203172915)
        ·
          refine ⟨24420700811012677804759373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16280467207341785203172915 24420700811012677804759373)
          ·
            refine ⟨9157762804129754176784765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24420700811012677804759373 9157762804129754176784765)
            ·
              refine ⟨3434161051548657816294287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9157762804129754176784765 3434161051548657816294287)
              ·
                refine ⟨5151241577322986724441431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434161051548657816294287 5151241577322986724441431)
                ·
                  refine ⟨7726862365984480086662147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5151241577322986724441431 7726862365984480086662147)
                  ·
                    refine ⟨11590293548976720129993221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7726862365984480086662147 11590293548976720129993221)
                    ·
                      refine ⟨2173180040433135024373729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11590293548976720129993221 2173180040433135024373729)
                      ·
                        rfl

theorem cell23_4232253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_4232253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232253 prefixEnd_4232253 := by exact prefixLift 4232253
  have htrace : WordTrace (prefixWord ++ tailWord_4232253) baseStart_4232253 baseEnd_4232253 := by
    simpa [prefixWord, tailWord_4232253, baseEnd_4232253] using wordTrace_append hprefix tailTrace_4232253
  have hstable : (prefixWord ++ tailWord_4232253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232253).length < 2 ^ (prefixWord ++ tailWord_4232253).sum := by decide
  have hdescent : baseEnd_4232253 < baseStart_4232253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232270 : List Nat := [4, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_4232270 : Nat := 118140960795 + 4232270 * 2 ^ 59
def prefixEnd_4232270 : Nat := 4983230072969 + 3 ^ 40 * 4232270 * 2
def baseEnd_4232270 : Nat := 2173188769604261457861151

theorem tailTrace_4232270 : CollatzResearch.WordTrace tailWord_4232270 prefixEnd_4232270 2173188769604261457861151 := by
  unfold tailWord_4232270
  simp only [CollatzResearch.WordTrace]
  refine ⟨19295446047152009876866783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102909045584810719343289509 19295446047152009876866783)
  ·
    refine ⟨28943169070728014815300175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19295446047152009876866783 28943169070728014815300175)
    ·
      refine ⟨43414753606092022222950263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28943169070728014815300175 43414753606092022222950263)
      ·
        refine ⟨65122130409138033334425395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43414753606092022222950263 65122130409138033334425395)
        ·
          refine ⟨97683195613707050001638093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65122130409138033334425395 97683195613707050001638093)
          ·
            refine ⟨36631198355140143750614285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97683195613707050001638093 36631198355140143750614285)
            ·
              refine ⟨13736699383177553906480357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36631198355140143750614285 13736699383177553906480357)
              ·
                refine ⟨2575631134345791357465067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13736699383177553906480357 2575631134345791357465067)
                ·
                  refine ⟨3863446701518687036197601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575631134345791357465067 3863446701518687036197601)
                  ·
                    refine ⟨2897585026139015277148201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3863446701518687036197601 2897585026139015277148201)
                    ·
                      refine ⟨2173188769604261457861151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897585026139015277148201 2173188769604261457861151)
                      ·
                        rfl

theorem cell23_4232270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_4232270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232270 prefixEnd_4232270 := by exact prefixLift 4232270
  have htrace : WordTrace (prefixWord ++ tailWord_4232270) baseStart_4232270 baseEnd_4232270 := by
    simpa [prefixWord, tailWord_4232270, baseEnd_4232270] using wordTrace_append hprefix tailTrace_4232270
  have hstable : (prefixWord ++ tailWord_4232270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232270).length < 2 ^ (prefixWord ++ tailWord_4232270).sum := by decide
  have hdescent : baseEnd_4232270 < baseStart_4232270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232339 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4]
def baseStart_4232339 : Nat := 118140960795 + 4232339 * 2 ^ 59
def prefixEnd_4232339 : Nat := 4983230072969 + 3 ^ 40 * 4232339 * 2
def baseEnd_4232339 : Nat := 2173224199769421687898333

theorem tailTrace_4232339 : CollatzResearch.WordTrace tailWord_4232339 prefixEnd_4232339 2173224199769421687898333 := by
  unfold tailWord_4232339
  simp only [CollatzResearch.WordTrace]
  refine ⟨154366085013966103799196071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102910723342644069199464047 154366085013966103799196071)
  ·
    refine ⟨231549127520949155698794107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154366085013966103799196071 231549127520949155698794107)
    ·
      refine ⟨347323691281423733548191161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231549127520949155698794107 347323691281423733548191161)
      ·
        refine ⟨260492768461067800161143371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347323691281423733548191161 260492768461067800161143371)
        ·
          refine ⟨390739152691601700241715057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260492768461067800161143371 390739152691601700241715057)
          ·
            refine ⟨293054364518701275181286293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390739152691601700241715057 293054364518701275181286293)
            ·
              refine ⟨13736923336814122274122795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 293054364518701275181286293 13736923336814122274122795)
              ·
                refine ⟨20605385005221183411184193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13736923336814122274122795 20605385005221183411184193)
                ·
                  refine ⟨15454038753915887558388145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20605385005221183411184193 15454038753915887558388145)
                  ·
                    refine ⟨11590529065436915668791109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15454038753915887558388145 11590529065436915668791109)
                    ·
                      refine ⟨2173224199769421687898333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11590529065436915668791109 2173224199769421687898333)
                      ·
                        rfl

theorem cell23_4232339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_4232339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232339 prefixEnd_4232339 := by exact prefixLift 4232339
  have htrace : WordTrace (prefixWord ++ tailWord_4232339) baseStart_4232339 baseEnd_4232339 := by
    simpa [prefixWord, tailWord_4232339, baseEnd_4232339] using wordTrace_append hprefix tailTrace_4232339
  have hstable : (prefixWord ++ tailWord_4232339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232339).length < 2 ^ (prefixWord ++ tailWord_4232339).sum := by decide
  have hdescent : baseEnd_4232339 < baseStart_4232339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232343 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 1, 4, 2]
def baseStart_4232343 : Nat := 118140960795 + 4232343 * 2 ^ 59
def prefixEnd_4232343 : Nat := 4983230072969 + 3 ^ 40 * 4232343 * 2
def baseEnd_4232343 : Nat := 2173226253692039672248315

theorem tailTrace_4232343 : CollatzResearch.WordTrace tailWord_4232343 prefixEnd_4232343 2173226253692039672248315 := by
  unfold tailWord_4232343
  simp only [CollatzResearch.WordTrace]
  refine ⟨154366230905951612482341683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102910820603967741654894455 154366230905951612482341683)
  ·
    refine ⟨231549346358927418723512525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154366230905951612482341683 231549346358927418723512525)
    ·
      refine ⟨86831004884597782021317197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231549346358927418723512525 86831004884597782021317197)
      ·
        refine ⟨32561626831724168257993949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86831004884597782021317197 32561626831724168257993949)
        ·
          refine ⟨12210610061896563096747731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32561626831724168257993949 12210610061896563096747731)
          ·
            refine ⟨18315915092844844645121597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12210610061896563096747731 18315915092844844645121597)
            ·
              refine ⟨6868468159816816741920599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18315915092844844645121597 6868468159816816741920599)
              ·
                refine ⟨10302702239725225112880899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6868468159816816741920599 10302702239725225112880899)
                ·
                  refine ⟨15454053359587837669321349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10302702239725225112880899 15454053359587837669321349)
                  ·
                    refine ⟨2897635004922719562997753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15454053359587837669321349 2897635004922719562997753)
                    ·
                      refine ⟨2173226253692039672248315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897635004922719562997753 2173226253692039672248315)
                      ·
                        rfl

theorem cell23_4232343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_4232343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232343 prefixEnd_4232343 := by exact prefixLift 4232343
  have htrace : WordTrace (prefixWord ++ tailWord_4232343) baseStart_4232343 baseEnd_4232343 := by
    simpa [prefixWord, tailWord_4232343, baseEnd_4232343] using wordTrace_append hprefix tailTrace_4232343
  have hstable : (prefixWord ++ tailWord_4232343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232343).length < 2 ^ (prefixWord ++ tailWord_4232343).sum := by decide
  have hdescent : baseEnd_4232343 < baseStart_4232343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232349 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 7]
def baseStart_4232349 : Nat := 118140960795 + 4232349 * 2 ^ 59
def prefixEnd_4232349 : Nat := 4983230072969 + 3 ^ 40 * 4232349 * 2
def baseEnd_4232349 : Nat := 241469926063996294308143

theorem tailTrace_4232349 : CollatzResearch.WordTrace tailWord_4232349 prefixEnd_4232349 241469926063996294308143 := by
  unfold tailWord_4232349
  simp only [CollatzResearch.WordTrace]
  refine ⟨154366449743929875507060101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102910966495953250338040067 154366449743929875507060101)
  ·
    refine ⟨28943709326986851657573769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154366449743929875507060101 28943709326986851657573769)
    ·
      refine ⟨21707781995240138743180327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28943709326986851657573769 21707781995240138743180327)
      ·
        refine ⟨32561672992860208114770491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21707781995240138743180327 32561672992860208114770491)
        ·
          refine ⟨48842509489290312172155737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32561672992860208114770491 48842509489290312172155737)
          ·
            refine ⟨36631882116967734129116803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48842509489290312172155737 36631882116967734129116803)
            ·
              refine ⟨54947823175451601193675205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36631882116967734129116803 54947823175451601193675205)
              ·
                refine ⟨10302716845397175223814101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54947823175451601193675205 10302716845397175223814101)
                ·
                  refine ⟨241469926063996294308143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10302716845397175223814101 241469926063996294308143)
                  ·
                    rfl

theorem cell23_4232349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_4232349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232349 prefixEnd_4232349 := by exact prefixLift 4232349
  have htrace : WordTrace (prefixWord ++ tailWord_4232349) baseStart_4232349 baseEnd_4232349 := by
    simpa [prefixWord, tailWord_4232349, baseEnd_4232349] using wordTrace_append hprefix tailTrace_4232349
  have hstable : (prefixWord ++ tailWord_4232349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232349).length < 2 ^ (prefixWord ++ tailWord_4232349).sum := by decide
  have hdescent : baseEnd_4232349 < baseStart_4232349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232399 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_4232399 : Nat := 118140960795 + 4232399 * 2 ^ 59
def prefixEnd_4232399 : Nat := 4983230072969 + 3 ^ 40 * 4232399 * 2
def baseEnd_4232399 : Nat := 2173255008608691453148057

theorem tailTrace_4232399 : CollatzResearch.WordTrace tailWord_4232399 prefixEnd_4232399 2173255008608691453148057 := by
  unfold tailWord_4232399
  simp only [CollatzResearch.WordTrace]
  refine ⟨154368273393748734046380251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102912182262499156030920167 154368273393748734046380251)
  ·
    refine ⟨231552410090623101069570377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154368273393748734046380251 231552410090623101069570377)
    ·
      refine ⟨173664307567967325802177783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231552410090623101069570377 173664307567967325802177783)
      ·
        refine ⟨260496461351950988703266675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173664307567967325802177783 260496461351950988703266675)
        ·
          refine ⟨390744692027926483054900013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260496461351950988703266675 390744692027926483054900013)
          ·
            refine ⟨146529259510472431145587505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 390744692027926483054900013 146529259510472431145587505)
            ·
              refine ⟨109896944632854323359190629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146529259510472431145587505 109896944632854323359190629)
              ·
                refine ⟨20605677118660185629848243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109896944632854323359190629 20605677118660185629848243)
                ·
                  refine ⟨30908515677990278444772365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20605677118660185629848243 30908515677990278444772365)
                  ·
                    refine ⟨11590693379246354416789637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30908515677990278444772365 11590693379246354416789637)
                    ·
                      refine ⟨2173255008608691453148057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11590693379246354416789637 2173255008608691453148057)
                      ·
                        rfl

theorem cell23_4232399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_4232399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232399 prefixEnd_4232399 := by exact prefixLift 4232399
  have htrace : WordTrace (prefixWord ++ tailWord_4232399) baseStart_4232399 baseEnd_4232399 := by
    simpa [prefixWord, tailWord_4232399, baseEnd_4232399] using wordTrace_append hprefix tailTrace_4232399
  have hstable : (prefixWord ++ tailWord_4232399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232399).length < 2 ^ (prefixWord ++ tailWord_4232399).sum := by decide
  have hdescent : baseEnd_4232399 < baseStart_4232399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232416 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_4232416 : Nat := 118140960795 + 4232416 * 2 ^ 59
def prefixEnd_4232416 : Nat := 4983230072969 + 3 ^ 40 * 4232416 * 2
def baseEnd_4232416 : Nat := 2173263737779817886635479

theorem tailTrace_4232416 : CollatzResearch.WordTrace tailWord_4232416 prefixEnd_4232416 2173263737779817886635479 := by
  unfold tailWord_4232416
  simp only [CollatzResearch.WordTrace]
  refine ⟨77184446717343572974874551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102912595623124763966499401 77184446717343572974874551)
  ·
    refine ⟨115776670076015359462311827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77184446717343572974874551 115776670076015359462311827)
    ·
      refine ⟨173665005114023039193467741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115776670076015359462311827 173665005114023039193467741)
      ·
        refine ⟨65124376917758639697550403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173665005114023039193467741 65124376917758639697550403)
        ·
          refine ⟨97686565376637959546325605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65124376917758639697550403 97686565376637959546325605)
          ·
            refine ⟨18316231008119617414936051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97686565376637959546325605 18316231008119617414936051)
            ·
              refine ⟨27474346512179426122404077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18316231008119617414936051 27474346512179426122404077)
              ·
                refine ⟨10302879942067284795901529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27474346512179426122404077 10302879942067284795901529)
                ·
                  refine ⟨7727159956550463596926147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10302879942067284795901529 7727159956550463596926147)
                  ·
                    refine ⟨11590739934825695395389221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7727159956550463596926147 11590739934825695395389221)
                    ·
                      refine ⟨2173263737779817886635479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11590739934825695395389221 2173263737779817886635479)
                      ·
                        rfl

theorem cell23_4232416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_4232416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232416 prefixEnd_4232416 := by exact prefixLift 4232416
  have htrace : WordTrace (prefixWord ++ tailWord_4232416) baseStart_4232416 baseEnd_4232416 := by
    simpa [prefixWord, tailWord_4232416, baseEnd_4232416] using wordTrace_append hprefix tailTrace_4232416
  have hstable : (prefixWord ++ tailWord_4232416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232416).length < 2 ^ (prefixWord ++ tailWord_4232416).sum := by decide
  have hdescent : baseEnd_4232416 < baseStart_4232416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232477 : List Nat := [1, 4, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_4232477 : Nat := 118140960795 + 4232477 * 2 ^ 59
def prefixEnd_4232477 : Nat := 4983230072969 + 3 ^ 40 * 4232477 * 2
def baseEnd_4232477 : Nat := 724431686699914049324233

theorem tailTrace_4232477 : CollatzResearch.WordTrace tailWord_4232477 prefixEnd_4232477 724431686699914049324233 := by
  unfold tailWord_4232477
  simp only [CollatzResearch.WordTrace]
  refine ⟨154371118287466153367719685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102914078858310768911813123 154371118287466153367719685)
  ·
    refine ⟨28944584678899903756447441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154371118287466153367719685 28944584678899903756447441)
    ·
      refine ⟨21708438509174927817335581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28944584678899903756447441 21708438509174927817335581)
      ·
        refine ⟨8140664440940597931500843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21708438509174927817335581 8140664440940597931500843)
        ·
          refine ⟨12210996661410896897251265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140664440940597931500843 12210996661410896897251265)
          ·
            refine ⟨9158247496058172672938449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12210996661410896897251265 9158247496058172672938449)
            ·
              refine ⟨6868685622043629504703837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9158247496058172672938449 6868685622043629504703837)
              ·
                refine ⟨2575757108266361064263939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6868685622043629504703837 2575757108266361064263939)
                ·
                  refine ⟨3863635662399541596395909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575757108266361064263939 3863635662399541596395909)
                  ·
                    refine ⟨724431686699914049324233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3863635662399541596395909 724431686699914049324233)
                    ·
                      rfl

theorem cell23_4232477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_4232477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232477 prefixEnd_4232477 := by exact prefixLift 4232477
  have htrace : WordTrace (prefixWord ++ tailWord_4232477) baseStart_4232477 baseEnd_4232477 := by
    simpa [prefixWord, tailWord_4232477, baseEnd_4232477] using wordTrace_append hprefix tailTrace_4232477
  have hstable : (prefixWord ++ tailWord_4232477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232477).length < 2 ^ (prefixWord ++ tailWord_4232477).sum := by decide
  have hdescent : baseEnd_4232477 < baseStart_4232477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232490 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 6]
def baseStart_4232490 : Nat := 118140960795 + 4232490 * 2 ^ 59
def prefixEnd_4232490 : Nat := 4983230072969 + 3 ^ 40 * 4232490 * 2
def baseEnd_4232490 : Nat := 241477970594250066345571

theorem tailTrace_4232490 : CollatzResearch.WordTrace tailWord_4232490 prefixEnd_4232490 241477970594250066345571 := by
  unfold tailWord_4232490
  simp only [CollatzResearch.WordTrace]
  refine ⟨38592898109104764146985731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102914394957612704391961949 38592898109104764146985731)
  ·
    refine ⟨57889347163657146220478597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38592898109104764146985731 57889347163657146220478597)
    ·
      refine ⟨10854252593185714916339737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57889347163657146220478597 10854252593185714916339737)
      ·
        refine ⟨8140689444889286187254803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10854252593185714916339737 8140689444889286187254803)
        ·
          refine ⟨12211034167333929280882205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140689444889286187254803 12211034167333929280882205)
          ·
            refine ⟨4579137812750223480330827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12211034167333929280882205 4579137812750223480330827)
            ·
              refine ⟨6868706719125335220496241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4579137812750223480330827 6868706719125335220496241)
              ·
                refine ⟨5151530039344001415372181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6868706719125335220496241 5151530039344001415372181)
                ·
                  refine ⟨241477970594250066345571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5151530039344001415372181 241477970594250066345571)
                  ·
                    rfl

theorem cell23_4232490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_4232490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232490 prefixEnd_4232490 := by exact prefixLift 4232490
  have htrace : WordTrace (prefixWord ++ tailWord_4232490) baseStart_4232490 baseEnd_4232490 := by
    simpa [prefixWord, tailWord_4232490, baseEnd_4232490] using wordTrace_append hprefix tailTrace_4232490
  have hstable : (prefixWord ++ tailWord_4232490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232490).length < 2 ^ (prefixWord ++ tailWord_4232490).sum := by decide
  have hdescent : baseEnd_4232490 < baseStart_4232490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232493 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4232493 : Nat := 118140960795 + 4232493 * 2 ^ 59
def prefixEnd_4232493 : Nat := 4983230072969 + 3 ^ 40 * 4232493 * 2
def baseEnd_4232493 : Nat := 2173303275790214085372625

theorem tailTrace_4232493 : CollatzResearch.WordTrace tailWord_4232493 prefixEnd_4232493 2173303275790214085372625 := by
  unfold tailWord_4232493
  simp only [CollatzResearch.WordTrace]
  refine ⟨154371701855408188100302133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102914467903605458733534755 154371701855408188100302133)
  ·
    refine ⟨14472347048944517634403325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154371701855408188100302133 14472347048944517634403325)
    ·
      refine ⟨5427130143354194112901247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14472347048944517634403325 5427130143354194112901247)
      ·
        refine ⟨8140695215031291169351871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5427130143354194112901247 8140695215031291169351871)
        ·
          refine ⟨12211042822546936754027807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8140695215031291169351871 12211042822546936754027807)
          ·
            refine ⟨18316564233820405131041711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12211042822546936754027807 18316564233820405131041711)
            ·
              refine ⟨27474846350730607696562567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18316564233820405131041711 27474846350730607696562567)
              ·
                refine ⟨41212269526095911544843851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27474846350730607696562567 41212269526095911544843851)
                ·
                  refine ⟨61818404289143867317265777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41212269526095911544843851 61818404289143867317265777)
                  ·
                    refine ⟨46363803216857900487949333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61818404289143867317265777 46363803216857900487949333)
                    ·
                      refine ⟨2173303275790214085372625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46363803216857900487949333 2173303275790214085372625)
                      ·
                        rfl

theorem cell23_4232493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4232493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232493 prefixEnd_4232493 := by exact prefixLift 4232493
  have htrace : WordTrace (prefixWord ++ tailWord_4232493) baseStart_4232493 baseEnd_4232493 := by
    simpa [prefixWord, tailWord_4232493, baseEnd_4232493] using wordTrace_append hprefix tailTrace_4232493
  have hstable : (prefixWord ++ tailWord_4232493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232493).length < 2 ^ (prefixWord ++ tailWord_4232493).sum := by decide
  have hdescent : baseEnd_4232493 < baseStart_4232493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232526 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_4232526 : Nat := 118140960795 + 4232526 * 2 ^ 59
def prefixEnd_4232526 : Nat := 4983230072969 + 3 ^ 40 * 4232526 * 2
def baseEnd_4232526 : Nat := 2173320220651812456259973

theorem tailTrace_4232526 : CollatzResearch.WordTrace tailWord_4232526 prefixEnd_4232526 2173320220651812456259973 := by
  unfold tailWord_4232526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19296613183036079342031679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102915270309525756490835621 19296613183036079342031679)
  ·
    refine ⟨28944919774554119013047519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19296613183036079342031679 28944919774554119013047519)
    ·
      refine ⟨43417379661831178519571279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28944919774554119013047519 43417379661831178519571279)
      ·
        refine ⟨65126069492746767779356919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43417379661831178519571279 65126069492746767779356919)
        ·
          refine ⟨97689104239120151669035379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65126069492746767779356919 97689104239120151669035379)
          ·
            refine ⟨146533656358680227503553069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97689104239120151669035379 146533656358680227503553069)
            ·
              refine ⟨54950121134505085313832401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146533656358680227503553069 54950121134505085313832401)
              ·
                refine ⟨41212590850878813985374301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54950121134505085313832401 41212590850878813985374301)
                ·
                  refine ⟨15454721569079555244515363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41212590850878813985374301 15454721569079555244515363)
                  ·
                    refine ⟨23182082353619332866773045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15454721569079555244515363 23182082353619332866773045)
                    ·
                      refine ⟨2173320220651812456259973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23182082353619332866773045 2173320220651812456259973)
                      ·
                        rfl

theorem cell23_4232526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_4232526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232526 prefixEnd_4232526 := by exact prefixLift 4232526
  have htrace : WordTrace (prefixWord ++ tailWord_4232526) baseStart_4232526 baseEnd_4232526 := by
    simpa [prefixWord, tailWord_4232526, baseEnd_4232526] using wordTrace_append hprefix tailTrace_4232526
  have hstable : (prefixWord ++ tailWord_4232526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232526).length < 2 ^ (prefixWord ++ tailWord_4232526).sum := by decide
  have hdescent : baseEnd_4232526 < baseStart_4232526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232533 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_4232533 : Nat := 118140960795 + 4232533 * 2 ^ 59
def prefixEnd_4232533 : Nat := 4983230072969 + 3 ^ 40 * 4232533 * 2
def baseEnd_4232533 : Nat := 724441271672131309624147

theorem tailTrace_4232533 : CollatzResearch.WordTrace tailWord_4232533 prefixEnd_4232533 724441271672131309624147 := by
  unfold tailWord_4232533
  simp only [CollatzResearch.WordTrace]
  refine ⟨154373160775263274931758253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102915440516842183287838835 154373160775263274931758253)
  ·
    refine ⟨57889935290723728099409345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154373160775263274931758253 57889935290723728099409345)
    ·
      refine ⟨43417451468042796074557009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57889935290723728099409345 43417451468042796074557009)
      ·
        refine ⟨32563088601032097055917757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43417451468042796074557009 32563088601032097055917757)
        ·
          refine ⟨12211158225387036395969159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32563088601032097055917757 12211158225387036395969159)
          ·
            refine ⟨18316737338080554593953739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12211158225387036395969159 18316737338080554593953739)
            ·
              refine ⟨27475106007120831890930609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18316737338080554593953739 27475106007120831890930609)
              ·
                refine ⟨20606329505340623918197957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27475106007120831890930609 20606329505340623918197957)
                ·
                  refine ⟨3863686782251366984662117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20606329505340623918197957 3863686782251366984662117)
                  ·
                    refine ⟨724441271672131309624147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3863686782251366984662117 724441271672131309624147)
                    ·
                      rfl

theorem cell23_4232533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_4232533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232533 prefixEnd_4232533 := by exact prefixLift 4232533
  have htrace : WordTrace (prefixWord ++ tailWord_4232533) baseStart_4232533 baseEnd_4232533 := by
    simpa [prefixWord, tailWord_4232533, baseEnd_4232533] using wordTrace_append hprefix tailTrace_4232533
  have hstable : (prefixWord ++ tailWord_4232533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232533).length < 2 ^ (prefixWord ++ tailWord_4232533).sum := by decide
  have hdescent : baseEnd_4232533 < baseStart_4232533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232536 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_4232536 : Nat := 118140960795 + 4232536 * 2 ^ 59
def prefixEnd_4232536 : Nat := 4983230072969 + 3 ^ 40 * 4232536 * 2
def baseEnd_4232536 : Nat := 2173325355458357417134927

theorem tailTrace_4232536 : CollatzResearch.WordTrace tailWord_4232536 prefixEnd_4232536 2173325355458357417134927 := by
  unfold tailWord_4232536
  simp only [CollatzResearch.WordTrace]
  refine ⟨77186635097126203222058731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102915513462834937629411641 77186635097126203222058731)
  ·
    refine ⟨115779952645689304833088097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77186635097126203222058731 115779952645689304833088097)
    ·
      refine ⟨86834964484266978624816073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115779952645689304833088097 86834964484266978624816073)
      ·
        refine ⟨65126223363200233968612055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86834964484266978624816073 65126223363200233968612055)
        ·
          refine ⟨97689335044800350952918083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65126223363200233968612055 97689335044800350952918083)
          ·
            refine ⟨146534002567200526429377125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97689335044800350952918083 146534002567200526429377125)
            ·
              refine ⟨27475125481350098705508211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146534002567200526429377125 27475125481350098705508211)
              ·
                refine ⟨41212688222025148058262317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27475125481350098705508211 41212688222025148058262317)
                ·
                  refine ⟨15454758083259430521848369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41212688222025148058262317 15454758083259430521848369)
                  ·
                    refine ⟨11591068562444572891386277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15454758083259430521848369 11591068562444572891386277)
                    ·
                      refine ⟨2173325355458357417134927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11591068562444572891386277 2173325355458357417134927)
                      ·
                        rfl

theorem cell23_4232536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_4232536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232536 prefixEnd_4232536 := by exact prefixLift 4232536
  have htrace : WordTrace (prefixWord ++ tailWord_4232536) baseStart_4232536 baseEnd_4232536 := by
    simpa [prefixWord, tailWord_4232536, baseEnd_4232536] using wordTrace_append hprefix tailTrace_4232536
  have hstable : (prefixWord ++ tailWord_4232536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232536).length < 2 ^ (prefixWord ++ tailWord_4232536).sum := by decide
  have hdescent : baseEnd_4232536 < baseStart_4232536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232557 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_4232557 : Nat := 118140960795 + 4232557 * 2 ^ 59
def prefixEnd_4232557 : Nat := 4983230072969 + 3 ^ 40 * 4232557 * 2
def baseEnd_4232557 : Nat := 2173336138552101834972331

theorem tailTrace_4232557 : CollatzResearch.WordTrace tailWord_4232557 prefixEnd_4232557 2173336138552101834972331 := by
  unfold tailWord_4232557
  simp only [CollatzResearch.WordTrace]
  refine ⟨154374036127176327030631925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102916024084784218020421283 154374036127176327030631925)
  ·
    refine ⟨14472565886922780659121743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154374036127176327030631925 14472565886922780659121743)
    ·
      refine ⟨21708848830384170988682615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14472565886922780659121743 21708848830384170988682615)
      ·
        refine ⟨32563273245576256483023923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21708848830384170988682615 32563273245576256483023923)
        ·
          refine ⟨48844909868364384724535885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32563273245576256483023923 48844909868364384724535885)
          ·
            refine ⟨18316841200636644271700957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48844909868364384724535885 18316841200636644271700957)
            ·
              refine ⟨6868815450238741601887859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18316841200636644271700957 6868815450238741601887859)
              ·
                refine ⟨10303223175358112402831789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6868815450238741601887859 10303223175358112402831789)
                ·
                  refine ⟨3863708690759292151061921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10303223175358112402831789 3863708690759292151061921)
                  ·
                    refine ⟨2897781518069469113296441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3863708690759292151061921 2897781518069469113296441)
                    ·
                      refine ⟨2173336138552101834972331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897781518069469113296441 2173336138552101834972331)
                      ·
                        rfl

theorem cell23_4232557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_4232557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232557 prefixEnd_4232557 := by exact prefixLift 4232557
  have htrace : WordTrace (prefixWord ++ tailWord_4232557) baseStart_4232557 baseEnd_4232557 := by
    simpa [prefixWord, tailWord_4232557, baseEnd_4232557] using wordTrace_append hprefix tailTrace_4232557
  have hstable : (prefixWord ++ tailWord_4232557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232557).length < 2 ^ (prefixWord ++ tailWord_4232557).sum := by decide
  have hdescent : baseEnd_4232557 < baseStart_4232557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232573 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_4232573 : Nat := 118140960795 + 4232573 * 2 ^ 59
def prefixEnd_4232573 : Nat := 4983230072969 + 3 ^ 40 * 4232573 * 2
def baseEnd_4232573 : Nat := 2173344354242573772372257

theorem tailTrace_4232573 : CollatzResearch.WordTrace tailWord_4232573 prefixEnd_4232573 2173344354242573772372257 := by
  unfold tailWord_4232573
  simp only [CollatzResearch.WordTrace]
  refine ⟨154374619695118361763214373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102916413130078907842142915 154374619695118361763214373)
  ·
    refine ⟨28945241192834692830602695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154374619695118361763214373 28945241192834692830602695)
    ·
      refine ⟨43417861789252039245904043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28945241192834692830602695 43417861789252039245904043)
      ·
        refine ⟨65126792683878058868856065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43417861789252039245904043 65126792683878058868856065)
        ·
          refine ⟨48845094512908544151642049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65126792683878058868856065 48845094512908544151642049)
          ·
            refine ⟨36633820884681408113731537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48845094512908544151642049 36633820884681408113731537)
            ·
              refine ⟨27475365663511056085298653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36633820884681408113731537 27475365663511056085298653)
              ·
                refine ⟨10303262123816646031986995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27475365663511056085298653 10303262123816646031986995)
                ·
                  refine ⟨15454893185724969047980493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10303262123816646031986995 15454893185724969047980493)
                  ·
                    refine ⟨5795584944646863392992685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15454893185724969047980493 5795584944646863392992685)
                    ·
                      refine ⟨2173344354242573772372257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5795584944646863392992685 2173344354242573772372257)
                      ·
                        rfl

theorem cell23_4232573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_4232573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232573 prefixEnd_4232573 := by exact prefixLift 4232573
  have htrace : WordTrace (prefixWord ++ tailWord_4232573) baseStart_4232573 baseEnd_4232573 := by
    simpa [prefixWord, tailWord_4232573, baseEnd_4232573] using wordTrace_append hprefix tailTrace_4232573
  have hstable : (prefixWord ++ tailWord_4232573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232573).length < 2 ^ (prefixWord ++ tailWord_4232573).sum := by decide
  have hdescent : baseEnd_4232573 < baseStart_4232573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232594 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4232594 : Nat := 118140960795 + 4232594 * 2 ^ 59
def prefixEnd_4232594 : Nat := 4983230072969 + 3 ^ 40 * 4232594 * 2
def baseEnd_4232594 : Nat := 2173355137336318190209661

theorem tailTrace_4232594 : CollatzResearch.WordTrace tailWord_4232594 prefixEnd_4232594 2173355137336318190209661 := by
  unfold tailWord_4232594
  simp only [CollatzResearch.WordTrace]
  refine ⟨38593846407010570587432209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102916923752028188233152557 38593846407010570587432209)
  ·
    refine ⟨28945384805257927940574157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38593846407010570587432209 28945384805257927940574157)
    ·
      refine ⟨10854519301971722977715309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28945384805257927940574157 10854519301971722977715309)
      ·
        refine ⟨4070444738239396116643241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10854519301971722977715309 4070444738239396116643241)
        ·
          refine ⟨3052833553679547087482431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070444738239396116643241 3052833553679547087482431)
          ·
            refine ⟨4579250330519320631223647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3052833553679547087482431 4579250330519320631223647)
            ·
              refine ⟨6868875495778980946835471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4579250330519320631223647 6868875495778980946835471)
              ·
                refine ⟨10303313243668471420253207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6868875495778980946835471 10303313243668471420253207)
                ·
                  refine ⟨15454969865502707130379811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10303313243668471420253207 15454969865502707130379811)
                  ·
                    refine ⟨23182454798254060695569717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15454969865502707130379811 23182454798254060695569717)
                    ·
                      refine ⟨2173355137336318190209661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23182454798254060695569717 2173355137336318190209661)
                      ·
                        rfl

theorem cell23_4232594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4232594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232594 prefixEnd_4232594 := by exact prefixLift 4232594
  have htrace : WordTrace (prefixWord ++ tailWord_4232594) baseStart_4232594 baseEnd_4232594 := by
    simpa [prefixWord, tailWord_4232594, baseEnd_4232594] using wordTrace_append hprefix tailTrace_4232594
  have hstable : (prefixWord ++ tailWord_4232594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232594).length < 2 ^ (prefixWord ++ tailWord_4232594).sum := by decide
  have hdescent : baseEnd_4232594 < baseStart_4232594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232607 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 3]
def baseStart_4232607 : Nat := 118140960795 + 4232607 * 2 ^ 59
def prefixEnd_4232607 : Nat := 4983230072969 + 3 ^ 40 * 4232607 * 2
def baseEnd_4232607 : Nat := 2173361812584826639347101

theorem tailTrace_4232607 : CollatzResearch.WordTrace tailWord_4232607 prefixEnd_4232607 2173361812584826639347101 := by
  unfold tailWord_4232607
  simp only [CollatzResearch.WordTrace]
  refine ⟨154375859776995185569952075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102917239851330123713301383 154375859776995185569952075)
  ·
    refine ⟨231563789665492778354928113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154375859776995185569952075 231563789665492778354928113)
    ·
      refine ⟨173672842249119583766196085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231563789665492778354928113 173672842249119583766196085)
      ·
        refine ⟨16281828960854960978080883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173672842249119583766196085 16281828960854960978080883)
        ·
          refine ⟨24422743441282441467121325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16281828960854960978080883 24422743441282441467121325)
          ·
            refine ⟨9158528790480915550170497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24422743441282441467121325 9158528790480915550170497)
            ·
              refine ⟨6868896592860686662627873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9158528790480915550170497 6868896592860686662627873)
              ·
                refine ⟨5151672444645514996970905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6868896592860686662627873 5151672444645514996970905)
                ·
                  refine ⟨3863754333484136247728179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5151672444645514996970905 3863754333484136247728179)
                  ·
                    refine ⟨5795631500226204371592269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3863754333484136247728179 5795631500226204371592269)
                    ·
                      refine ⟨2173361812584826639347101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5795631500226204371592269 2173361812584826639347101)
                      ·
                        rfl

theorem cell23_4232607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_4232607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232607 prefixEnd_4232607 := by exact prefixLift 4232607
  have htrace : WordTrace (prefixWord ++ tailWord_4232607) baseStart_4232607 baseEnd_4232607 := by
    simpa [prefixWord, tailWord_4232607, baseEnd_4232607] using wordTrace_append hprefix tailTrace_4232607
  have hstable : (prefixWord ++ tailWord_4232607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232607).length < 2 ^ (prefixWord ++ tailWord_4232607).sum := by decide
  have hdescent : baseEnd_4232607 < baseStart_4232607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232642 : List Nat := [3, 5, 2, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4232642 : Nat := 118140960795 + 4232642 * 2 ^ 59
def prefixEnd_4232642 : Nat := 4983230072969 + 3 ^ 40 * 4232642 * 2
def baseEnd_4232642 : Nat := 2173379784407734002409441

theorem tailTrace_4232642 : CollatzResearch.WordTrace tailWord_4232642 prefixEnd_4232642 2173379784407734002409441 := by
  unfold tailWord_4232642
  simp only [CollatzResearch.WordTrace]
  refine ⟨38594284082967096636869045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102918090887912257698317453 38594284082967096636869045)
  ·
    refine ⟨3618214132778165309706473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38594284082967096636869045 3618214132778165309706473)
    ·
      refine ⟨2713660599583623982279855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3618214132778165309706473 2713660599583623982279855)
      ·
        refine ⟨4070490899375435973419783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713660599583623982279855 4070490899375435973419783)
        ·
          refine ⟨6105736349063153960129675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070490899375435973419783 6105736349063153960129675)
          ·
            refine ⟨9158604523594730940194513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6105736349063153960129675 9158604523594730940194513)
            ·
              refine ⟨6868953392696048205145885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9158604523594730940194513 6868953392696048205145885)
              ·
                refine ⟨2575857522261018076929707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6868953392696048205145885 2575857522261018076929707)
                ·
                  refine ⟨3863786283391527115394561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575857522261018076929707 3863786283391527115394561)
                  ·
                    refine ⟨2897839712543645336545921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3863786283391527115394561 2897839712543645336545921)
                    ·
                      refine ⟨2173379784407734002409441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897839712543645336545921 2173379784407734002409441)
                      ·
                        rfl

theorem cell23_4232642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4232642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232642 prefixEnd_4232642 := by exact prefixLift 4232642
  have htrace : WordTrace (prefixWord ++ tailWord_4232642) baseStart_4232642 baseEnd_4232642 := by
    simpa [prefixWord, tailWord_4232642, baseEnd_4232642] using wordTrace_append hprefix tailTrace_4232642
  have hstable : (prefixWord ++ tailWord_4232642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232642).length < 2 ^ (prefixWord ++ tailWord_4232642).sum := by decide
  have hdescent : baseEnd_4232642 < baseStart_4232642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232757 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_4232757 : Nat := 118140960795 + 4232757 * 2 ^ 59
def prefixEnd_4232757 : Nat := 4983230072969 + 3 ^ 40 * 4232757 * 2
def baseEnd_4232757 : Nat := 2173438834683001052471411

theorem tailTrace_4232757 : CollatzResearch.WordTrace tailWord_4232757 prefixEnd_4232757 2173438834683001052471411 := by
  unfold tailWord_4232757
  simp only [CollatzResearch.WordTrace]
  refine ⟨154381330726451761187912525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102920887150967840791941683 154381330726451761187912525)
  ·
    refine ⟨57892999022419410445467197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154381330726451761187912525 57892999022419410445467197)
    ·
      refine ⟨21709874633407278917050199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57892999022419410445467197 21709874633407278917050199)
      ·
        refine ⟨32564811950110918375575299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21709874633407278917050199 32564811950110918375575299)
        ·
          refine ⟨48847217925166377563362949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32564811950110918375575299 48847217925166377563362949)
          ·
            refine ⟨9158853360968695793130553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48847217925166377563362949 9158853360968695793130553)
            ·
              refine ⟨6869140020726521844847915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9158853360968695793130553 6869140020726521844847915)
              ·
                refine ⟨10303710031089782767271873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6869140020726521844847915 10303710031089782767271873)
                ·
                  refine ⟨7727782523317337075453905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10303710031089782767271873 7727782523317337075453905)
                  ·
                    refine ⟨5795836892488002806590429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7727782523317337075453905 5795836892488002806590429)
                    ·
                      refine ⟨2173438834683001052471411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5795836892488002806590429 2173438834683001052471411)
                      ·
                        rfl

theorem cell23_4232757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_4232757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232757 prefixEnd_4232757 := by exact prefixLift 4232757
  have htrace : WordTrace (prefixWord ++ tailWord_4232757) baseStart_4232757 baseEnd_4232757 := by
    simpa [prefixWord, tailWord_4232757, baseEnd_4232757] using wordTrace_append hprefix tailTrace_4232757
  have hstable : (prefixWord ++ tailWord_4232757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232757).length < 2 ^ (prefixWord ++ tailWord_4232757).sum := by decide
  have hdescent : baseEnd_4232757 < baseStart_4232757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232781 : List Nat := [1, 6, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4232781 : Nat := 118140960795 + 4232781 * 2 ^ 59
def prefixEnd_4232781 : Nat := 4983230072969 + 3 ^ 40 * 4232781 * 2
def baseEnd_4232781 : Nat := 724483719406236319523767

theorem tailTrace_4232781 : CollatzResearch.WordTrace tailWord_4232781 prefixEnd_4232781 724483719406236319523767 := by
  unfold tailWord_4232781
  simp only [CollatzResearch.WordTrace]
  refine ⟨154382206078364813286786197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102921470718909875524524131 154382206078364813286786197)
  ·
    refine ⟨7236665909923350622818103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154382206078364813286786197 7236665909923350622818103)
    ·
      refine ⟨10854998864885025934227155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7236665909923350622818103 10854998864885025934227155)
      ·
        refine ⟨16282498297327538901340733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10854998864885025934227155 16282498297327538901340733)
        ·
          refine ⟨6105936861497827088002775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16282498297327538901340733 6105936861497827088002775)
          ·
            refine ⟨9158905292246740632004163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6105936861497827088002775 9158905292246740632004163)
            ·
              refine ⟨13738357938370110948006245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9158905292246740632004163 13738357938370110948006245)
              ·
                refine ⟨2575942113444395802751171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13738357938370110948006245 2575942113444395802751171)
                ·
                  refine ⟨3863913170166593704126757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575942113444395802751171 3863913170166593704126757)
                  ·
                    refine ⟨724483719406236319523767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3863913170166593704126757 724483719406236319523767)
                    ·
                      rfl

theorem cell23_4232781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4232781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232781 prefixEnd_4232781 := by exact prefixLift 4232781
  have htrace : WordTrace (prefixWord ++ tailWord_4232781) baseStart_4232781 baseEnd_4232781 := by
    simpa [prefixWord, tailWord_4232781, baseEnd_4232781] using wordTrace_append hprefix tailTrace_4232781
  have hstable : (prefixWord ++ tailWord_4232781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232781).length < 2 ^ (prefixWord ++ tailWord_4232781).sum := by decide
  have hdescent : baseEnd_4232781 < baseStart_4232781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232814 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_4232814 : Nat := 118140960795 + 4232814 * 2 ^ 59
def prefixEnd_4232814 : Nat := 4983230072969 + 3 ^ 40 * 4232814 * 2
def baseEnd_4232814 : Nat := 2173468103080307329458649

theorem tailTrace_4232814 : CollatzResearch.WordTrace tailWord_4232814 prefixEnd_4232814 2173468103080307329458649 := by
  unfold tailWord_4232814
  simp only [CollatzResearch.WordTrace]
  refine ⟨19297926210905657490342187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102922273124830173281824997 19297926210905657490342187)
  ·
    refine ⟨28946889316358486235513281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19297926210905657490342187 28946889316358486235513281)
    ·
      refine ⟨21710166987268864676634961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28946889316358486235513281 21710166987268864676634961)
      ·
        refine ⟨16282625240451648507476221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21710166987268864676634961 16282625240451648507476221)
        ·
          refine ⟨6105984465169368190303583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16282625240451648507476221 6105984465169368190303583)
          ·
            refine ⟨9158976697754052285455375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6105984465169368190303583 9158976697754052285455375)
            ·
              refine ⟨13738465046631078428183063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9158976697754052285455375 13738465046631078428183063)
              ·
                refine ⟨20607697569946617642274595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13738465046631078428183063 20607697569946617642274595)
                ·
                  refine ⟨30911546354919926463411893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20607697569946617642274595 30911546354919926463411893)
                  ·
                    refine ⟨2897957470773743105944865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30911546354919926463411893 2897957470773743105944865)
                    ·
                      refine ⟨2173468103080307329458649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897957470773743105944865 2173468103080307329458649)
                      ·
                        rfl

theorem cell23_4232814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_4232814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232814 prefixEnd_4232814 := by exact prefixLift 4232814
  have htrace : WordTrace (prefixWord ++ tailWord_4232814) baseStart_4232814 baseEnd_4232814 := by
    simpa [prefixWord, tailWord_4232814, baseEnd_4232814] using wordTrace_append hprefix tailTrace_4232814
  have hstable : (prefixWord ++ tailWord_4232814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232814).length < 2 ^ (prefixWord ++ tailWord_4232814).sum := by decide
  have hdescent : baseEnd_4232814 < baseStart_4232814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232821 : List Nat := [1, 3, 4, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4232821 : Nat := 118140960795 + 4232821 * 2 ^ 59
def prefixEnd_4232821 : Nat := 4983230072969 + 3 ^ 40 * 4232821 * 2
def baseEnd_4232821 : Nat := 2173471697444888802071117

theorem tailTrace_4232821 : CollatzResearch.WordTrace tailWord_4232821 prefixEnd_4232821 2173471697444888802071117 := by
  unfold tailWord_4232821
  simp only [CollatzResearch.WordTrace]
  refine ⟨154383664998219900118242317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102922443332146600078828211 154383664998219900118242317)
  ·
    refine ⟨57893874374332462544340869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154383664998219900118242317 57893874374332462544340869)
    ·
      refine ⟨10855101445187336727063913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57893874374332462544340869 10855101445187336727063913)
      ·
        refine ⟨8141326083890502545297935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10855101445187336727063913 8141326083890502545297935)
        ·
          refine ⟨12211989125835753817946903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8141326083890502545297935 12211989125835753817946903)
          ·
            refine ⟨18317983688753630726920355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12211989125835753817946903 18317983688753630726920355)
            ·
              refine ⟨27476975533130446090380533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18317983688753630726920355 27476975533130446090380533)
              ·
                refine ⟨2575966456230979320973175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27476975533130446090380533 2575966456230979320973175)
                ·
                  refine ⟨3863949684346468981459763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575966456230979320973175 3863949684346468981459763)
                  ·
                    refine ⟨5795924526519703472189645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3863949684346468981459763 5795924526519703472189645)
                    ·
                      refine ⟨2173471697444888802071117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5795924526519703472189645 2173471697444888802071117)
                      ·
                        rfl

theorem cell23_4232821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4232821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232821 prefixEnd_4232821 := by exact prefixLift 4232821
  have htrace : WordTrace (prefixWord ++ tailWord_4232821) baseStart_4232821 baseEnd_4232821 := by
    simpa [prefixWord, tailWord_4232821, baseEnd_4232821] using wordTrace_append hprefix tailTrace_4232821
  have hstable : (prefixWord ++ tailWord_4232821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232821).length < 2 ^ (prefixWord ++ tailWord_4232821).sum := by decide
  have hdescent : baseEnd_4232821 < baseStart_4232821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232823 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_4232823 : Nat := 118140960795 + 4232823 * 2 ^ 59
def prefixEnd_4232823 : Nat := 4983230072969 + 3 ^ 40 * 4232823 * 2
def baseEnd_4232823 : Nat := 2173472724406197794246107

theorem tailTrace_4232823 : CollatzResearch.WordTrace tailWord_4232823 prefixEnd_4232823 2173472724406197794246107 := by
  unfold tailWord_4232823
  simp only [CollatzResearch.WordTrace]
  refine ⟨154383737944212654459815123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102922491962808436306543415 154383737944212654459815123)
  ·
    refine ⟨231575606916318981689722685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154383737944212654459815123 231575606916318981689722685)
    ·
      refine ⟨86840852593619618133646007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231575606916318981689722685 86840852593619618133646007)
      ·
        refine ⟨130261278890429427200469011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86840852593619618133646007 130261278890429427200469011)
        ·
          refine ⟨195391918335644140800703517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130261278890429427200469011 195391918335644140800703517)
          ·
            refine ⟨73271969375866552800263819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195391918335644140800703517 73271969375866552800263819)
            ·
              refine ⟨109907954063799829200395729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73271969375866552800263819 109907954063799829200395729)
              ·
                refine ⟨82430965547849871900296797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109907954063799829200395729 82430965547849871900296797)
                ·
                  refine ⟨30911612080443701962611299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82430965547849871900296797 30911612080443701962611299)
                  ·
                    refine ⟨46367418120665552943916949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30911612080443701962611299 46367418120665552943916949)
                    ·
                      refine ⟨2173472724406197794246107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46367418120665552943916949 2173472724406197794246107)
                      ·
                        rfl

theorem cell23_4232823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_4232823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232823 prefixEnd_4232823 := by exact prefixLift 4232823
  have htrace : WordTrace (prefixWord ++ tailWord_4232823) baseStart_4232823 baseEnd_4232823 := by
    simpa [prefixWord, tailWord_4232823, baseEnd_4232823] using wordTrace_append hprefix tailTrace_4232823
  have hstable : (prefixWord ++ tailWord_4232823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232823).length < 2 ^ (prefixWord ++ tailWord_4232823).sum := by decide
  have hdescent : baseEnd_4232823 < baseStart_4232823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232827 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 5, 2, 2]
def baseStart_4232827 : Nat := 118140960795 + 4232827 * 2 ^ 59
def prefixEnd_4232827 : Nat := 4983230072969 + 3 ^ 40 * 4232827 * 2
def baseEnd_4232827 : Nat := 2173474778328815778596089

theorem tailTrace_4232827 : CollatzResearch.WordTrace tailWord_4232827 prefixEnd_4232827 2173474778328815778596089 := by
  unfold tailWord_4232827
  simp only [CollatzResearch.WordTrace]
  refine ⟨154383883836198163142960735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102922589224132108761973823 154383883836198163142960735)
  ·
    refine ⟨231575825754297244714441103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154383883836198163142960735 231575825754297244714441103)
    ·
      refine ⟨347363738631445867071661655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231575825754297244714441103 347363738631445867071661655)
      ·
        refine ⟨521045607947168800607492483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347363738631445867071661655 521045607947168800607492483)
        ·
          refine ⟨781568411920753200911238725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521045607947168800607492483 781568411920753200911238725)
          ·
            refine ⟨146544077235141225170857261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 781568411920753200911238725 146544077235141225170857261)
            ·
              refine ⟨54954028963177959439071473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146544077235141225170857261 54954028963177959439071473)
              ·
                refine ⟨41215521722383469579303605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54954028963177959439071473 41215521722383469579303605)
                ·
                  refine ⟨3863955161473450273059713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41215521722383469579303605 3863955161473450273059713)
                  ·
                    refine ⟨2897966371105087704794785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3863955161473450273059713 2897966371105087704794785)
                    ·
                      refine ⟨2173474778328815778596089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897966371105087704794785 2173474778328815778596089)
                      ·
                        rfl

theorem cell23_4232827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 2, 2].length) (baseStart_4232827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232827 prefixEnd_4232827 := by exact prefixLift 4232827
  have htrace : WordTrace (prefixWord ++ tailWord_4232827) baseStart_4232827 baseEnd_4232827 := by
    simpa [prefixWord, tailWord_4232827, baseEnd_4232827] using wordTrace_append hprefix tailTrace_4232827
  have hstable : (prefixWord ++ tailWord_4232827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232827).length < 2 ^ (prefixWord ++ tailWord_4232827).sum := by decide
  have hdescent : baseEnd_4232827 < baseStart_4232827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232844 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 3, 2, 2]
def baseStart_4232844 : Nat := 118140960795 + 4232844 * 2 ^ 59
def prefixEnd_4232844 : Nat := 4983230072969 + 3 ^ 40 * 4232844 * 2
def baseEnd_4232844 : Nat := 2173483507499942212083511

theorem tailTrace_4232844 : CollatzResearch.WordTrace tailWord_4232844 prefixEnd_4232844 2173483507499942212083511 := by
  unfold tailWord_4232844
  simp only [CollatzResearch.WordTrace]
  refine ⟨77192251938568287523164793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102923002584757716697553057 77192251938568287523164793)
  ·
    refine ⟨57894188953926215642373595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77192251938568287523164793 57894188953926215642373595)
    ·
      refine ⟨86841283430889323463560393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57894188953926215642373595 86841283430889323463560393)
      ·
        refine ⟨65130962573166992597670295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86841283430889323463560393 65130962573166992597670295)
        ·
          refine ⟨97696443859750488896505443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65130962573166992597670295 97696443859750488896505443)
          ·
            refine ⟨146544665789625733344758165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97696443859750488896505443 146544665789625733344758165)
            ·
              refine ⟨6869281208888706250535539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146544665789625733344758165 6869281208888706250535539)
              ·
                refine ⟨10303921813333059375803309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6869281208888706250535539 10303921813333059375803309)
                ·
                  refine ⟨3863970679999897265926241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10303921813333059375803309 3863970679999897265926241)
                  ·
                    refine ⟨2897978009999922949444681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3863970679999897265926241 2897978009999922949444681)
                    ·
                      refine ⟨2173483507499942212083511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2897978009999922949444681 2173483507499942212083511)
                      ·
                        rfl

theorem cell23_4232844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_4232844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232844 prefixEnd_4232844 := by exact prefixLift 4232844
  have htrace : WordTrace (prefixWord ++ tailWord_4232844) baseStart_4232844 baseEnd_4232844 := by
    simpa [prefixWord, tailWord_4232844, baseEnd_4232844] using wordTrace_append hprefix tailTrace_4232844
  have hstable : (prefixWord ++ tailWord_4232844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232844).length < 2 ^ (prefixWord ++ tailWord_4232844).sum := by decide
  have hdescent : baseEnd_4232844 < baseStart_4232844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232864 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3]
def baseStart_4232864 : Nat := 118140960795 + 4232864 * 2 ^ 59
def prefixEnd_4232864 : Nat := 4983230072969 + 3 ^ 40 * 4232864 * 2
def baseEnd_4232864 : Nat := 2173493777113032133833419

theorem tailTrace_4232864 : CollatzResearch.WordTrace tailWord_4232864 prefixEnd_4232864 2173493777113032133833419 := by
  unfold tailWord_4232864
  simp only [CollatzResearch.WordTrace]
  refine ⟨77192616668532059231028823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102923488891376078974705097 77192616668532059231028823)
  ·
    refine ⟨115788925002798088846543235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77192616668532059231028823 115788925002798088846543235)
    ·
      refine ⟨173683387504197133269814853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115788925002798088846543235 173683387504197133269814853)
      ·
        refine ⟨32565635157036962488090285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173683387504197133269814853 32565635157036962488090285)
        ·
          refine ⟨12212113183888860933033857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32565635157036962488090285 12212113183888860933033857)
          ·
            refine ⟨9159084887916645699775393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12212113183888860933033857 9159084887916645699775393)
            ·
              refine ⟨6869313665937484274831545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9159084887916645699775393 6869313665937484274831545)
              ·
                refine ⟨5151985249453113206123659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6869313665937484274831545 5151985249453113206123659)
                ·
                  refine ⟨7727977874179669809185489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5151985249453113206123659 7727977874179669809185489)
                  ·
                    refine ⟨5795983405634752356889117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7727977874179669809185489 5795983405634752356889117)
                    ·
                      refine ⟨2173493777113032133833419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5795983405634752356889117 2173493777113032133833419)
                      ·
                        rfl

theorem cell23_4232864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_4232864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232864 prefixEnd_4232864 := by exact prefixLift 4232864
  have htrace : WordTrace (prefixWord ++ tailWord_4232864) baseStart_4232864 baseEnd_4232864 := by
    simpa [prefixWord, tailWord_4232864, baseEnd_4232864] using wordTrace_append hprefix tailTrace_4232864
  have hstable : (prefixWord ++ tailWord_4232864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232864).length < 2 ^ (prefixWord ++ tailWord_4232864).sum := by decide
  have hdescent : baseEnd_4232864 < baseStart_4232864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232872 : List Nat := [2, 1, 7, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4232872 : Nat := 118140960795 + 4232872 * 2 ^ 59
def prefixEnd_4232872 : Nat := 4983230072969 + 3 ^ 40 * 4232872 * 2
def baseEnd_4232872 : Nat := 2173497884958268102533383

theorem tailTrace_4232872 : CollatzResearch.WordTrace tailWord_4232872 prefixEnd_4232872 2173497884958268102533383 := by
  unfold tailWord_4232872
  simp only [CollatzResearch.WordTrace]
  refine ⟨77192762560517567914174435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102923683414023423885565913 77192762560517567914174435)
  ·
    refine ⟨115789143840776351871261653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77192762560517567914174435 115789143840776351871261653)
    ·
      refine ⟨2713808058768195746982695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 115789143840776351871261653 2713808058768195746982695)
      ·
        refine ⟨4070712088152293620474043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713808058768195746982695 4070712088152293620474043)
        ·
          refine ⟨6106068132228440430711065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4070712088152293620474043 6106068132228440430711065)
          ·
            refine ⟨4579551099171330323033299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6106068132228440430711065 4579551099171330323033299)
            ·
              refine ⟨6869326648756995484549949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4579551099171330323033299 6869326648756995484549949)
              ·
                refine ⟨2575997493283873306706231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6869326648756995484549949 2575997493283873306706231)
                ·
                  refine ⟨3863996239925809960059347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2575997493283873306706231 3863996239925809960059347)
                  ·
                    refine ⟨5795994359888714940089021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3863996239925809960059347 5795994359888714940089021)
                    ·
                      refine ⟨2173497884958268102533383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5795994359888714940089021 2173497884958268102533383)
                      ·
                        rfl

theorem cell23_4232872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4232872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232872 prefixEnd_4232872 := by exact prefixLift 4232872
  have htrace : WordTrace (prefixWord ++ tailWord_4232872) baseStart_4232872 baseEnd_4232872 := by
    simpa [prefixWord, tailWord_4232872, baseEnd_4232872] using wordTrace_append hprefix tailTrace_4232872
  have hstable : (prefixWord ++ tailWord_4232872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232872).length < 2 ^ (prefixWord ++ tailWord_4232872).sum := by decide
  have hdescent : baseEnd_4232872 < baseStart_4232872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232873 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_4232873 : Nat := 118140960795 + 4232873 * 2 ^ 59
def prefixEnd_4232873 : Nat := 4983230072969 + 3 ^ 40 * 4232873 * 2
def baseEnd_4232873 : Nat := 2173498398438922598620877

theorem tailTrace_4232873 : CollatzResearch.WordTrace tailWord_4232873 prefixEnd_4232873 2173498398438922598620877 := by
  unfold tailWord_4232873
  simp only [CollatzResearch.WordTrace]
  refine ⟨154385561594031512999135273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102923707729354341999423515 154385561594031512999135273)
  ·
    refine ⟨115789171195523634749351455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154385561594031512999135273 115789171195523634749351455)
    ·
      refine ⟨173683756793285452124027183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115789171195523634749351455 173683756793285452124027183)
      ·
        refine ⟨260525635189928178186040775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173683756793285452124027183 260525635189928178186040775)
        ·
          refine ⟨390788452784892267279061163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260525635189928178186040775 390788452784892267279061163)
          ·
            refine ⟨586182679177338400918591745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390788452784892267279061163 586182679177338400918591745)
            ·
              refine ⟨439637009383003800688943809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586182679177338400918591745 439637009383003800688943809)
              ·
                refine ⟨329727757037252850516707857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439637009383003800688943809 329727757037252850516707857)
                ·
                  refine ⟨247295817777939637887530893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329727757037252850516707857 247295817777939637887530893)
                  ·
                    refine ⟨92735931666727364207824085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247295817777939637887530893 92735931666727364207824085)
                    ·
                      refine ⟨2173498398438922598620877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92735931666727364207824085 2173498398438922598620877)
                      ·
                        rfl

theorem cell23_4232873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_4232873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232873 prefixEnd_4232873 := by exact prefixLift 4232873
  have htrace : WordTrace (prefixWord ++ tailWord_4232873) baseStart_4232873 baseEnd_4232873 := by
    simpa [prefixWord, tailWord_4232873, baseEnd_4232873] using wordTrace_append hprefix tailTrace_4232873
  have hstable : (prefixWord ++ tailWord_4232873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232873).length < 2 ^ (prefixWord ++ tailWord_4232873).sum := by decide
  have hdescent : baseEnd_4232873 < baseStart_4232873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232877 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_4232877 : Nat := 118140960795 + 4232877 * 2 ^ 59
def prefixEnd_4232877 : Nat := 4983230072969 + 3 ^ 40 * 4232877 * 2
def baseEnd_4232877 : Nat := 2173500452361540582970859

theorem tailTrace_4232877 : CollatzResearch.WordTrace tailWord_4232877 prefixEnd_4232877 2173500452361540582970859 := by
  unfold tailWord_4232877
  simp only [CollatzResearch.WordTrace]
  refine ⟨154385707486017021682280885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102923804990678014454853923 154385707486017021682280885)
  ·
    refine ⟨14473660076814095782713833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154385707486017021682280885 14473660076814095782713833)
    ·
      refine ⟨10855245057610571837035375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14473660076814095782713833 10855245057610571837035375)
      ·
        refine ⟨16282867586415857755553063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10855245057610571837035375 16282867586415857755553063)
        ·
          refine ⟨24424301379623786633329595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16282867586415857755553063 24424301379623786633329595)
          ·
            refine ⟨36636452069435679949994393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24424301379623786633329595 36636452069435679949994393)
            ·
              refine ⟨27477339052076759962495795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36636452069435679949994393 27477339052076759962495795)
              ·
                refine ⟨41216008578115139943743693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27477339052076759962495795 41216008578115139943743693)
                ·
                  refine ⟨15456003216793177478903885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41216008578115139943743693 15456003216793177478903885)
                  ·
                    refine ⟨5796001206297441554588957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15456003216793177478903885 5796001206297441554588957)
                    ·
                      refine ⟨2173500452361540582970859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5796001206297441554588957 2173500452361540582970859)
                      ·
                        rfl

theorem cell23_4232877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_4232877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232877 prefixEnd_4232877 := by exact prefixLift 4232877
  have htrace : WordTrace (prefixWord ++ tailWord_4232877) baseStart_4232877 baseEnd_4232877 := by
    simpa [prefixWord, tailWord_4232877, baseEnd_4232877] using wordTrace_append hprefix tailTrace_4232877
  have hstable : (prefixWord ++ tailWord_4232877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232877).length < 2 ^ (prefixWord ++ tailWord_4232877).sum := by decide
  have hdescent : baseEnd_4232877 < baseStart_4232877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232894 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_4232894 : Nat := 118140960795 + 4232894 * 2 ^ 59
def prefixEnd_4232894 : Nat := 4983230072969 + 3 ^ 40 * 4232894 * 2
def baseEnd_4232894 : Nat := 2173509181532667016458281

theorem tailTrace_4232894 : CollatzResearch.WordTrace tailWord_4232894 prefixEnd_4232894 2173509181532667016458281 := by
  unfold tailWord_4232894
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298290940869429198206217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102924218351303622390433157 19298290940869429198206217)
  ·
    refine ⟨14473718205652071898654663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19298290940869429198206217 14473718205652071898654663)
    ·
      refine ⟨21710577308478107847981995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14473718205652071898654663 21710577308478107847981995)
      ·
        refine ⟨32565865962717161771972993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21710577308478107847981995 32565865962717161771972993)
        ·
          refine ⟨24424399472037871328979745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32565865962717161771972993 24424399472037871328979745)
          ·
            refine ⟨18318299604028403496734809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24424399472037871328979745 18318299604028403496734809)
            ·
              refine ⟨13738724703021302622551107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18318299604028403496734809 13738724703021302622551107)
              ·
                refine ⟨20608087054531953933826661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13738724703021302622551107 20608087054531953933826661)
                ·
                  refine ⟨3864016322724741362592499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20608087054531953933826661 3864016322724741362592499)
                  ·
                    refine ⟨5796024484087112043888749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3864016322724741362592499 5796024484087112043888749)
                    ·
                      refine ⟨2173509181532667016458281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5796024484087112043888749 2173509181532667016458281)
                      ·
                        rfl

theorem cell23_4232894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_4232894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232894 prefixEnd_4232894 := by exact prefixLift 4232894
  have htrace : WordTrace (prefixWord ++ tailWord_4232894) baseStart_4232894 baseEnd_4232894 := by
    simpa [prefixWord, tailWord_4232894, baseEnd_4232894] using wordTrace_append hprefix tailTrace_4232894
  have hstable : (prefixWord ++ tailWord_4232894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232894).length < 2 ^ (prefixWord ++ tailWord_4232894).sum := by decide
  have hdescent : baseEnd_4232894 < baseStart_4232894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232910 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_4232910 : Nat := 118140960795 + 4232910 * 2 ^ 59
def prefixEnd_4232910 : Nat := 4983230072969 + 3 ^ 40 * 4232910 * 2
def baseEnd_4232910 : Nat := 724505799074379651286069

theorem tailTrace_4232910 : CollatzResearch.WordTrace tailWord_4232910 prefixEnd_4232910 724505799074379651286069 := by
  unfold tailWord_4232910
  simp only [CollatzResearch.WordTrace]
  refine ⟨19298363886862183539779023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102924607396598312212154789 19298363886862183539779023)
  ·
    refine ⟨28947545830293275309668535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19298363886862183539779023 28947545830293275309668535)
    ·
      refine ⟨43421318745439912964502803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28947545830293275309668535 43421318745439912964502803)
      ·
        refine ⟨65131978118159869446754205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43421318745439912964502803 65131978118159869446754205)
        ·
          refine ⟨24424491794309951042532827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65131978118159869446754205 24424491794309951042532827)
          ·
            refine ⟨36636737691464926563799241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24424491794309951042532827 36636737691464926563799241)
            ·
              refine ⟨27477553268598694922849431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36636737691464926563799241 27477553268598694922849431)
              ·
                refine ⟨41216329902898042384274147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27477553268598694922849431 41216329902898042384274147)
                ·
                  refine ⟨61824494854347063576411221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41216329902898042384274147 61824494854347063576411221)
                  ·
                    refine ⟨724505799074379651286069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61824494854347063576411221 724505799074379651286069)
                    ·
                      rfl

theorem cell23_4232910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_4232910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232910 prefixEnd_4232910 := by exact prefixLift 4232910
  have htrace : WordTrace (prefixWord ++ tailWord_4232910) baseStart_4232910 baseEnd_4232910 := by
    simpa [prefixWord, tailWord_4232910, baseEnd_4232910] using wordTrace_append hprefix tailTrace_4232910
  have hstable : (prefixWord ++ tailWord_4232910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232910).length < 2 ^ (prefixWord ++ tailWord_4232910).sum := by decide
  have hdescent : baseEnd_4232910 < baseStart_4232910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232920 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_4232920 : Nat := 118140960795 + 4232920 * 2 ^ 59
def prefixEnd_4232920 : Nat := 4983230072969 + 3 ^ 40 * 4232920 * 2
def baseEnd_4232920 : Nat := 2173522532029683914733161

theorem tailTrace_4232920 : CollatzResearch.WordTrace tailWord_4232920 prefixEnd_4232920 2173522532029683914733161 := by
  unfold tailWord_4232920
  simp only [CollatzResearch.WordTrace]
  refine ⟨77193637912430620013048107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102924850549907493350730809 77193637912430620013048107)
  ·
    refine ⟨115790456868645930019572161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77193637912430620013048107 115790456868645930019572161)
    ·
      refine ⟨86842842651484447514679121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115790456868645930019572161 86842842651484447514679121)
      ·
        refine ⟨65132131988613335636009341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86842842651484447514679121 65132131988613335636009341)
        ·
          refine ⟨24424549495730000863503503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65132131988613335636009341 24424549495730000863503503)
          ·
            refine ⟨36636824243595001295255255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24424549495730000863503503 36636824243595001295255255)
            ·
              refine ⟨54955236365392501942882883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36636824243595001295255255 54955236365392501942882883)
              ·
                refine ⟨82432854548088752914324325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54955236365392501942882883 82432854548088752914324325)
                ·
                  refine ⟨15456160227766641171435811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82432854548088752914324325 15456160227766641171435811)
                  ·
                    refine ⟨23184240341649961757153717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15456160227766641171435811 23184240341649961757153717)
                    ·
                      refine ⟨2173522532029683914733161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23184240341649961757153717 2173522532029683914733161)
                      ·
                        rfl

theorem cell23_4232920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_4232920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232920 prefixEnd_4232920 := by exact prefixLift 4232920
  have htrace : WordTrace (prefixWord ++ tailWord_4232920) baseStart_4232920 baseEnd_4232920 := by
    simpa [prefixWord, tailWord_4232920, baseEnd_4232920] using wordTrace_append hprefix tailTrace_4232920
  have hstable : (prefixWord ++ tailWord_4232920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232920).length < 2 ^ (prefixWord ++ tailWord_4232920).sum := by decide
  have hdescent : baseEnd_4232920 < baseStart_4232920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
