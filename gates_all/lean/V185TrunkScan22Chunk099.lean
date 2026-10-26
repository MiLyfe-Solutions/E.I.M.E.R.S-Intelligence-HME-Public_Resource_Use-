import V185TrunkScan22Chunk098

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_888263 : List Nat := [1, 1, 4, 1, 1, 3, 3, 8]
def baseStart_888263 : Nat := 118140960795 + 888263 * 2 ^ 59
def prefixEnd_888263 : Nat := 4983230072969 + 3 ^ 40 * 888263 * 2
def baseEnd_888263 : Nat := 33785619748500992639071

theorem tailTrace_888263 : CollatzResearch.WordTrace tailWord_888263 prefixEnd_888263 33785619748500992639071 := by
  unfold tailWord_888263
  simp only [CollatzResearch.WordTrace]
  refine ⟨32397613180982329087797443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21598408787321552725198295 32397613180982329087797443)
  ·
    refine ⟨48596419771473493631696165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32397613180982329087797443 48596419771473493631696165)
    ·
      refine ⟨9111828707151280055943031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48596419771473493631696165 9111828707151280055943031)
      ·
        refine ⟨13667743060726920083914547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9111828707151280055943031 13667743060726920083914547)
        ·
          refine ⟨20501614591090380125871821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13667743060726920083914547 20501614591090380125871821)
          ·
            refine ⟨7688105471658892547201933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20501614591090380125871821 7688105471658892547201933)
            ·
              refine ⟨2883039551872084705200725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7688105471658892547201933 2883039551872084705200725)
              ·
                refine ⟨33785619748500992639071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2883039551872084705200725 33785619748500992639071)
                ·
                  rfl

theorem cell22_888263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 8].length) (baseStart_888263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888263 prefixEnd_888263 := by exact prefixLift 888263
  have htrace : WordTrace (prefixWord ++ tailWord_888263) baseStart_888263 baseEnd_888263 := by
    simpa [prefixWord, tailWord_888263, baseEnd_888263] using wordTrace_append hprefix tailTrace_888263
  have hstable : (prefixWord ++ tailWord_888263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888263).length < 2 ^ (prefixWord ++ tailWord_888263).sum := by decide
  have hdescent : baseEnd_888263 < baseStart_888263 := by decide
  rcases family_descends (prefixWord ++ tailWord_888263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888323 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 3, 7]
def baseStart_888323 : Nat := 118140960795 + 888323 * 2 ^ 59
def prefixEnd_888323 : Nat := 4983230072969 + 3 ^ 40 * 888323 * 2
def baseEnd_888323 : Nat := 304091116962688777251455

theorem tailTrace_888323 : CollatzResearch.WordTrace tailWord_888323 prefixEnd_888323 304091116962688777251455 := by
  unfold tailWord_888323
  simp only [CollatzResearch.WordTrace]
  refine ⟨32399801560764959334981623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21599867707176639556654415 32399801560764959334981623)
  ·
    refine ⟨48599702341147439002472435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32399801560764959334981623 48599702341147439002472435)
    ·
      refine ⟨72899553511721158503708653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48599702341147439002472435 72899553511721158503708653)
      ·
        refine ⟨27337332566895434438890745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72899553511721158503708653 27337332566895434438890745)
        ·
          refine ⟨20502999425171575829168059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27337332566895434438890745 20502999425171575829168059)
          ·
            refine ⟨30754499137757363743752089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20502999425171575829168059 30754499137757363743752089)
            ·
              refine ⟨23065874353318022807814067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30754499137757363743752089 23065874353318022807814067)
              ·
                refine ⟨34598811529977034211721101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23065874353318022807814067 34598811529977034211721101)
                ·
                  refine ⟨12974554323741387829395413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34598811529977034211721101 12974554323741387829395413)
                  ·
                    refine ⟨304091116962688777251455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12974554323741387829395413 304091116962688777251455)
                    ·
                      rfl

theorem cell22_888323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_888323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888323 prefixEnd_888323 := by exact prefixLift 888323
  have htrace : WordTrace (prefixWord ++ tailWord_888323) baseStart_888323 baseEnd_888323 := by
    simpa [prefixWord, tailWord_888323, baseEnd_888323] using wordTrace_append hprefix tailTrace_888323
  have hstable : (prefixWord ++ tailWord_888323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888323).length < 2 ^ (prefixWord ++ tailWord_888323).sum := by decide
  have hdescent : baseEnd_888323 < baseStart_888323 := by decide
  rcases family_descends (prefixWord ++ tailWord_888323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888400 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_888400 : Nat := 118140960795 + 888400 * 2 ^ 59
def prefixEnd_888400 : Nat := 4983230072969 + 3 ^ 40 * 888400 * 2
def baseEnd_888400 : Nat := 304117475636286243076219

theorem tailTrace_888400 : CollatzResearch.WordTrace tailWord_888400 prefixEnd_888400 304117475636286243076219 := by
  unfold tailWord_888400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201304990743000742767327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21601739987657334323689769 16201304990743000742767327)
  ·
    refine ⟨24301957486114501114150991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16201304990743000742767327 24301957486114501114150991)
    ·
      refine ⟨36452936229171751671226487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24301957486114501114150991 36452936229171751671226487)
      ·
        refine ⟨54679404343757627506839731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36452936229171751671226487 54679404343757627506839731)
        ·
          refine ⟨82019106515636441260259597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54679404343757627506839731 82019106515636441260259597)
          ·
            refine ⟨30757164943363665472597349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82019106515636441260259597 30757164943363665472597349)
            ·
              refine ⟨5766968426880687276112003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30757164943363665472597349 5766968426880687276112003)
              ·
                refine ⟨8650452640321030914168005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5766968426880687276112003 8650452640321030914168005)
                ·
                  refine ⟨1621959870060193296406501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8650452640321030914168005 1621959870060193296406501)
                  ·
                    refine ⟨304117475636286243076219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1621959870060193296406501 304117475636286243076219)
                    ·
                      rfl

theorem cell22_888400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_888400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888400 prefixEnd_888400 := by exact prefixLift 888400
  have htrace : WordTrace (prefixWord ++ tailWord_888400) baseStart_888400 baseEnd_888400 := by
    simpa [prefixWord, tailWord_888400, baseEnd_888400] using wordTrace_append hprefix tailTrace_888400
  have hstable : (prefixWord ++ tailWord_888400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888400).length < 2 ^ (prefixWord ++ tailWord_888400).sum := by decide
  have hdescent : baseEnd_888400 < baseStart_888400 := by decide
  rcases family_descends (prefixWord ++ tailWord_888400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888432 : List Nat := [2, 1, 1, 1, 6, 1, 4, 6]
def baseStart_888432 : Nat := 118140960795 + 888432 * 2 ^ 59
def prefixEnd_888432 : Nat := 4983230072969 + 3 ^ 40 * 888432 * 2
def baseEnd_888432 : Nat := 33792047765583202919569

theorem tailTrace_888432 : CollatzResearch.WordTrace tailWord_888432 prefixEnd_888432 33792047765583202919569 := by
  unfold tailWord_888432
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201888558685035475349775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21602518078246713967133033 16201888558685035475349775)
  ·
    refine ⟨24302832838027553213024663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16201888558685035475349775 24302832838027553213024663)
    ·
      refine ⟨36454249257041329819536995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24302832838027553213024663 36454249257041329819536995)
      ·
        refine ⟨54681373885561994729305493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36454249257041329819536995 54681373885561994729305493)
        ·
          refine ⟨2563189400885718502936195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54681373885561994729305493 2563189400885718502936195)
          ·
            refine ⟨3844784101328577754404293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563189400885718502936195 3844784101328577754404293)
            ·
              refine ⟨720897018999108328950805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3844784101328577754404293 720897018999108328950805)
              ·
                refine ⟨33792047765583202919569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 720897018999108328950805 33792047765583202919569)
                ·
                  rfl

theorem cell22_888432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 6].length) (baseStart_888432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888432 prefixEnd_888432 := by exact prefixLift 888432
  have htrace : WordTrace (prefixWord ++ tailWord_888432) baseStart_888432 baseEnd_888432 := by
    simpa [prefixWord, tailWord_888432, baseEnd_888432] using wordTrace_append hprefix tailTrace_888432
  have hstable : (prefixWord ++ tailWord_888432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888432).length < 2 ^ (prefixWord ++ tailWord_888432).sum := by decide
  have hdescent : baseEnd_888432 < baseStart_888432 := by decide
  rcases family_descends (prefixWord ++ tailWord_888432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888460 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 7]
def baseStart_888460 : Nat := 118140960795 + 888460 * 2 ^ 59
def prefixEnd_888460 : Nat := 4983230072969 + 3 ^ 40 * 888460 * 2
def baseEnd_888460 : Nat := 101379338287488695525345

theorem tailTrace_888460 : CollatzResearch.WordTrace tailWord_888460 prefixEnd_888460 101379338287488695525345 := by
  unfold tailWord_888460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16202399180634315866359417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21603198907512421155145889 16202399180634315866359417)
  ·
    refine ⟨12151799385475736899769563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16202399180634315866359417 12151799385475736899769563)
    ·
      refine ⟨18227699078213605349654345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12151799385475736899769563 18227699078213605349654345)
      ·
        refine ⟨13670774308660204012240759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18227699078213605349654345 13670774308660204012240759)
        ·
          refine ⟨20506161462990306018361139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670774308660204012240759 20506161462990306018361139)
          ·
            refine ⟨30759242194485459027541709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20506161462990306018361139 30759242194485459027541709)
            ·
              refine ⟨11534715822932047135328141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30759242194485459027541709 11534715822932047135328141)
              ·
                refine ⟨4325518433599517675748053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11534715822932047135328141 4325518433599517675748053)
                ·
                  refine ⟨101379338287488695525345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4325518433599517675748053 101379338287488695525345)
                  ·
                    rfl

theorem cell22_888460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_888460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888460 prefixEnd_888460 := by exact prefixLift 888460
  have htrace : WordTrace (prefixWord ++ tailWord_888460) baseStart_888460 baseEnd_888460 := by
    simpa [prefixWord, tailWord_888460, baseEnd_888460] using wordTrace_append hprefix tailTrace_888460
  have hstable : (prefixWord ++ tailWord_888460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888460).length < 2 ^ (prefixWord ++ tailWord_888460).sum := by decide
  have hdescent : baseEnd_888460 < baseStart_888460 := by decide
  rcases family_descends (prefixWord ++ tailWord_888460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888464 : List Nat := [2, 1, 1, 1, 1, 1, 3, 8, 1, 3]
def baseStart_888464 : Nat := 118140960795 + 888464 * 2 ^ 59
def prefixEnd_888464 : Nat := 4983230072969 + 3 ^ 40 * 888464 * 2
def baseEnd_888464 : Nat := 304139384144211409476023

theorem tailTrace_888464 : CollatzResearch.WordTrace tailWord_888464 prefixEnd_888464 304139384144211409476023 := by
  unfold tailWord_888464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16202472126627070207932223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21603296168836093610576297 16202472126627070207932223)
  ·
    refine ⟨24303708189940605311898335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16202472126627070207932223 24303708189940605311898335)
    ·
      refine ⟨36455562284910907967847503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24303708189940605311898335 36455562284910907967847503)
      ·
        refine ⟨54683343427366361951771255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36455562284910907967847503 54683343427366361951771255)
        ·
          refine ⟨82025015141049542927656883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54683343427366361951771255 82025015141049542927656883)
          ·
            refine ⟨123037522711574314391485325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82025015141049542927656883 123037522711574314391485325)
            ·
              refine ⟨46139071016840367896806997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123037522711574314391485325 46139071016840367896806997)
              ·
                refine ⟨540692238478598061290707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 46139071016840367896806997 540692238478598061290707)
                ·
                  refine ⟨811038357717897091936061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540692238478598061290707 811038357717897091936061)
                  ·
                    refine ⟨304139384144211409476023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811038357717897091936061 304139384144211409476023)
                    ·
                      rfl

theorem cell22_888464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 3].length) (baseStart_888464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888464 prefixEnd_888464 := by exact prefixLift 888464
  have htrace : WordTrace (prefixWord ++ tailWord_888464) baseStart_888464 baseEnd_888464 := by
    simpa [prefixWord, tailWord_888464, baseEnd_888464] using wordTrace_append hprefix tailTrace_888464
  have hstable : (prefixWord ++ tailWord_888464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888464).length < 2 ^ (prefixWord ++ tailWord_888464).sum := by decide
  have hdescent : baseEnd_888464 < baseStart_888464 := by decide
  rcases family_descends (prefixWord ++ tailWord_888464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888507 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 1, 4]
def baseStart_888507 : Nat := 118140960795 + 888507 * 2 ^ 59
def prefixEnd_888507 : Nat := 4983230072969 + 3 ^ 40 * 888507 * 2
def baseEnd_888507 : Nat := 304154103922973630650891

theorem tailTrace_888507 : CollatzResearch.WordTrace tailWord_888507 prefixEnd_888507 304154103922973630650891 := by
  unfold tailWord_888507
  simp only [CollatzResearch.WordTrace]
  refine ⟨32406512592098358759679775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21604341728065572506453183 32406512592098358759679775)
  ·
    refine ⟨48609768888147538139519663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32406512592098358759679775 48609768888147538139519663)
    ·
      refine ⟨72914653332221307209279495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48609768888147538139519663 72914653332221307209279495)
      ·
        refine ⟨109371979998331960813919243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72914653332221307209279495 109371979998331960813919243)
        ·
          refine ⟨164057969997497941220878865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109371979998331960813919243 164057969997497941220878865)
          ·
            refine ⟨123043477498123455915659149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164057969997497941220878865 123043477498123455915659149)
            ·
              refine ⟨46141304061796295968372181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123043477498123455915659149 46141304061796295968372181)
              ·
                refine ⟨1081436813948350686758723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46141304061796295968372181 1081436813948350686758723)
                ·
                  refine ⟨1622155220922526030138085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081436813948350686758723 1622155220922526030138085)
                  ·
                    refine ⟨304154103922973630650891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1622155220922526030138085 304154103922973630650891)
                    ·
                      rfl

theorem cell22_888507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 4].length) (baseStart_888507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888507 prefixEnd_888507 := by exact prefixLift 888507
  have htrace : WordTrace (prefixWord ++ tailWord_888507) baseStart_888507 baseEnd_888507 := by
    simpa [prefixWord, tailWord_888507, baseEnd_888507] using wordTrace_append hprefix tailTrace_888507
  have hstable : (prefixWord ++ tailWord_888507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888507).length < 2 ^ (prefixWord ++ tailWord_888507).sum := by decide
  have hdescent : baseEnd_888507 < baseStart_888507 := by decide
  rcases family_descends (prefixWord ++ tailWord_888507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888537 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_888537 : Nat := 118140960795 + 888537 * 2 ^ 59
def prefixEnd_888537 : Nat := 4983230072969 + 3 ^ 40 * 888537 * 2
def baseEnd_888537 : Nat := 304164373536063552400799

theorem tailTrace_888537 : CollatzResearch.WordTrace tailWord_888537 prefixEnd_888537 304164373536063552400799 := by
  unfold tailWord_888537
  simp only [CollatzResearch.WordTrace]
  refine ⟨32407606781989673883271865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21605071187993115922181243 32407606781989673883271865)
  ·
    refine ⟨24305705086492255412453899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32407606781989673883271865 24305705086492255412453899)
    ·
      refine ⟨36458557629738383118680849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24305705086492255412453899 36458557629738383118680849)
      ·
        refine ⟨27343918222303787339010637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36458557629738383118680849 27343918222303787339010637)
        ·
          refine ⟨10253969333363920252128989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27343918222303787339010637 10253969333363920252128989)
          ·
            refine ⟨3845238500011470094548371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10253969333363920252128989 3845238500011470094548371)
            ·
              refine ⟨5767857750017205141822557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3845238500011470094548371 5767857750017205141822557)
              ·
                refine ⟨2162946656256451928183459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5767857750017205141822557 2162946656256451928183459)
                ·
                  refine ⟨3244419984384677892275189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2162946656256451928183459 3244419984384677892275189)
                  ·
                    refine ⟨304164373536063552400799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3244419984384677892275189 304164373536063552400799)
                    ·
                      rfl

theorem cell22_888537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_888537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888537 prefixEnd_888537 := by exact prefixLift 888537
  have htrace : WordTrace (prefixWord ++ tailWord_888537) baseStart_888537 baseEnd_888537 := by
    simpa [prefixWord, tailWord_888537, baseEnd_888537] using wordTrace_append hprefix tailTrace_888537
  have hstable : (prefixWord ++ tailWord_888537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888537).length < 2 ^ (prefixWord ++ tailWord_888537).sum := by decide
  have hdescent : baseEnd_888537 < baseStart_888537 := by decide
  rcases family_descends (prefixWord ++ tailWord_888537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888687 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 5, 6]
def baseStart_888687 : Nat := 118140960795 + 888687 * 2 ^ 59
def prefixEnd_888687 : Nat := 4983230072969 + 3 ^ 40 * 888687 * 2
def baseEnd_888687 : Nat := 304215721601513161150339

theorem tailTrace_888687 : CollatzResearch.WordTrace tailWord_888687 prefixEnd_888687 304215721601513161150339 := by
  unfold tailWord_888687
  simp only [CollatzResearch.WordTrace]
  refine ⟨32413077731446249501232315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21608718487630833000821543 32413077731446249501232315)
  ·
    refine ⟨48619616597169374251848473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32413077731446249501232315 48619616597169374251848473)
    ·
      refine ⟨36464712447877030688886355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48619616597169374251848473 36464712447877030688886355)
      ·
        refine ⟨54697068671815546033329533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36464712447877030688886355 54697068671815546033329533)
        ·
          refine ⟨20511400751930829762498575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54697068671815546033329533 20511400751930829762498575)
          ·
            refine ⟨30767101127896244643747863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20511400751930829762498575 30767101127896244643747863)
            ·
              refine ⟨46150651691844366965621795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30767101127896244643747863 46150651691844366965621795)
              ·
                refine ⟨69225977537766550448432693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46150651691844366965621795 69225977537766550448432693)
                ·
                  refine ⟨6489935394165614104540565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69225977537766550448432693 6489935394165614104540565)
                  ·
                    refine ⟨304215721601513161150339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6489935394165614104540565 304215721601513161150339)
                    ·
                      rfl

theorem cell22_888687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_888687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888687 prefixEnd_888687 := by exact prefixLift 888687
  have htrace : WordTrace (prefixWord ++ tailWord_888687) baseStart_888687 baseEnd_888687 := by
    simpa [prefixWord, tailWord_888687, baseEnd_888687] using wordTrace_append hprefix tailTrace_888687
  have hstable : (prefixWord ++ tailWord_888687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888687).length < 2 ^ (prefixWord ++ tailWord_888687).sum := by decide
  have hdescent : baseEnd_888687 < baseStart_888687 := by decide
  rcases family_descends (prefixWord ++ tailWord_888687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888751 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 3, 3]
def baseStart_888751 : Nat := 118140960795 + 888751 * 2 ^ 59
def prefixEnd_888751 : Nat := 4983230072969 + 3 ^ 40 * 888751 * 2
def baseEnd_888751 : Nat := 304237630109438327550143

theorem tailTrace_888751 : CollatzResearch.WordTrace tailWord_888751 prefixEnd_888751 304237630109438327550143 := by
  unfold tailWord_888751
  simp only [CollatzResearch.WordTrace]
  refine ⟨32415412003214388431562107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21610274668809592287708071 32415412003214388431562107)
  ·
    refine ⟨48623118004821582647343161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32415412003214388431562107 48623118004821582647343161)
    ·
      refine ⟨36467338503616186985507371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48623118004821582647343161 36467338503616186985507371)
      ·
        refine ⟨54701007755424280478261057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36467338503616186985507371 54701007755424280478261057)
        ·
          refine ⟨41025755816568210358695793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54701007755424280478261057 41025755816568210358695793)
          ·
            refine ⟨30769316862426157769021845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41025755816568210358695793 30769316862426157769021845)
            ·
              refine ⟨1442311727926226145422899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30769316862426157769021845 1442311727926226145422899)
              ·
                refine ⟨2163467591889339218134349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442311727926226145422899 2163467591889339218134349)
                ·
                  refine ⟨811300346958502206800381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2163467591889339218134349 811300346958502206800381)
                  ·
                    refine ⟨304237630109438327550143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811300346958502206800381 304237630109438327550143)
                    ·
                      rfl

theorem cell22_888751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_888751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888751 prefixEnd_888751 := by exact prefixLift 888751
  have htrace : WordTrace (prefixWord ++ tailWord_888751) baseStart_888751 baseEnd_888751 := by
    simpa [prefixWord, tailWord_888751, baseEnd_888751] using wordTrace_append hprefix tailTrace_888751
  have hstable : (prefixWord ++ tailWord_888751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888751).length < 2 ^ (prefixWord ++ tailWord_888751).sum := by decide
  have hdescent : baseEnd_888751 < baseStart_888751 := by decide
  rcases family_descends (prefixWord ++ tailWord_888751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888802 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_888802 : Nat := 118140960795 + 888802 * 2 ^ 59
def prefixEnd_888802 : Nat := 4983230072969 + 3 ^ 40 * 888802 * 2
def baseEnd_888802 : Nat := 304255088451691194524987

theorem tailTrace_888802 : CollatzResearch.WordTrace tailWord_888802 prefixEnd_888802 304255088451691194524987 := by
  unfold tailWord_888802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104318031507406035417165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21611514750686416094445773 8104318031507406035417165)
  ·
    refine ⟨3039119261815277263281437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8104318031507406035417165 3039119261815277263281437)
    ·
      refine ⟨1139669723180728973730539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3039119261815277263281437 1139669723180728973730539)
      ·
        refine ⟨1709504584771093460595809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139669723180728973730539 1709504584771093460595809)
        ·
          refine ⟨1282128438578320095446857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709504584771093460595809 1282128438578320095446857)
          ·
            refine ⟨961596328933740071585143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282128438578320095446857 961596328933740071585143)
            ·
              refine ⟨1442394493400610107377715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961596328933740071585143 1442394493400610107377715)
              ·
                refine ⟨2163591740100915161066573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442394493400610107377715 2163591740100915161066573)
                ·
                  refine ⟨811346902537843185399965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2163591740100915161066573 811346902537843185399965)
                  ·
                    refine ⟨304255088451691194524987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811346902537843185399965 304255088451691194524987)
                    ·
                      rfl

theorem cell22_888802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_888802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888802 prefixEnd_888802 := by exact prefixLift 888802
  have htrace : WordTrace (prefixWord ++ tailWord_888802) baseStart_888802 baseEnd_888802 := by
    simpa [prefixWord, tailWord_888802, baseEnd_888802] using wordTrace_append hprefix tailTrace_888802
  have hstable : (prefixWord ++ tailWord_888802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888802).length < 2 ^ (prefixWord ++ tailWord_888802).sum := by decide
  have hdescent : baseEnd_888802 < baseStart_888802 := by decide
  rcases family_descends (prefixWord ++ tailWord_888802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888854 : List Nat := [5, 17]
def baseStart_888854 : Nat := 118140960795 + 888854 * 2 ^ 59
def prefixEnd_888854 : Nat := 4983230072969 + 3 ^ 40 * 888854 * 2
def baseEnd_888854 : Nat := 46375992853891234907

theorem tailTrace_888854 : CollatzResearch.WordTrace tailWord_888854 prefixEnd_888854 46375992853891234907 := by
  unfold tailWord_888854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026198045115077313910101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21612779147894158015041077 2026198045115077313910101)
  ·
    refine ⟨46375992853891234907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 17 2026198045115077313910101 46375992853891234907)
    ·
      rfl

theorem cell22_888854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 17].length) (baseStart_888854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888854 prefixEnd_888854 := by exact prefixLift 888854
  have htrace : WordTrace (prefixWord ++ tailWord_888854) baseStart_888854 baseEnd_888854 := by
    simpa [prefixWord, tailWord_888854, baseEnd_888854] using wordTrace_append hprefix tailTrace_888854
  have hstable : (prefixWord ++ tailWord_888854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888854).length < 2 ^ (prefixWord ++ tailWord_888854).sum := by decide
  have hdescent : baseEnd_888854 < baseStart_888854 := by decide
  rcases family_descends (prefixWord ++ tailWord_888854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888856 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_888856 : Nat := 118140960795 + 888856 * 2 ^ 59
def prefixEnd_888856 : Nat := 4983230072969 + 3 ^ 40 * 888856 * 2
def baseEnd_888856 : Nat := 304273573755253053674821

theorem tailTrace_888856 : CollatzResearch.WordTrace tailWord_888856 prefixEnd_888856 304273573755253053674821 := by
  unfold tailWord_888856
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209620833916995682067211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21612827778555994242756281 16209620833916995682067211)
  ·
    refine ⟨24314431250875493523100817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16209620833916995682067211 24314431250875493523100817)
    ·
      refine ⟨18235823438156620142325613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24314431250875493523100817 18235823438156620142325613)
      ·
        refine ⟨6838433789308732553372105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18235823438156620142325613 6838433789308732553372105)
        ·
          refine ⟨5128825341981549415029079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6838433789308732553372105 5128825341981549415029079)
          ·
            refine ⟨7693238012972324122543619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5128825341981549415029079 7693238012972324122543619)
            ·
              refine ⟨11539857019458486183815429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7693238012972324122543619 11539857019458486183815429)
              ·
                refine ⟨2163723191148466159465393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11539857019458486183815429 2163723191148466159465393)
                ·
                  refine ⟨1622792393361349619599045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2163723191148466159465393 1622792393361349619599045)
                  ·
                    refine ⟨304273573755253053674821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1622792393361349619599045 304273573755253053674821)
                    ·
                      rfl

theorem cell22_888856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_888856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888856 prefixEnd_888856 := by exact prefixLift 888856
  have htrace : WordTrace (prefixWord ++ tailWord_888856) baseStart_888856 baseEnd_888856 := by
    simpa [prefixWord, tailWord_888856, baseEnd_888856] using wordTrace_append hprefix tailTrace_888856
  have hstable : (prefixWord ++ tailWord_888856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888856).length < 2 ^ (prefixWord ++ tailWord_888856).sum := by decide
  have hdescent : baseEnd_888856 < baseStart_888856 := by decide
  rcases family_descends (prefixWord ++ tailWord_888856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888858 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_888858 : Nat := 118140960795 + 888858 * 2 ^ 59
def prefixEnd_888858 : Nat := 4983230072969 + 3 ^ 40 * 888858 * 2
def baseEnd_888858 : Nat := 304274258396125715124815

theorem tailTrace_888858 : CollatzResearch.WordTrace tailWord_888858 prefixEnd_888858 304274258396125715124815 := by
  unfold tailWord_888858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104828653456686426426807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21612876409217830470471485 8104828653456686426426807)
  ·
    refine ⟨12157242980185029639640211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8104828653456686426426807 12157242980185029639640211)
    ·
      refine ⟨18235864470277544459460317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12157242980185029639640211 18235864470277544459460317)
      ·
        refine ⟨6838449176354079172297619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18235864470277544459460317 6838449176354079172297619)
        ·
          refine ⟨10257673764531118758446429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6838449176354079172297619 10257673764531118758446429)
          ·
            refine ⟨3846627661699169534417411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10257673764531118758446429 3846627661699169534417411)
            ·
              refine ⟨5769941492548754301626117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3846627661699169534417411 5769941492548754301626117)
              ·
                refine ⟨1081864029852891431554897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5769941492548754301626117 1081864029852891431554897)
                ·
                  refine ⟨811398022389668573666173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1081864029852891431554897 811398022389668573666173)
                  ·
                    refine ⟨304274258396125715124815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811398022389668573666173 304274258396125715124815)
                    ·
                      rfl

theorem cell22_888858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_888858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888858 prefixEnd_888858 := by exact prefixLift 888858
  have htrace : WordTrace (prefixWord ++ tailWord_888858) baseStart_888858 baseEnd_888858 := by
    simpa [prefixWord, tailWord_888858, baseEnd_888858] using wordTrace_append hprefix tailTrace_888858
  have hstable : (prefixWord ++ tailWord_888858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888858).length < 2 ^ (prefixWord ++ tailWord_888858).sum := by decide
  have hdescent : baseEnd_888858 < baseStart_888858 := by decide
  rcases family_descends (prefixWord ++ tailWord_888858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888860 : List Nat := [2, 2, 3, 1, 3, 1, 4, 2, 4]
def baseStart_888860 : Nat := 118140960795 + 888860 * 2 ^ 59
def prefixEnd_888860 : Nat := 4983230072969 + 3 ^ 40 * 888860 * 2
def baseEnd_888860 : Nat := 101424981012332792191603

theorem tailTrace_888860 : CollatzResearch.WordTrace tailWord_888860 prefixEnd_888860 101424981012332792191603 := by
  unfold tailWord_888860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209693779909750023640017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21612925039879666698186689 16209693779909750023640017)
  ·
    refine ⟨12157270334932312517730013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16209693779909750023640017 12157270334932312517730013)
    ·
      refine ⟨4558976375599617194148755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12157270334932312517730013 4558976375599617194148755)
      ·
        refine ⟨6838464563399425791223133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558976375599617194148755 6838464563399425791223133)
        ·
          refine ⟨2564424211274784671708675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6838464563399425791223133 2564424211274784671708675)
          ·
            refine ⟨3846636316912177007563013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564424211274784671708675 3846636316912177007563013)
            ·
              refine ⟨721244309421033188918065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3846636316912177007563013 721244309421033188918065)
              ·
                refine ⟨540933232065774891688549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721244309421033188918065 540933232065774891688549)
                ·
                  refine ⟨101424981012332792191603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540933232065774891688549 101424981012332792191603)
                  ·
                    rfl

theorem cell22_888860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_888860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888860 prefixEnd_888860 := by exact prefixLift 888860
  have htrace : WordTrace (prefixWord ++ tailWord_888860) baseStart_888860 baseEnd_888860 := by
    simpa [prefixWord, tailWord_888860, baseEnd_888860] using wordTrace_append hprefix tailTrace_888860
  have hstable : (prefixWord ++ tailWord_888860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888860).length < 2 ^ (prefixWord ++ tailWord_888860).sum := by decide
  have hdescent : baseEnd_888860 < baseStart_888860 := by decide
  rcases family_descends (prefixWord ++ tailWord_888860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888888 : List Nat := [2, 1, 2, 1, 6, 1, 3, 6]
def baseStart_888888 : Nat := 118140960795 + 888888 * 2 ^ 59
def prefixEnd_888888 : Nat := 4983230072969 + 3 ^ 40 * 888888 * 2
def baseEnd_888888 : Nat := 33809392001023959652747

theorem tailTrace_888888 : CollatzResearch.WordTrace tailWord_888888 prefixEnd_888888 33809392001023959652747 := by
  unfold tailWord_888888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16210204401859030414649659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21613605869145373886199545 16210204401859030414649659)
  ·
    refine ⟨24315306602788545621974489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16210204401859030414649659 24315306602788545621974489)
    ·
      refine ⟨18236479952091409216480867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24315306602788545621974489 18236479952091409216480867)
      ·
        refine ⟨27354719928137113824721301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18236479952091409216480867 27354719928137113824721301)
        ·
          refine ⟨1282252496631427210533811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27354719928137113824721301 1282252496631427210533811)
          ·
            refine ⟨1923378744947140815800717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282252496631427210533811 1923378744947140815800717)
            ·
              refine ⟨721267029355177805925269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1923378744947140815800717 721267029355177805925269)
              ·
                refine ⟨33809392001023959652747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 721267029355177805925269 33809392001023959652747)
                ·
                  rfl

theorem cell22_888888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 6].length) (baseStart_888888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888888 prefixEnd_888888 := by exact prefixLift 888888
  have htrace : WordTrace (prefixWord ++ tailWord_888888) baseStart_888888 baseEnd_888888 := by
    simpa [prefixWord, tailWord_888888, baseEnd_888888] using wordTrace_append hprefix tailTrace_888888
  have hstable : (prefixWord ++ tailWord_888888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888888).length < 2 ^ (prefixWord ++ tailWord_888888).sum := by decide
  have hdescent : baseEnd_888888 < baseStart_888888 := by decide
  rcases family_descends (prefixWord ++ tailWord_888888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888920 : List Nat := [2, 1, 2, 2, 1, 4, 2, 4, 1, 3]
def baseStart_888920 : Nat := 118140960795 + 888920 * 2 ^ 59
def prefixEnd_888920 : Nat := 4983230072969 + 3 ^ 40 * 888920 * 2
def baseEnd_888920 : Nat := 304295482263178220074625

theorem tailTrace_888920 : CollatzResearch.WordTrace tailWord_888920 prefixEnd_888920 304295482263178220074625 := by
  unfold tailWord_888920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16210787969801065147232107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21614383959734753529642809 16210787969801065147232107)
  ·
    refine ⟨24316181954701597720848161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16210787969801065147232107 24316181954701597720848161)
    ·
      refine ⟨18237136466026198290636121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24316181954701597720848161 18237136466026198290636121)
      ·
        refine ⟨13677852349519648717977091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18237136466026198290636121 13677852349519648717977091)
        ·
          refine ⟨20516778524279473076965637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13677852349519648717977091 20516778524279473076965637)
          ·
            refine ⟨3846895973302401201931057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20516778524279473076965637 3846895973302401201931057)
            ·
              refine ⟨2885171979976800901448293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846895973302401201931057 2885171979976800901448293)
              ·
                refine ⟨540969746245650169021555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2885171979976800901448293 540969746245650169021555)
                ·
                  refine ⟨811454619368475253532333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540969746245650169021555 811454619368475253532333)
                  ·
                    refine ⟨304295482263178220074625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811454619368475253532333 304295482263178220074625)
                    ·
                      rfl

theorem cell22_888920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_888920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888920 prefixEnd_888920 := by exact prefixLift 888920
  have htrace : WordTrace (prefixWord ++ tailWord_888920) baseStart_888920 baseEnd_888920 := by
    simpa [prefixWord, tailWord_888920, baseEnd_888920] using wordTrace_append hprefix tailTrace_888920
  have hstable : (prefixWord ++ tailWord_888920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888920).length < 2 ^ (prefixWord ++ tailWord_888920).sum := by decide
  have hdescent : baseEnd_888920 < baseStart_888920 := by decide
  rcases family_descends (prefixWord ++ tailWord_888920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888926 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_888926 : Nat := 118140960795 + 888926 * 2 ^ 59
def prefixEnd_888926 : Nat := 4983230072969 + 3 ^ 40 * 888926 * 2
def baseEnd_888926 : Nat := 304297536185796204424607

theorem tailTrace_888926 : CollatzResearch.WordTrace tailWord_888926 prefixEnd_888926 304297536185796204424607 := by
  unfold tailWord_888926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052724347197549164897829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21614529851720262212788421 4052724347197549164897829)
  ·
    refine ⟨759885815099540468418343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4052724347197549164897829 759885815099540468418343)
    ·
      refine ⟨1139828722649310702627515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759885815099540468418343 1139828722649310702627515)
      ·
        refine ⟨1709743083973966053941273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139828722649310702627515 1709743083973966053941273)
        ·
          refine ⟨1282307312980474540455955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1709743083973966053941273 1282307312980474540455955)
          ·
            refine ⟨1923460969470711810683933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282307312980474540455955 1923460969470711810683933)
            ·
              refine ⟨721297863551516929006475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1923460969470711810683933 721297863551516929006475)
              ·
                refine ⟨1081946795327275393509713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721297863551516929006475 1081946795327275393509713)
                ·
                  refine ⟨811460096495456545132285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1081946795327275393509713 811460096495456545132285)
                  ·
                    refine ⟨304297536185796204424607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811460096495456545132285 304297536185796204424607)
                    ·
                      rfl

theorem cell22_888926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_888926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888926 prefixEnd_888926 := by exact prefixLift 888926
  have htrace : WordTrace (prefixWord ++ tailWord_888926) baseStart_888926 baseEnd_888926 := by
    simpa [prefixWord, tailWord_888926, baseEnd_888926] using wordTrace_append hprefix tailTrace_888926
  have hstable : (prefixWord ++ tailWord_888926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888926).length < 2 ^ (prefixWord ++ tailWord_888926).sum := by decide
  have hdescent : baseEnd_888926 < baseStart_888926 := by decide
  rcases family_descends (prefixWord ++ tailWord_888926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888931 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 2, 5]
def baseStart_888931 : Nat := 118140960795 + 888931 * 2 ^ 59
def prefixEnd_888931 : Nat := 4983230072969 + 3 ^ 40 * 888931 * 2
def baseEnd_888931 : Nat := 304299247787977858049591

theorem tailTrace_888931 : CollatzResearch.WordTrace tailWord_888931 prefixEnd_888931 304299247787977858049591 := by
  unfold tailWord_888931
  simp only [CollatzResearch.WordTrace]
  refine ⟨32421977142562279173114647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21614651428374852782076431 32421977142562279173114647)
  ·
    refine ⟨48632965713843418759671971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32421977142562279173114647 48632965713843418759671971)
    ·
      refine ⟨72949448570765128139507957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48632965713843418759671971 72949448570765128139507957)
      ·
        refine ⟨6839010803509230763078871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72949448570765128139507957 6839010803509230763078871)
        ·
          refine ⟨10258516205263846144618307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6839010803509230763078871 10258516205263846144618307)
          ·
            refine ⟨15387774307895769216927461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10258516205263846144618307 15387774307895769216927461)
            ·
              refine ⟨2885207682730456728173899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15387774307895769216927461 2885207682730456728173899)
              ·
                refine ⟨4327811524095685092260849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2885207682730456728173899 4327811524095685092260849)
                ·
                  refine ⟨3245858643071763819195637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4327811524095685092260849 3245858643071763819195637)
                  ·
                    refine ⟨304299247787977858049591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3245858643071763819195637 304299247787977858049591)
                    ·
                      rfl

theorem cell22_888931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_888931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888931 prefixEnd_888931 := by exact prefixLift 888931
  have htrace : WordTrace (prefixWord ++ tailWord_888931) baseStart_888931 baseEnd_888931 := by
    simpa [prefixWord, tailWord_888931, baseEnd_888931] using wordTrace_append hprefix tailTrace_888931
  have hstable : (prefixWord ++ tailWord_888931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888931).length < 2 ^ (prefixWord ++ tailWord_888931).sum := by decide
  have hdescent : baseEnd_888931 < baseStart_888931 := by decide
  rcases family_descends (prefixWord ++ tailWord_888931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_888963 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 1, 4]
def baseStart_888963 : Nat := 118140960795 + 888963 * 2 ^ 59
def prefixEnd_888963 : Nat := 4983230072969 + 3 ^ 40 * 888963 * 2
def baseEnd_888963 : Nat := 304310202041940441249493

theorem tailTrace_888963 : CollatzResearch.WordTrace tailWord_888963 prefixEnd_888963 304310202041940441249493 := by
  unfold tailWord_888963
  simp only [CollatzResearch.WordTrace]
  refine ⟨32423144278446348638279543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21615429518964232425519695 32423144278446348638279543)
  ·
    refine ⟨48634716417669522957419315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32423144278446348638279543 48634716417669522957419315)
    ·
      refine ⟨72952074626504284436128973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48634716417669522957419315 72952074626504284436128973)
      ·
        refine ⟨27357027984939106663548365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72952074626504284436128973 27357027984939106663548365)
        ·
          refine ⟨10258885494352164998830637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27357027984939106663548365 10258885494352164998830637)
          ·
            refine ⟨3847082060382061874561489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10258885494352164998830637 3847082060382061874561489)
            ·
              refine ⟨2885311545286546405921117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3847082060382061874561489 2885311545286546405921117)
              ·
                refine ⟨1081991829482454902220419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2885311545286546405921117 1081991829482454902220419)
                ·
                  refine ⟨1622987744223682353330629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1081991829482454902220419 1622987744223682353330629)
                  ·
                    refine ⟨304310202041940441249493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1622987744223682353330629 304310202041940441249493)
                    ·
                      rfl

theorem cell22_888963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 4].length) (baseStart_888963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_888963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_888963 prefixEnd_888963 := by exact prefixLift 888963
  have htrace : WordTrace (prefixWord ++ tailWord_888963) baseStart_888963 baseEnd_888963 := by
    simpa [prefixWord, tailWord_888963, baseEnd_888963] using wordTrace_append hprefix tailTrace_888963
  have hstable : (prefixWord ++ tailWord_888963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_888963).length < 2 ^ (prefixWord ++ tailWord_888963).sum := by decide
  have hdescent : baseEnd_888963 < baseStart_888963 := by decide
  rcases family_descends (prefixWord ++ tailWord_888963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889059 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 2, 4]
def baseStart_889059 : Nat := 118140960795 + 889059 * 2 ^ 59
def prefixEnd_889059 : Nat := 4983230072969 + 3 ^ 40 * 889059 * 2
def baseEnd_889059 : Nat := 304343064803828190849199

theorem tailTrace_889059 : CollatzResearch.WordTrace tailWord_889059 prefixEnd_889059 304343064803828190849199 := by
  unfold tailWord_889059
  simp only [CollatzResearch.WordTrace]
  refine ⟨32426645686098557033774231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21617763790732371355849487 32426645686098557033774231)
  ·
    refine ⟨48639968529147835550661347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32426645686098557033774231 48639968529147835550661347)
    ·
      refine ⟨72959952793721753325992021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48639968529147835550661347 72959952793721753325992021)
      ·
        refine ⟨854999446801426796788969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 72959952793721753325992021 854999446801426796788969)
        ·
          refine ⟨641249585101070097591727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854999446801426796788969 641249585101070097591727)
          ·
            refine ⟨961874377651605146387591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641249585101070097591727 961874377651605146387591)
            ·
              refine ⟨1442811566477407719581387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961874377651605146387591 1442811566477407719581387)
              ·
                refine ⟨2164217349716111579372081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442811566477407719581387 2164217349716111579372081)
                ·
                  refine ⟨1623163012287083684529061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2164217349716111579372081 1623163012287083684529061)
                  ·
                    refine ⟨304343064803828190849199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1623163012287083684529061 304343064803828190849199)
                    ·
                      rfl

theorem cell22_889059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 4].length) (baseStart_889059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889059 prefixEnd_889059 := by exact prefixLift 889059
  have htrace : WordTrace (prefixWord ++ tailWord_889059) baseStart_889059 baseEnd_889059 := by
    simpa [prefixWord, tailWord_889059, baseEnd_889059] using wordTrace_append hprefix tailTrace_889059
  have hstable : (prefixWord ++ tailWord_889059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889059).length < 2 ^ (prefixWord ++ tailWord_889059).sum := by decide
  have hdescent : baseEnd_889059 < baseStart_889059 := by decide
  rcases family_descends (prefixWord ++ tailWord_889059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889098 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_889098 : Nat := 118140960795 + 889098 * 2 ^ 59
def prefixEnd_889098 : Nat := 4983230072969 + 3 ^ 40 * 889098 * 2
def baseEnd_889098 : Nat := 304356415300845089124079

theorem tailTrace_889098 : CollatzResearch.WordTrace tailWord_889098 prefixEnd_889098 304356415300845089124079 := by
  unfold tailWord_889098
  simp only [CollatzResearch.WordTrace]
  refine ⟨8107017033239316673610987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21618712088638177796295965 8107017033239316673610987)
  ·
    refine ⟨12160525549858975010416481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8107017033239316673610987 12160525549858975010416481)
    ·
      refine ⟨9120394162394231257812361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12160525549858975010416481 9120394162394231257812361)
      ·
        refine ⟨6840295621795673443359271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9120394162394231257812361 6840295621795673443359271)
        ·
          refine ⟨10260443432693510165038907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840295621795673443359271 10260443432693510165038907)
          ·
            refine ⟨15390665149040265247558361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10260443432693510165038907 15390665149040265247558361)
            ·
              refine ⟨11542998861780198935668771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15390665149040265247558361 11542998861780198935668771)
              ·
                refine ⟨17314498292670298403503157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11542998861780198935668771 17314498292670298403503157)
                ·
                  refine ⟨1623234214937840475328421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17314498292670298403503157 1623234214937840475328421)
                  ·
                    refine ⟨304356415300845089124079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1623234214937840475328421 304356415300845089124079)
                    ·
                      rfl

theorem cell22_889098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_889098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889098 prefixEnd_889098 := by exact prefixLift 889098
  have htrace : WordTrace (prefixWord ++ tailWord_889098) baseStart_889098 baseEnd_889098 := by
    simpa [prefixWord, tailWord_889098, baseEnd_889098] using wordTrace_append hprefix tailTrace_889098
  have hstable : (prefixWord ++ tailWord_889098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889098).length < 2 ^ (prefixWord ++ tailWord_889098).sum := by decide
  have hdescent : baseEnd_889098 < baseStart_889098 := by decide
  rcases family_descends (prefixWord ++ tailWord_889098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889205 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_889205 : Nat := 118140960795 + 889205 * 2 ^ 59
def prefixEnd_889205 : Nat := 4983230072969 + 3 ^ 40 * 889205 * 2
def baseEnd_889205 : Nat := 304393043587532476698751

theorem tailTrace_889205 : CollatzResearch.WordTrace tailWord_889205 prefixEnd_889205 304393043587532476698751 := by
  unfold tailWord_889205
  simp only [CollatzResearch.WordTrace]
  refine ⟨32431970743569623968589069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21621313829046415979059379 32431970743569623968589069)
  ·
    refine ⟨12161989028838608988220901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32431970743569623968589069 12161989028838608988220901)
    ·
      refine ⟨2280372942907239185291419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12161989028838608988220901 2280372942907239185291419)
      ·
        refine ⟨3420559414360858777937129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280372942907239185291419 3420559414360858777937129)
        ·
          refine ⟨2565419560770644083452847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3420559414360858777937129 2565419560770644083452847)
          ·
            refine ⟨3848129341155966125179271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2565419560770644083452847 3848129341155966125179271)
            ·
              refine ⟨5772194011733949187768907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848129341155966125179271 5772194011733949187768907)
              ·
                refine ⟨8658291017600923781653361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5772194011733949187768907 8658291017600923781653361)
                ·
                  refine ⟨6493718263200692836240021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8658291017600923781653361 6493718263200692836240021)
                  ·
                    refine ⟨304393043587532476698751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6493718263200692836240021 304393043587532476698751)
                    ·
                      rfl

theorem cell22_889205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_889205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889205 prefixEnd_889205 := by exact prefixLift 889205
  have htrace : WordTrace (prefixWord ++ tailWord_889205) baseStart_889205 baseEnd_889205 := by
    simpa [prefixWord, tailWord_889205, baseEnd_889205] using wordTrace_append hprefix tailTrace_889205
  have hstable : (prefixWord ++ tailWord_889205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889205).length < 2 ^ (prefixWord ++ tailWord_889205).sum := by decide
  have hdescent : baseEnd_889205 < baseStart_889205 := by decide
  rcases family_descends (prefixWord ++ tailWord_889205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889220 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 5]
def baseStart_889220 : Nat := 118140960795 + 889220 * 2 ^ 59
def prefixEnd_889220 : Nat := 4983230072969 + 3 ^ 40 * 889220 * 2
def baseEnd_889220 : Nat := 101466059464692479191235

theorem tailTrace_889220 : CollatzResearch.WordTrace tailWord_889220 prefixEnd_889220 101466059464692479191235 := by
  unfold tailWord_889220
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216258919257640765192557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21621678559010187686923409 16216258919257640765192557)
  ·
    refine ⟨6081097094721615286947209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16216258919257640765192557 6081097094721615286947209)
    ·
      refine ⟨4560822821041211465210407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6081097094721615286947209 4560822821041211465210407)
      ·
        refine ⟨6841234231561817197815611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560822821041211465210407 6841234231561817197815611)
        ·
          refine ⟨10261851347342725796723417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841234231561817197815611 10261851347342725796723417)
          ·
            refine ⟨7696388510507044347542563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10261851347342725796723417 7696388510507044347542563)
            ·
              refine ⟨11544582765760566521313845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7696388510507044347542563 11544582765760566521313845)
              ·
                refine ⟨1082304634290053111373173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11544582765760566521313845 1082304634290053111373173)
                ·
                  refine ⟨101466059464692479191235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1082304634290053111373173 101466059464692479191235)
                  ·
                    rfl

theorem cell22_889220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_889220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889220 prefixEnd_889220 := by exact prefixLift 889220
  have htrace : WordTrace (prefixWord ++ tailWord_889220) baseStart_889220 baseEnd_889220 := by
    simpa [prefixWord, tailWord_889220, baseEnd_889220] using wordTrace_append hprefix tailTrace_889220
  have hstable : (prefixWord ++ tailWord_889220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889220).length < 2 ^ (prefixWord ++ tailWord_889220).sum := by decide
  have hdescent : baseEnd_889220 < baseStart_889220 := by decide
  rcases family_descends (prefixWord ++ tailWord_889220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889258 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_889258 : Nat := 118140960795 + 889258 * 2 ^ 59
def prefixEnd_889258 : Nat := 4983230072969 + 3 ^ 40 * 889258 * 2
def baseEnd_889258 : Nat := 304411186570658005123589

theorem tailTrace_889258 : CollatzResearch.WordTrace tailWord_889258 prefixEnd_889258 304411186570658005123589 := by
  unfold tailWord_889258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8108475953094403505067107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21622602541585076013512285 8108475953094403505067107)
  ·
    refine ⟨12162713929641605257600661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8108475953094403505067107 12162713929641605257600661)
    ·
      refine ⟨570127215451950246450031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12162713929641605257600661 570127215451950246450031)
      ·
        refine ⟨855190823177925369675047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570127215451950246450031 855190823177925369675047)
        ·
          refine ⟨1282786234766888054512571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855190823177925369675047 1282786234766888054512571)
          ·
            refine ⟨1924179352150332081768857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282786234766888054512571 1924179352150332081768857)
            ·
              refine ⟨1443134514112749061326643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924179352150332081768857 1443134514112749061326643)
              ·
                refine ⟨2164701771169123591989965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443134514112749061326643 2164701771169123591989965)
                ·
                  refine ⟨811763164188421346996237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2164701771169123591989965 811763164188421346996237)
                  ·
                    refine ⟨304411186570658005123589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 811763164188421346996237 304411186570658005123589)
                    ·
                      rfl

theorem cell22_889258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_889258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889258 prefixEnd_889258 := by exact prefixLift 889258
  have htrace : WordTrace (prefixWord ++ tailWord_889258) baseStart_889258 baseEnd_889258 := by
    simpa [prefixWord, tailWord_889258, baseEnd_889258] using wordTrace_append hprefix tailTrace_889258
  have hstable : (prefixWord ++ tailWord_889258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889258).length < 2 ^ (prefixWord ++ tailWord_889258).sum := by decide
  have hdescent : baseEnd_889258 < baseStart_889258 := by decide
  rcases family_descends (prefixWord ++ tailWord_889258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889263 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 9]
def baseStart_889263 : Nat := 118140960795 + 889263 * 2 ^ 59
def prefixEnd_889263 : Nat := 4983230072969 + 3 ^ 40 * 889263 * 2
def baseEnd_889263 : Nat := 304412898172839658748573

theorem tailTrace_889263 : CollatzResearch.WordTrace tailWord_889263 prefixEnd_889263 304412898172839658748573 := by
  unfold tailWord_889263
  simp only [CollatzResearch.WordTrace]
  refine ⟨32434086177359499874200443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21622724118239666582800295 32434086177359499874200443)
  ·
    refine ⟨48651129266039249811300665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32434086177359499874200443 48651129266039249811300665)
    ·
      refine ⟨36488346949529437358475499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48651129266039249811300665 36488346949529437358475499)
      ·
        refine ⟨54732520424294156037713249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36488346949529437358475499 54732520424294156037713249)
        ·
          refine ⟨41049390318220617028284937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54732520424294156037713249 41049390318220617028284937)
          ·
            refine ⟨30787042738665462771213703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41049390318220617028284937 30787042738665462771213703)
            ·
              refine ⟨46180564107998194156820555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30787042738665462771213703 46180564107998194156820555)
              ·
                refine ⟨69270846161997291235230833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46180564107998194156820555 69270846161997291235230833)
                ·
                  refine ⟨51953134621497968426423125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69270846161997291235230833 51953134621497968426423125)
                  ·
                    refine ⟨304412898172839658748573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 51953134621497968426423125 304412898172839658748573)
                    ·
                      rfl

theorem cell22_889263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_889263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889263 prefixEnd_889263 := by exact prefixLift 889263
  have htrace : WordTrace (prefixWord ++ tailWord_889263) baseStart_889263 baseEnd_889263 := by
    simpa [prefixWord, tailWord_889263, baseEnd_889263] using wordTrace_append hprefix tailTrace_889263
  have hstable : (prefixWord ++ tailWord_889263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889263).length < 2 ^ (prefixWord ++ tailWord_889263).sum := by decide
  have hdescent : baseEnd_889263 < baseStart_889263 := by decide
  rcases family_descends (prefixWord ++ tailWord_889263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889265 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 6]
def baseStart_889265 : Nat := 118140960795 + 889265 * 2 ^ 59
def prefixEnd_889265 : Nat := 4983230072969 + 3 ^ 40 * 889265 * 2
def baseEnd_889265 : Nat := 101471194271237440066189

theorem tailTrace_889265 : CollatzResearch.WordTrace tailWord_889265 prefixEnd_889265 101471194271237440066189 := by
  unfold tailWord_889265
  simp only [CollatzResearch.WordTrace]
  refine ⟨32434159123352254215773249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21622772748901502810515499 32434159123352254215773249)
  ·
    refine ⟨24325619342514190661829937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32434159123352254215773249 24325619342514190661829937)
    ·
      refine ⟨18244214506885642996372453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24325619342514190661829937 18244214506885642996372453)
      ·
        refine ⟨3420790220041058061819835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18244214506885642996372453 3420790220041058061819835)
        ·
          refine ⟨5131185330061587092729753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3420790220041058061819835 5131185330061587092729753)
          ·
            refine ⟨3848388997546190319547315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5131185330061587092729753 3848388997546190319547315)
            ·
              refine ⟨5772583496319285479320973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848388997546190319547315 5772583496319285479320973)
              ·
                refine ⟨2164718811119732054745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5772583496319285479320973 2164718811119732054745365)
                ·
                  refine ⟨101471194271237440066189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2164718811119732054745365 101471194271237440066189)
                  ·
                    rfl

theorem cell22_889265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_889265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889265 prefixEnd_889265 := by exact prefixLift 889265
  have htrace : WordTrace (prefixWord ++ tailWord_889265) baseStart_889265 baseEnd_889265 := by
    simpa [prefixWord, tailWord_889265, baseEnd_889265] using wordTrace_append hprefix tailTrace_889265
  have hstable : (prefixWord ++ tailWord_889265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889265).length < 2 ^ (prefixWord ++ tailWord_889265).sum := by decide
  have hdescent : baseEnd_889265 < baseStart_889265 := by decide
  rcases family_descends (prefixWord ++ tailWord_889265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889295 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 2, 4]
def baseStart_889295 : Nat := 118140960795 + 889295 * 2 ^ 59
def prefixEnd_889295 : Nat := 4983230072969 + 3 ^ 40 * 889295 * 2
def baseEnd_889295 : Nat := 304423852426802241948475

theorem tailTrace_889295 : CollatzResearch.WordTrace tailWord_889295 prefixEnd_889295 304423852426802241948475 := by
  unfold tailWord_889295
  simp only [CollatzResearch.WordTrace]
  refine ⟨32435253313243569339365339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21623502208829046226243559 32435253313243569339365339)
  ·
    refine ⟨48652879969865354009048009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32435253313243569339365339 48652879969865354009048009)
    ·
      refine ⟨36489659977399015506786007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48652879969865354009048009 36489659977399015506786007)
      ·
        refine ⟨54734489966098523260179011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36489659977399015506786007 54734489966098523260179011)
        ·
          refine ⟨82101734949147784890268517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54734489966098523260179011 82101734949147784890268517)
          ·
            refine ⟨15394075302965209666925347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82101734949147784890268517 15394075302965209666925347)
            ·
              refine ⟨23091112954447814500388021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15394075302965209666925347 23091112954447814500388021)
              ·
                refine ⟨2164791839479482609411377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23091112954447814500388021 2164791839479482609411377)
                ·
                  refine ⟨1623593879609611957058533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2164791839479482609411377 1623593879609611957058533)
                  ·
                    refine ⟨304423852426802241948475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1623593879609611957058533 304423852426802241948475)
                    ·
                      rfl

theorem cell22_889295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_889295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889295 prefixEnd_889295 := by exact prefixLift 889295
  have htrace : WordTrace (prefixWord ++ tailWord_889295) baseStart_889295 baseEnd_889295 := by
    simpa [prefixWord, tailWord_889295, baseEnd_889295] using wordTrace_append hprefix tailTrace_889295
  have hstable : (prefixWord ++ tailWord_889295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889295).length < 2 ^ (prefixWord ++ tailWord_889295).sum := by decide
  have hdescent : baseEnd_889295 < baseStart_889295 := by decide
  rcases family_descends (prefixWord ++ tailWord_889295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889346 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_889346 : Nat := 118140960795 + 889346 * 2 ^ 59
def prefixEnd_889346 : Nat := 4983230072969 + 3 ^ 40 * 889346 * 2
def baseEnd_889346 : Nat := 304441310769055108923319

theorem tailTrace_889346 : CollatzResearch.WordTrace tailWord_889346 prefixEnd_889346 304441310769055108923319 := by
  unfold tailWord_889346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8109278359014701262367973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21624742290705870032981261 8109278359014701262367973)
  ·
    refine ⟨1520489692315256486693995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8109278359014701262367973 1520489692315256486693995)
    ·
      refine ⟨2280734538472884730040993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520489692315256486693995 2280734538472884730040993)
      ·
        refine ⟨1710550903854663547530745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2280734538472884730040993 1710550903854663547530745)
        ·
          refine ⟨1282913177890997660648059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1710550903854663547530745 1282913177890997660648059)
          ·
            refine ⟨1924369766836496490972089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282913177890997660648059 1924369766836496490972089)
            ·
              refine ⟨1443277325127372368229067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924369766836496490972089 1443277325127372368229067)
              ·
                refine ⟨2164915987691058552343601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443277325127372368229067 2164915987691058552343601)
                ·
                  refine ⟨1623686990768293914257701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2164915987691058552343601 1623686990768293914257701)
                  ·
                    refine ⟨304441310769055108923319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1623686990768293914257701 304441310769055108923319)
                    ·
                      rfl

theorem cell22_889346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_889346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889346 prefixEnd_889346 := by exact prefixLift 889346
  have htrace : WordTrace (prefixWord ++ tailWord_889346) baseStart_889346 baseEnd_889346 := by
    simpa [prefixWord, tailWord_889346, baseEnd_889346] using wordTrace_append hprefix tailTrace_889346
  have hstable : (prefixWord ++ tailWord_889346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889346).length < 2 ^ (prefixWord ++ tailWord_889346).sum := by decide
  have hdescent : baseEnd_889346 < baseStart_889346 := by decide
  rcases family_descends (prefixWord ++ tailWord_889346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889372 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 5]
def baseStart_889372 : Nat := 118140960795 + 889372 * 2 ^ 59
def prefixEnd_889372 : Nat := 4983230072969 + 3 ^ 40 * 889372 * 2
def baseEnd_889372 : Nat := 101483403700133235924413

theorem tailTrace_889372 : CollatzResearch.WordTrace tailWord_889372 prefixEnd_889372 101483403700133235924413 := by
  unfold tailWord_889372
  simp only [CollatzResearch.WordTrace]
  refine ⟨16219030866982305744959185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21625374489309740993278913 16219030866982305744959185)
  ·
    refine ⟨12164273150236729308719389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16219030866982305744959185 12164273150236729308719389)
    ·
      refine ⟨4561602431338773490769771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12164273150236729308719389 4561602431338773490769771)
      ·
        refine ⟨6842403647008160236154657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4561602431338773490769771 6842403647008160236154657)
        ·
          refine ⟨5131802735256120177115993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6842403647008160236154657 5131802735256120177115993)
          ·
            refine ⟨3848852051442090132836995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5131802735256120177115993 3848852051442090132836995)
            ·
              refine ⟨5773278077163135199255493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3848852051442090132836995 5773278077163135199255493)
              ·
                refine ⟨1082489639468087849860405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5773278077163135199255493 1082489639468087849860405)
                ·
                  refine ⟨101483403700133235924413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1082489639468087849860405 101483403700133235924413)
                  ·
                    rfl

theorem cell22_889372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_889372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889372 prefixEnd_889372 := by exact prefixLift 889372
  have htrace : WordTrace (prefixWord ++ tailWord_889372) baseStart_889372 baseEnd_889372 := by
    simpa [prefixWord, tailWord_889372, baseEnd_889372] using wordTrace_append hprefix tailTrace_889372
  have hstable : (prefixWord ++ tailWord_889372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889372).length < 2 ^ (prefixWord ++ tailWord_889372).sum := by decide
  have hdescent : baseEnd_889372 < baseStart_889372 := by decide
  rcases family_descends (prefixWord ++ tailWord_889372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889402 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_889402 : Nat := 118140960795 + 889402 * 2 ^ 59
def prefixEnd_889402 : Nat := 4983230072969 + 3 ^ 40 * 889402 * 2
def baseEnd_889402 : Nat := 304460480713489629523147

theorem tailTrace_889402 : CollatzResearch.WordTrace tailWord_889402 prefixEnd_889402 304460480713489629523147 := by
  unfold tailWord_889402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8109788980963981653377615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21626103949237284409006973 8109788980963981653377615)
  ·
    refine ⟨12164683471445972480066423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8109788980963981653377615 12164683471445972480066423)
    ·
      refine ⟨18247025207168958720099635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12164683471445972480066423 18247025207168958720099635)
      ·
        refine ⟨27370537810753438080149453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18247025207168958720099635 27370537810753438080149453)
        ·
          refine ⟨10263951679032539280056045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27370537810753438080149453 10263951679032539280056045)
          ·
            refine ⟨3848981879637202230021017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10263951679032539280056045 3848981879637202230021017)
            ·
              refine ⟨2886736409727901672515763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3848981879637202230021017 2886736409727901672515763)
              ·
                refine ⟨4330104614591852508773645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886736409727901672515763 4330104614591852508773645)
                ·
                  refine ⟨1623789230471944690790117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4330104614591852508773645 1623789230471944690790117)
                  ·
                    refine ⟨304460480713489629523147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1623789230471944690790117 304460480713489629523147)
                    ·
                      rfl

theorem cell22_889402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_889402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889402 prefixEnd_889402 := by exact prefixLift 889402
  have htrace : WordTrace (prefixWord ++ tailWord_889402) baseStart_889402 baseEnd_889402 := by
    simpa [prefixWord, tailWord_889402, baseEnd_889402] using wordTrace_append hprefix tailTrace_889402
  have hstable : (prefixWord ++ tailWord_889402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889402).length < 2 ^ (prefixWord ++ tailWord_889402).sum := by decide
  have hdescent : baseEnd_889402 < baseStart_889402 := by decide
  rcases family_descends (prefixWord ++ tailWord_889402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889419 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 1, 4]
def baseStart_889419 : Nat := 118140960795 + 889419 * 2 ^ 59
def prefixEnd_889419 : Nat := 4983230072969 + 3 ^ 40 * 889419 * 2
def baseEnd_889419 : Nat := 304466300160907251848095

theorem tailTrace_889419 : CollatzResearch.WordTrace tailWord_889419 prefixEnd_889419 304466300160907251848095 := by
  unfold tailWord_889419
  simp only [CollatzResearch.WordTrace]
  refine ⟨32439775964794338516879311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21626517309862892344586207 32439775964794338516879311)
  ·
    refine ⟨48659663947191507775318967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32439775964794338516879311 48659663947191507775318967)
    ·
      refine ⟨72989495920787261662978451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48659663947191507775318967 72989495920787261662978451)
      ·
        refine ⟨109484243881180892494467677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72989495920787261662978451 109484243881180892494467677)
        ·
          refine ⟨41056591455442834685425379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109484243881180892494467677 41056591455442834685425379)
          ·
            refine ⟨61584887183164252028138069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41056591455442834685425379 61584887183164252028138069)
            ·
              refine ⟨721697896677706078454743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 61584887183164252028138069 721697896677706078454743)
              ·
                refine ⟨1082546845016559117682115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721697896677706078454743 1082546845016559117682115)
                ·
                  refine ⟨1623820267524838676523173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1082546845016559117682115 1623820267524838676523173)
                  ·
                    refine ⟨304466300160907251848095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1623820267524838676523173 304466300160907251848095)
                    ·
                      rfl

theorem cell22_889419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 4].length) (baseStart_889419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889419 prefixEnd_889419 := by exact prefixLift 889419
  have htrace : WordTrace (prefixWord ++ tailWord_889419) baseStart_889419 baseEnd_889419 := by
    simpa [prefixWord, tailWord_889419, baseEnd_889419] using wordTrace_append hprefix tailTrace_889419
  have hstable : (prefixWord ++ tailWord_889419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889419).length < 2 ^ (prefixWord ++ tailWord_889419).sum := by decide
  have hdescent : baseEnd_889419 < baseStart_889419 := by decide
  rcases family_descends (prefixWord ++ tailWord_889419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889522 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_889522 : Nat := 118140960795 + 889522 * 2 ^ 59
def prefixEnd_889522 : Nat := 4983230072969 + 3 ^ 40 * 889522 * 2
def baseEnd_889522 : Nat := 304501559165849316522779

theorem tailTrace_889522 : CollatzResearch.WordTrace tailWord_889522 prefixEnd_889522 304501559165849316522779 := by
  unfold tailWord_889522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8110883170855296776969705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21629021788947458071919213 8110883170855296776969705)
  ·
    refine ⟨6083162378141472582727279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8110883170855296776969705 6083162378141472582727279)
    ·
      refine ⟨9124743567212208874090919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083162378141472582727279 9124743567212208874090919)
      ·
        refine ⟨13687115350818313311136379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9124743567212208874090919 13687115350818313311136379)
        ·
          refine ⟨20530673026227469966704569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13687115350818313311136379 20530673026227469966704569)
          ·
            refine ⟨15398004769670602475028427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20530673026227469966704569 15398004769670602475028427)
            ·
              refine ⟨23097007154505903712542641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15398004769670602475028427 23097007154505903712542641)
              ·
                refine ⟨17322755365879427784406981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23097007154505903712542641 17322755365879427784406981)
                ·
                  refine ⟨3248016631102392709576309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17322755365879427784406981 3248016631102392709576309)
                  ·
                    refine ⟨304501559165849316522779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3248016631102392709576309 304501559165849316522779)
                    ·
                      rfl

theorem cell22_889522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_889522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889522 prefixEnd_889522 := by exact prefixLift 889522
  have htrace : WordTrace (prefixWord ++ tailWord_889522) baseStart_889522 baseEnd_889522 := by
    simpa [prefixWord, tailWord_889522, baseEnd_889522] using wordTrace_append hprefix tailTrace_889522
  have hstable : (prefixWord ++ tailWord_889522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889522).length < 2 ^ (prefixWord ++ tailWord_889522).sum := by decide
  have hdescent : baseEnd_889522 < baseStart_889522 := by decide
  rcases family_descends (prefixWord ++ tailWord_889522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889556 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_889556 : Nat := 118140960795 + 889556 * 2 ^ 59
def prefixEnd_889556 : Nat := 4983230072969 + 3 ^ 40 * 889556 * 2
def baseEnd_889556 : Nat := 304513198060684561172675

theorem tailTrace_889556 : CollatzResearch.WordTrace tailWord_889556 prefixEnd_889556 304513198060684561172675 := by
  unfold tailWord_889556
  simp only [CollatzResearch.WordTrace]
  refine ⟨16222386382649005457308261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21629848510198673943077681 16222386382649005457308261)
  ·
    refine ⟨3041697446746688523245299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16222386382649005457308261 3041697446746688523245299)
    ·
      refine ⟨4562546170120032784867949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3041697446746688523245299 4562546170120032784867949)
      ·
        refine ⟨1710954813795012294325481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4562546170120032784867949 1710954813795012294325481)
        ·
          refine ⟨1283216110346259220744111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1710954813795012294325481 1283216110346259220744111)
          ·
            refine ⟨1924824165519388831116167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283216110346259220744111 1924824165519388831116167)
            ·
              refine ⟨2887236248279083246674251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924824165519388831116167 2887236248279083246674251)
              ·
                refine ⟨4330854372418624870011377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887236248279083246674251 4330854372418624870011377)
                ·
                  refine ⟨3248140779313968652508533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4330854372418624870011377 3248140779313968652508533)
                  ·
                    refine ⟨304513198060684561172675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3248140779313968652508533 304513198060684561172675)
                    ·
                      rfl

theorem cell22_889556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_889556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889556 prefixEnd_889556 := by exact prefixLift 889556
  have htrace : WordTrace (prefixWord ++ tailWord_889556) baseStart_889556 baseEnd_889556 := by
    simpa [prefixWord, tailWord_889556, baseEnd_889556] using wordTrace_append hprefix tailTrace_889556
  have hstable : (prefixWord ++ tailWord_889556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889556).length < 2 ^ (prefixWord ++ tailWord_889556).sum := by decide
  have hdescent : baseEnd_889556 < baseStart_889556 := by decide
  rcases family_descends (prefixWord ++ tailWord_889556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889569 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 6]
def baseStart_889569 : Nat := 118140960795 + 889569 * 2 ^ 59
def prefixEnd_889569 : Nat := 4983230072969 + 3 ^ 40 * 889569 * 2
def baseEnd_889569 : Nat := 101505882742118953532545

theorem tailTrace_889569 : CollatzResearch.WordTrace tailWord_889569 prefixEnd_889569 101505882742118953532545 := by
  unfold tailWord_889569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32445246914250914134839761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21630164609500609423226507 32445246914250914134839761)
  ·
    refine ⟨24333935185688185601129821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32445246914250914134839761 24333935185688185601129821)
    ·
      refine ⟨9125225694633069600423683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24333935185688185601129821 9125225694633069600423683)
      ·
        refine ⟨13687838541949604400635525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9125225694633069600423683 13687838541949604400635525)
        ·
          refine ⟨2566469726615550825119161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13687838541949604400635525 2566469726615550825119161)
          ·
            refine ⟨1924852294961663118839371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566469726615550825119161 1924852294961663118839371)
            ·
              refine ⟨2887278442442494678259057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1924852294961663118839371 2887278442442494678259057)
              ·
                refine ⟨2165458831831871008694293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2887278442442494678259057 2165458831831871008694293)
                ·
                  refine ⟨101505882742118953532545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2165458831831871008694293 101505882742118953532545)
                  ·
                    rfl

theorem cell22_889569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_889569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889569 prefixEnd_889569 := by exact prefixLift 889569
  have htrace : WordTrace (prefixWord ++ tailWord_889569) baseStart_889569 baseEnd_889569 := by
    simpa [prefixWord, tailWord_889569, baseEnd_889569] using wordTrace_append hprefix tailTrace_889569
  have hstable : (prefixWord ++ tailWord_889569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889569).length < 2 ^ (prefixWord ++ tailWord_889569).sum := by decide
  have hdescent : baseEnd_889569 < baseStart_889569 := by decide
  rcases family_descends (prefixWord ++ tailWord_889569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889584 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 4, 3]
def baseStart_889584 : Nat := 118140960795 + 889584 * 2 ^ 59
def prefixEnd_889584 : Nat := 4983230072969 + 3 ^ 40 * 889584 * 2
def baseEnd_889584 : Nat := 304522783032901821472589

theorem tailTrace_889584 : CollatzResearch.WordTrace tailWord_889584 prefixEnd_889584 304522783032901821472589 := by
  unfold tailWord_889584
  simp only [CollatzResearch.WordTrace]
  refine ⟨16222897004598285848317903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21630529339464381131090537 16222897004598285848317903)
  ·
    refine ⟨24334345506897428772476855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16222897004598285848317903 24334345506897428772476855)
    ·
      refine ⟨36501518260346143158715283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24334345506897428772476855 36501518260346143158715283)
      ·
        refine ⟨54752277390519214738072925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36501518260346143158715283 54752277390519214738072925)
        ·
          refine ⟨20532104021444705526777347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54752277390519214738072925 20532104021444705526777347)
          ·
            refine ⟨30798156032167058290166021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20532104021444705526777347 30798156032167058290166021)
            ·
              refine ⟨5774654256031323429406129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30798156032167058290166021 5774654256031323429406129)
              ·
                refine ⟨4330990692023492572054597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5774654256031323429406129 4330990692023492572054597)
                ·
                  refine ⟨812060754754404857260237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4330990692023492572054597 812060754754404857260237)
                  ·
                    refine ⟨304522783032901821472589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812060754754404857260237 304522783032901821472589)
                    ·
                      rfl

theorem cell22_889584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_889584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889584 prefixEnd_889584 := by exact prefixLift 889584
  have htrace : WordTrace (prefixWord ++ tailWord_889584) baseStart_889584 baseEnd_889584 := by
    simpa [prefixWord, tailWord_889584, baseEnd_889584] using wordTrace_append hprefix tailTrace_889584
  have hstable : (prefixWord ++ tailWord_889584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889584).length < 2 ^ (prefixWord ++ tailWord_889584).sum := by decide
  have hdescent : baseEnd_889584 < baseStart_889584 := by decide
  rcases family_descends (prefixWord ++ tailWord_889584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889586 : List Nat := [3, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_889586 : Nat := 118140960795 + 889586 * 2 ^ 59
def prefixEnd_889586 : Nat := 4983230072969 + 3 ^ 40 * 889586 * 2
def baseEnd_889586 : Nat := 101507822557924827640861

theorem tailTrace_889586 : CollatzResearch.WordTrace tailWord_889586 prefixEnd_889586 101507822557924827640861 := by
  unfold tailWord_889586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8111466738797331509552153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21630577970126217358805741 8111466738797331509552153)
  ·
    refine ⟨6083600054097998632164115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8111466738797331509552153 6083600054097998632164115)
    ·
      refine ⟨9125400081146997948246173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083600054097998632164115 9125400081146997948246173)
      ·
        refine ⟨3422025030430124230592315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9125400081146997948246173 3422025030430124230592315)
        ·
          refine ⟨5133037545645186345888473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422025030430124230592315 5133037545645186345888473)
          ·
            refine ⟨3849778159233889759416355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5133037545645186345888473 3849778159233889759416355)
            ·
              refine ⟨5774667238850834639124533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3849778159233889759416355 5774667238850834639124533)
              ·
                refine ⟨541375053642265747417925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5774667238850834639124533 541375053642265747417925)
                ·
                  refine ⟨101507822557924827640861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541375053642265747417925 101507822557924827640861)
                  ·
                    rfl

theorem cell22_889586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_889586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889586 prefixEnd_889586 := by exact prefixLift 889586
  have htrace : WordTrace (prefixWord ++ tailWord_889586) baseStart_889586 baseEnd_889586 := by
    simpa [prefixWord, tailWord_889586, baseEnd_889586] using wordTrace_append hprefix tailTrace_889586
  have hstable : (prefixWord ++ tailWord_889586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889586).length < 2 ^ (prefixWord ++ tailWord_889586).sum := by decide
  have hdescent : baseEnd_889586 < baseStart_889586 := by decide
  rcases family_descends (prefixWord ++ tailWord_889586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889597 : List Nat := [1, 4, 1, 1, 1, 1, 13]
def baseStart_889597 : Nat := 118140960795 + 889597 * 2 ^ 59
def prefixEnd_889597 : Nat := 4983230072969 + 3 ^ 40 * 889597 * 2
def baseEnd_889597 : Nat := 11278786414762004477687

theorem tailTrace_889597 : CollatzResearch.WordTrace tailWord_889597 prefixEnd_889597 11278786414762004477687 := by
  unfold tailWord_889597
  simp only [CollatzResearch.WordTrace]
  refine ⟨32446268158149474916859045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21630845438766316611239363 32446268158149474916859045)
  ·
    refine ⟨6083675279653026546911071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32446268158149474916859045 6083675279653026546911071)
    ·
      refine ⟨9125512919479539820366607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6083675279653026546911071 9125512919479539820366607)
      ·
        refine ⟨13688269379219309730549911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9125512919479539820366607 13688269379219309730549911)
        ·
          refine ⟨20532404068828964595824867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13688269379219309730549911 20532404068828964595824867)
          ·
            refine ⟨30798606103243446893737301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20532404068828964595824867 30798606103243446893737301)
            ·
              refine ⟨11278786414762004477687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 30798606103243446893737301 11278786414762004477687)
              ·
                rfl

theorem cell22_889597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 13].length) (baseStart_889597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889597 prefixEnd_889597 := by exact prefixLift 889597
  have htrace : WordTrace (prefixWord ++ tailWord_889597) baseStart_889597 baseEnd_889597 := by
    simpa [prefixWord, tailWord_889597, baseEnd_889597] using wordTrace_append hprefix tailTrace_889597
  have hstable : (prefixWord ++ tailWord_889597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889597).length < 2 ^ (prefixWord ++ tailWord_889597).sum := by decide
  have hdescent : baseEnd_889597 < baseStart_889597 := by decide
  rcases family_descends (prefixWord ++ tailWord_889597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889631 : List Nat := [1, 1, 2, 4, 2, 4, 2, 6]
def baseStart_889631 : Nat := 118140960795 + 889631 * 2 ^ 59
def prefixEnd_889631 : Nat := 4983230072969 + 3 ^ 40 * 889631 * 2
def baseEnd_889631 : Nat := 33837652454823262838605

theorem tailTrace_889631 : CollatzResearch.WordTrace tailWord_889631 prefixEnd_889631 33837652454823262838605 := by
  unfold tailWord_889631
  simp only [CollatzResearch.WordTrace]
  refine ⟨32447508240026298723596747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21631672160017532482397831 32447508240026298723596747)
  ·
    refine ⟨48671262360039448085395121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32447508240026298723596747 48671262360039448085395121)
    ·
      refine ⟨36503446770029586064046341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48671262360039448085395121 36503446770029586064046341)
      ·
        refine ⟨6844396269380547387008689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36503446770029586064046341 6844396269380547387008689)
        ·
          refine ⟨5133297202035410540256517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6844396269380547387008689 5133297202035410540256517)
          ·
            refine ⟨962493225381639476298097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5133297202035410540256517 962493225381639476298097)
            ·
              refine ⟨721869919036229607223573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962493225381639476298097 721869919036229607223573)
              ·
                refine ⟨33837652454823262838605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 721869919036229607223573 33837652454823262838605)
                ·
                  rfl

theorem cell22_889631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 6].length) (baseStart_889631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889631 prefixEnd_889631 := by exact prefixLift 889631
  have htrace : WordTrace (prefixWord ++ tailWord_889631) baseStart_889631 baseEnd_889631 := by
    simpa [prefixWord, tailWord_889631, baseEnd_889631] using wordTrace_append hprefix tailTrace_889631
  have hstable : (prefixWord ++ tailWord_889631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889631).length < 2 ^ (prefixWord ++ tailWord_889631).sum := by decide
  have hdescent : baseEnd_889631 < baseStart_889631 := by decide
  rcases family_descends (prefixWord ++ tailWord_889631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889663 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 3, 3]
def baseStart_889663 : Nat := 118140960795 + 889663 * 2 ^ 59
def prefixEnd_889663 : Nat := 4983230072969 + 3 ^ 40 * 889663 * 2
def baseEnd_889663 : Nat := 304549826347371948747347

theorem tailTrace_889663 : CollatzResearch.WordTrace tailWord_889663 prefixEnd_889663 304549826347371948747347 := by
  unfold tailWord_889663
  simp only [CollatzResearch.WordTrace]
  refine ⟨32448675375910368188761643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21632450250606912125841095 32448675375910368188761643)
  ·
    refine ⟨48673013063865552283142465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32448675375910368188761643 48673013063865552283142465)
    ·
      refine ⟨36504759797899164212356849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48673013063865552283142465 36504759797899164212356849)
      ·
        refine ⟨27378569848424373159267637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36504759797899164212356849 27378569848424373159267637)
        ·
          refine ⟨2566740923289784983681341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27378569848424373159267637 2566740923289784983681341)
          ·
            refine ⟨962527846233669368880503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2566740923289784983681341 962527846233669368880503)
            ·
              refine ⟨1443791769350504053320755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962527846233669368880503 1443791769350504053320755)
              ·
                refine ⟨2165687654025756079981133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443791769350504053320755 2165687654025756079981133)
                ·
                  refine ⟨812132870259658529992925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2165687654025756079981133 812132870259658529992925)
                  ·
                    refine ⟨304549826347371948747347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812132870259658529992925 304549826347371948747347)
                    ·
                      rfl

theorem cell22_889663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_889663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889663 prefixEnd_889663 := by exact prefixLift 889663
  have htrace : WordTrace (prefixWord ++ tailWord_889663) baseStart_889663 baseEnd_889663 := by
    simpa [prefixWord, tailWord_889663, baseEnd_889663] using wordTrace_append hprefix tailTrace_889663
  have hstable : (prefixWord ++ tailWord_889663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889663).length < 2 ^ (prefixWord ++ tailWord_889663).sum := by decide
  have hdescent : baseEnd_889663 < baseStart_889663 := by decide
  rcases family_descends (prefixWord ++ tailWord_889663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889676 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 5]
def baseStart_889676 : Nat := 118140960795 + 889676 * 2 ^ 59
def prefixEnd_889676 : Nat := 4983230072969 + 3 ^ 40 * 889676 * 2
def baseEnd_889676 : Nat := 101518092171014749390769

theorem tailTrace_889676 : CollatzResearch.WordTrace tailWord_889676 prefixEnd_889676 101518092171014749390769 := by
  unfold tailWord_889676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16224574762431635704492441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21632766349908847605989921 16224574762431635704492441)
  ·
    refine ⟨12168431071823726778369331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16224574762431635704492441 12168431071823726778369331)
    ·
      refine ⟨18252646607735590167553997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12168431071823726778369331 18252646607735590167553997)
      ·
        refine ⟨6844742477900846312832749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18252646607735590167553997 6844742477900846312832749)
        ·
          refine ⟨2566778429212817367312281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6844742477900846312832749 2566778429212817367312281)
          ·
            refine ⟨1925083821909613025484211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566778429212817367312281 1925083821909613025484211)
            ·
              refine ⟨2887625732864419538226317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925083821909613025484211 2887625732864419538226317)
              ·
                refine ⟨1082859649824157326834869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2887625732864419538226317 1082859649824157326834869)
                ·
                  refine ⟨101518092171014749390769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1082859649824157326834869 101518092171014749390769)
                  ·
                    rfl

theorem cell22_889676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_889676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889676 prefixEnd_889676 := by exact prefixLift 889676
  have htrace : WordTrace (prefixWord ++ tailWord_889676) baseStart_889676 baseEnd_889676 := by
    simpa [prefixWord, tailWord_889676, baseEnd_889676] using wordTrace_append hprefix tailTrace_889676
  have hstable : (prefixWord ++ tailWord_889676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889676).length < 2 ^ (prefixWord ++ tailWord_889676).sum := by decide
  have hdescent : baseEnd_889676 < baseStart_889676 := by decide
  rcases family_descends (prefixWord ++ tailWord_889676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889736 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_889736 : Nat := 118140960795 + 889736 * 2 ^ 59
def prefixEnd_889736 : Nat := 4983230072969 + 3 ^ 40 * 889736 * 2
def baseEnd_889736 : Nat := 304574815739224091672123

theorem tailTrace_889736 : CollatzResearch.WordTrace tailWord_889736 prefixEnd_889736 304574815739224091672123 := by
  unfold tailWord_889736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16225668952322950828084531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21634225269763934437446041 16225668952322950828084531)
  ·
    refine ⟨24338503428484426242126797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16225668952322950828084531 24338503428484426242126797)
    ·
      refine ⟨9126938785681659840797549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24338503428484426242126797 9126938785681659840797549)
      ·
        refine ⟨3422602044630622440299081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9126938785681659840797549 3422602044630622440299081)
        ·
          refine ⟨2566951533472966830224311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3422602044630622440299081 2566951533472966830224311)
          ·
            refine ⟨3850427300209450245336467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566951533472966830224311 3850427300209450245336467)
            ·
              refine ⟨5775640950314175368004701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850427300209450245336467 5775640950314175368004701)
              ·
                refine ⟨2165865356367815763001763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5775640950314175368004701 2165865356367815763001763)
                ·
                  refine ⟨3248798034551723644502645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2165865356367815763001763 3248798034551723644502645)
                  ·
                    refine ⟨304574815739224091672123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3248798034551723644502645 304574815739224091672123)
                    ·
                      rfl

theorem cell22_889736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_889736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889736 prefixEnd_889736 := by exact prefixLift 889736
  have htrace : WordTrace (prefixWord ++ tailWord_889736) baseStart_889736 baseEnd_889736 := by
    simpa [prefixWord, tailWord_889736, baseEnd_889736] using wordTrace_append hprefix tailTrace_889736
  have hstable : (prefixWord ++ tailWord_889736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889736).length < 2 ^ (prefixWord ++ tailWord_889736).sum := by decide
  have hdescent : baseEnd_889736 < baseStart_889736 := by decide
  rcases family_descends (prefixWord ++ tailWord_889736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889779 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 2, 6]
def baseStart_889779 : Nat := 118140960795 + 889779 * 2 ^ 59
def prefixEnd_889779 : Nat := 4983230072969 + 3 ^ 40 * 889779 * 2
def baseEnd_889779 : Nat := 304589535517986312846991

theorem tailTrace_889779 : CollatzResearch.WordTrace tailWord_889779 prefixEnd_889779 304589535517986312846991 := by
  unfold tailWord_889779
  simp only [CollatzResearch.WordTrace]
  refine ⟨32452906243490119999984391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21635270828993413333322927 32452906243490119999984391)
  ·
    refine ⟨48679359365235179999976587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32452906243490119999984391 48679359365235179999976587)
    ·
      refine ⟨73019039047852769999964881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48679359365235179999976587 73019039047852769999964881)
      ·
        refine ⟨54764279285889577499973661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73019039047852769999964881 54764279285889577499973661)
        ·
          refine ⟨20536604732208591562490123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54764279285889577499973661 20536604732208591562490123)
          ·
            refine ⟨30804907098312887343735185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20536604732208591562490123 30804907098312887343735185)
            ·
              refine ⟨23103680323734665507801389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30804907098312887343735185 23103680323734665507801389)
              ·
                refine ⟨8663880121400499565425521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23103680323734665507801389 8663880121400499565425521)
                ·
                  refine ⟨6497910091050374674069141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8663880121400499565425521 6497910091050374674069141)
                  ·
                    refine ⟨304589535517986312846991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6497910091050374674069141 304589535517986312846991)
                    ·
                      rfl

theorem cell22_889779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_889779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889779 prefixEnd_889779 := by exact prefixLift 889779
  have htrace : WordTrace (prefixWord ++ tailWord_889779) baseStart_889779 baseEnd_889779 := by
    simpa [prefixWord, tailWord_889779, baseEnd_889779] using wordTrace_append hprefix tailTrace_889779
  have hstable : (prefixWord ++ tailWord_889779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889779).length < 2 ^ (prefixWord ++ tailWord_889779).sum := by decide
  have hdescent : baseEnd_889779 < baseStart_889779 := by decide
  rcases family_descends (prefixWord ++ tailWord_889779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889800 : List Nat := [2, 1, 3, 1, 6, 1, 2, 6]
def baseStart_889800 : Nat := 118140960795 + 889800 * 2 ^ 59
def prefixEnd_889800 : Nat := 4983230072969 + 3 ^ 40 * 889800 * 2
def baseEnd_889800 : Nat := 33844080471905473119103

theorem tailTrace_889800 : CollatzResearch.WordTrace tailWord_889800 prefixEnd_889800 33844080471905473119103 := by
  unfold tailWord_889800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16226836088207020293249427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21635781450942693724332569 16226836088207020293249427)
  ·
    refine ⟨24340254132310530439874141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16226836088207020293249427 24340254132310530439874141)
    ·
      refine ⟨9127595299616448914952803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24340254132310530439874141 9127595299616448914952803)
      ·
        refine ⟨13691392949424673372429205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9127595299616448914952803 13691392949424673372429205)
        ·
          refine ⟨641784044504281564332619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13691392949424673372429205 641784044504281564332619)
          ·
            refine ⟨962676066756422346498929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641784044504281564332619 962676066756422346498929)
            ·
              refine ⟨722007050067316759874197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962676066756422346498929 722007050067316759874197)
              ·
                refine ⟨33844080471905473119103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 722007050067316759874197 33844080471905473119103)
                ·
                  rfl

theorem cell22_889800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 6].length) (baseStart_889800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889800 prefixEnd_889800 := by exact prefixLift 889800
  have htrace : WordTrace (prefixWord ++ tailWord_889800) baseStart_889800 baseEnd_889800 := by
    simpa [prefixWord, tailWord_889800, baseEnd_889800] using wordTrace_append hprefix tailTrace_889800
  have hstable : (prefixWord ++ tailWord_889800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889800).length < 2 ^ (prefixWord ++ tailWord_889800).sum := by decide
  have hdescent : baseEnd_889800 < baseStart_889800 := by decide
  rcases family_descends (prefixWord ++ tailWord_889800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_889890 : List Nat := [3, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_889890 : Nat := 118140960795 + 889890 * 2 ^ 59
def prefixEnd_889890 : Nat := 4983230072969 + 3 ^ 40 * 889890 * 2
def baseEnd_889890 : Nat := 101542511028806341107217

theorem tailTrace_889890 : CollatzResearch.WordTrace tailWord_889890 prefixEnd_889890 101542511028806341107217 := by
  unfold tailWord_889890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8114238686521996489318781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21637969830725323971516749 8114238686521996489318781)
  ·
    refine ⟨3042839507445748683494543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8114238686521996489318781 3042839507445748683494543)
    ·
      refine ⟨4564259261168623025241815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042839507445748683494543 4564259261168623025241815)
      ·
        refine ⟨6846388891752934537862723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564259261168623025241815 6846388891752934537862723)
        ·
          refine ⟨10269583337629401806794085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6846388891752934537862723 10269583337629401806794085)
          ·
            refine ⟨1925546875805512838773891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10269583337629401806794085 1925546875805512838773891)
            ·
              refine ⟨2888320313708269258160837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925546875805512838773891 2888320313708269258160837)
              ·
                refine ⟨541560058820300485905157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2888320313708269258160837 541560058820300485905157)
                ·
                  refine ⟨101542511028806341107217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541560058820300485905157 101542511028806341107217)
                  ·
                    rfl

theorem cell22_889890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_889890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_889890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_889890 prefixEnd_889890 := by exact prefixLift 889890
  have htrace : WordTrace (prefixWord ++ tailWord_889890) baseStart_889890 baseEnd_889890 := by
    simpa [prefixWord, tailWord_889890, baseEnd_889890] using wordTrace_append hprefix tailTrace_889890
  have hstable : (prefixWord ++ tailWord_889890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_889890).length < 2 ^ (prefixWord ++ tailWord_889890).sum := by decide
  have hdescent : baseEnd_889890 < baseStart_889890 := by decide
  rcases family_descends (prefixWord ++ tailWord_889890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890014 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_890014 : Nat := 118140960795 + 890014 * 2 ^ 59
def prefixEnd_890014 : Nat := 4983230072969 + 3 ^ 40 * 890014 * 2
def baseEnd_890014 : Nat := 101556660273508011073757

theorem tailTrace_890014 : CollatzResearch.WordTrace tailWord_890014 prefixEnd_890014 101556660273508011073757 := by
  unfold tailWord_890014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4057684674704844391848637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21640984931759170089859397 4057684674704844391848637)
  ·
    refine ⟨1521631753014316646943239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4057684674704844391848637 1521631753014316646943239)
    ·
      refine ⟨2282447629521474970414859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521631753014316646943239 2282447629521474970414859)
      ·
        refine ⟨3423671444282212455622289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282447629521474970414859 3423671444282212455622289)
        ·
          refine ⟨2567753583211659341716717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3423671444282212455622289 2567753583211659341716717)
          ·
            refine ⟨962907593704372253143769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2567753583211659341716717 962907593704372253143769)
            ·
              refine ⟨722180695278279189857827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962907593704372253143769 722180695278279189857827)
              ·
                refine ⟨1083271042917418784786741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722180695278279189857827 1083271042917418784786741)
                ·
                  refine ⟨101556660273508011073757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1083271042917418784786741 101556660273508011073757)
                  ·
                    rfl

theorem cell22_890014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_890014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890014 prefixEnd_890014 := by exact prefixLift 890014
  have htrace : WordTrace (prefixWord ++ tailWord_890014) baseStart_890014 baseEnd_890014 := by
    simpa [prefixWord, tailWord_890014, baseEnd_890014] using wordTrace_append hprefix tailTrace_890014
  have hstable : (prefixWord ++ tailWord_890014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890014).length < 2 ^ (prefixWord ++ tailWord_890014).sum := by decide
  have hdescent : baseEnd_890014 < baseStart_890014 := by decide
  rcases family_descends (prefixWord ++ tailWord_890014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890087 : List Nat := [1, 1, 5, 3, 2, 1, 3, 6]
def baseStart_890087 : Nat := 118140960795 + 890087 * 2 ^ 59
def prefixEnd_890087 : Nat := 4983230072969 + 3 ^ 40 * 890087 * 2
def baseEnd_890087 : Nat := 33854996690264019571783

theorem tailTrace_890087 : CollatzResearch.WordTrace tailWord_890087 prefixEnd_890087 33854996690264019571783 := by
  unfold tailWord_890087
  simp only [CollatzResearch.WordTrace]
  refine ⟨32464139926374288602196515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21642759950916192401464343 32464139926374288602196515)
  ·
    refine ⟨48696209889561432903294773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32464139926374288602196515 48696209889561432903294773)
    ·
      refine ⟨4565269677146384334683885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48696209889561432903294773 4565269677146384334683885)
      ·
        refine ⟨1711976128929894125506457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4565269677146384334683885 1711976128929894125506457)
        ·
          refine ⟨1283982096697420594129843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1711976128929894125506457 1283982096697420594129843)
          ·
            refine ⟨1925973145046130891194765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283982096697420594129843 1925973145046130891194765)
            ·
              refine ⟨722239929392299084198037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925973145046130891194765 722239929392299084198037)
              ·
                refine ⟨33854996690264019571783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 722239929392299084198037 33854996690264019571783)
                ·
                  rfl

theorem cell22_890087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 6].length) (baseStart_890087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890087 prefixEnd_890087 := by exact prefixLift 890087
  have htrace : WordTrace (prefixWord ++ tailWord_890087) baseStart_890087 baseEnd_890087 := by
    simpa [prefixWord, tailWord_890087, baseEnd_890087] using wordTrace_append hprefix tailTrace_890087
  have hstable : (prefixWord ++ tailWord_890087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890087).length < 2 ^ (prefixWord ++ tailWord_890087).sum := by decide
  have hdescent : baseEnd_890087 < baseStart_890087 := by decide
  rcases family_descends (prefixWord ++ tailWord_890087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890115 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 5]
def baseStart_890115 : Nat := 118140960795 + 890115 * 2 ^ 59
def prefixEnd_890115 : Nat := 4983230072969 + 3 ^ 40 * 890115 * 2
def baseEnd_890115 : Nat := 101568185061531145481987

theorem tailTrace_890115 : CollatzResearch.WordTrace tailWord_890115 prefixEnd_890115 101568185061531145481987 := by
  unfold tailWord_890115
  simp only [CollatzResearch.WordTrace]
  refine ⟨32465161170272849384215799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21643440780181899589477199 32465161170272849384215799)
  ·
    refine ⟨48697741755409274076323699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32465161170272849384215799 48697741755409274076323699)
    ·
      refine ⟨73046612633113911114485549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48697741755409274076323699 73046612633113911114485549)
      ·
        refine ⟨27392479737417716667932081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73046612633113911114485549 27392479737417716667932081)
        ·
          refine ⟨20544359803063287500949061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27392479737417716667932081 20544359803063287500949061)
          ·
            refine ⟨3852067463074366406427949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20544359803063287500949061 3852067463074366406427949)
            ·
              refine ⟨1444525298652887402410481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3852067463074366406427949 1444525298652887402410481)
              ·
                refine ⟨1083393973989665551807861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444525298652887402410481 1083393973989665551807861)
                ·
                  refine ⟨101568185061531145481987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1083393973989665551807861 101568185061531145481987)
                  ·
                    rfl

theorem cell22_890115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 5].length) (baseStart_890115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890115 prefixEnd_890115 := by exact prefixLift 890115
  have htrace : WordTrace (prefixWord ++ tailWord_890115) baseStart_890115 baseEnd_890115 := by
    simpa [prefixWord, tailWord_890115, baseEnd_890115] using wordTrace_append hprefix tailTrace_890115
  have hstable : (prefixWord ++ tailWord_890115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890115).length < 2 ^ (prefixWord ++ tailWord_890115).sum := by decide
  have hdescent : baseEnd_890115 < baseStart_890115 := by decide
  rcases family_descends (prefixWord ++ tailWord_890115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890162 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_890162 : Nat := 118140960795 + 890162 * 2 ^ 59
def prefixEnd_890162 : Nat := 4983230072969 + 3 ^ 40 * 890162 * 2
def baseEnd_890162 : Nat := 304720644245100980520817

theorem tailTrace_890162 : CollatzResearch.WordTrace tailWord_890162 prefixEnd_890162 304720644245100980520817 := by
  unfold tailWord_890162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116718850275644102794185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21644583600735050940784493 8116718850275644102794185)
  ·
    refine ⟨6087539137706733077095639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8116718850275644102794185 6087539137706733077095639)
    ·
      refine ⟨9131308706560099615643459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087539137706733077095639 9131308706560099615643459)
      ·
        refine ⟨13696963059840149423465189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9131308706560099615643459 13696963059840149423465189)
        ·
          refine ⟨2568180573720028016899723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13696963059840149423465189 2568180573720028016899723)
          ·
            refine ⟨3852270860580042025349585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568180573720028016899723 3852270860580042025349585)
            ·
              refine ⟨2889203145435031519012189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3852270860580042025349585 2889203145435031519012189)
              ·
                refine ⟨1083451179538136819629571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2889203145435031519012189 1083451179538136819629571)
                ·
                  refine ⟨1625176769307205229444357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083451179538136819629571 1625176769307205229444357)
                  ·
                    refine ⟨304720644245100980520817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1625176769307205229444357 304720644245100980520817)
                    ·
                      rfl

theorem cell22_890162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_890162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890162 prefixEnd_890162 := by exact prefixLift 890162
  have htrace : WordTrace (prefixWord ++ tailWord_890162) baseStart_890162 baseEnd_890162 := by
    simpa [prefixWord, tailWord_890162, baseEnd_890162] using wordTrace_append hprefix tailTrace_890162
  have hstable : (prefixWord ++ tailWord_890162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890162).length < 2 ^ (prefixWord ++ tailWord_890162).sum := by decide
  have hdescent : baseEnd_890162 < baseStart_890162 := by decide
  rcases family_descends (prefixWord ++ tailWord_890162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890177 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 6]
def baseStart_890177 : Nat := 118140960795 + 890177 * 2 ^ 59
def prefixEnd_890177 : Nat := 4983230072969 + 3 ^ 40 * 890177 * 2
def baseEnd_890177 : Nat := 101575259683881980465257

theorem tailTrace_890177 : CollatzResearch.WordTrace tailWord_890177 prefixEnd_890177 101575259683881980465257 := by
  unfold tailWord_890177
  simp only [CollatzResearch.WordTrace]
  refine ⟨32467422496048233972972785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21644948330698822648648523 32467422496048233972972785)
  ·
    refine ⟨24350566872036175479729589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32467422496048233972972785 24350566872036175479729589)
    ·
      refine ⟨2282865644253391451224649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24350566872036175479729589 2282865644253391451224649)
      ·
        refine ⟨1712149233190043588418487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2282865644253391451224649 1712149233190043588418487)
        ·
          refine ⟨2568223849785065382627731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712149233190043588418487 2568223849785065382627731)
          ·
            refine ⟨3852335774677598073941597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568223849785065382627731 3852335774677598073941597)
            ·
              refine ⟨1444625915504099277728099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3852335774677598073941597 1444625915504099277728099)
              ·
                refine ⟨2166938873256148916592149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444625915504099277728099 2166938873256148916592149)
                ·
                  refine ⟨101575259683881980465257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2166938873256148916592149 101575259683881980465257)
                  ·
                    rfl

theorem cell22_890177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_890177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890177 prefixEnd_890177 := by exact prefixLift 890177
  have htrace : WordTrace (prefixWord ++ tailWord_890177) baseStart_890177 baseEnd_890177 := by
    simpa [prefixWord, tailWord_890177, baseEnd_890177] using wordTrace_append hprefix tailTrace_890177
  have hstable : (prefixWord ++ tailWord_890177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890177).length < 2 ^ (prefixWord ++ tailWord_890177).sum := by decide
  have hdescent : baseEnd_890177 < baseStart_890177 := by decide
  rcases family_descends (prefixWord ++ tailWord_890177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890190 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_890190 : Nat := 118140960795 + 890190 * 2 ^ 59
def prefixEnd_890190 : Nat := 4983230072969 + 3 ^ 40 * 890190 * 2
def baseEnd_890190 : Nat := 304730229217318240820731

theorem tailTrace_890190 : CollatzResearch.WordTrace tailWord_890190 prefixEnd_890190 304730229217318240820731 := by
  unfold tailWord_890190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058487080625142149149503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21645264430000758128797349 4058487080625142149149503)
  ·
    refine ⟨6087730620937713223724255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058487080625142149149503 6087730620937713223724255)
    ·
      refine ⟨9131595931406569835586383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087730620937713223724255 9131595931406569835586383)
      ·
        refine ⟨13697393897109854753379575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9131595931406569835586383 13697393897109854753379575)
        ·
          refine ⟨20546090845664782130069363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13697393897109854753379575 20546090845664782130069363)
          ·
            refine ⟨30819136268497173195104045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20546090845664782130069363 30819136268497173195104045)
            ·
              refine ⟨11557176100686439948164017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30819136268497173195104045 11557176100686439948164017)
              ·
                refine ⟨8667882075514829961123013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11557176100686439948164017 8667882075514829961123013)
                ·
                  refine ⟨1625227889159030617710565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8667882075514829961123013 1625227889159030617710565)
                  ·
                    refine ⟨304730229217318240820731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1625227889159030617710565 304730229217318240820731)
                    ·
                      rfl

theorem cell22_890190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_890190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890190 prefixEnd_890190 := by exact prefixLift 890190
  have htrace : WordTrace (prefixWord ++ tailWord_890190) baseStart_890190 baseEnd_890190 := by
    simpa [prefixWord, tailWord_890190, baseEnd_890190] using wordTrace_append hprefix tailTrace_890190
  have hstable : (prefixWord ++ tailWord_890190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890190).length < 2 ^ (prefixWord ++ tailWord_890190).sum := by decide
  have hdescent : baseEnd_890190 < baseStart_890190 := by decide
  rcases family_descends (prefixWord ++ tailWord_890190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890192 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 2, 3]
def baseStart_890192 : Nat := 118140960795 + 890192 * 2 ^ 59
def prefixEnd_890192 : Nat := 4983230072969 + 3 ^ 40 * 890192 * 2
def baseEnd_890192 : Nat := 304730913858190902270725

theorem tailTrace_890192 : CollatzResearch.WordTrace tailWord_890192 prefixEnd_890192 304730913858190902270725 := by
  unfold tailWord_890192
  simp only [CollatzResearch.WordTrace]
  refine ⟨16233984795496945767384415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21645313060662594356512553 16233984795496945767384415)
  ·
    refine ⟨24350977193245418651076623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16233984795496945767384415 24350977193245418651076623)
    ·
      refine ⟨36526465789868127976614935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24350977193245418651076623 36526465789868127976614935)
      ·
        refine ⟨54789698684802191964922403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36526465789868127976614935 54789698684802191964922403)
        ·
          refine ⟨82184548027203287947383605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54789698684802191964922403 82184548027203287947383605)
          ·
            refine ⟨7704801377550308245067213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82184548027203287947383605 7704801377550308245067213)
            ·
              refine ⟨2889300516581365591900205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7704801377550308245067213 2889300516581365591900205)
              ·
                refine ⟨1083487693718012096962577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2889300516581365591900205 1083487693718012096962577)
                ·
                  refine ⟨812615770288509072721933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1083487693718012096962577 812615770288509072721933)
                  ·
                    refine ⟨304730913858190902270725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812615770288509072721933 304730913858190902270725)
                    ·
                      rfl

theorem cell22_890192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_890192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890192 prefixEnd_890192 := by exact prefixLift 890192
  have htrace : WordTrace (prefixWord ++ tailWord_890192) baseStart_890192 baseEnd_890192 := by
    simpa [prefixWord, tailWord_890192, baseEnd_890192] using wordTrace_append hprefix tailTrace_890192
  have hstable : (prefixWord ++ tailWord_890192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890192).length < 2 ^ (prefixWord ++ tailWord_890192).sum := by decide
  have hdescent : baseEnd_890192 < baseStart_890192 := by decide
  rcases family_descends (prefixWord ++ tailWord_890192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890222 : List Nat := [4, 1, 2, 4, 1, 10]
def baseStart_890222 : Nat := 118140960795 + 890222 * 2 ^ 59
def prefixEnd_890222 : Nat := 4983230072969 + 3 ^ 40 * 890222 * 2
def baseEnd_890222 : Nat := 3762236832978775605193

theorem tailTrace_890222 : CollatzResearch.WordTrace tailWord_890222 prefixEnd_890222 3762236832978775605193 := by
  unfold tailWord_890222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058632972610650832295115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21646042520590137772240613 4058632972610650832295115)
  ·
    refine ⟨6087949458915976248442673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058632972610650832295115 6087949458915976248442673)
    ·
      refine ⟨4565962094186982186332005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6087949458915976248442673 4565962094186982186332005)
      ·
        refine ⟨856117892660059159937251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4565962094186982186332005 856117892660059159937251)
        ·
          refine ⟨1284176838990088739905877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856117892660059159937251 1284176838990088739905877)
          ·
            refine ⟨3762236832978775605193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1284176838990088739905877 3762236832978775605193)
            ·
              rfl

theorem cell22_890222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 10].length) (baseStart_890222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890222 prefixEnd_890222 := by exact prefixLift 890222
  have htrace : WordTrace (prefixWord ++ tailWord_890222) baseStart_890222 baseEnd_890222 := by
    simpa [prefixWord, tailWord_890222, baseEnd_890222] using wordTrace_append hprefix tailTrace_890222
  have hstable : (prefixWord ++ tailWord_890222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890222).length < 2 ^ (prefixWord ++ tailWord_890222).sum := by decide
  have hdescent : baseEnd_890222 < baseStart_890222 := by decide
  rcases family_descends (prefixWord ++ tailWord_890222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890237 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_890237 : Nat := 118140960795 + 890237 * 2 ^ 59
def prefixEnd_890237 : Nat := 4983230072969 + 3 ^ 40 * 890237 * 2
def baseEnd_890237 : Nat := 304746318277825784895587

theorem tailTrace_890237 : CollatzResearch.WordTrace tailWord_890237 prefixEnd_890237 304746318277825784895587 := by
  unfold tailWord_890237
  simp only [CollatzResearch.WordTrace]
  refine ⟨32469610875830864220156965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21646407250553909480104643 32469610875830864220156965)
  ·
    refine ⟨6088052039218287041279431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32469610875830864220156965 6088052039218287041279431)
    ·
      refine ⟨9132078058827430561919147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6088052039218287041279431 9132078058827430561919147)
      ·
        refine ⟨13698117088241145842878721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132078058827430561919147 13698117088241145842878721)
        ·
          refine ⟨10273587816180859382159041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13698117088241145842878721 10273587816180859382159041)
          ·
            refine ⟨7705190862135644536619281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10273587816180859382159041 7705190862135644536619281)
            ·
              refine ⟨5778893146601733402464461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7705190862135644536619281 5778893146601733402464461)
              ·
                refine ⟨2167084929975650025924173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5778893146601733402464461 2167084929975650025924173)
                ·
                  refine ⟨812656848740868759721565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2167084929975650025924173 812656848740868759721565)
                  ·
                    refine ⟨304746318277825784895587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812656848740868759721565 304746318277825784895587)
                    ·
                      rfl

theorem cell22_890237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_890237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890237 prefixEnd_890237 := by exact prefixLift 890237
  have htrace : WordTrace (prefixWord ++ tailWord_890237) baseStart_890237 baseEnd_890237 := by
    simpa [prefixWord, tailWord_890237, baseEnd_890237] using wordTrace_append hprefix tailTrace_890237
  have hstable : (prefixWord ++ tailWord_890237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890237).length < 2 ^ (prefixWord ++ tailWord_890237).sum := by decide
  have hdescent : baseEnd_890237 < baseStart_890237 := by decide
  rcases family_descends (prefixWord ++ tailWord_890237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890258 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_890258 : Nat := 118140960795 + 890258 * 2 ^ 59
def prefixEnd_890258 : Nat := 4983230072969 + 3 ^ 40 * 890258 * 2
def baseEnd_890258 : Nat := 304753507006988730120523

theorem tailTrace_890258 : CollatzResearch.WordTrace tailWord_890258 prefixEnd_890258 304753507006988730120523 := by
  unfold tailWord_890258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117594202188696201667857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21646917872503189871114285 8117594202188696201667857)
  ·
    refine ⟨6088195651641522151250893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8117594202188696201667857 6088195651641522151250893)
    ·
      refine ⟨2283073369365570806719085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6088195651641522151250893 2283073369365570806719085)
      ·
        refine ⟨856152513512089052519657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2283073369365570806719085 856152513512089052519657)
        ·
          refine ⟨642114385134066789389743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856152513512089052519657 642114385134066789389743)
          ·
            refine ⟨963171577701100184084615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642114385134066789389743 963171577701100184084615)
            ·
              refine ⟨1444757366551650276126923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963171577701100184084615 1444757366551650276126923)
              ·
                refine ⟨2167136049827475414190385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444757366551650276126923 2167136049827475414190385)
                ·
                  refine ⟨1625352037370606560642789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2167136049827475414190385 1625352037370606560642789)
                  ·
                    refine ⟨304753507006988730120523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1625352037370606560642789 304753507006988730120523)
                    ·
                      rfl

theorem cell22_890258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_890258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890258 prefixEnd_890258 := by exact prefixLift 890258
  have htrace : WordTrace (prefixWord ++ tailWord_890258) baseStart_890258 baseEnd_890258 := by
    simpa [prefixWord, tailWord_890258, baseEnd_890258] using wordTrace_append hprefix tailTrace_890258
  have hstable : (prefixWord ++ tailWord_890258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890258).length < 2 ^ (prefixWord ++ tailWord_890258).sum := by decide
  have hdescent : baseEnd_890258 < baseStart_890258 := by decide
  rcases family_descends (prefixWord ++ tailWord_890258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890271 : List Nat := [1, 1, 2, 5, 1, 3, 2, 3, 1, 3]
def baseStart_890271 : Nat := 118140960795 + 890271 * 2 ^ 59
def prefixEnd_890271 : Nat := 4983230072969 + 3 ^ 40 * 890271 * 2
def baseEnd_890271 : Nat := 304757957172661029545483

theorem tailTrace_890271 : CollatzResearch.WordTrace tailWord_890271 prefixEnd_890271 304757957172661029545483 := by
  unfold tailWord_890271
  simp only [CollatzResearch.WordTrace]
  refine ⟨32470850957707688026894667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21647233971805125351263111 32470850957707688026894667)
  ·
    refine ⟨48706276436561532040342001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32470850957707688026894667 48706276436561532040342001)
    ·
      refine ⟨36529707327421149030256501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48706276436561532040342001 36529707327421149030256501)
      ·
        refine ⟨3424660061945732721586547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36529707327421149030256501 3424660061945732721586547)
        ·
          refine ⟨5136990092918599082379821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424660061945732721586547 5136990092918599082379821)
          ·
            refine ⟨1926371284844474655892433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5136990092918599082379821 1926371284844474655892433)
            ·
              refine ⟨1444778463633355991919325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926371284844474655892433 1444778463633355991919325)
              ·
                refine ⟨541791923862508496969747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444778463633355991919325 541791923862508496969747)
                ·
                  refine ⟨812687885793762745454621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541791923862508496969747 812687885793762745454621)
                  ·
                    refine ⟨304757957172661029545483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812687885793762745454621 304757957172661029545483)
                    ·
                      rfl

theorem cell22_890271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 3].length) (baseStart_890271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890271 prefixEnd_890271 := by exact prefixLift 890271
  have htrace : WordTrace (prefixWord ++ tailWord_890271) baseStart_890271 baseEnd_890271 := by
    simpa [prefixWord, tailWord_890271, baseEnd_890271] using wordTrace_append hprefix tailTrace_890271
  have hstable : (prefixWord ++ tailWord_890271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890271).length < 2 ^ (prefixWord ++ tailWord_890271).sum := by decide
  have hdescent : baseEnd_890271 < baseStart_890271 := by decide
  rcases family_descends (prefixWord ++ tailWord_890271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890314 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_890314 : Nat := 118140960795 + 890314 * 2 ^ 59
def prefixEnd_890314 : Nat := 4983230072969 + 3 ^ 40 * 890314 * 2
def baseEnd_890314 : Nat := 304772676951423250720351

theorem tailTrace_890314 : CollatzResearch.WordTrace tailWord_890314 prefixEnd_890314 304772676951423250720351 := by
  unfold tailWord_890314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118104824137976592677499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21648279531034604247139997 8118104824137976592677499)
  ·
    refine ⟨12177157236206964889016249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8118104824137976592677499 12177157236206964889016249)
    ·
      refine ⟨9132867927155223666762187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12177157236206964889016249 9132867927155223666762187)
      ·
        refine ⟨13699301890732835500143281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132867927155223666762187 13699301890732835500143281)
        ·
          refine ⟨10274476418049626625107461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13699301890732835500143281 10274476418049626625107461)
          ·
            refine ⟨1926464328384304992207649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10274476418049626625107461 1926464328384304992207649)
            ·
              refine ⟨1444848246288228744155737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926464328384304992207649 1444848246288228744155737)
              ·
                refine ⟨1083636184716171558116803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444848246288228744155737 1083636184716171558116803)
                ·
                  refine ⟨1625454277074257337175205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083636184716171558116803 1625454277074257337175205)
                  ·
                    refine ⟨304772676951423250720351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1625454277074257337175205 304772676951423250720351)
                    ·
                      rfl

theorem cell22_890314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_890314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890314 prefixEnd_890314 := by exact prefixLift 890314
  have htrace : WordTrace (prefixWord ++ tailWord_890314) baseStart_890314 baseEnd_890314 := by
    simpa [prefixWord, tailWord_890314, baseEnd_890314] using wordTrace_append hprefix tailTrace_890314
  have hstable : (prefixWord ++ tailWord_890314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890314).length < 2 ^ (prefixWord ++ tailWord_890314).sum := by decide
  have hdescent : baseEnd_890314 < baseStart_890314 := by decide
  rcases family_descends (prefixWord ++ tailWord_890314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890329 : List Nat := [1, 2, 1, 2, 4, 2, 3, 3, 4]
def baseStart_890329 : Nat := 118140960795 + 890329 * 2 ^ 59
def prefixEnd_890329 : Nat := 4983230072969 + 3 ^ 40 * 890329 * 2
def baseEnd_890329 : Nat := 101592603919322737198435

theorem tailTrace_890329 : CollatzResearch.WordTrace tailWord_890329 prefixEnd_890329 101592603919322737198435 := by
  unfold tailWord_890329
  simp only [CollatzResearch.WordTrace]
  refine ⟨32472966391497563932506041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21648644260998375955004027 32472966391497563932506041)
  ·
    refine ⟨24354724793623172949379531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32472966391497563932506041 24354724793623172949379531)
    ·
      refine ⟨36532087190434759424069297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24354724793623172949379531 36532087190434759424069297)
      ·
        refine ⟨27399065392826069568051973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36532087190434759424069297 27399065392826069568051973)
        ·
          refine ⟨5137324761154888044009745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27399065392826069568051973 5137324761154888044009745)
          ·
            refine ⟨3852993570866166033007309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5137324761154888044009745 3852993570866166033007309)
            ·
              refine ⟨1444872589074812262377741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3852993570866166033007309 1444872589074812262377741)
              ·
                refine ⟨541827220903054598391653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1444872589074812262377741 541827220903054598391653)
                ·
                  refine ⟨101592603919322737198435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541827220903054598391653 101592603919322737198435)
                  ·
                    rfl

theorem cell22_890329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_890329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890329 prefixEnd_890329 := by exact prefixLift 890329
  have htrace : WordTrace (prefixWord ++ tailWord_890329) baseStart_890329 baseEnd_890329 := by
    simpa [prefixWord, tailWord_890329, baseEnd_890329] using wordTrace_append hprefix tailTrace_890329
  have hstable : (prefixWord ++ tailWord_890329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890329).length < 2 ^ (prefixWord ++ tailWord_890329).sum := by decide
  have hdescent : baseEnd_890329 < baseStart_890329 := by decide
  rcases family_descends (prefixWord ++ tailWord_890329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890344 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 2, 3]
def baseStart_890344 : Nat := 118140960795 + 890344 * 2 ^ 59
def prefixEnd_890344 : Nat := 4983230072969 + 3 ^ 40 * 890344 * 2
def baseEnd_890344 : Nat := 304782946564513172470259

theorem tailTrace_890344 : CollatzResearch.WordTrace tailWord_890344 prefixEnd_890344 304782946564513172470259 := by
  unfold tailWord_890344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16236756743221610747151043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21649008990962147662868057 16236756743221610747151043)
  ·
    refine ⟨24355135114832416120726565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16236756743221610747151043 24355135114832416120726565)
    ·
      refine ⟨4566587834031078022636231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24355135114832416120726565 4566587834031078022636231)
      ·
        refine ⟨6849881751046617033954347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566587834031078022636231 6849881751046617033954347)
        ·
          refine ⟨10274822626569925550931521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6849881751046617033954347 10274822626569925550931521)
          ·
            refine ⟨7706116969927444163198641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10274822626569925550931521 7706116969927444163198641)
            ·
              refine ⟨5779587727445583122398981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7706116969927444163198641 5779587727445583122398981)
              ·
                refine ⟨1083672698896046835449809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5779587727445583122398981 1083672698896046835449809)
                ·
                  refine ⟨812754524172035126587357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1083672698896046835449809 812754524172035126587357)
                  ·
                    refine ⟨304782946564513172470259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812754524172035126587357 304782946564513172470259)
                    ·
                      rfl

theorem cell22_890344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_890344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890344 prefixEnd_890344 := by exact prefixLift 890344
  have htrace : WordTrace (prefixWord ++ tailWord_890344) baseStart_890344 baseEnd_890344 := by
    simpa [prefixWord, tailWord_890344, baseEnd_890344] using wordTrace_append hprefix tailTrace_890344
  have hstable : (prefixWord ++ tailWord_890344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890344).length < 2 ^ (prefixWord ++ tailWord_890344).sum := by decide
  have hdescent : baseEnd_890344 < baseStart_890344 := by decide
  rcases family_descends (prefixWord ++ tailWord_890344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890346 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_890346 : Nat := 118140960795 + 890346 * 2 ^ 59
def prefixEnd_890346 : Nat := 4983230072969 + 3 ^ 40 * 890346 * 2
def baseEnd_890346 : Nat := 101594543735128611306751

theorem tailTrace_890346 : CollatzResearch.WordTrace tailWord_890346 prefixEnd_890346 101594543735128611306751 := by
  unfold tailWord_890346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118396608108993958968723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21649057621623983890583261 8118396608108993958968723)
  ·
    refine ⟨12177594912163490938453085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8118396608108993958968723 12177594912163490938453085)
    ·
      refine ⟨4566598092061309101919907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12177594912163490938453085 4566598092061309101919907)
      ·
        refine ⟨6849897138091963652879861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566598092061309101919907 6849897138091963652879861)
        ·
          refine ⟨642177856696121592457487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6849897138091963652879861 642177856696121592457487)
          ·
            refine ⟨963266785044182388686231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642177856696121592457487 963266785044182388686231)
            ·
              refine ⟨1444900177566273583029347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963266785044182388686231 1444900177566273583029347)
              ·
                refine ⟨2167350266349410374544021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444900177566273583029347 2167350266349410374544021)
                ·
                  refine ⟨101594543735128611306751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2167350266349410374544021 101594543735128611306751)
                  ·
                    rfl

theorem cell22_890346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_890346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890346 prefixEnd_890346 := by exact prefixLift 890346
  have htrace : WordTrace (prefixWord ++ tailWord_890346) baseStart_890346 baseEnd_890346 := by
    simpa [prefixWord, tailWord_890346, baseEnd_890346] using wordTrace_append hprefix tailTrace_890346
  have hstable : (prefixWord ++ tailWord_890346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890346).length < 2 ^ (prefixWord ++ tailWord_890346).sum := by decide
  have hdescent : baseEnd_890346 < baseStart_890346 := by decide
  rcases family_descends (prefixWord ++ tailWord_890346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890355 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 2, 7]
def baseStart_890355 : Nat := 118140960795 + 890355 * 2 ^ 59
def prefixEnd_890355 : Nat := 4983230072969 + 3 ^ 40 * 890355 * 2
def baseEnd_890355 : Nat := 304786712089312810445225

theorem tailTrace_890355 : CollatzResearch.WordTrace tailWord_890355 prefixEnd_890355 304786712089312810445225 := by
  unfold tailWord_890355
  simp only [CollatzResearch.WordTrace]
  refine ⟨32473914689403370372952519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21649276459602246915301679 32473914689403370372952519)
  ·
    refine ⟨48710872034105055559428779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32473914689403370372952519 48710872034105055559428779)
    ·
      refine ⟨73066308051157583339143169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48710872034105055559428779 73066308051157583339143169)
      ·
        refine ⟨54799731038368187504357377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73066308051157583339143169 54799731038368187504357377)
        ·
          refine ⟨41099798278776140628268033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54799731038368187504357377 41099798278776140628268033)
          ·
            refine ⟨30824848709082105471201025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41099798278776140628268033 30824848709082105471201025)
            ·
              refine ⟨23118636531811579103400769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30824848709082105471201025 23118636531811579103400769)
              ·
                refine ⟨17338977398858684327550577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23118636531811579103400769 17338977398858684327550577)
                ·
                  refine ⟨13004233049144013245662933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17338977398858684327550577 13004233049144013245662933)
                  ·
                    refine ⟨304786712089312810445225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13004233049144013245662933 304786712089312810445225)
                    ·
                      rfl

theorem cell22_890355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_890355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890355 prefixEnd_890355 := by exact prefixLift 890355
  have htrace : WordTrace (prefixWord ++ tailWord_890355) baseStart_890355 baseEnd_890355 := by
    simpa [prefixWord, tailWord_890355, baseEnd_890355] using wordTrace_append hprefix tailTrace_890355
  have hstable : (prefixWord ++ tailWord_890355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890355).length < 2 ^ (prefixWord ++ tailWord_890355).sum := by decide
  have hdescent : baseEnd_890355 < baseStart_890355 := by decide
  rcases family_descends (prefixWord ++ tailWord_890355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890402 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_890402 : Nat := 118140960795 + 890402 * 2 ^ 59
def prefixEnd_890402 : Nat := 4983230072969 + 3 ^ 40 * 890402 * 2
def baseEnd_890402 : Nat := 101600933716606784840027

theorem tailTrace_890402 : CollatzResearch.WordTrace tailWord_890402 prefixEnd_890402 101600933716606784840027 := by
  unfold tailWord_890402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118907230058274349978365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21650419280155398266608973 8118907230058274349978365)
  ·
    refine ⟨3044590211271852881241887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8118907230058274349978365 3044590211271852881241887)
    ·
      refine ⟨4566885316907779321862831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3044590211271852881241887 4566885316907779321862831)
      ·
        refine ⟨6850327975361668982794247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566885316907779321862831 6850327975361668982794247)
        ·
          refine ⟨10275491963042503474191371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6850327975361668982794247 10275491963042503474191371)
          ·
            refine ⟨15413237944563755211287057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275491963042503474191371 15413237944563755211287057)
            ·
              refine ⟨11559928458422816408465293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15413237944563755211287057 11559928458422816408465293)
              ·
                refine ⟨4334973171908556153174485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11559928458422816408465293 4334973171908556153174485)
                ·
                  refine ⟨101600933716606784840027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4334973171908556153174485 101600933716606784840027)
                  ·
                    rfl

theorem cell22_890402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_890402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890402 prefixEnd_890402 := by exact prefixLift 890402
  have htrace : WordTrace (prefixWord ++ tailWord_890402) baseStart_890402 baseEnd_890402 := by
    simpa [prefixWord, tailWord_890402, baseEnd_890402] using wordTrace_append hprefix tailTrace_890402
  have hstable : (prefixWord ++ tailWord_890402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890402).length < 2 ^ (prefixWord ++ tailWord_890402).sum := by decide
  have hdescent : baseEnd_890402 < baseStart_890402 := by decide
  rcases family_descends (prefixWord ++ tailWord_890402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890449 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_890449 : Nat := 118140960795 + 890449 * 2 ^ 59
def prefixEnd_890449 : Nat := 4983230072969 + 3 ^ 40 * 890449 * 2
def baseEnd_890449 : Nat := 304818890210327898594937

theorem tailTrace_890449 : CollatzResearch.WordTrace tailWord_890449 prefixEnd_890449 304818890210327898594937 := by
  unfold tailWord_890449
  simp only [CollatzResearch.WordTrace]
  refine ⟨32477343151062824426874401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21651562100708549617916267 32477343151062824426874401)
  ·
    refine ⟨24358007363297118320155801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32477343151062824426874401 24358007363297118320155801)
    ·
      refine ⟨18268505522472838740116851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24358007363297118320155801 18268505522472838740116851)
      ·
        refine ⟨27402758283709258110175277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18268505522472838740116851 27402758283709258110175277)
        ·
          refine ⟨10276034356390971791315729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27402758283709258110175277 10276034356390971791315729)
          ·
            refine ⟨7707025767293228843486797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10276034356390971791315729 7707025767293228843486797)
            ·
              refine ⟨2890134662734960816307549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7707025767293228843486797 2890134662734960816307549)
              ·
                refine ⟨1083800498525610306115331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2890134662734960816307549 1083800498525610306115331)
                ·
                  refine ⟨1625700747788415459172997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083800498525610306115331 1625700747788415459172997)
                  ·
                    refine ⟨304818890210327898594937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1625700747788415459172997 304818890210327898594937)
                    ·
                      rfl

theorem cell22_890449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_890449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890449 prefixEnd_890449 := by exact prefixLift 890449
  have htrace : WordTrace (prefixWord ++ tailWord_890449) baseStart_890449 baseEnd_890449 := by
    simpa [prefixWord, tailWord_890449, baseEnd_890449] using wordTrace_append hprefix tailTrace_890449
  have hstable : (prefixWord ++ tailWord_890449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890449).length < 2 ^ (prefixWord ++ tailWord_890449).sum := by decide
  have hdescent : baseEnd_890449 < baseStart_890449 := by decide
  rcases family_descends (prefixWord ++ tailWord_890449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890526 : List Nat := [4, 3, 1, 1, 1, 3, 2, 7]
def baseStart_890526 : Nat := 118140960795 + 890526 * 2 ^ 59
def prefixEnd_890526 : Nat := 4983230072969 + 3 ^ 40 * 890526 * 2
def baseEnd_890526 : Nat := 33871694320436151602189

theorem tailTrace_890526 : CollatzResearch.WordTrace tailWord_890526 prefixEnd_890526 33871694320436151602189 := by
  unfold tailWord_890526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060018946472983322178429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21653434381189244384951621 4060018946472983322178429)
  ·
    refine ⟨1522507104927368745816911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4060018946472983322178429 1522507104927368745816911)
    ·
      refine ⟨2283760657391053118725367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522507104927368745816911 2283760657391053118725367)
      ·
        refine ⟨3425640986086579678088051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283760657391053118725367 3425640986086579678088051)
        ·
          refine ⟨5138461479129869517132077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425640986086579678088051 5138461479129869517132077)
          ·
            refine ⟨1926923054673701068924529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5138461479129869517132077 1926923054673701068924529)
            ·
              refine ⟨1445192291005275801693397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926923054673701068924529 1445192291005275801693397)
              ·
                refine ⟨33871694320436151602189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1445192291005275801693397 33871694320436151602189)
                ·
                  rfl

theorem cell22_890526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_890526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890526 prefixEnd_890526 := by exact prefixLift 890526
  have htrace : WordTrace (prefixWord ++ tailWord_890526) baseStart_890526 baseEnd_890526 := by
    simpa [prefixWord, tailWord_890526, baseEnd_890526] using wordTrace_append hprefix tailTrace_890526
  have hstable : (prefixWord ++ tailWord_890526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890526).length < 2 ^ (prefixWord ++ tailWord_890526).sum := by decide
  have hdescent : baseEnd_890526 < baseStart_890526 := by decide
  rcases family_descends (prefixWord ++ tailWord_890526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890530 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_890530 : Nat := 118140960795 + 890530 * 2 ^ 59
def prefixEnd_890530 : Nat := 4983230072969 + 3 ^ 40 * 890530 * 2
def baseEnd_890530 : Nat := 304846618165670687319689

theorem tailTrace_890530 : CollatzResearch.WordTrace tailWord_890530 prefixEnd_890530 304846618165670687319689 := by
  unfold tailWord_890530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8120074365942343815143261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21653531642512916840382029 8120074365942343815143261)
  ·
    refine ⟨3045027887228378930678723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8120074365942343815143261 3045027887228378930678723)
    ·
      refine ⟨4567541830842568396018085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045027887228378930678723 4567541830842568396018085)
      ·
        refine ⟨856414093282981574253391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4567541830842568396018085 856414093282981574253391)
        ·
          refine ⟨1284621139924472361380087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856414093282981574253391 1284621139924472361380087)
          ·
            refine ⟨1926931709886708542070131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284621139924472361380087 1926931709886708542070131)
            ·
              refine ⟨2890397564830062813105197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926931709886708542070131 2890397564830062813105197)
              ·
                refine ⟨1083899086811273554914449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2890397564830062813105197 1083899086811273554914449)
                ·
                  refine ⟨812924315108455166185837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1083899086811273554914449 812924315108455166185837)
                  ·
                    refine ⟨304846618165670687319689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812924315108455166185837 304846618165670687319689)
                    ·
                      rfl

theorem cell22_890530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_890530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890530 prefixEnd_890530 := by exact prefixLift 890530
  have htrace : WordTrace (prefixWord ++ tailWord_890530) baseStart_890530 baseEnd_890530 := by
    simpa [prefixWord, tailWord_890530, baseEnd_890530] using wordTrace_append hprefix tailTrace_890530
  have hstable : (prefixWord ++ tailWord_890530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890530).length < 2 ^ (prefixWord ++ tailWord_890530).sum := by decide
  have hdescent : baseEnd_890530 < baseStart_890530 := by decide
  rcases family_descends (prefixWord ++ tailWord_890530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890541 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_890541 : Nat := 118140960795 + 890541 * 2 ^ 59
def prefixEnd_890541 : Nat := 4983230072969 + 3 ^ 40 * 890541 * 2
def baseEnd_890541 : Nat := 304850383690470325294655

theorem tailTrace_890541 : CollatzResearch.WordTrace tailWord_890541 prefixEnd_890541 304850383690470325294655 := by
  unfold tailWord_890541
  simp only [CollatzResearch.WordTrace]
  refine ⟨32480698666729524139223477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21653799111153016092815651 32480698666729524139223477)
  ·
    refine ⟨3045065500005892888052201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32480698666729524139223477 3045065500005892888052201)
    ·
      refine ⟨2283799125004419666039151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3045065500005892888052201 2283799125004419666039151)
      ·
        refine ⟨3425698687506629499058727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283799125004419666039151 3425698687506629499058727)
        ·
          refine ⟨5138548031259944248588091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425698687506629499058727 5138548031259944248588091)
          ·
            refine ⟨7707822046889916372882137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138548031259944248588091 7707822046889916372882137)
            ·
              refine ⟨5780866535167437279661603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7707822046889916372882137 5780866535167437279661603)
              ·
                refine ⟨8671299802751155919492405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5780866535167437279661603 8671299802751155919492405)
                ·
                  refine ⟨812934356507920867452413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8671299802751155919492405 812934356507920867452413)
                  ·
                    refine ⟨304850383690470325294655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 812934356507920867452413 304850383690470325294655)
                    ·
                      rfl

theorem cell22_890541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_890541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890541 prefixEnd_890541 := by exact prefixLift 890541
  have htrace : WordTrace (prefixWord ++ tailWord_890541) baseStart_890541 baseEnd_890541 := by
    simpa [prefixWord, tailWord_890541, baseEnd_890541] using wordTrace_append hprefix tailTrace_890541
  have hstable : (prefixWord ++ tailWord_890541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890541).length < 2 ^ (prefixWord ++ tailWord_890541).sum := by decide
  have hdescent : baseEnd_890541 < baseStart_890541 := by decide
  rcases family_descends (prefixWord ++ tailWord_890541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890584 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_890584 : Nat := 118140960795 + 890584 * 2 ^ 59
def prefixEnd_890584 : Nat := 4983230072969 + 3 ^ 40 * 890584 * 2
def baseEnd_890584 : Nat := 304865103469232546469523

theorem tailTrace_890584 : CollatzResearch.WordTrace tailWord_890584 prefixEnd_890584 304865103469232546469523 := by
  unfold tailWord_890584
  simp only [CollatzResearch.WordTrace]
  refine ⟨16241133502786871241519403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21654844670382494988692537 16241133502786871241519403)
  ·
    refine ⟨24361700254180306862279105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16241133502786871241519403 24361700254180306862279105)
    ·
      refine ⟨18271275190635230146709329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24361700254180306862279105 18271275190635230146709329)
      ·
        refine ⟨13703456392976422610031997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18271275190635230146709329 13703456392976422610031997)
        ·
          refine ⟨5138796147366158478761999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13703456392976422610031997 5138796147366158478761999)
          ·
            refine ⟨7708194221049237718142999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138796147366158478761999 7708194221049237718142999)
            ·
              refine ⟨11562291331573856577214499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708194221049237718142999 11562291331573856577214499)
              ·
                refine ⟨17343436997360784865821749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11562291331573856577214499 17343436997360784865821749)
                ·
                  refine ⟨1625947218502573581170789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17343436997360784865821749 1625947218502573581170789)
                  ·
                    refine ⟨304865103469232546469523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1625947218502573581170789 304865103469232546469523)
                    ·
                      rfl

theorem cell22_890584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_890584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890584 prefixEnd_890584 := by exact prefixLift 890584
  have htrace : WordTrace (prefixWord ++ tailWord_890584) baseStart_890584 baseEnd_890584 := by
    simpa [prefixWord, tailWord_890584, baseEnd_890584] using wordTrace_append hprefix tailTrace_890584
  have hstable : (prefixWord ++ tailWord_890584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890584).length < 2 ^ (prefixWord ++ tailWord_890584).sum := by decide
  have hdescent : baseEnd_890584 < baseStart_890584 := by decide
  rcases family_descends (prefixWord ++ tailWord_890584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890661 : List Nat := [1, 3, 1, 2, 3, 2, 4, 6]
def baseStart_890661 : Nat := 118140960795 + 890661 * 2 ^ 59
def prefixEnd_890661 : Nat := 4983230072969 + 3 ^ 40 * 890661 * 2
def baseEnd_890661 : Nat := 33876829126981112477143

theorem tailTrace_890661 : CollatzResearch.WordTrace tailWord_890661 prefixEnd_890661 33876829126981112477143 := by
  unfold tailWord_890661
  simp only [CollatzResearch.WordTrace]
  refine ⟨32485075426294784633591837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21656716950863189755727891 32485075426294784633591837)
  ·
    refine ⟨12181903284860544237596939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32485075426294784633591837 12181903284860544237596939)
    ·
      refine ⟨18272854927290816356395409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12181903284860544237596939 18272854927290816356395409)
      ·
        refine ⟨13704641195468112267296557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18272854927290816356395409 13704641195468112267296557)
        ·
          refine ⟨5139240448300542100236209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13704641195468112267296557 5139240448300542100236209)
          ·
            refine ⟨3854430336225406575177157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5139240448300542100236209 3854430336225406575177157)
            ·
              refine ⟨722705688042263732845717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3854430336225406575177157 722705688042263732845717)
              ·
                refine ⟨33876829126981112477143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 722705688042263732845717 33876829126981112477143)
                ·
                  rfl

theorem cell22_890661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 6].length) (baseStart_890661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890661 prefixEnd_890661 := by exact prefixLift 890661
  have htrace : WordTrace (prefixWord ++ tailWord_890661) baseStart_890661 baseEnd_890661 := by
    simpa [prefixWord, tailWord_890661, baseEnd_890661] using wordTrace_append hprefix tailTrace_890661
  have hstable : (prefixWord ++ tailWord_890661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890661).length < 2 ^ (prefixWord ++ tailWord_890661).sum := by decide
  have hdescent : baseEnd_890661 < baseStart_890661 := by decide
  rcases family_descends (prefixWord ++ tailWord_890661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890678 : List Nat := [5, 1, 2, 2, 1, 3, 8]
def baseStart_890678 : Nat := 118140960795 + 890678 * 2 ^ 59
def prefixEnd_890678 : Nat := 4983230072969 + 3 ^ 40 * 890678 * 2
def baseEnd_890678 : Nat := 11292491910749912393305

theorem tailTrace_890678 : CollatzResearch.WordTrace tailWord_890678 prefixEnd_890678 11292491910749912393305 := by
  unfold tailWord_890678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030355966702074783560043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21657130311488797691307125 2030355966702074783560043)
  ·
    refine ⟨3045533950053112175340065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030355966702074783560043 3045533950053112175340065)
    ·
      refine ⟨2284150462539834131505049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3045533950053112175340065 2284150462539834131505049)
      ·
        refine ⟨1713112846904875598628787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2284150462539834131505049 1713112846904875598628787)
        ·
          refine ⟨2569669270357313397943181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713112846904875598628787 2569669270357313397943181)
          ·
            refine ⟨963625976383992524228693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2569669270357313397943181 963625976383992524228693)
            ·
              refine ⟨11292491910749912393305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 963625976383992524228693 11292491910749912393305)
              ·
                rfl

theorem cell22_890678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 8].length) (baseStart_890678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890678 prefixEnd_890678 := by exact prefixLift 890678
  have htrace : WordTrace (prefixWord ++ tailWord_890678) baseStart_890678 baseEnd_890678 := by
    simpa [prefixWord, tailWord_890678, baseEnd_890678] using wordTrace_append hprefix tailTrace_890678
  have hstable : (prefixWord ++ tailWord_890678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890678).length < 2 ^ (prefixWord ++ tailWord_890678).sum := by decide
  have hdescent : baseEnd_890678 < baseStart_890678 := by decide
  rcases family_descends (prefixWord ++ tailWord_890678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890704 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_890704 : Nat := 118140960795 + 890704 * 2 ^ 59
def prefixEnd_890704 : Nat := 4983230072969 + 3 ^ 40 * 890704 * 2
def baseEnd_890704 : Nat := 304906181921592233469155

theorem tailTrace_890704 : CollatzResearch.WordTrace tailWord_890704 prefixEnd_890704 304906181921592233469155 := by
  unfold tailWord_890704
  simp only [CollatzResearch.WordTrace]
  refine ⟨16243321882569501488703583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21657762510092668651604777 16243321882569501488703583)
  ·
    refine ⟨24364982823854252233055375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16243321882569501488703583 24364982823854252233055375)
    ·
      refine ⟨36547474235781378349583063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24364982823854252233055375 36547474235781378349583063)
      ·
        refine ⟨54821211353672067524374595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36547474235781378349583063 54821211353672067524374595)
        ·
          refine ⟨82231817030508101286561893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54821211353672067524374595 82231817030508101286561893)
          ·
            refine ⟨15418465693220268991230355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82231817030508101286561893 15418465693220268991230355)
            ·
              refine ⟨23127698539830403486845533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15418465693220268991230355 23127698539830403486845533)
              ·
                refine ⟨8672886952436401307567075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23127698539830403486845533 8672886952436401307567075)
                ·
                  refine ⟨13009330428654601961350613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8672886952436401307567075 13009330428654601961350613)
                  ·
                    refine ⟨304906181921592233469155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13009330428654601961350613 304906181921592233469155)
                    ·
                      rfl

theorem cell22_890704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_890704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890704 prefixEnd_890704 := by exact prefixLift 890704
  have htrace : WordTrace (prefixWord ++ tailWord_890704) baseStart_890704 baseEnd_890704 := by
    simpa [prefixWord, tailWord_890704, baseEnd_890704] using wordTrace_append hprefix tailTrace_890704
  have hstable : (prefixWord ++ tailWord_890704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890704).length < 2 ^ (prefixWord ++ tailWord_890704).sum := by decide
  have hdescent : baseEnd_890704 < baseStart_890704 := by decide
  rcases family_descends (prefixWord ++ tailWord_890704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890826 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_890826 : Nat := 118140960795 + 890826 * 2 ^ 59
def prefixEnd_890826 : Nat := 4983230072969 + 3 ^ 40 * 890826 * 2
def baseEnd_890826 : Nat := 304947945014824581918781

theorem tailTrace_890826 : CollatzResearch.WordTrace tailWord_890826 prefixEnd_890826 304947945014824581918781 := by
  unfold tailWord_890826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8122773367674254453337083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21660728980464678542232221 8122773367674254453337083)
  ·
    refine ⟨12184160051511381680005625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8122773367674254453337083 12184160051511381680005625)
    ·
      refine ⟨9138120038633536260004219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12184160051511381680005625 9138120038633536260004219)
      ·
        refine ⟨13707180057950304390006329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9138120038633536260004219 13707180057950304390006329)
        ·
          refine ⟨10280385043462728292504747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13707180057950304390006329 10280385043462728292504747)
          ·
            refine ⟨15420577565194092438757121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10280385043462728292504747 15420577565194092438757121)
            ·
              refine ⟨11565433173895569329067841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15420577565194092438757121 11565433173895569329067841)
              ·
                refine ⟨8674074880421676996800881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11565433173895569329067841 8674074880421676996800881)
                ·
                  refine ⟨6505556160316257747600661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8674074880421676996800881 6505556160316257747600661)
                  ·
                    refine ⟨304947945014824581918781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6505556160316257747600661 304947945014824581918781)
                    ·
                      rfl

theorem cell22_890826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_890826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890826 prefixEnd_890826 := by exact prefixLift 890826
  have htrace : WordTrace (prefixWord ++ tailWord_890826) baseStart_890826 baseEnd_890826 := by
    simpa [prefixWord, tailWord_890826, baseEnd_890826] using wordTrace_append hprefix tailTrace_890826
  have hstable : (prefixWord ++ tailWord_890826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890826).length < 2 ^ (prefixWord ++ tailWord_890826).sum := by decide
  have hdescent : baseEnd_890826 < baseStart_890826 := by decide
  rcases family_descends (prefixWord ++ tailWord_890826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890858 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_890858 : Nat := 118140960795 + 890858 * 2 ^ 59
def prefixEnd_890858 : Nat := 4983230072969 + 3 ^ 40 * 890858 * 2
def baseEnd_890858 : Nat := 101652966422929055039561

theorem tailTrace_890858 : CollatzResearch.WordTrace tailWord_890858 prefixEnd_890858 101652966422929055039561 := by
  unfold tailWord_890858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8123065151645271819628307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21661507071054058185675485 8123065151645271819628307)
  ·
    refine ⟨12184597727467907729442461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8123065151645271819628307 12184597727467907729442461)
    ·
      refine ⟨4569224147800465398540923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12184597727467907729442461 4569224147800465398540923)
      ·
        refine ⟨6853836221700698097811385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569224147800465398540923 6853836221700698097811385)
        ·
          refine ⟨5140377166275523573358539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6853836221700698097811385 5140377166275523573358539)
          ·
            refine ⟨7710565749413285360037809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5140377166275523573358539 7710565749413285360037809)
            ·
              refine ⟨5782924312059964020028357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7710565749413285360037809 5782924312059964020028357)
              ·
                refine ⟨1084298308511243253755317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5782924312059964020028357 1084298308511243253755317)
                ·
                  refine ⟨101652966422929055039561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1084298308511243253755317 101652966422929055039561)
                  ·
                    rfl

theorem cell22_890858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_890858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890858 prefixEnd_890858 := by exact prefixLift 890858
  have htrace : WordTrace (prefixWord ++ tailWord_890858) baseStart_890858 baseEnd_890858 := by
    simpa [prefixWord, tailWord_890858, baseEnd_890858] using wordTrace_append hprefix tailTrace_890858
  have hstable : (prefixWord ++ tailWord_890858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890858).length < 2 ^ (prefixWord ++ tailWord_890858).sum := by decide
  have hdescent : baseEnd_890858 < baseStart_890858 := by decide
  rcases family_descends (prefixWord ++ tailWord_890858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890862 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_890862 : Nat := 118140960795 + 890862 * 2 ^ 59
def prefixEnd_890862 : Nat := 4983230072969 + 3 ^ 40 * 890862 * 2
def baseEnd_890862 : Nat := 304960268550532488018671

theorem tailTrace_890862 : CollatzResearch.WordTrace tailWord_890862 prefixEnd_890862 304960268550532488018671 := by
  unfold tailWord_890862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061550812320824495207355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21661604332377730641105893 4061550812320824495207355)
  ·
    refine ⟨6092326218481236742811033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061550812320824495207355 6092326218481236742811033)
    ·
      refine ⟨4569244663860927557108275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6092326218481236742811033 4569244663860927557108275)
      ·
        refine ⟨6853866995791391335662413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569244663860927557108275 6853866995791391335662413)
        ·
          refine ⟨2570200123421771750873405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6853866995791391335662413 2570200123421771750873405)
          ·
            refine ⟨963825046283164406577527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2570200123421771750873405 963825046283164406577527)
            ·
              refine ⟨1445737569424746609866291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963825046283164406577527 1445737569424746609866291)
              ·
                refine ⟨2168606354137119914799437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445737569424746609866291 2168606354137119914799437)
                ·
                  refine ⟨813227382801419968049789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2168606354137119914799437 813227382801419968049789)
                  ·
                    refine ⟨304960268550532488018671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813227382801419968049789 304960268550532488018671)
                    ·
                      rfl

theorem cell22_890862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_890862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890862 prefixEnd_890862 := by exact prefixLift 890862
  have htrace : WordTrace (prefixWord ++ tailWord_890862) baseStart_890862 baseEnd_890862 := by
    simpa [prefixWord, tailWord_890862, baseEnd_890862] using wordTrace_append hprefix tailTrace_890862
  have hstable : (prefixWord ++ tailWord_890862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890862).length < 2 ^ (prefixWord ++ tailWord_890862).sum := by decide
  have hdescent : baseEnd_890862 < baseStart_890862 := by decide
  rcases family_descends (prefixWord ++ tailWord_890862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890888 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_890888 : Nat := 118140960795 + 890888 * 2 ^ 59
def prefixEnd_890888 : Nat := 4983230072969 + 3 ^ 40 * 890888 * 2
def baseEnd_890888 : Nat := 304969168881877086868591

theorem tailTrace_890888 : CollatzResearch.WordTrace tailWord_890888 prefixEnd_890888 304969168881877086868591 := by
  unfold tailWord_890888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16246677398236201201052659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21662236530981601601403545 16246677398236201201052659)
  ·
    refine ⟨24370016097354301801578989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16246677398236201201052659 24370016097354301801578989)
    ·
      refine ⟨9138756036507863175592121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24370016097354301801578989 9138756036507863175592121)
      ·
        refine ⟨6854067027380897381694091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9138756036507863175592121 6854067027380897381694091)
        ·
          refine ⟨10281100541071346072541137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854067027380897381694091 10281100541071346072541137)
          ·
            refine ⟨7710825405803509554405853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10281100541071346072541137 7710825405803509554405853)
            ·
              refine ⟨2891559527176316082902195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7710825405803509554405853 2891559527176316082902195)
              ·
                refine ⟨4337339290764474124353293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891559527176316082902195 4337339290764474124353293)
                ·
                  refine ⟨1626502234036677796632485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4337339290764474124353293 1626502234036677796632485)
                  ·
                    refine ⟨304969168881877086868591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1626502234036677796632485 304969168881877086868591)
                    ·
                      rfl

theorem cell22_890888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_890888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890888 prefixEnd_890888 := by exact prefixLift 890888
  have htrace : WordTrace (prefixWord ++ tailWord_890888) baseStart_890888 baseEnd_890888 := by
    simpa [prefixWord, tailWord_890888, baseEnd_890888] using wordTrace_append hprefix tailTrace_890888
  have hstable : (prefixWord ++ tailWord_890888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890888).length < 2 ^ (prefixWord ++ tailWord_890888).sum := by decide
  have hdescent : baseEnd_890888 < baseStart_890888 := by decide
  rcases family_descends (prefixWord ++ tailWord_890888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890933 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_890933 : Nat := 118140960795 + 890933 * 2 ^ 59
def prefixEnd_890933 : Nat := 4983230072969 + 3 ^ 40 * 890933 * 2
def baseEnd_890933 : Nat := 304984573301511969493453

theorem tailTrace_890933 : CollatzResearch.WordTrace tailWord_890933 prefixEnd_890933 304984573301511969493453 := by
  unfold tailWord_890933
  simp only [CollatzResearch.WordTrace]
  refine ⟨32494996081309375087493453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21663330720872916724995635 32494996081309375087493453)
  ·
    refine ⟨12185623530491015657810045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32494996081309375087493453 12185623530491015657810045)
    ·
      refine ⟨4569608823934130871678767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12185623530491015657810045 4569608823934130871678767)
      ·
        refine ⟨6854413235901196307518151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569608823934130871678767 6854413235901196307518151)
        ·
          refine ⟨10281619853851794461277227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854413235901196307518151 10281619853851794461277227)
          ·
            refine ⟨15422429780777691691915841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281619853851794461277227 15422429780777691691915841)
            ·
              refine ⟨11566822335583268768936881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15422429780777691691915841 11566822335583268768936881)
              ·
                refine ⟨8675116751687451576702661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11566822335583268768936881 8675116751687451576702661)
                ·
                  refine ⟨1626584390941397170631749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8675116751687451576702661 1626584390941397170631749)
                  ·
                    refine ⟨304984573301511969493453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1626584390941397170631749 304984573301511969493453)
                    ·
                      rfl

theorem cell22_890933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_890933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890933 prefixEnd_890933 := by exact prefixLift 890933
  have htrace : WordTrace (prefixWord ++ tailWord_890933) baseStart_890933 baseEnd_890933 := by
    simpa [prefixWord, tailWord_890933, baseEnd_890933] using wordTrace_append hprefix tailTrace_890933
  have hstable : (prefixWord ++ tailWord_890933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890933).length < 2 ^ (prefixWord ++ tailWord_890933).sum := by decide
  have hdescent : baseEnd_890933 < baseStart_890933 := by decide
  rcases family_descends (prefixWord ++ tailWord_890933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890935 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 2, 3]
def baseStart_890935 : Nat := 118140960795 + 890935 * 2 ^ 59
def prefixEnd_890935 : Nat := 4983230072969 + 3 ^ 40 * 890935 * 2
def baseEnd_890935 : Nat := 304985257942384630943447

theorem tailTrace_890935 : CollatzResearch.WordTrace tailWord_890935 prefixEnd_890935 304985257942384630943447 := by
  unfold tailWord_890935
  simp only [CollatzResearch.WordTrace]
  refine ⟨32495069027302129429066259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21663379351534752952710839 32495069027302129429066259)
  ·
    refine ⟨48742603540953194143599389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32495069027302129429066259 48742603540953194143599389)
    ·
      refine ⟨18278476327857447803849771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48742603540953194143599389 18278476327857447803849771)
      ·
        refine ⟨27417714491786171705774657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18278476327857447803849771 27417714491786171705774657)
        ·
          refine ⟨20563285868839628779330993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27417714491786171705774657 20563285868839628779330993)
          ·
            refine ⟨15422464401629721584498245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20563285868839628779330993 15422464401629721584498245)
            ·
              refine ⟨2891712075305572797093421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15422464401629721584498245 2891712075305572797093421)
              ·
                refine ⟨1084392028239589798910033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2891712075305572797093421 1084392028239589798910033)
                ·
                  refine ⟨813294021179692349182525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1084392028239589798910033 813294021179692349182525)
                  ·
                    refine ⟨304985257942384630943447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813294021179692349182525 304985257942384630943447)
                    ·
                      rfl

theorem cell22_890935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_890935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890935 prefixEnd_890935 := by exact prefixLift 890935
  have htrace : WordTrace (prefixWord ++ tailWord_890935) baseStart_890935 baseEnd_890935 := by
    simpa [prefixWord, tailWord_890935, baseEnd_890935] using wordTrace_append hprefix tailTrace_890935
  have hstable : (prefixWord ++ tailWord_890935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890935).length < 2 ^ (prefixWord ++ tailWord_890935).sum := by decide
  have hdescent : baseEnd_890935 < baseStart_890935 := by decide
  rcases family_descends (prefixWord ++ tailWord_890935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_890980 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_890980 : Nat := 118140960795 + 890980 * 2 ^ 59
def prefixEnd_890980 : Nat := 4983230072969 + 3 ^ 40 * 890980 * 2
def baseEnd_890980 : Nat := 305000662362019513568309

theorem tailTrace_890980 : CollatzResearch.WordTrace tailWord_890980 prefixEnd_890980 305000662362019513568309 := by
  unfold tailWord_890980
  simp only [CollatzResearch.WordTrace]
  refine ⟨16248355156069551057227197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21664473541426068076302929 16248355156069551057227197)
  ·
    refine ⟨6093133183526081646460199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16248355156069551057227197 6093133183526081646460199)
    ·
      refine ⟨9139699775289122469690299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093133183526081646460199 9139699775289122469690299)
      ·
        refine ⟨13709549662933683704535449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139699775289122469690299 13709549662933683704535449)
        ·
          refine ⟨10282162247200262778401587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13709549662933683704535449 10282162247200262778401587)
          ·
            refine ⟨15423243370800394167602381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282162247200262778401587 15423243370800394167602381)
            ·
              refine ⟨5783716264050147812850893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15423243370800394167602381 5783716264050147812850893)
              ·
                refine ⟨2168893599018805429819085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5783716264050147812850893 2168893599018805429819085)
                ·
                  refine ⟨813335099632052036182157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2168893599018805429819085 813335099632052036182157)
                  ·
                    refine ⟨305000662362019513568309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813335099632052036182157 305000662362019513568309)
                    ·
                      rfl

theorem cell22_890980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_890980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_890980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_890980 prefixEnd_890980 := by exact prefixLift 890980
  have htrace : WordTrace (prefixWord ++ tailWord_890980) baseStart_890980 baseEnd_890980 := by
    simpa [prefixWord, tailWord_890980, baseEnd_890980] using wordTrace_append hprefix tailTrace_890980
  have hstable : (prefixWord ++ tailWord_890980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_890980).length < 2 ^ (prefixWord ++ tailWord_890980).sum := by decide
  have hdescent : baseEnd_890980 < baseStart_890980 := by decide
  rcases family_descends (prefixWord ++ tailWord_890980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891031 : List Nat := [1, 1, 3, 3, 4, 1, 3, 2, 1, 3]
def baseStart_891031 : Nat := 118140960795 + 891031 * 2 ^ 59
def prefixEnd_891031 : Nat := 4983230072969 + 3 ^ 40 * 891031 * 2
def baseEnd_891031 : Nat := 305018120704272380543153

theorem tailTrace_891031 : CollatzResearch.WordTrace tailWord_891031 prefixEnd_891031 305018120704272380543153 := by
  unfold tailWord_891031
  simp only [CollatzResearch.WordTrace]
  refine ⟨32498570434954337824560947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21665713623302891883040631 32498570434954337824560947)
  ·
    refine ⟨48747855652431506736841421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32498570434954337824560947 48747855652431506736841421)
    ·
      refine ⟨18280445869661815026315533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48747855652431506736841421 18280445869661815026315533)
      ·
        refine ⟨6855167201123180634868325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18280445869661815026315533 6855167201123180634868325)
        ·
          refine ⟨1285343850210596369037811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6855167201123180634868325 1285343850210596369037811)
          ·
            refine ⟨1928015775315894553556717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285343850210596369037811 1928015775315894553556717)
            ·
              refine ⟨723005915743460457583769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928015775315894553556717 723005915743460457583769)
              ·
                refine ⟨542254436807595343187827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723005915743460457583769 542254436807595343187827)
                ·
                  refine ⟨813381655211393014781741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542254436807595343187827 813381655211393014781741)
                  ·
                    refine ⟨305018120704272380543153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813381655211393014781741 305018120704272380543153)
                    ·
                      rfl

theorem cell22_891031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_891031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891031 prefixEnd_891031 := by exact prefixLift 891031
  have htrace : WordTrace (prefixWord ++ tailWord_891031) baseStart_891031 baseEnd_891031 := by
    simpa [prefixWord, tailWord_891031, baseEnd_891031] using wordTrace_append hprefix tailTrace_891031
  have hstable : (prefixWord ++ tailWord_891031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891031).length < 2 ^ (prefixWord ++ tailWord_891031).sum := by decide
  have hdescent : baseEnd_891031 < baseStart_891031 := by decide
  rcases family_descends (prefixWord ++ tailWord_891031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891044 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 5]
def baseStart_891044 : Nat := 118140960795 + 891044 * 2 ^ 59
def prefixEnd_891044 : Nat := 4983230072969 + 3 ^ 40 * 891044 * 2
def baseEnd_891044 : Nat := 101674190289981559989371

theorem tailTrace_891044 : CollatzResearch.WordTrace tailWord_891044 prefixEnd_891044 101674190289981559989371 := by
  unfold tailWord_891044
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249522291953620522392093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21666029722604827363189457 16249522291953620522392093)
  ·
    refine ⟨6093570859482607695897035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16249522291953620522392093 6093570859482607695897035)
    ·
      refine ⟨9140356289223911543845553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6093570859482607695897035 9140356289223911543845553)
      ·
        refine ⟨6855267216917933657884165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9140356289223911543845553 6855267216917933657884165)
        ·
          refine ⟨1285362603172112560853281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6855267216917933657884165 1285362603172112560853281)
          ·
            refine ⟨964021952379084420639961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285362603172112560853281 964021952379084420639961)
            ·
              refine ⟨723016464284313315479971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964021952379084420639961 723016464284313315479971)
              ·
                refine ⟨1084524696426469973219957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723016464284313315479971 1084524696426469973219957)
                ·
                  refine ⟨101674190289981559989371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1084524696426469973219957 101674190289981559989371)
                  ·
                    rfl

theorem cell22_891044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_891044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891044 prefixEnd_891044 := by exact prefixLift 891044
  have htrace : WordTrace (prefixWord ++ tailWord_891044) baseStart_891044 baseEnd_891044 := by
    simpa [prefixWord, tailWord_891044, baseEnd_891044] using wordTrace_append hprefix tailTrace_891044
  have hstable : (prefixWord ++ tailWord_891044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891044).length < 2 ^ (prefixWord ++ tailWord_891044).sum := by decide
  have hdescent : baseEnd_891044 < baseStart_891044 := by decide
  rcases family_descends (prefixWord ++ tailWord_891044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891057 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_891057 : Nat := 118140960795 + 891057 * 2 ^ 59
def prefixEnd_891057 : Nat := 4983230072969 + 3 ^ 40 * 891057 * 2
def baseEnd_891057 : Nat := 305027021035616979393073

theorem tailTrace_891057 : CollatzResearch.WordTrace tailWord_891057 prefixEnd_891057 305027021035616979393073 := by
  unfold tailWord_891057
  simp only [CollatzResearch.WordTrace]
  refine ⟨32499518732860144265007425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21666345821906762843338283 32499518732860144265007425)
  ·
    refine ⟨24374639049645108198755569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32499518732860144265007425 24374639049645108198755569)
    ·
      refine ⟨18280979287233831149066677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24374639049645108198755569 18280979287233831149066677)
      ·
        refine ⟨1713841808178171670225001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18280979287233831149066677 1713841808178171670225001)
        ·
          refine ⟨1285381356133628752668751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1713841808178171670225001 1285381356133628752668751)
          ·
            refine ⟨1928072034200443129003127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285381356133628752668751 1928072034200443129003127)
            ·
              refine ⟨2892108051300664693504691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928072034200443129003127 2892108051300664693504691)
              ·
                refine ⟨4338162076950997040257037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892108051300664693504691 4338162076950997040257037)
                ·
                  refine ⟨1626810778856623890096389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4338162076950997040257037 1626810778856623890096389)
                  ·
                    refine ⟨305027021035616979393073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1626810778856623890096389 305027021035616979393073)
                    ·
                      rfl

theorem cell22_891057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_891057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891057 prefixEnd_891057 := by exact prefixLift 891057
  have htrace : WordTrace (prefixWord ++ tailWord_891057) baseStart_891057 baseEnd_891057 := by
    simpa [prefixWord, tailWord_891057, baseEnd_891057] using wordTrace_append hprefix tailTrace_891057
  have hstable : (prefixWord ++ tailWord_891057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891057).length < 2 ^ (prefixWord ++ tailWord_891057).sum := by decide
  have hdescent : baseEnd_891057 < baseStart_891057 := by decide
  rcases family_descends (prefixWord ++ tailWord_891057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891087 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 2, 3]
def baseStart_891087 : Nat := 118140960795 + 891087 * 2 ^ 59
def prefixEnd_891087 : Nat := 4983230072969 + 3 ^ 40 * 891087 * 2
def baseEnd_891087 : Nat := 305037290648706901142981

theorem tailTrace_891087 : CollatzResearch.WordTrace tailWord_891087 prefixEnd_891087 305037290648706901142981 := by
  unfold tailWord_891087
  simp only [CollatzResearch.WordTrace]
  refine ⟨32500612922751459388599515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21667075281834306259066343 32500612922751459388599515)
  ·
    refine ⟨48750919384127189082899273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32500612922751459388599515 48750919384127189082899273)
    ·
      refine ⟨36563189538095391812174455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48750919384127189082899273 36563189538095391812174455)
      ·
        refine ⟨54844784307143087718261683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36563189538095391812174455 54844784307143087718261683)
        ·
          refine ⟨82267176460714631577392525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54844784307143087718261683 82267176460714631577392525)
          ·
            refine ⟨30850191172767986841522197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82267176460714631577392525 30850191172767986841522197)
            ·
              refine ⟨1446102711223499383196353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30850191172767986841522197 1446102711223499383196353)
              ·
                refine ⟨1084577033417624537397265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446102711223499383196353 1084577033417624537397265)
                ·
                  refine ⟨813432775063218403047949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1084577033417624537397265 813432775063218403047949)
                  ·
                    refine ⟨305037290648706901142981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813432775063218403047949 305037290648706901142981)
                    ·
                      rfl

theorem cell22_891087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_891087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891087 prefixEnd_891087 := by exact prefixLift 891087
  have htrace : WordTrace (prefixWord ++ tailWord_891087) baseStart_891087 baseEnd_891087 := by
    simpa [prefixWord, tailWord_891087, baseEnd_891087] using wordTrace_append hprefix tailTrace_891087
  have hstable : (prefixWord ++ tailWord_891087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891087).length < 2 ^ (prefixWord ++ tailWord_891087).sum := by decide
  have hdescent : baseEnd_891087 < baseStart_891087 := by decide
  rcases family_descends (prefixWord ++ tailWord_891087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891106 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_891106 : Nat := 118140960795 + 891106 * 2 ^ 59
def prefixEnd_891106 : Nat := 4983230072969 + 3 ^ 40 * 891106 * 2
def baseEnd_891106 : Nat := 101681264912332394972641

theorem tailTrace_891106 : CollatzResearch.WordTrace tailWord_891106 prefixEnd_891106 101681264912332394972641 := by
  unfold tailWord_891106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125326477420656408385293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21667537273121750422360781 8125326477420656408385293)
  ·
    refine ⟨3046997429032746153144485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8125326477420656408385293 3046997429032746153144485)
    ·
      refine ⟨571312017943639903714591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3046997429032746153144485 571312017943639903714591)
      ·
        refine ⟨856968026915459855571887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571312017943639903714591 856968026915459855571887)
        ·
          refine ⟨1285452040373189783357831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856968026915459855571887 1285452040373189783357831)
          ·
            refine ⟨1928178060559784675036747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285452040373189783357831 1928178060559784675036747)
            ·
              refine ⟨2892267090839677012555121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928178060559784675036747 2892267090839677012555121)
              ·
                refine ⟨2169200318129757759416341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892267090839677012555121 2169200318129757759416341)
                ·
                  refine ⟨101681264912332394972641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2169200318129757759416341 101681264912332394972641)
                  ·
                    rfl

theorem cell22_891106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_891106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891106 prefixEnd_891106 := by exact prefixLift 891106
  have htrace : WordTrace (prefixWord ++ tailWord_891106) baseStart_891106 baseEnd_891106 := by
    simpa [prefixWord, tailWord_891106, baseEnd_891106] using wordTrace_append hprefix tailTrace_891106
  have hstable : (prefixWord ++ tailWord_891106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891106).length < 2 ^ (prefixWord ++ tailWord_891106).sum := by decide
  have hdescent : baseEnd_891106 < baseStart_891106 := by decide
  rcases family_descends (prefixWord ++ tailWord_891106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891145 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 7]
def baseStart_891145 : Nat := 118140960795 + 891145 * 2 ^ 59
def prefixEnd_891145 : Nat := 4983230072969 + 3 ^ 40 * 891145 * 2
def baseEnd_891145 : Nat := 101685715078004694397601

theorem tailTrace_891145 : CollatzResearch.WordTrace tailWord_891145 prefixEnd_891145 101685715078004694397601 := by
  unfold tailWord_891145
  simp only [CollatzResearch.WordTrace]
  refine ⟨32502728356541335294210889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21668485571027556862807259 32502728356541335294210889)
  ·
    refine ⟨24377046267406001470658167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32502728356541335294210889 24377046267406001470658167)
    ·
      refine ⟨36565569401109002205987251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24377046267406001470658167 36565569401109002205987251)
      ·
        refine ⟨54848354101663503308980877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36565569401109002205987251 54848354101663503308980877)
        ·
          refine ⟨20568132788123813740867829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54848354101663503308980877 20568132788123813740867829)
          ·
            refine ⟨1928262448886607538206359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20568132788123813740867829 1928262448886607538206359)
            ·
              refine ⟨2892393673329911307309539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928262448886607538206359 2892393673329911307309539)
              ·
                refine ⟨4338590509994866960964309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892393673329911307309539 4338590509994866960964309)
                ·
                  refine ⟨101685715078004694397601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4338590509994866960964309 101685715078004694397601)
                  ·
                    rfl

theorem cell22_891145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_891145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891145 prefixEnd_891145 := by exact prefixLift 891145
  have htrace : WordTrace (prefixWord ++ tailWord_891145) baseStart_891145 baseEnd_891145 := by
    simpa [prefixWord, tailWord_891145, baseEnd_891145] using wordTrace_append hprefix tailTrace_891145
  have hstable : (prefixWord ++ tailWord_891145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891145).length < 2 ^ (prefixWord ++ tailWord_891145).sum := by decide
  have hdescent : baseEnd_891145 < baseStart_891145 := by decide
  rcases family_descends (prefixWord ++ tailWord_891145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891160 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_891160 : Nat := 118140960795 + 891160 * 2 ^ 59
def prefixEnd_891160 : Nat := 4983230072969 + 3 ^ 40 * 891160 * 2
def baseEnd_891160 : Nat := 305062280040559044067757

theorem tailTrace_891160 : CollatzResearch.WordTrace tailWord_891160 prefixEnd_891160 305062280040559044067757 := by
  unfold tailWord_891160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16251637725743496428003467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21668850300991328570671289 16251637725743496428003467)
  ·
    refine ⟨24377456588615244642005201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16251637725743496428003467 24377456588615244642005201)
    ·
      refine ⟨18283092441461433481503901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24377456588615244642005201 18283092441461433481503901)
      ·
        refine ⟨6856159665548037555563963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18283092441461433481503901 6856159665548037555563963)
        ·
          refine ⟨10284239498322056333345945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856159665548037555563963 10284239498322056333345945)
          ·
            refine ⟨7713179623741542250009459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10284239498322056333345945 7713179623741542250009459)
            ·
              refine ⟨11569769435612313375014189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713179623741542250009459 11569769435612313375014189)
              ·
                refine ⟨4338663538354617515630321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11569769435612313375014189 4338663538354617515630321)
                ·
                  refine ⟨3253997653765963136722741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4338663538354617515630321 3253997653765963136722741)
                  ·
                    refine ⟨305062280040559044067757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3253997653765963136722741 305062280040559044067757)
                    ·
                      rfl

theorem cell22_891160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_891160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891160 prefixEnd_891160 := by exact prefixLift 891160
  have htrace : WordTrace (prefixWord ++ tailWord_891160) baseStart_891160 baseEnd_891160 := by
    simpa [prefixWord, tailWord_891160, baseEnd_891160] using wordTrace_append hprefix tailTrace_891160
  have hstable : (prefixWord ++ tailWord_891160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891160).length < 2 ^ (prefixWord ++ tailWord_891160).sum := by decide
  have hdescent : baseEnd_891160 < baseStart_891160 := by decide
  rcases family_descends (prefixWord ++ tailWord_891160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891166 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_891166 : Nat := 118140960795 + 891166 * 2 ^ 59
def prefixEnd_891166 : Nat := 4983230072969 + 3 ^ 40 * 891166 * 2
def baseEnd_891166 : Nat := 305064333963177028417739

theorem tailTrace_891166 : CollatzResearch.WordTrace tailWord_891166 prefixEnd_891166 305064333963177028417739 := by
  unfold tailWord_891166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4062936786183156985090669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21668996192976837253816901 4062936786183156985090669)
  ·
    refine ⟨1523601294818683869409001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4062936786183156985090669 1523601294818683869409001)
    ·
      refine ⟨1142700971114012902056751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1523601294818683869409001 1142700971114012902056751)
      ·
        refine ⟨1714051456671019353085127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1142700971114012902056751 1714051456671019353085127)
        ·
          refine ⟨2571077185006529029627691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714051456671019353085127 2571077185006529029627691)
          ·
            refine ⟨3856615777509793544441537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571077185006529029627691 3856615777509793544441537)
            ·
              refine ⟨2892461833132345158331153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3856615777509793544441537 2892461833132345158331153)
              ·
                refine ⟨2169346374849258868748365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892461833132345158331153 2169346374849258868748365)
                ·
                  refine ⟨813504890568472075780637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2169346374849258868748365 813504890568472075780637)
                  ·
                    refine ⟨305064333963177028417739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813504890568472075780637 305064333963177028417739)
                    ·
                      rfl

theorem cell22_891166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_891166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891166 prefixEnd_891166 := by exact prefixLift 891166
  have htrace : WordTrace (prefixWord ++ tailWord_891166) baseStart_891166 baseEnd_891166 := by
    simpa [prefixWord, tailWord_891166, baseEnd_891166] using wordTrace_append hprefix tailTrace_891166
  have hstable : (prefixWord ++ tailWord_891166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891166).length < 2 ^ (prefixWord ++ tailWord_891166).sum := by decide
  have hdescent : baseEnd_891166 < baseStart_891166 := by decide
  rcases family_descends (prefixWord ++ tailWord_891166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891192 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_891192 : Nat := 118140960795 + 891192 * 2 ^ 59
def prefixEnd_891192 : Nat := 4983230072969 + 3 ^ 40 * 891192 * 2
def baseEnd_891192 : Nat := 305073234294521627267659

theorem tailTrace_891192 : CollatzResearch.WordTrace tailWord_891192 prefixEnd_891192 305073234294521627267659 := by
  unfold tailWord_891192
  simp only [CollatzResearch.WordTrace]
  refine ⟨16252221293685531160585915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21669628391580708214114553 16252221293685531160585915)
  ·
    refine ⟨24378331940528296740878873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16252221293685531160585915 24378331940528296740878873)
    ·
      refine ⟨18283748955396222555659155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24378331940528296740878873 18283748955396222555659155)
      ·
        refine ⟨27425623433094333833488733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18283748955396222555659155 27425623433094333833488733)
        ·
          refine ⟨10284608787410375187558275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27425623433094333833488733 10284608787410375187558275)
          ·
            refine ⟨15426913181115562781337413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10284608787410375187558275 15426913181115562781337413)
            ·
              refine ⟨2892546221459168021500765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15426913181115562781337413 2892546221459168021500765)
              ·
                refine ⟨1084704833047188008062787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2892546221459168021500765 1084704833047188008062787)
                ·
                  refine ⟨1627057249570782012094181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084704833047188008062787 1627057249570782012094181)
                  ·
                    refine ⟨305073234294521627267659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1627057249570782012094181 305073234294521627267659)
                    ·
                      rfl

theorem cell22_891192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_891192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891192 prefixEnd_891192 := by exact prefixLift 891192
  have htrace : WordTrace (prefixWord ++ tailWord_891192) baseStart_891192 baseEnd_891192 := by
    simpa [prefixWord, tailWord_891192, baseEnd_891192] using wordTrace_append hprefix tailTrace_891192
  have hstable : (prefixWord ++ tailWord_891192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891192).length < 2 ^ (prefixWord ++ tailWord_891192).sum := by decide
  have hdescent : baseEnd_891192 < baseStart_891192 := by decide
  rcases family_descends (prefixWord ++ tailWord_891192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891235 : List Nat := [1, 1, 1, 5, 2, 1, 1, 10]
def baseStart_891235 : Nat := 118140960795 + 891235 * 2 ^ 59
def prefixEnd_891235 : Nat := 4983230072969 + 3 ^ 40 * 891235 * 2
def baseEnd_891235 : Nat := 33898661563698205382503

theorem tailTrace_891235 : CollatzResearch.WordTrace tailWord_891235 prefixEnd_891235 33898661563698205382503 := by
  unfold tailWord_891235
  simp only [CollatzResearch.WordTrace]
  refine ⟨32506010926215280664987159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21670673950810187109991439 32506010926215280664987159)
  ·
    refine ⟨48759016389322920997480739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32506010926215280664987159 48759016389322920997480739)
    ·
      refine ⟨73138524583984381496221109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48759016389322920997480739 73138524583984381496221109)
      ·
        refine ⟨6856736679748535765270729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73138524583984381496221109 6856736679748535765270729)
        ·
          refine ⟨5142552509811401823953047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6856736679748535765270729 5142552509811401823953047)
          ·
            refine ⟨7713828764717102735929571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142552509811401823953047 7713828764717102735929571)
            ·
              refine ⟨11570743147075654103894357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713828764717102735929571 11570743147075654103894357)
              ·
                refine ⟨33898661563698205382503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11570743147075654103894357 33898661563698205382503)
                ·
                  rfl

theorem cell22_891235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 10].length) (baseStart_891235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891235 prefixEnd_891235 := by exact prefixLift 891235
  have htrace : WordTrace (prefixWord ++ tailWord_891235) baseStart_891235 baseEnd_891235 := by
    simpa [prefixWord, tailWord_891235, baseEnd_891235] using wordTrace_append hprefix tailTrace_891235
  have hstable : (prefixWord ++ tailWord_891235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891235).length < 2 ^ (prefixWord ++ tailWord_891235).sum := by decide
  have hdescent : baseEnd_891235 < baseStart_891235 := by decide
  rcases family_descends (prefixWord ++ tailWord_891235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891237 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_891237 : Nat := 118140960795 + 891237 * 2 ^ 59
def prefixEnd_891237 : Nat := 4983230072969 + 3 ^ 40 * 891237 * 2
def baseEnd_891237 : Nat := 305088638714156509892521

theorem tailTrace_891237 : CollatzResearch.WordTrace tailWord_891237 prefixEnd_891237 305088638714156509892521 := by
  unfold tailWord_891237
  simp only [CollatzResearch.WordTrace]
  refine ⟨32506083872208035006559965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21670722581472023337706643 32506083872208035006559965)
  ·
    refine ⟨12189781452078013127459987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32506083872208035006559965 12189781452078013127459987)
    ·
      refine ⟨18284672178117019691189981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12189781452078013127459987 18284672178117019691189981)
      ·
        refine ⟨6856752066793882384196243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18284672178117019691189981 6856752066793882384196243)
        ·
          refine ⟨10285128100190823576294365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856752066793882384196243 10285128100190823576294365)
          ·
            refine ⟨3856923037571558841110387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10285128100190823576294365 3856923037571558841110387)
            ·
              refine ⟨5785384556357338261665581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856923037571558841110387 5785384556357338261665581)
              ·
                refine ⟨2169519208634001848124593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5785384556357338261665581 2169519208634001848124593)
                ·
                  refine ⟨1627139406475501386093445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169519208634001848124593 1627139406475501386093445)
                  ·
                    refine ⟨305088638714156509892521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1627139406475501386093445 305088638714156509892521)
                    ·
                      rfl

theorem cell22_891237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_891237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891237 prefixEnd_891237 := by exact prefixLift 891237
  have htrace : WordTrace (prefixWord ++ tailWord_891237) baseStart_891237 baseEnd_891237 := by
    simpa [prefixWord, tailWord_891237, baseEnd_891237] using wordTrace_append hprefix tailTrace_891237
  have hstable : (prefixWord ++ tailWord_891237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891237).length < 2 ^ (prefixWord ++ tailWord_891237).sum := by decide
  have hdescent : baseEnd_891237 < baseStart_891237 := by decide
  rcases family_descends (prefixWord ++ tailWord_891237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891301 : List Nat := [1, 3, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_891301 : Nat := 118140960795 + 891301 * 2 ^ 59
def prefixEnd_891301 : Nat := 4983230072969 + 3 ^ 40 * 891301 * 2
def baseEnd_891301 : Nat := 305110547222081676292325

theorem tailTrace_891301 : CollatzResearch.WordTrace tailWord_891301 prefixEnd_891301 305110547222081676292325 := by
  unfold tailWord_891301
  simp only [CollatzResearch.WordTrace]
  refine ⟨32508418143976173936889757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21672278762650782624593171 32508418143976173936889757)
  ·
    refine ⟨12190656803991065226333659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32508418143976173936889757 12190656803991065226333659)
    ·
      refine ⟨18285985205986597839500489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12190656803991065226333659 18285985205986597839500489)
      ·
        refine ⟨13714488904489948379625367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18285985205986597839500489 13714488904489948379625367)
        ·
          refine ⟨20571733356734922569438051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13714488904489948379625367 20571733356734922569438051)
          ·
            refine ⟨30857600035102383854157077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20571733356734922569438051 30857600035102383854157077)
            ·
              refine ⟨1446450001645424243163613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30857600035102383854157077 1446450001645424243163613)
              ·
                refine ⟨542418750617034091186355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1446450001645424243163613 542418750617034091186355)
                ·
                  refine ⟨813628125925551136779533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542418750617034091186355 813628125925551136779533)
                  ·
                    refine ⟨305110547222081676292325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 813628125925551136779533 305110547222081676292325)
                    ·
                      rfl

theorem cell22_891301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_891301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891301 prefixEnd_891301 := by exact prefixLift 891301
  have htrace : WordTrace (prefixWord ++ tailWord_891301) baseStart_891301 baseEnd_891301 := by
    simpa [prefixWord, tailWord_891301, baseEnd_891301] using wordTrace_append hprefix tailTrace_891301
  have hstable : (prefixWord ++ tailWord_891301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891301).length < 2 ^ (prefixWord ++ tailWord_891301).sum := by decide
  have hdescent : baseEnd_891301 < baseStart_891301 := by decide
  rcases family_descends (prefixWord ++ tailWord_891301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891376 : List Nat := [2, 1, 1, 1, 3, 3, 5, 2, 4]
def baseStart_891376 : Nat := 118140960795 + 891376 * 2 ^ 59
def prefixEnd_891376 : Nat := 4983230072969 + 3 ^ 40 * 891376 * 2
def baseEnd_891376 : Nat := 101712073751602160222365

theorem tailTrace_891376 : CollatzResearch.WordTrace tailWord_891376 prefixEnd_891376 101712073751602160222365 := by
  unfold tailWord_891376
  simp only [CollatzResearch.WordTrace]
  refine ⟨16255576809352230872934991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21674102412469641163913321 16255576809352230872934991)
  ·
    refine ⟨24383365214028346309402487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16255576809352230872934991 24383365214028346309402487)
    ·
      refine ⟨36575047821042519464103731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24383365214028346309402487 36575047821042519464103731)
      ·
        refine ⟨54862571731563779196155597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36575047821042519464103731 54862571731563779196155597)
        ·
          refine ⟨20573464399336417198558349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54862571731563779196155597 20573464399336417198558349)
          ·
            refine ⟨7715049149751156449459381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20573464399336417198558349 7715049149751156449459381)
            ·
              refine ⟨723285857789170917136817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7715049149751156449459381 723285857789170917136817)
              ·
                refine ⟨542464393341878187852613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723285857789170917136817 542464393341878187852613)
                ·
                  refine ⟨101712073751602160222365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 542464393341878187852613 101712073751602160222365)
                  ·
                    rfl

theorem cell22_891376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_891376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891376 prefixEnd_891376 := by exact prefixLift 891376
  have htrace : WordTrace (prefixWord ++ tailWord_891376) baseStart_891376 baseEnd_891376 := by
    simpa [prefixWord, tailWord_891376, baseEnd_891376] using wordTrace_append hprefix tailTrace_891376
  have hstable : (prefixWord ++ tailWord_891376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891376).length < 2 ^ (prefixWord ++ tailWord_891376).sum := by decide
  have hdescent : baseEnd_891376 < baseStart_891376 := by decide
  rcases family_descends (prefixWord ++ tailWord_891376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891406 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_891406 : Nat := 118140960795 + 891406 * 2 ^ 59
def prefixEnd_891406 : Nat := 4983230072969 + 3 ^ 40 * 891406 * 2
def baseEnd_891406 : Nat := 305146490867896402417003

theorem tailTrace_891406 : CollatzResearch.WordTrace tailWord_891406 prefixEnd_891406 305146490867896402417003 := by
  unfold tailWord_891406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064030976074472108682759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21674831872397184579641381 4064030976074472108682759)
  ·
    refine ⟨6096046464111708163024139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064030976074472108682759 6096046464111708163024139)
    ·
      refine ⟨9144069696167562244536209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096046464111708163024139 9144069696167562244536209)
      ·
        refine ⟨6858052272125671683402157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9144069696167562244536209 6858052272125671683402157)
        ·
          refine ⟨2571769602047126881275809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6858052272125671683402157 2571769602047126881275809)
          ·
            refine ⟨1928827201535345160956857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2571769602047126881275809 1928827201535345160956857)
            ·
              refine ⟨1446620401151508870717643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928827201535345160956857 1446620401151508870717643)
              ·
                refine ⟨2169930601727263306076465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446620401151508870717643 2169930601727263306076465)
                ·
                  refine ⟨1627447951295447479557349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169930601727263306076465 1627447951295447479557349)
                  ·
                    refine ⟨305146490867896402417003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1627447951295447479557349 305146490867896402417003)
                    ·
                      rfl

theorem cell22_891406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_891406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891406 prefixEnd_891406 := by exact prefixLift 891406
  have htrace : WordTrace (prefixWord ++ tailWord_891406) baseStart_891406 baseEnd_891406 := by
    simpa [prefixWord, tailWord_891406, baseEnd_891406] using wordTrace_append hprefix tailTrace_891406
  have hstable : (prefixWord ++ tailWord_891406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891406).length < 2 ^ (prefixWord ++ tailWord_891406).sum := by decide
  have hdescent : baseEnd_891406 < baseStart_891406 := by decide
  rcases family_descends (prefixWord ++ tailWord_891406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891434 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_891434 : Nat := 118140960795 + 891434 * 2 ^ 59
def prefixEnd_891434 : Nat := 4983230072969 + 3 ^ 40 * 891434 * 2
def baseEnd_891434 : Nat := 305156075840113662716917

theorem tailTrace_891434 : CollatzResearch.WordTrace tailWord_891434 prefixEnd_891434 305156075840113662716917 := by
  unfold tailWord_891434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8128317263123584412870339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21675512701662891767654237 8128317263123584412870339)
  ·
    refine ⟨12192475894685376619305509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8128317263123584412870339 12192475894685376619305509)
    ·
      refine ⟨2286089230253508116119783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12192475894685376619305509 2286089230253508116119783)
      ·
        refine ⟨3429133845380262174179675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286089230253508116119783 3429133845380262174179675)
        ·
          refine ⟨5143700768070393261269513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429133845380262174179675 5143700768070393261269513)
          ·
            refine ⟨3857775576052794945952135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5143700768070393261269513 3857775576052794945952135)
            ·
              refine ⟨5786663364079192418928203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857775576052794945952135 5786663364079192418928203)
              ·
                refine ⟨8679995046118788628392305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5786663364079192418928203 8679995046118788628392305)
                ·
                  refine ⟨6509996284589091471294229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8679995046118788628392305 6509996284589091471294229)
                  ·
                    refine ⟨305156075840113662716917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6509996284589091471294229 305156075840113662716917)
                    ·
                      rfl

theorem cell22_891434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_891434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891434 prefixEnd_891434 := by exact prefixLift 891434
  have htrace : WordTrace (prefixWord ++ tailWord_891434) baseStart_891434 baseEnd_891434 := by
    simpa [prefixWord, tailWord_891434, baseEnd_891434] using wordTrace_append hprefix tailTrace_891434
  have hstable : (prefixWord ++ tailWord_891434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891434).length < 2 ^ (prefixWord ++ tailWord_891434).sum := by decide
  have hdescent : baseEnd_891434 < baseStart_891434 := by decide
  rcases family_descends (prefixWord ++ tailWord_891434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891438 : List Nat := [4, 1, 3, 1, 4, 1, 1, 7]
def baseStart_891438 : Nat := 118140960795 + 891438 * 2 ^ 59
def prefixEnd_891438 : Nat := 4983230072969 + 3 ^ 40 * 891438 * 2
def baseEnd_891438 : Nat := 33906382791317665068545

theorem tailTrace_891438 : CollatzResearch.WordTrace tailWord_891438 prefixEnd_891438 33906382791317665068545 := by
  unfold tailWord_891438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064176868059980791828371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21675609962986564223084645 4064176868059980791828371)
  ·
    refine ⟨6096265302089971187742557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064176868059980791828371 6096265302089971187742557)
    ·
      refine ⟨2286099488283739195403459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6096265302089971187742557 2286099488283739195403459)
      ·
        refine ⟨3429149232425608793105189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286099488283739195403459 3429149232425608793105189)
        ·
          refine ⟨642965481079801648707223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3429149232425608793105189 642965481079801648707223)
          ·
            refine ⟨964448221619702473060835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642965481079801648707223 964448221619702473060835)
            ·
              refine ⟨1446672332429553709591253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964448221619702473060835 1446672332429553709591253)
              ·
                refine ⟨33906382791317665068545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1446672332429553709591253 33906382791317665068545)
                ·
                  rfl

theorem cell22_891438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_891438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891438 prefixEnd_891438 := by exact prefixLift 891438
  have htrace : WordTrace (prefixWord ++ tailWord_891438) baseStart_891438 baseEnd_891438 := by
    simpa [prefixWord, tailWord_891438, baseEnd_891438] using wordTrace_append hprefix tailTrace_891438
  have hstable : (prefixWord ++ tailWord_891438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891438).length < 2 ^ (prefixWord ++ tailWord_891438).sum := by decide
  have hdescent : baseEnd_891438 < baseStart_891438 := by decide
  rcases family_descends (prefixWord ++ tailWord_891438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891449 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 5]
def baseStart_891449 : Nat := 118140960795 + 891449 * 2 ^ 59
def prefixEnd_891449 : Nat := 4983230072969 + 3 ^ 40 * 891449 * 2
def baseEnd_891449 : Nat := 101720403548886207863957

theorem tailTrace_891449 : CollatzResearch.WordTrace tailWord_891449 prefixEnd_891449 101720403548886207863957 := by
  unfold tailWord_891449
  simp only [CollatzResearch.WordTrace]
  refine ⟨32513816147439995213277401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21675877431626663475518267 32513816147439995213277401)
  ·
    refine ⟨24385362110579996409958051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32513816147439995213277401 24385362110579996409958051)
    ·
      refine ⟨36578043165869994614937077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24385362110579996409958051 36578043165869994614937077)
      ·
        refine ⟨3429191546800311995150351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36578043165869994614937077 3429191546800311995150351)
        ·
          refine ⟨5143787320200467992725527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429191546800311995150351 5143787320200467992725527)
          ·
            refine ⟨7715680980300701989088291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5143787320200467992725527 7715680980300701989088291)
            ·
              refine ⟨11573521470451052983632437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7715680980300701989088291 11573521470451052983632437)
              ·
                refine ⟨1085017637854786217215541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11573521470451052983632437 1085017637854786217215541)
                ·
                  refine ⟨101720403548886207863957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1085017637854786217215541 101720403548886207863957)
                  ·
                    rfl

theorem cell22_891449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_891449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891449 prefixEnd_891449 := by exact prefixLift 891449
  have htrace : WordTrace (prefixWord ++ tailWord_891449) baseStart_891449 baseEnd_891449 := by
    simpa [prefixWord, tailWord_891449, baseEnd_891449] using wordTrace_append hprefix tailTrace_891449
  have hstable : (prefixWord ++ tailWord_891449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891449).length < 2 ^ (prefixWord ++ tailWord_891449).sum := by decide
  have hdescent : baseEnd_891449 < baseStart_891449 := by decide
  rcases family_descends (prefixWord ++ tailWord_891449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891590 : List Nat := [6, 1, 2, 1, 3, 9]
def baseStart_891590 : Nat := 118140960795 + 891590 * 2 ^ 59
def prefixEnd_891590 : Nat := 4983230072969 + 3 ^ 40 * 891590 * 2
def baseEnd_891590 : Nat := 3768018244792361182919

theorem tailTrace_891590 : CollatzResearch.WordTrace tailWord_891590 prefixEnd_891590 3768018244792361182919 := by
  unfold tailWord_891590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016217463747786759192507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21679305893286117529440149 1016217463747786759192507)
  ·
    refine ⟨1524326195621680138788761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1016217463747786759192507 1524326195621680138788761)
    ·
      refine ⟨1143244646716260104091571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524326195621680138788761 1143244646716260104091571)
      ·
        refine ⟨1714866970074390156137357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143244646716260104091571 1714866970074390156137357)
        ·
          refine ⟨643075113777896308551509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1714866970074390156137357 643075113777896308551509)
          ·
            refine ⟨3768018244792361182919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 643075113777896308551509 3768018244792361182919)
            ·
              rfl

theorem cell22_891590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 9].length) (baseStart_891590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891590 prefixEnd_891590 := by exact prefixLift 891590
  have htrace : WordTrace (prefixWord ++ tailWord_891590) baseStart_891590 baseEnd_891590 := by
    simpa [prefixWord, tailWord_891590, baseEnd_891590] using wordTrace_append hprefix tailTrace_891590
  have hstable : (prefixWord ++ tailWord_891590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891590).length < 2 ^ (prefixWord ++ tailWord_891590).sum := by decide
  have hdescent : baseEnd_891590 < baseStart_891590 := by decide
  rcases family_descends (prefixWord ++ tailWord_891590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891601 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 5]
def baseStart_891601 : Nat := 118140960795 + 891601 * 2 ^ 59
def prefixEnd_891601 : Nat := 4983230072969 + 3 ^ 40 * 891601 * 2
def baseEnd_891601 : Nat := 101737747784326964597135

theorem tailTrace_891601 : CollatzResearch.WordTrace tailWord_891601 prefixEnd_891601 101737747784326964597135 := by
  unfold tailWord_891601
  simp only [CollatzResearch.WordTrace]
  refine ⟨32519360042889325172810657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21679573361926216781873771 32519360042889325172810657)
  ·
    refine ⟨24389520032166993879607993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32519360042889325172810657 24389520032166993879607993)
    ·
      refine ⟨18292140024125245409705995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24389520032166993879607993 18292140024125245409705995)
      ·
        refine ⟨27438210036187868114558993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18292140024125245409705995 27438210036187868114558993)
        ·
          refine ⟨20578657527140901085919245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27438210036187868114558993 20578657527140901085919245)
          ·
            refine ⟨7716996572677837907219717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20578657527140901085919245 7716996572677837907219717)
            ·
              refine ⟨1446936857377094607603697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7716996572677837907219717 1446936857377094607603697)
              ·
                refine ⟨1085202643032820955702773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446936857377094607603697 1085202643032820955702773)
                ·
                  refine ⟨101737747784326964597135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1085202643032820955702773 101737747784326964597135)
                  ·
                    rfl

theorem cell22_891601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_891601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891601 prefixEnd_891601 := by exact prefixLift 891601
  have htrace : WordTrace (prefixWord ++ tailWord_891601) baseStart_891601 baseEnd_891601 := by
    simpa [prefixWord, tailWord_891601, baseEnd_891601] using wordTrace_append hprefix tailTrace_891601
  have hstable : (prefixWord ++ tailWord_891601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891601).length < 2 ^ (prefixWord ++ tailWord_891601).sum := by decide
  have hdescent : baseEnd_891601 < baseStart_891601 := by decide
  rcases family_descends (prefixWord ++ tailWord_891601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891631 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 3, 4]
def baseStart_891631 : Nat := 118140960795 + 891631 * 2 ^ 59
def prefixEnd_891631 : Nat := 4983230072969 + 3 ^ 40 * 891631 * 2
def baseEnd_891631 : Nat := 305223512966070815541313

theorem tailTrace_891631 : CollatzResearch.WordTrace tailWord_891631 prefixEnd_891631 305223512966070815541313 := by
  unfold tailWord_891631
  simp only [CollatzResearch.WordTrace]
  refine ⟨32520454232780640296402747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21680302821853760197601831 32520454232780640296402747)
  ·
    refine ⟨48780681349170960444604121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32520454232780640296402747 48780681349170960444604121)
    ·
      refine ⟨36585511011878220333453091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48780681349170960444604121 36585511011878220333453091)
      ·
        refine ⟨54878266517817330500179637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36585511011878220333453091 54878266517817330500179637)
        ·
          refine ⟨5144837486045374734391841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54878266517817330500179637 5144837486045374734391841)
          ·
            refine ⟨3858628114534031050793881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144837486045374734391841 3858628114534031050793881)
            ·
              refine ⟨2893971085900523288095411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858628114534031050793881 2893971085900523288095411)
              ·
                refine ⟨4340956628850784932143117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893971085900523288095411 4340956628850784932143117)
                ·
                  refine ⟨1627858735819044349553669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4340956628850784932143117 1627858735819044349553669)
                  ·
                    refine ⟨305223512966070815541313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1627858735819044349553669 305223512966070815541313)
                    ·
                      rfl

theorem cell22_891631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_891631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891631 prefixEnd_891631 := by exact prefixLift 891631
  have htrace : WordTrace (prefixWord ++ tailWord_891631) baseStart_891631 baseEnd_891631 := by
    simpa [prefixWord, tailWord_891631, baseEnd_891631] using wordTrace_append hprefix tailTrace_891631
  have hstable : (prefixWord ++ tailWord_891631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891631).length < 2 ^ (prefixWord ++ tailWord_891631).sum := by decide
  have hdescent : baseEnd_891631 < baseStart_891631 := by decide
  rcases family_descends (prefixWord ++ tailWord_891631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891676 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_891676 : Nat := 118140960795 + 891676 * 2 ^ 59
def prefixEnd_891676 : Nat := 4983230072969 + 3 ^ 40 * 891676 * 2
def baseEnd_891676 : Nat := 305238917385705698166175

theorem tailTrace_891676 : CollatzResearch.WordTrace tailWord_891676 prefixEnd_891676 305238917385705698166175 := by
  unfold tailWord_891676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16261047758808806490895441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21681397011745075321193921 16261047758808806490895441)
  ·
    refine ⟨12195785819106604868171581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16261047758808806490895441 12195785819106604868171581)
    ·
      refine ⟨4573419682164976825564343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12195785819106604868171581 4573419682164976825564343)
      ·
        refine ⟨6860129523247465238346515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4573419682164976825564343 6860129523247465238346515)
        ·
          refine ⟨10290194284871197857519773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6860129523247465238346515 10290194284871197857519773)
          ·
            refine ⟨3858822856826699196569915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10290194284871197857519773 3858822856826699196569915)
            ·
              refine ⟨5788234285240048794854873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858822856826699196569915 5788234285240048794854873)
              ·
                refine ⟨4341175713930036596141155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5788234285240048794854873 4341175713930036596141155)
                ·
                  refine ⟨6511763570895054894211733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4341175713930036596141155 6511763570895054894211733)
                  ·
                    refine ⟨305238917385705698166175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6511763570895054894211733 305238917385705698166175)
                    ·
                      rfl

theorem cell22_891676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_891676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891676 prefixEnd_891676 := by exact prefixLift 891676
  have htrace : WordTrace (prefixWord ++ tailWord_891676) baseStart_891676 baseEnd_891676 := by
    simpa [prefixWord, tailWord_891676, baseEnd_891676] using wordTrace_append hprefix tailTrace_891676
  have hstable : (prefixWord ++ tailWord_891676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891676).length < 2 ^ (prefixWord ++ tailWord_891676).sum := by decide
  have hdescent : baseEnd_891676 < baseStart_891676 := by decide
  rcases family_descends (prefixWord ++ tailWord_891676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891710 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_891710 : Nat := 118140960795 + 891710 * 2 ^ 59
def prefixEnd_891710 : Nat := 4983230072969 + 3 ^ 40 * 891710 * 2
def baseEnd_891710 : Nat := 305250556280540942816071

theorem tailTrace_891710 : CollatzResearch.WordTrace tailWord_891710 prefixEnd_891710 305250556280540942816071 := by
  unfold tailWord_891710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4065416949936804598566073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21682223732996291192352389 4065416949936804598566073)
  ·
    refine ⟨3049062712452603448924555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4065416949936804598566073 3049062712452603448924555)
    ·
      refine ⟨4573594068678905173386833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3049062712452603448924555 4573594068678905173386833)
      ·
        refine ⟨3430195551509178880040125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4573594068678905173386833 3430195551509178880040125)
        ·
          refine ⟨1286323331815942080015047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3430195551509178880040125 1286323331815942080015047)
          ·
            refine ⟨1929484997723913120022571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286323331815942080015047 1929484997723913120022571)
            ·
              refine ⟨2894227496585869680033857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929484997723913120022571 2894227496585869680033857)
              ·
                refine ⟨2170670622439402260025393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2894227496585869680033857 2170670622439402260025393)
                ·
                  refine ⟨1628002966829551695019045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2170670622439402260025393 1628002966829551695019045)
                  ·
                    refine ⟨305250556280540942816071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1628002966829551695019045 305250556280540942816071)
                    ·
                      rfl

theorem cell22_891710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_891710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891710 prefixEnd_891710 := by exact prefixLift 891710
  have htrace : WordTrace (prefixWord ++ tailWord_891710) baseStart_891710 baseEnd_891710 := by
    simpa [prefixWord, tailWord_891710, baseEnd_891710] using wordTrace_append hprefix tailTrace_891710
  have hstable : (prefixWord ++ tailWord_891710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891710).length < 2 ^ (prefixWord ++ tailWord_891710).sum := by decide
  have hdescent : baseEnd_891710 < baseStart_891710 := by decide
  rcases family_descends (prefixWord ++ tailWord_891710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891725 : List Nat := [1, 6, 1, 2, 2, 1, 2, 7]
def baseStart_891725 : Nat := 118140960795 + 891725 * 2 ^ 59
def prefixEnd_891725 : Nat := 4983230072969 + 3 ^ 40 * 891725 * 2
def baseEnd_891725 : Nat := 33917299009676211521225

theorem tailTrace_891725 : CollatzResearch.WordTrace tailWord_891725 prefixEnd_891725 33917299009676211521225 := by
  unfold tailWord_891725
  simp only [CollatzResearch.WordTrace]
  refine ⟨32523882694440094350324629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21682588462960062900216419 32523882694440094350324629)
  ·
    refine ⟨1524557001301879422671467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32523882694440094350324629 1524557001301879422671467)
    ·
      refine ⟨2286835501952819134007201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524557001301879422671467 2286835501952819134007201)
      ·
        refine ⟨1715126626464614350505401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2286835501952819134007201 1715126626464614350505401)
        ·
          refine ⟨1286344969848460762879051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1715126626464614350505401 1286344969848460762879051)
          ·
            refine ⟨1929517454772691144318577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286344969848460762879051 1929517454772691144318577)
            ·
              refine ⟨1447138091079518358238933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929517454772691144318577 1447138091079518358238933)
              ·
                refine ⟨33917299009676211521225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1447138091079518358238933 33917299009676211521225)
                ·
                  rfl

theorem cell22_891725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 7].length) (baseStart_891725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891725 prefixEnd_891725 := by exact prefixLift 891725
  have htrace : WordTrace (prefixWord ++ tailWord_891725) baseStart_891725 baseEnd_891725 := by
    simpa [prefixWord, tailWord_891725, baseEnd_891725] using wordTrace_append hprefix tailTrace_891725
  have hstable : (prefixWord ++ tailWord_891725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891725).length < 2 ^ (prefixWord ++ tailWord_891725).sum := by decide
  have hdescent : baseEnd_891725 < baseStart_891725 := by decide
  rcases family_descends (prefixWord ++ tailWord_891725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891729 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 2, 3]
def baseStart_891729 : Nat := 118140960795 + 891729 * 2 ^ 59
def prefixEnd_891729 : Nat := 4983230072969 + 3 ^ 40 * 891729 * 2
def baseEnd_891729 : Nat := 305257060368831226591013

theorem tailTrace_891729 : CollatzResearch.WordTrace tailWord_891729 prefixEnd_891729 305257060368831226591013 := by
  unfold tailWord_891729
  simp only [CollatzResearch.WordTrace]
  refine ⟨32524028586425603033470241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21682685724283735355646827 32524028586425603033470241)
  ·
    refine ⟨24393021439819202275102681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32524028586425603033470241 24393021439819202275102681)
    ·
      refine ⟨18294766079864401706327011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24393021439819202275102681 18294766079864401706327011)
      ·
        refine ⟨27442149119796602559490517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18294766079864401706327011 27442149119796602559490517)
        ·
          refine ⟨643175369995232872488059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27442149119796602559490517 643175369995232872488059)
          ·
            refine ⟨964763054992849308732089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643175369995232872488059 964763054992849308732089)
            ·
              refine ⟨723572291244636981549067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964763054992849308732089 723572291244636981549067)
              ·
                refine ⟨1085358436866955472323601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723572291244636981549067 1085358436866955472323601)
                ·
                  refine ⟨814018827650216604242701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1085358436866955472323601 814018827650216604242701)
                  ·
                    refine ⟨305257060368831226591013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814018827650216604242701 305257060368831226591013)
                    ·
                      rfl

theorem cell22_891729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_891729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891729 prefixEnd_891729 := by exact prefixLift 891729
  have htrace : WordTrace (prefixWord ++ tailWord_891729) baseStart_891729 baseEnd_891729 := by
    simpa [prefixWord, tailWord_891729, baseEnd_891729] using wordTrace_append hprefix tailTrace_891729
  have hstable : (prefixWord ++ tailWord_891729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891729).length < 2 ^ (prefixWord ++ tailWord_891729).sum := by decide
  have hdescent : baseEnd_891729 < baseStart_891729 := by decide
  rcases family_descends (prefixWord ++ tailWord_891729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891783 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 3, 4]
def baseStart_891783 : Nat := 118140960795 + 891783 * 2 ^ 59
def prefixEnd_891783 : Nat := 4983230072969 + 3 ^ 40 * 891783 * 2
def baseEnd_891783 : Nat := 305275545672393085740847

theorem tailTrace_891783 : CollatzResearch.WordTrace tailWord_891783 prefixEnd_891783 305275545672393085740847 := by
  unfold tailWord_891783
  simp only [CollatzResearch.WordTrace]
  refine ⟨32525998128229970255936003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21683998752153313503957335 32525998128229970255936003)
  ·
    refine ⟨48788997192344955383904005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32525998128229970255936003 48788997192344955383904005)
    ·
      refine ⟨9147936973564679134482001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48788997192344955383904005 9147936973564679134482001)
      ·
        refine ⟨6860952730173509350861501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9147936973564679134482001 6860952730173509350861501)
        ·
          refine ⟨2572857273815066006573063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6860952730173509350861501 2572857273815066006573063)
          ·
            refine ⟨3859285910722599009859595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572857273815066006573063 3859285910722599009859595)
            ·
              refine ⟨5788928866083898514789393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859285910722599009859595 5788928866083898514789393)
              ·
                refine ⟨4341696649562923886092045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5788928866083898514789393 4341696649562923886092045)
                ·
                  refine ⟨1628136243586096457284517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4341696649562923886092045 1628136243586096457284517)
                  ·
                    refine ⟨305275545672393085740847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1628136243586096457284517 305275545672393085740847)
                    ·
                      rfl

theorem cell22_891783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_891783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891783 prefixEnd_891783 := by exact prefixLift 891783
  have htrace : WordTrace (prefixWord ++ tailWord_891783) baseStart_891783 baseEnd_891783 := by
    simpa [prefixWord, tailWord_891783, baseEnd_891783] using wordTrace_append hprefix tailTrace_891783
  have hstable : (prefixWord ++ tailWord_891783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891783).length < 2 ^ (prefixWord ++ tailWord_891783).sum := by decide
  have hdescent : baseEnd_891783 < baseStart_891783 := by decide
  rcases family_descends (prefixWord ++ tailWord_891783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891860 : List Nat := [2, 4, 1, 2, 1, 2, 4, 6]
def baseStart_891860 : Nat := 118140960795 + 891860 * 2 ^ 59
def prefixEnd_891860 : Nat := 4983230072969 + 3 ^ 40 * 891860 * 2
def baseEnd_891860 : Nat := 33922433816221172396179

theorem tailTrace_891860 : CollatzResearch.WordTrace tailWord_891860 prefixEnd_891860 33922433816221172396179 := by
  unfold tailWord_891860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16264403274475506203244517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21685871032634008270992689 16264403274475506203244517)
  ·
    refine ⟨3049575613964157413108347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16264403274475506203244517 3049575613964157413108347)
    ·
      refine ⟨4574363420946236119662521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3049575613964157413108347 4574363420946236119662521)
      ·
        refine ⟨3430772565709677089746891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4574363420946236119662521 3430772565709677089746891)
        ·
          refine ⟨5146158848564515634620337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3430772565709677089746891 5146158848564515634620337)
          ·
            refine ⟨3859619136423386725965253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5146158848564515634620337 3859619136423386725965253)
            ·
              refine ⟨723678588079385011118485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3859619136423386725965253 723678588079385011118485)
              ·
                refine ⟨33922433816221172396179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 723678588079385011118485 33922433816221172396179)
                ·
                  rfl

theorem cell22_891860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 6].length) (baseStart_891860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891860 prefixEnd_891860 := by exact prefixLift 891860
  have htrace : WordTrace (prefixWord ++ tailWord_891860) baseStart_891860 baseEnd_891860 := by
    simpa [prefixWord, tailWord_891860, baseEnd_891860] using wordTrace_append hprefix tailTrace_891860
  have hstable : (prefixWord ++ tailWord_891860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891860).length < 2 ^ (prefixWord ++ tailWord_891860).sum := by decide
  have hdescent : baseEnd_891860 < baseStart_891860 := by decide
  rcases family_descends (prefixWord ++ tailWord_891860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891877 : List Nat := [1, 3, 1, 6, 2, 1, 8]
def baseStart_891877 : Nat := 118140960795 + 891877 * 2 ^ 59
def prefixEnd_891877 : Nat := 4983230072969 + 3 ^ 40 * 891877 * 2
def baseEnd_891877 : Nat := 11307693473829932366317

theorem tailTrace_891877 : CollatzResearch.WordTrace tailWord_891877 prefixEnd_891877 11307693473829932366317 := by
  unfold tailWord_891877
  simp only [CollatzResearch.WordTrace]
  refine ⟨32529426589889424309857885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21686284393259616206571923 32529426589889424309857885)
  ·
    refine ⟨12198534971208534116196707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32529426589889424309857885 12198534971208534116196707)
    ·
      refine ⟨18297802456812801174295061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12198534971208534116196707 18297802456812801174295061)
      ·
        refine ⟨857709490163100055045081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18297802456812801174295061 857709490163100055045081)
        ·
          refine ⟨643282117622325041283811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857709490163100055045081 643282117622325041283811)
          ·
            refine ⟨964923176433487561925717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643282117622325041283811 964923176433487561925717)
            ·
              refine ⟨11307693473829932366317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 964923176433487561925717 11307693473829932366317)
              ·
                rfl

theorem cell22_891877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 8].length) (baseStart_891877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891877 prefixEnd_891877 := by exact prefixLift 891877
  have htrace : WordTrace (prefixWord ++ tailWord_891877) baseStart_891877 baseEnd_891877 := by
    simpa [prefixWord, tailWord_891877, baseEnd_891877] using wordTrace_append hprefix tailTrace_891877
  have hstable : (prefixWord ++ tailWord_891877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891877).length < 2 ^ (prefixWord ++ tailWord_891877).sum := by decide
  have hdescent : baseEnd_891877 < baseStart_891877 := by decide
  rcases family_descends (prefixWord ++ tailWord_891877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891888 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 5]
def baseStart_891888 : Nat := 118140960795 + 891888 * 2 ^ 59
def prefixEnd_891888 : Nat := 4983230072969 + 3 ^ 40 * 891888 * 2
def baseEnd_891888 : Nat := 101770496439402603955175

theorem tailTrace_891888 : CollatzResearch.WordTrace tailWord_891888 prefixEnd_891888 101770496439402603955175 := by
  unfold tailWord_891888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16264913896424786594254159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21686551861899715459005545 16264913896424786594254159)
  ·
    refine ⟨24397370844637179891381239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16264913896424786594254159 24397370844637179891381239)
    ·
      refine ⟨36596056266955769837071859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24397370844637179891381239 36596056266955769837071859)
      ·
        refine ⟨54894084400433654755607789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36596056266955769837071859 54894084400433654755607789)
        ·
          refine ⟨20585281650162620533352921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54894084400433654755607789 20585281650162620533352921)
          ·
            refine ⟨15438961237621965400014691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20585281650162620533352921 15438961237621965400014691)
            ·
              refine ⟨23158441856432948100022037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15438961237621965400014691 23158441856432948100022037)
              ·
                refine ⟨1085551962020294442188533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23158441856432948100022037 1085551962020294442188533)
                ·
                  refine ⟨101770496439402603955175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1085551962020294442188533 101770496439402603955175)
                  ·
                    rfl

theorem cell22_891888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_891888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891888 prefixEnd_891888 := by exact prefixLift 891888
  have htrace : WordTrace (prefixWord ++ tailWord_891888) baseStart_891888 baseEnd_891888 := by
    simpa [prefixWord, tailWord_891888, baseEnd_891888] using wordTrace_append hprefix tailTrace_891888
  have hstable : (prefixWord ++ tailWord_891888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891888).length < 2 ^ (prefixWord ++ tailWord_891888).sum := by decide
  have hdescent : baseEnd_891888 < baseStart_891888 := by decide
  rcases family_descends (prefixWord ++ tailWord_891888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891905 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 5]
def baseStart_891905 : Nat := 118140960795 + 891905 * 2 ^ 59
def prefixEnd_891905 : Nat := 4983230072969 + 3 ^ 40 * 891905 * 2
def baseEnd_891905 : Nat := 101772436255208478063491

theorem tailTrace_891905 : CollatzResearch.WordTrace tailWord_891905 prefixEnd_891905 101772436255208478063491 := by
  unfold tailWord_891905
  simp only [CollatzResearch.WordTrace]
  refine ⟨32530447833787985091877169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21686965222525323394584779 32530447833787985091877169)
  ·
    refine ⟨24397835875340988818907877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32530447833787985091877169 24397835875340988818907877)
    ·
      refine ⟨4574594226626435403545227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24397835875340988818907877 4574594226626435403545227)
      ·
        refine ⟨6861891339939653105317841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4574594226626435403545227 6861891339939653105317841)
        ·
          refine ⟨5146418504954739828988381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6861891339939653105317841 5146418504954739828988381)
          ·
            refine ⟨1929906939358027435870643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5146418504954739828988381 1929906939358027435870643)
            ·
              refine ⟨2894860409037041153805965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1929906939358027435870643 2894860409037041153805965)
              ·
                refine ⟨1085572653388890432677237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2894860409037041153805965 1085572653388890432677237)
                ·
                  refine ⟨101772436255208478063491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1085572653388890432677237 101772436255208478063491)
                  ·
                    rfl

theorem cell22_891905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_891905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891905 prefixEnd_891905 := by exact prefixLift 891905
  have htrace : WordTrace (prefixWord ++ tailWord_891905) baseStart_891905 baseEnd_891905 := by
    simpa [prefixWord, tailWord_891905, baseEnd_891905] using wordTrace_append hprefix tailTrace_891905
  have hstable : (prefixWord ++ tailWord_891905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891905).length < 2 ^ (prefixWord ++ tailWord_891905).sum := by decide
  have hdescent : baseEnd_891905 < baseStart_891905 := by decide
  rcases family_descends (prefixWord ++ tailWord_891905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891943 : List Nat := [1, 1, 7, 1, 1, 3, 2, 2, 1, 3]
def baseStart_891943 : Nat := 118140960795 + 891943 * 2 ^ 59
def prefixEnd_891943 : Nat := 4983230072969 + 3 ^ 40 * 891943 * 2
def baseEnd_891943 : Nat := 305330316942206001740357

theorem tailTrace_891943 : CollatzResearch.WordTrace tailWord_891943 prefixEnd_891943 305330316942206001740357 := by
  unfold tailWord_891943
  simp only [CollatzResearch.WordTrace]
  refine ⟨32531833807650317581760483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21687889205100211721173655 32531833807650317581760483)
  ·
    refine ⟨48797750711475476372640725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32531833807650317581760483 48797750711475476372640725)
    ·
      refine ⟨1143697282300206477483767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 48797750711475476372640725 1143697282300206477483767)
      ·
        refine ⟨1715545923450309716225651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143697282300206477483767 1715545923450309716225651)
        ·
          refine ⟨2573318885175464574338477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715545923450309716225651 2573318885175464574338477)
          ·
            refine ⟨964994581940799215376929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2573318885175464574338477 964994581940799215376929)
            ·
              refine ⟨723745936455599411532697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964994581940799215376929 723745936455599411532697)
              ·
                refine ⟨542809452341699558649523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723745936455599411532697 542809452341699558649523)
                ·
                  refine ⟨814214178512549337974285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542809452341699558649523 814214178512549337974285)
                  ·
                    refine ⟨305330316942206001740357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814214178512549337974285 305330316942206001740357)
                    ·
                      rfl

theorem cell22_891943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_891943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891943 prefixEnd_891943 := by exact prefixLift 891943
  have htrace : WordTrace (prefixWord ++ tailWord_891943) baseStart_891943 baseEnd_891943 := by
    simpa [prefixWord, tailWord_891943, baseEnd_891943] using wordTrace_append hprefix tailTrace_891943
  have hstable : (prefixWord ++ tailWord_891943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891943).length < 2 ^ (prefixWord ++ tailWord_891943).sum := by decide
  have hdescent : baseEnd_891943 < baseStart_891943 := by decide
  rcases family_descends (prefixWord ++ tailWord_891943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891948 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_891948 : Nat := 118140960795 + 891948 * 2 ^ 59
def prefixEnd_891948 : Nat := 4983230072969 + 3 ^ 40 * 891948 * 2
def baseEnd_891948 : Nat := 305332028544387655365341

theorem tailTrace_891948 : CollatzResearch.WordTrace tailWord_891948 prefixEnd_891948 305332028544387655365341 := by
  unfold tailWord_891948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16266008086316101717846249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21688010781754802290461665 16266008086316101717846249)
  ·
    refine ⟨12199506064737076288384687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16266008086316101717846249 12199506064737076288384687)
    ·
      refine ⟨18299259097105614432577031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12199506064737076288384687 18299259097105614432577031)
      ·
        refine ⟨27448888645658421648865547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18299259097105614432577031 27448888645658421648865547)
        ·
          refine ⟨41173332968487632473298321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27448888645658421648865547 41173332968487632473298321)
          ·
            refine ⟨30879999726365724354973741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41173332968487632473298321 30879999726365724354973741)
            ·
              refine ⟨11579999897387146633115153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30879999726365724354973741 11579999897387146633115153)
              ·
                refine ⟨8684999923040359974836365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11579999897387146633115153 8684999923040359974836365)
                ·
                  refine ⟨3256874971140134990563637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8684999923040359974836365 3256874971140134990563637)
                  ·
                    refine ⟨305332028544387655365341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3256874971140134990563637 305332028544387655365341)
                    ·
                      rfl

theorem cell22_891948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_891948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891948 prefixEnd_891948 := by exact prefixLift 891948
  have htrace : WordTrace (prefixWord ++ tailWord_891948) baseStart_891948 baseEnd_891948 := by
    simpa [prefixWord, tailWord_891948, baseEnd_891948] using wordTrace_append hprefix tailTrace_891948
  have hstable : (prefixWord ++ tailWord_891948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891948).length < 2 ^ (prefixWord ++ tailWord_891948).sum := by decide
  have hdescent : baseEnd_891948 < baseStart_891948 := by decide
  rcases family_descends (prefixWord ++ tailWord_891948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891950 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_891950 : Nat := 118140960795 + 891950 * 2 ^ 59
def prefixEnd_891950 : Nat := 4983230072969 + 3 ^ 40 * 891950 * 2
def baseEnd_891950 : Nat := 101777571061753438938445

theorem tailTrace_891950 : CollatzResearch.WordTrace tailWord_891950 prefixEnd_891950 101777571061753438938445 := by
  unfold tailWord_891950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4066511139828119722158163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21688059412416638518176869 4066511139828119722158163)
  ·
    refine ⟨6099766709742179583237245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4066511139828119722158163 6099766709742179583237245)
    ·
      refine ⟨2287412516153317343713967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6099766709742179583237245 2287412516153317343713967)
      ·
        refine ⟨3431118774229976015570951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2287412516153317343713967 3431118774229976015570951)
        ·
          refine ⟨5146678161344964023356427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431118774229976015570951 5146678161344964023356427)
          ·
            refine ⟨7720017242017446035034641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146678161344964023356427 7720017242017446035034641)
            ·
              refine ⟨5790012931513084526275981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7720017242017446035034641 5790012931513084526275981)
              ·
                refine ⟨2171254849317406697353493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5790012931513084526275981 2171254849317406697353493)
                ·
                  refine ⟨101777571061753438938445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2171254849317406697353493 101777571061753438938445)
                  ·
                    rfl

theorem cell22_891950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_891950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891950 prefixEnd_891950 := by exact prefixLift 891950
  have htrace : WordTrace (prefixWord ++ tailWord_891950) baseStart_891950 baseEnd_891950 := by
    simpa [prefixWord, tailWord_891950, baseEnd_891950] using wordTrace_append hprefix tailTrace_891950
  have hstable : (prefixWord ++ tailWord_891950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891950).length < 2 ^ (prefixWord ++ tailWord_891950).sum := by decide
  have hdescent : baseEnd_891950 < baseStart_891950 := by decide
  rcases family_descends (prefixWord ++ tailWord_891950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891965 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_891965 : Nat := 118140960795 + 891965 * 2 ^ 59
def prefixEnd_891965 : Nat := 4983230072969 + 3 ^ 40 * 891965 * 2
def baseEnd_891965 : Nat := 305337847991805277690289

theorem tailTrace_891965 : CollatzResearch.WordTrace tailWord_891965 prefixEnd_891965 305337847991805277690289 := by
  unfold tailWord_891965
  simp only [CollatzResearch.WordTrace]
  refine ⟨32532636213570615339061349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21688424142380410226040899 32532636213570615339061349)
  ·
    refine ⟨6099869290044490376074003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32532636213570615339061349 6099869290044490376074003)
    ·
      refine ⟨9149803935066735564111005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6099869290044490376074003 9149803935066735564111005)
      ·
        refine ⟨3431176475650025836541627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9149803935066735564111005 3431176475650025836541627)
        ·
          refine ⟨5146764713475038754812441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431176475650025836541627 5146764713475038754812441)
          ·
            refine ⟨3860073535106279066109331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5146764713475038754812441 3860073535106279066109331)
            ·
              refine ⟨5790110302659418599163997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3860073535106279066109331 5790110302659418599163997)
              ·
                refine ⟨2171291363497281974686499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5790110302659418599163997 2171291363497281974686499)
                ·
                  refine ⟨3256937045245922962029749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171291363497281974686499 3256937045245922962029749)
                  ·
                    refine ⟨305337847991805277690289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3256937045245922962029749 305337847991805277690289)
                    ·
                      rfl

theorem cell22_891965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_891965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891965 prefixEnd_891965 := by exact prefixLift 891965
  have htrace : WordTrace (prefixWord ++ tailWord_891965) baseStart_891965 baseEnd_891965 := by
    simpa [prefixWord, tailWord_891965, baseEnd_891965] using wordTrace_append hprefix tailTrace_891965
  have hstable : (prefixWord ++ tailWord_891965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891965).length < 2 ^ (prefixWord ++ tailWord_891965).sum := by decide
  have hdescent : baseEnd_891965 < baseStart_891965 := by decide
  rcases family_descends (prefixWord ++ tailWord_891965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_891978 : List Nat := [3, 1, 2, 1, 1, 2, 2, 10]
def baseStart_891978 : Nat := 118140960795 + 891978 * 2 ^ 59
def prefixEnd_891978 : Nat := 4983230072969 + 3 ^ 40 * 891978 * 2
def baseEnd_891978 : Nat := 33926922017497508568361

theorem tailTrace_891978 : CollatzResearch.WordTrace tailWord_891978 prefixEnd_891978 33926922017497508568361 := by
  unfold tailWord_891978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133277590630879639821147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21688740241682345706189725 8133277590630879639821147)
  ·
    refine ⟨12199916385946319459731721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8133277590630879639821147 12199916385946319459731721)
    ·
      refine ⟨9149937289459739594798791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12199916385946319459731721 9149937289459739594798791)
      ·
        refine ⟨13724905934189609392198187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9149937289459739594798791 13724905934189609392198187)
        ·
          refine ⟨20587358901284414088297281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13724905934189609392198187 20587358901284414088297281)
          ·
            refine ⟨15440519175963310566222961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20587358901284414088297281 15440519175963310566222961)
            ·
              refine ⟨11580389381972482924667221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15440519175963310566222961 11580389381972482924667221)
              ·
                refine ⟨33926922017497508568361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11580389381972482924667221 33926922017497508568361)
                ·
                  rfl

theorem cell22_891978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_891978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_891978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_891978 prefixEnd_891978 := by exact prefixLift 891978
  have htrace : WordTrace (prefixWord ++ tailWord_891978) baseStart_891978 baseEnd_891978 := by
    simpa [prefixWord, tailWord_891978, baseEnd_891978] using wordTrace_append hprefix tailTrace_891978
  have hstable : (prefixWord ++ tailWord_891978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_891978).length < 2 ^ (prefixWord ++ tailWord_891978).sum := by decide
  have hdescent : baseEnd_891978 < baseStart_891978 := by decide
  rcases family_descends (prefixWord ++ tailWord_891978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892061 : List Nat := [1, 4, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_892061 : Nat := 118140960795 + 892061 * 2 ^ 59
def prefixEnd_892061 : Nat := 4983230072969 + 3 ^ 40 * 892061 * 2
def baseEnd_892061 : Nat := 305370710753693027289995

theorem tailTrace_892061 : CollatzResearch.WordTrace tailWord_892061 prefixEnd_892061 305370710753693027289995 := by
  unfold tailWord_892061
  simp only [CollatzResearch.WordTrace]
  refine ⟨32536137621222823734556037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21690758414148549156370691 32536137621222823734556037)
  ·
    refine ⟨6100525803979279450229257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32536137621222823734556037 6100525803979279450229257)
    ·
      refine ⟨4575394352984459587671943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6100525803979279450229257 4575394352984459587671943)
      ·
        refine ⟨6863091529476689381507915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575394352984459587671943 6863091529476689381507915)
        ·
          refine ⟨10294637294215034072261873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863091529476689381507915 10294637294215034072261873)
          ·
            refine ⟨7720977970661275554196405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10294637294215034072261873 7720977970661275554196405)
            ·
              refine ⟨723841684749494583205913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7720977970661275554196405 723841684749494583205913)
              ·
                refine ⟨542881263562120937404435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723841684749494583205913 542881263562120937404435)
                ·
                  refine ⟨814321895343181406106653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542881263562120937404435 814321895343181406106653)
                  ·
                    refine ⟨305370710753693027289995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814321895343181406106653 305370710753693027289995)
                    ·
                      rfl

theorem cell22_892061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_892061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892061 prefixEnd_892061 := by exact prefixLift 892061
  have htrace : WordTrace (prefixWord ++ tailWord_892061) baseStart_892061 baseEnd_892061 := by
    simpa [prefixWord, tailWord_892061, baseEnd_892061] using wordTrace_append hprefix tailTrace_892061
  have hstable : (prefixWord ++ tailWord_892061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892061).length < 2 ^ (prefixWord ++ tailWord_892061).sum := by decide
  have hdescent : baseEnd_892061 < baseStart_892061 := by decide
  rcases family_descends (prefixWord ++ tailWord_892061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892074 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_892074 : Nat := 118140960795 + 892074 * 2 ^ 59
def prefixEnd_892074 : Nat := 4983230072969 + 3 ^ 40 * 892074 * 2
def baseEnd_892074 : Nat := 101791720306455108904985

theorem tailTrace_892074 : CollatzResearch.WordTrace tailWord_892074 prefixEnd_892074 101791720306455108904985 := by
  unfold tailWord_892074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8134152942543931738694819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21691074513450484636519517 8134152942543931738694819)
  ·
    refine ⟨12201229413815897608042229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8134152942543931738694819 12201229413815897608042229)
    ·
      refine ⟨1143865257545240400753959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12201229413815897608042229 1143865257545240400753959)
      ·
        refine ⟨1715797886317860601130939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143865257545240400753959 1715797886317860601130939)
        ·
          refine ⟨2573696829476790901696409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715797886317860601130939 2573696829476790901696409)
          ·
            refine ⟨1930272622107593176272307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2573696829476790901696409 1930272622107593176272307)
            ·
              refine ⟨2895408933161389764408461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930272622107593176272307 2895408933161389764408461)
              ·
                refine ⟨1085778349935521161653173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2895408933161389764408461 1085778349935521161653173)
                ·
                  refine ⟨101791720306455108904985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1085778349935521161653173 101791720306455108904985)
                  ·
                    rfl

theorem cell22_892074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_892074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892074 prefixEnd_892074 := by exact prefixLift 892074
  have htrace : WordTrace (prefixWord ++ tailWord_892074) baseStart_892074 baseEnd_892074 := by
    simpa [prefixWord, tailWord_892074, baseEnd_892074] using wordTrace_append hprefix tailTrace_892074
  have hstable : (prefixWord ++ tailWord_892074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892074).length < 2 ^ (prefixWord ++ tailWord_892074).sum := by decide
  have hdescent : baseEnd_892074 < baseStart_892074 := by decide
  rcases family_descends (prefixWord ++ tailWord_892074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892119 : List Nat := [1, 1, 3, 2, 1, 2, 6, 2, 4]
def baseStart_892119 : Nat := 118140960795 + 892119 * 2 ^ 59
def prefixEnd_892119 : Nat := 4983230072969 + 3 ^ 40 * 892119 * 2
def baseEnd_892119 : Nat := 101796855113000069779939

theorem tailTrace_892119 : CollatzResearch.WordTrace tailWord_892119 prefixEnd_892119 101796855113000069779939 := by
  unfold tailWord_892119
  simp only [CollatzResearch.WordTrace]
  refine ⟨32538253055012699640167411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21692168703341799760111607 32538253055012699640167411)
  ·
    refine ⟨48807379582519049460251117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32538253055012699640167411 48807379582519049460251117)
    ·
      refine ⟨18302767343444643547594169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48807379582519049460251117 18302767343444643547594169)
      ·
        refine ⟨13727075507583482660695627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18302767343444643547594169 13727075507583482660695627)
        ·
          refine ⟨20590613261375223991043441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13727075507583482660695627 20590613261375223991043441)
          ·
            refine ⟨15442959946031417993282581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20590613261375223991043441 15442959946031417993282581)
            ·
              refine ⟨723888747470222718435121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15442959946031417993282581 723888747470222718435121)
              ·
                refine ⟨542916560602667038826341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723888747470222718435121 542916560602667038826341)
                ·
                  refine ⟨101796855113000069779939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 542916560602667038826341 101796855113000069779939)
                  ·
                    rfl

theorem cell22_892119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 4].length) (baseStart_892119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892119 prefixEnd_892119 := by exact prefixLift 892119
  have htrace : WordTrace (prefixWord ++ tailWord_892119) baseStart_892119 baseEnd_892119 := by
    simpa [prefixWord, tailWord_892119, baseEnd_892119] using wordTrace_append hprefix tailTrace_892119
  have hstable : (prefixWord ++ tailWord_892119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892119).length < 2 ^ (prefixWord ++ tailWord_892119).sum := by decide
  have hdescent : baseEnd_892119 < baseStart_892119 := by decide
  rcases family_descends (prefixWord ++ tailWord_892119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892147 : List Nat := [1, 1, 1, 2, 2, 6, 3, 6]
def baseStart_892147 : Nat := 118140960795 + 892147 * 2 ^ 59
def prefixEnd_892147 : Nat := 4983230072969 + 3 ^ 40 * 892147 * 2
def baseEnd_892147 : Nat := 33933350034579718848859

theorem tailTrace_892147 : CollatzResearch.WordTrace tailWord_892147 prefixEnd_892147 33933350034579718848859 := by
  unfold tailWord_892147
  simp only [CollatzResearch.WordTrace]
  refine ⟨32539274298911260422186695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21692849532607506948124463 32539274298911260422186695)
  ·
    refine ⟨48808911448366890633280043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32539274298911260422186695 48808911448366890633280043)
    ·
      refine ⟨73213367172550335949920065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48808911448366890633280043 73213367172550335949920065)
      ·
        refine ⟨54910025379412751962440049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73213367172550335949920065 54910025379412751962440049)
        ·
          refine ⟨41182519034559563971830037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54910025379412751962440049 41182519034559563971830037)
          ·
            refine ⟨1930430579744979561179533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41182519034559563971830037 1930430579744979561179533)
            ·
              refine ⟨723911467404367335442325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1930430579744979561179533 723911467404367335442325)
              ·
                refine ⟨33933350034579718848859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 723911467404367335442325 33933350034579718848859)
                ·
                  rfl

theorem cell22_892147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 6].length) (baseStart_892147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892147 prefixEnd_892147 := by exact prefixLift 892147
  have htrace : WordTrace (prefixWord ++ tailWord_892147) baseStart_892147 baseEnd_892147 := by
    simpa [prefixWord, tailWord_892147, baseEnd_892147] using wordTrace_append hprefix tailTrace_892147
  have hstable : (prefixWord ++ tailWord_892147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892147).length < 2 ^ (prefixWord ++ tailWord_892147).sum := by decide
  have hdescent : baseEnd_892147 < baseStart_892147 := by decide
  rcases family_descends (prefixWord ++ tailWord_892147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892168 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 2, 3]
def baseStart_892168 : Nat := 118140960795 + 892168 * 2 ^ 59
def prefixEnd_892168 : Nat := 4983230072969 + 3 ^ 40 * 892168 * 2
def baseEnd_892168 : Nat := 305407339040380414864667

theorem tailTrace_892168 : CollatzResearch.WordTrace tailWord_892168 prefixEnd_892168 305407339040380414864667 := by
  unfold tailWord_892168
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270020115917590504350579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21693360154556787339134105 16270020115917590504350579)
  ·
    refine ⟨24405030173876385756525869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16270020115917590504350579 24405030173876385756525869)
    ·
      refine ⟨9151886315203644658697201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24405030173876385756525869 9151886315203644658697201)
      ·
        refine ⟨6863914736402733494022901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9151886315203644658697201 6863914736402733494022901)
        ·
          refine ⟨643492006537756265064647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6863914736402733494022901 643492006537756265064647)
          ·
            refine ⟨965238009806634397596971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643492006537756265064647 965238009806634397596971)
            ·
              refine ⟨1447857014709951596395457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965238009806634397596971 1447857014709951596395457)
              ·
                refine ⟨1085892761032463697296593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447857014709951596395457 1085892761032463697296593)
                ·
                  refine ⟨814419570774347772972445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1085892761032463697296593 814419570774347772972445)
                  ·
                    refine ⟨305407339040380414864667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814419570774347772972445 305407339040380414864667)
                    ·
                      rfl

theorem cell22_892168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_892168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892168 prefixEnd_892168 := by exact prefixLift 892168
  have htrace : WordTrace (prefixWord ++ tailWord_892168) baseStart_892168 baseEnd_892168 := by
    simpa [prefixWord, tailWord_892168, baseEnd_892168] using wordTrace_append hprefix tailTrace_892168
  have hstable : (prefixWord ++ tailWord_892168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892168).length < 2 ^ (prefixWord ++ tailWord_892168).sum := by decide
  have hdescent : baseEnd_892168 < baseStart_892168 := by decide
  rcases family_descends (prefixWord ++ tailWord_892168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892213 : List Nat := [1, 3, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_892213 : Nat := 118140960795 + 892213 * 2 ^ 59
def prefixEnd_892213 : Nat := 4983230072969 + 3 ^ 40 * 892213 * 2
def baseEnd_892213 : Nat := 305422743460015297489529

theorem tailTrace_892213 : CollatzResearch.WordTrace tailWord_892213 prefixEnd_892213 305422743460015297489529 := by
  unfold tailWord_892213
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541681516672153694089293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21694454344448102462726195 32541681516672153694089293)
  ·
    refine ⟨12203130568752057635283485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32541681516672153694089293 12203130568752057635283485)
    ·
      refine ⟨4576173963282021613231307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12203130568752057635283485 4576173963282021613231307)
      ·
        refine ⟨6864260944923032419846961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576173963282021613231307 6864260944923032419846961)
        ·
          refine ⟨5148195708692274314885221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6864260944923032419846961 5148195708692274314885221)
          ·
            refine ⟨965286695379801434040979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5148195708692274314885221 965286695379801434040979)
            ·
              refine ⟨1447930043069702151061469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965286695379801434040979 1447930043069702151061469)
              ·
                refine ⟨542973766151138306648051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1447930043069702151061469 542973766151138306648051)
                ·
                  refine ⟨814460649226707459972077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542973766151138306648051 814460649226707459972077)
                  ·
                    refine ⟨305422743460015297489529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814460649226707459972077 305422743460015297489529)
                    ·
                      rfl

theorem cell22_892213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_892213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892213 prefixEnd_892213 := by exact prefixLift 892213
  have htrace : WordTrace (prefixWord ++ tailWord_892213) baseStart_892213 baseEnd_892213 := by
    simpa [prefixWord, tailWord_892213, baseEnd_892213] using wordTrace_append hprefix tailTrace_892213
  have hstable : (prefixWord ++ tailWord_892213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892213).length < 2 ^ (prefixWord ++ tailWord_892213).sum := by decide
  have hdescent : baseEnd_892213 < baseStart_892213 := by decide
  rcases family_descends (prefixWord ++ tailWord_892213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892256 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 1, 4]
def baseStart_892256 : Nat := 118140960795 + 892256 * 2 ^ 59
def prefixEnd_892256 : Nat := 4983230072969 + 3 ^ 40 * 892256 * 2
def baseEnd_892256 : Nat := 305437463238777518664397

theorem tailTrace_892256 : CollatzResearch.WordTrace tailWord_892256 prefixEnd_892256 305437463238777518664397 := by
  unfold tailWord_892256
  simp only [CollatzResearch.WordTrace]
  refine ⟨16271624927758186018952311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21695499903677581358603081 16271624927758186018952311)
  ·
    refine ⟨24407437391637279028428467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16271624927758186018952311 24407437391637279028428467)
    ·
      refine ⟨36611156087455918542642701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24407437391637279028428467 36611156087455918542642701)
      ·
        refine ⟨13729183532795969453491013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36611156087455918542642701 13729183532795969453491013)
        ·
          refine ⟨2574221912399244272529565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13729183532795969453491013 2574221912399244272529565)
          ·
            refine ⟨965333217149716602198587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2574221912399244272529565 965333217149716602198587)
            ·
              refine ⟨1447999825724574903297881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965333217149716602198587 1447999825724574903297881)
              ·
                refine ⟨1085999869293431177473411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447999825724574903297881 1085999869293431177473411)
                ·
                  refine ⟨1628999803940146766210117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085999869293431177473411 1628999803940146766210117)
                  ·
                    refine ⟨305437463238777518664397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1628999803940146766210117 305437463238777518664397)
                    ·
                      rfl

theorem cell22_892256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_892256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892256 prefixEnd_892256 := by exact prefixLift 892256
  have htrace : WordTrace (prefixWord ++ tailWord_892256) baseStart_892256 baseEnd_892256 := by
    simpa [prefixWord, tailWord_892256, baseEnd_892256] using wordTrace_append hprefix tailTrace_892256
  have hstable : (prefixWord ++ tailWord_892256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892256).length < 2 ^ (prefixWord ++ tailWord_892256).sum := by decide
  have hdescent : baseEnd_892256 < baseStart_892256 := by decide
  rcases family_descends (prefixWord ++ tailWord_892256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892269 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_892269 : Nat := 118140960795 + 892269 * 2 ^ 59
def prefixEnd_892269 : Nat := 4983230072969 + 3 ^ 40 * 892269 * 2
def baseEnd_892269 : Nat := 305441913404449818089357

theorem tailTrace_892269 : CollatzResearch.WordTrace tailWord_892269 prefixEnd_892269 305441913404449818089357 := by
  unfold tailWord_892269
  simp only [CollatzResearch.WordTrace]
  refine ⟨32543724004469275258127861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21695816002979516838751907 32543724004469275258127861)
  ·
    refine ⟨3050974125418994555449487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32543724004469275258127861 3050974125418994555449487)
    ·
      refine ⟨4576461188128491833174231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3050974125418994555449487 4576461188128491833174231)
      ·
        refine ⟨6864691782192737749761347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576461188128491833174231 6864691782192737749761347)
        ·
          refine ⟨10297037673289106624642021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864691782192737749761347 10297037673289106624642021)
          ·
            refine ⟨1930694563741707492120379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10297037673289106624642021 1930694563741707492120379)
            ·
              refine ⟨2896041845612561238180569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930694563741707492120379 2896041845612561238180569)
              ·
                refine ⟨2172031384209420928635427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2896041845612561238180569 2172031384209420928635427)
                ·
                  refine ⟨3258047076314131392953141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172031384209420928635427 3258047076314131392953141)
                  ·
                    refine ⟨305441913404449818089357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3258047076314131392953141 305441913404449818089357)
                    ·
                      rfl

theorem cell22_892269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_892269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892269 prefixEnd_892269 := by exact prefixLift 892269
  have htrace : WordTrace (prefixWord ++ tailWord_892269) baseStart_892269 baseEnd_892269 := by
    simpa [prefixWord, tailWord_892269, baseEnd_892269] using wordTrace_append hprefix tailTrace_892269
  have hstable : (prefixWord ++ tailWord_892269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892269).length < 2 ^ (prefixWord ++ tailWord_892269).sum := by decide
  have hdescent : baseEnd_892269 < baseStart_892269 := by decide
  rcases family_descends (prefixWord ++ tailWord_892269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892344 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 5]
def baseStart_892344 : Nat := 118140960795 + 892344 * 2 ^ 59
def prefixEnd_892344 : Nat := 4983230072969 + 3 ^ 40 * 892344 * 2
def baseEnd_892344 : Nat := 101822529145724874154709

theorem tailTrace_892344 : CollatzResearch.WordTrace tailWord_892344 prefixEnd_892344 101822529145724874154709 := by
  unfold tailWord_892344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273229739598781533554043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21697639652798375378072057 16273229739598781533554043)
  ·
    refine ⟨24409844609398172300331065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16273229739598781533554043 24409844609398172300331065)
    ·
      refine ⟨18307383457048629225248299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24409844609398172300331065 18307383457048629225248299)
      ·
        refine ⟨27461075185572943837872449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18307383457048629225248299 27461075185572943837872449)
        ·
          refine ⟨20595806389179707878404337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27461075185572943837872449 20595806389179707878404337)
          ·
            refine ⟨15446854791884780908803253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20595806389179707878404337 15446854791884780908803253)
            ·
              refine ⟨1448142636739198210200305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15446854791884780908803253 1448142636739198210200305)
              ·
                refine ⟨1086106977554398657650229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448142636739198210200305 1086106977554398657650229)
                ·
                  refine ⟨101822529145724874154709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1086106977554398657650229 101822529145724874154709)
                  ·
                    rfl

theorem cell22_892344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_892344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892344 prefixEnd_892344 := by exact prefixLift 892344
  have htrace : WordTrace (prefixWord ++ tailWord_892344) baseStart_892344 baseEnd_892344 := by
    simpa [prefixWord, tailWord_892344, baseEnd_892344] using wordTrace_append hprefix tailTrace_892344
  have hstable : (prefixWord ++ tailWord_892344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892344).length < 2 ^ (prefixWord ++ tailWord_892344).sum := by decide
  have hdescent : baseEnd_892344 < baseStart_892344 := by decide
  rcases family_descends (prefixWord ++ tailWord_892344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892348 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_892348 : Nat := 118140960795 + 892348 * 2 ^ 59
def prefixEnd_892348 : Nat := 4983230072969 + 3 ^ 40 * 892348 * 2
def baseEnd_892348 : Nat := 305468956718919945364115

theorem tailTrace_892348 : CollatzResearch.WordTrace tailWord_892348 prefixEnd_892348 305468956718919945364115 := by
  unfold tailWord_892348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273302685591535875126849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21697736914122047833502465 16273302685591535875126849)
  ·
    refine ⟨12204977014193651906345137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16273302685591535875126849 12204977014193651906345137)
    ·
      refine ⟨9153732760645238929758853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12204977014193651906345137 9153732760645238929758853)
      ·
        refine ⟨1716324892620982299329785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9153732760645238929758853 1716324892620982299329785)
        ·
          refine ⟨1287243669465736724497339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716324892620982299329785 1287243669465736724497339)
          ·
            refine ⟨1930865504198605086746009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287243669465736724497339 1930865504198605086746009)
            ·
              refine ⟨1448149128148953815059507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1930865504198605086746009 1448149128148953815059507)
              ·
                refine ⟨2172223692223430722589261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448149128148953815059507 2172223692223430722589261)
                ·
                  refine ⟨814583884583786520970973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2172223692223430722589261 814583884583786520970973)
                  ·
                    refine ⟨305468956718919945364115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814583884583786520970973 305468956718919945364115)
                    ·
                      rfl

theorem cell22_892348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_892348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892348 prefixEnd_892348 := by exact prefixLift 892348
  have htrace : WordTrace (prefixWord ++ tailWord_892348) baseStart_892348 baseEnd_892348 := by
    simpa [prefixWord, tailWord_892348, baseEnd_892348] using wordTrace_append hprefix tailTrace_892348
  have hstable : (prefixWord ++ tailWord_892348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892348).length < 2 ^ (prefixWord ++ tailWord_892348).sum := by decide
  have hdescent : baseEnd_892348 < baseStart_892348 := by decide
  rcases family_descends (prefixWord ++ tailWord_892348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892354 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_892354 : Nat := 118140960795 + 892354 * 2 ^ 59
def prefixEnd_892354 : Nat := 4983230072969 + 3 ^ 40 * 892354 * 2
def baseEnd_892354 : Nat := 305471010641537929714097

theorem tailTrace_892354 : CollatzResearch.WordTrace tailWord_892354 prefixEnd_892354 305471010641537929714097 := by
  unfold tailWord_892354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136706052290333693743029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21697882806107556516648077 8136706052290333693743029)
  ·
    refine ⟨762816192402218783788409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8136706052290333693743029 762816192402218783788409)
    ·
      refine ⟨572112144301664087841307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 762816192402218783788409 572112144301664087841307)
      ·
        refine ⟨858168216452496131761961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572112144301664087841307 858168216452496131761961)
        ·
          refine ⟨643626162339372098821471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858168216452496131761961 643626162339372098821471)
          ·
            refine ⟨965439243509058148232207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643626162339372098821471 965439243509058148232207)
            ·
              refine ⟨1448158865263587222348311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965439243509058148232207 1448158865263587222348311)
              ·
                refine ⟨2172238297895380833522467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448158865263587222348311 2172238297895380833522467)
                ·
                  refine ⟨3258357446843071250283701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172238297895380833522467 3258357446843071250283701)
                  ·
                    refine ⟨305471010641537929714097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3258357446843071250283701 305471010641537929714097)
                    ·
                      rfl

theorem cell22_892354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_892354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892354 prefixEnd_892354 := by exact prefixLift 892354
  have htrace : WordTrace (prefixWord ++ tailWord_892354) baseStart_892354 baseEnd_892354 := by
    simpa [prefixWord, tailWord_892354, baseEnd_892354] using wordTrace_append hprefix tailTrace_892354
  have hstable : (prefixWord ++ tailWord_892354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892354).length < 2 ^ (prefixWord ++ tailWord_892354).sum := by decide
  have hdescent : baseEnd_892354 < baseStart_892354 := by decide
  rcases family_descends (prefixWord ++ tailWord_892354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892391 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 1, 4]
def baseStart_892391 : Nat := 118140960795 + 892391 * 2 ^ 59
def prefixEnd_892391 : Nat := 4983230072969 + 3 ^ 40 * 892391 * 2
def baseEnd_892391 : Nat := 305483676497682166538983

theorem tailTrace_892391 : CollatzResearch.WordTrace tailWord_892391 prefixEnd_892391 305483676497682166538983 := by
  unfold tailWord_892391
  simp only [CollatzResearch.WordTrace]
  refine ⟨32548173710027290094069027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21698782473351526729379351 32548173710027290094069027)
  ·
    refine ⟨48822260565040935141103541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32548173710027290094069027 48822260565040935141103541)
    ·
      refine ⟨4577086927972587669478457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48822260565040935141103541 4577086927972587669478457)
      ·
        refine ⟨3432815195979440752108843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577086927972587669478457 3432815195979440752108843)
        ·
          refine ⟨5149222793969161128163265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432815195979440752108843 5149222793969161128163265)
          ·
            refine ⟨3861917095476870846122449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149222793969161128163265 3861917095476870846122449)
            ·
              refine ⟨2896437821607653134591837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861917095476870846122449 2896437821607653134591837)
              ·
                refine ⟨1086164183102869925471939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2896437821607653134591837 1086164183102869925471939)
                ·
                  refine ⟨1629246274654304888207909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086164183102869925471939 1629246274654304888207909)
                  ·
                    refine ⟨305483676497682166538983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1629246274654304888207909 305483676497682166538983)
                    ·
                      rfl

theorem cell22_892391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_892391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892391 prefixEnd_892391 := by exact prefixLift 892391
  have htrace : WordTrace (prefixWord ++ tailWord_892391) baseStart_892391 baseEnd_892391 := by
    simpa [prefixWord, tailWord_892391, baseEnd_892391] using wordTrace_append hprefix tailTrace_892391
  have hstable : (prefixWord ++ tailWord_892391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892391).length < 2 ^ (prefixWord ++ tailWord_892391).sum := by decide
  have hdescent : baseEnd_892391 < baseStart_892391 := by decide
  rcases family_descends (prefixWord ++ tailWord_892391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892406 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_892406 : Nat := 118140960795 + 892406 * 2 ^ 59
def prefixEnd_892406 : Nat := 4983230072969 + 3 ^ 40 * 892406 * 2
def baseEnd_892406 : Nat := 101829603768075709137979

theorem tailTrace_892406 : CollatzResearch.WordTrace tailWord_892406 prefixEnd_892406 101829603768075709137979 := by
  unfold tailWord_892406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034295050310809228491567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21699147203315298437243381 2034295050310809228491567)
  ·
    refine ⟨3051442575466213842737351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2034295050310809228491567 3051442575466213842737351)
    ·
      refine ⟨4577163863199320764106027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051442575466213842737351 4577163863199320764106027)
      ·
        refine ⟨6865745794798981146159041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577163863199320764106027 6865745794798981146159041)
        ·
          refine ⟨5149309346099235859619281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6865745794798981146159041 5149309346099235859619281)
          ·
            refine ⟨3861982009574426894714461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149309346099235859619281 3861982009574426894714461)
            ·
              refine ⟨1448243253590410085517923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3861982009574426894714461 1448243253590410085517923)
              ·
                refine ⟨2172364880385615128276885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448243253590410085517923 2172364880385615128276885)
                ·
                  refine ⟨101829603768075709137979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2172364880385615128276885 101829603768075709137979)
                  ·
                    rfl

theorem cell22_892406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_892406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892406 prefixEnd_892406 := by exact prefixLift 892406
  have htrace : WordTrace (prefixWord ++ tailWord_892406) baseStart_892406 baseEnd_892406 := by
    simpa [prefixWord, tailWord_892406, baseEnd_892406] using wordTrace_append hprefix tailTrace_892406
  have hstable : (prefixWord ++ tailWord_892406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892406).length < 2 ^ (prefixWord ++ tailWord_892406).sum := by decide
  have hdescent : baseEnd_892406 < baseStart_892406 := by decide
  rcases family_descends (prefixWord ++ tailWord_892406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892466 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_892466 : Nat := 118140960795 + 892466 * 2 ^ 59
def prefixEnd_892466 : Nat := 4983230072969 + 3 ^ 40 * 892466 * 2
def baseEnd_892466 : Nat := 305509350530406970913753

theorem tailTrace_892466 : CollatzResearch.WordTrace tailWord_892466 prefixEnd_892466 305509350530406970913753 := by
  unfold tailWord_892466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137727296188894475762313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21700606123170385268699501 8137727296188894475762313)
  ·
    refine ⟨6103295472141670856821735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8137727296188894475762313 6103295472141670856821735)
    ·
      refine ⟨9154943208212506285232603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6103295472141670856821735 9154943208212506285232603)
      ·
        refine ⟨13732414812318759427848905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9154943208212506285232603 13732414812318759427848905)
        ·
          refine ⟨10299311109239069570886679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13732414812318759427848905 10299311109239069570886679)
          ·
            refine ⟨15448966663858604356330019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10299311109239069570886679 15448966663858604356330019)
            ·
              refine ⟨23173449995787906534495029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15448966663858604356330019 23173449995787906534495029)
              ·
                refine ⟨2172510937105116237608909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23173449995787906534495029 2172510937105116237608909)
                ·
                  refine ⟨814691601414418589103341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2172510937105116237608909 814691601414418589103341)
                  ·
                    refine ⟨305509350530406970913753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814691601414418589103341 305509350530406970913753)
                    ·
                      rfl

theorem cell22_892466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_892466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892466 prefixEnd_892466 := by exact prefixLift 892466
  have htrace : WordTrace (prefixWord ++ tailWord_892466) baseStart_892466 baseEnd_892466 := by
    simpa [prefixWord, tailWord_892466, baseEnd_892466] using wordTrace_append hprefix tailTrace_892466
  have hstable : (prefixWord ++ tailWord_892466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892466).length < 2 ^ (prefixWord ++ tailWord_892466).sum := by decide
  have hdescent : baseEnd_892466 < baseStart_892466 := by decide
  rcases family_descends (prefixWord ++ tailWord_892466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892494 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_892494 : Nat := 118140960795 + 892494 * 2 ^ 59
def prefixEnd_892494 : Nat := 4983230072969 + 3 ^ 40 * 892494 * 2
def baseEnd_892494 : Nat := 305518935502624231213667

theorem tailTrace_892494 : CollatzResearch.WordTrace tailWord_892494 prefixEnd_892494 305518935502624231213667 := by
  unfold tailWord_892494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068991303581767335633567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21701286952436092456712357 4068991303581767335633567)
  ·
    refine ⟨6103486955372651003450351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4068991303581767335633567 6103486955372651003450351)
    ·
      refine ⟨9155230433058976505175527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6103486955372651003450351 9155230433058976505175527)
      ·
        refine ⟨13732845649588464757763291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9155230433058976505175527 13732845649588464757763291)
        ·
          refine ⟨20599268474382697136644937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13732845649588464757763291 20599268474382697136644937)
          ·
            refine ⟨15449451355787022852483703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20599268474382697136644937 15449451355787022852483703)
            ·
              refine ⟨23174177033680534278725555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15449451355787022852483703 23174177033680534278725555)
              ·
                refine ⟨34761265550520801418088333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23174177033680534278725555 34761265550520801418088333)
                ·
                  refine ⟨13035474581445300531783125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34761265550520801418088333 13035474581445300531783125)
                  ·
                    refine ⟨305518935502624231213667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13035474581445300531783125 305518935502624231213667)
                    ·
                      rfl

theorem cell22_892494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_892494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892494 prefixEnd_892494 := by exact prefixLift 892494
  have htrace : WordTrace (prefixWord ++ tailWord_892494) baseStart_892494 baseEnd_892494 := by
    simpa [prefixWord, tailWord_892494, baseEnd_892494] using wordTrace_append hprefix tailTrace_892494
  have hstable : (prefixWord ++ tailWord_892494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892494).length < 2 ^ (prefixWord ++ tailWord_892494).sum := by decide
  have hdescent : baseEnd_892494 < baseStart_892494 := by decide
  rcases family_descends (prefixWord ++ tailWord_892494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892500 : List Nat := [2, 4, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_892500 : Nat := 118140960795 + 892500 * 2 ^ 59
def prefixEnd_892500 : Nat := 4983230072969 + 3 ^ 40 * 892500 * 2
def baseEnd_892500 : Nat := 305520989425242215563649

theorem tailTrace_892500 : CollatzResearch.WordTrace tailWord_892500 prefixEnd_892500 305520989425242215563649 := by
  unfold tailWord_892500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16276074633316200854893477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21701432844421601139857969 16276074633316200854893477)
  ·
    refine ⟨3051763993746787660292527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16276074633316200854893477 3051763993746787660292527)
    ·
      refine ⟨4577645990620181490438791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051763993746787660292527 4577645990620181490438791)
      ·
        refine ⟨6866468985930272235658187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4577645990620181490438791 6866468985930272235658187)
        ·
          refine ⟨10299703478895408353487281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6866468985930272235658187 10299703478895408353487281)
          ·
            refine ⟨7724777609171556265115461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10299703478895408353487281 7724777609171556265115461)
            ·
              refine ⟨1448395801719666799709149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7724777609171556265115461 1448395801719666799709149)
              ·
                refine ⟨543148425644875049890931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1448395801719666799709149 543148425644875049890931)
                ·
                  refine ⟨814722638467312574836397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543148425644875049890931 814722638467312574836397)
                  ·
                    refine ⟨305520989425242215563649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814722638467312574836397 305520989425242215563649)
                    ·
                      rfl

theorem cell22_892500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_892500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892500 prefixEnd_892500 := by exact prefixLift 892500
  have htrace : WordTrace (prefixWord ++ tailWord_892500) baseStart_892500 baseEnd_892500 := by
    simpa [prefixWord, tailWord_892500, baseEnd_892500] using wordTrace_append hprefix tailTrace_892500
  have hstable : (prefixWord ++ tailWord_892500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892500).length < 2 ^ (prefixWord ++ tailWord_892500).sum := by decide
  have hdescent : baseEnd_892500 < baseStart_892500 := by decide
  rcases family_descends (prefixWord ++ tailWord_892500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892541 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 6]
def baseStart_892541 : Nat := 118140960795 + 892541 * 2 ^ 59
def prefixEnd_892541 : Nat := 4983230072969 + 3 ^ 40 * 892541 * 2
def baseEnd_892541 : Nat := 101845008187710591762841

theorem tailTrace_892541 : CollatzResearch.WordTrace tailWord_892541 prefixEnd_892541 101845008187710591762841 := by
  unfold tailWord_892541
  simp only [CollatzResearch.WordTrace]
  refine ⟨32553644659483865712029477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21702429772989243808019651 32553644659483865712029477)
  ·
    refine ⟨6103808373653224821005527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32553644659483865712029477 6103808373653224821005527)
    ·
      refine ⟨9155712560479837231508291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6103808373653224821005527 9155712560479837231508291)
      ·
        refine ⟨13733568840719755847262437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9155712560479837231508291 13733568840719755847262437)
        ·
          refine ⟨2575044157634954221361707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13733568840719755847262437 2575044157634954221361707)
          ·
            refine ⟨3862566236452431332042561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575044157634954221361707 3862566236452431332042561)
            ·
              refine ⟨2896924677339323499031921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862566236452431332042561 2896924677339323499031921)
              ·
                refine ⟨2172693508004492624273941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2896924677339323499031921 2172693508004492624273941)
                ·
                  refine ⟨101845008187710591762841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2172693508004492624273941 101845008187710591762841)
                  ·
                    rfl

theorem cell22_892541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_892541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892541 prefixEnd_892541 := by exact prefixLift 892541
  have htrace : WordTrace (prefixWord ++ tailWord_892541) baseStart_892541 baseEnd_892541 := by
    simpa [prefixWord, tailWord_892541, baseEnd_892541] using wordTrace_append hprefix tailTrace_892541
  have hstable : (prefixWord ++ tailWord_892541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892541).length < 2 ^ (prefixWord ++ tailWord_892541).sum := by decide
  have hdescent : baseEnd_892541 < baseStart_892541 := by decide
  rcases family_descends (prefixWord ++ tailWord_892541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892556 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_892556 : Nat := 118140960795 + 892556 * 2 ^ 59
def prefixEnd_892556 : Nat := 4983230072969 + 3 ^ 40 * 892556 * 2
def baseEnd_892556 : Nat := 305540159369676736163477

theorem tailTrace_892556 : CollatzResearch.WordTrace tailWord_892556 prefixEnd_892556 305540159369676736163477 := by
  unfold tailWord_892556
  simp only [CollatzResearch.WordTrace]
  refine ⟨16277095877214761636912761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21702794502953015515883681 16277095877214761636912761)
  ·
    refine ⟨12207821907911071227684571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16277095877214761636912761 12207821907911071227684571)
    ·
      refine ⟨18311732861866606841526857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12207821907911071227684571 18311732861866606841526857)
      ·
        refine ⟨13733799646399955131145143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18311732861866606841526857 13733799646399955131145143)
        ·
          refine ⟨20600699469599932696717715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13733799646399955131145143 20600699469599932696717715)
          ·
            refine ⟨30901049204399899045076573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20600699469599932696717715 30901049204399899045076573)
            ·
              refine ⟨11587893451649962141903715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30901049204399899045076573 11587893451649962141903715)
              ·
                refine ⟨17381840177474943212855573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11587893451649962141903715 17381840177474943212855573)
                ·
                  refine ⟨814773758319137963102605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17381840177474943212855573 814773758319137963102605)
                  ·
                    refine ⟨305540159369676736163477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814773758319137963102605 305540159369676736163477)
                    ·
                      rfl

theorem cell22_892556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_892556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892556 prefixEnd_892556 := by exact prefixLift 892556
  have htrace : WordTrace (prefixWord ++ tailWord_892556) baseStart_892556 baseEnd_892556 := by
    simpa [prefixWord, tailWord_892556, baseEnd_892556] using wordTrace_append hprefix tailTrace_892556
  have hstable : (prefixWord ++ tailWord_892556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892556).length < 2 ^ (prefixWord ++ tailWord_892556).sum := by decide
  have hdescent : baseEnd_892556 < baseStart_892556 := by decide
  rcases family_descends (prefixWord ++ tailWord_892556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892573 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_892573 : Nat := 118140960795 + 892573 * 2 ^ 59
def prefixEnd_892573 : Nat := 4983230072969 + 3 ^ 40 * 892573 * 2
def baseEnd_892573 : Nat := 305545978817094358488425

theorem tailTrace_892573 : CollatzResearch.WordTrace tailWord_892573 prefixEnd_892573 305545978817094358488425 := by
  unfold tailWord_892573
  simp only [CollatzResearch.WordTrace]
  refine ⟨32554811795367935177194373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21703207863578623451462915 32554811795367935177194373)
  ·
    refine ⟨6104027211631487845723945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32554811795367935177194373 6104027211631487845723945)
    ·
      refine ⟨4578020408723615884292959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6104027211631487845723945 4578020408723615884292959)
      ·
        refine ⟨6867030613085423826439439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578020408723615884292959 6867030613085423826439439)
        ·
          refine ⟨10300545919628135739659159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6867030613085423826439439 10300545919628135739659159)
          ·
            refine ⟨15450818879442203609488739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10300545919628135739659159 15450818879442203609488739)
            ·
              refine ⟨23176228319163305414233109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15450818879442203609488739 23176228319163305414233109)
              ·
                refine ⟨1086385702460779941292177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23176228319163305414233109 1086385702460779941292177)
                ·
                  refine ⟨814789276845584955969133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086385702460779941292177 814789276845584955969133)
                  ·
                    refine ⟨305545978817094358488425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814789276845584955969133 305545978817094358488425)
                    ·
                      rfl

theorem cell22_892573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_892573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892573 prefixEnd_892573 := by exact prefixLift 892573
  have htrace : WordTrace (prefixWord ++ tailWord_892573) baseStart_892573 baseEnd_892573 := by
    simpa [prefixWord, tailWord_892573, baseEnd_892573] using wordTrace_append hprefix tailTrace_892573
  have hstable : (prefixWord ++ tailWord_892573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892573).length < 2 ^ (prefixWord ++ tailWord_892573).sum := by decide
  have hdescent : baseEnd_892573 < baseStart_892573 := by decide
  rcases family_descends (prefixWord ++ tailWord_892573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892575 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 6]
def baseStart_892575 : Nat := 118140960795 + 892575 * 2 ^ 59
def prefixEnd_892575 : Nat := 4983230072969 + 3 ^ 40 * 892575 * 2
def baseEnd_892575 : Nat := 101848887819322339979473

theorem tailTrace_892575 : CollatzResearch.WordTrace tailWord_892575 prefixEnd_892575 101848887819322339979473 := by
  unfold tailWord_892575
  simp only [CollatzResearch.WordTrace]
  refine ⟨32554884741360689518767179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21703256494240459679178119 32554884741360689518767179)
  ·
    refine ⟨48832327112041034278150769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32554884741360689518767179 48832327112041034278150769)
    ·
      refine ⟨36624245334030775708613077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48832327112041034278150769 36624245334030775708613077)
      ·
        refine ⟨858380750016346305670619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36624245334030775708613077 858380750016346305670619)
        ·
          refine ⟨1287571125024519458505929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858380750016346305670619 1287571125024519458505929)
          ·
            refine ⟨965678343768389593879447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287571125024519458505929 965678343768389593879447)
            ·
              refine ⟨1448517515652584390819171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965678343768389593879447 1448517515652584390819171)
              ·
                refine ⟨2172776273478876586228757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448517515652584390819171 2172776273478876586228757)
                ·
                  refine ⟨101848887819322339979473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2172776273478876586228757 101848887819322339979473)
                  ·
                    rfl

theorem cell22_892575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 6].length) (baseStart_892575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892575 prefixEnd_892575 := by exact prefixLift 892575
  have htrace : WordTrace (prefixWord ++ tailWord_892575) baseStart_892575 baseEnd_892575 := by
    simpa [prefixWord, tailWord_892575, baseEnd_892575] using wordTrace_append hprefix tailTrace_892575
  have hstable : (prefixWord ++ tailWord_892575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892575).length < 2 ^ (prefixWord ++ tailWord_892575).sum := by decide
  have hdescent : baseEnd_892575 < baseStart_892575 := by decide
  rcases family_descends (prefixWord ++ tailWord_892575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892637 : List Nat := [1, 4, 3, 3, 2, 1, 1, 7]
def baseStart_892637 : Nat := 118140960795 + 892637 * 2 ^ 59
def prefixEnd_892637 : Nat := 4983230072969 + 3 ^ 40 * 892637 * 2
def baseEnd_892637 : Nat := 33951987480557724987581

theorem tailTrace_892637 : CollatzResearch.WordTrace tailWord_892637 prefixEnd_892637 33951987480557724987581 := by
  unfold tailWord_892637
  simp only [CollatzResearch.WordTrace]
  refine ⟨32557146067136074107524165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21704764044757382738349443 32557146067136074107524165)
  ·
    refine ⟨6104464887588013895160781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32557146067136074107524165 6104464887588013895160781)
    ·
      refine ⟨2289174332845505210685293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6104464887588013895160781 2289174332845505210685293)
      ·
        refine ⟨858440374817064454006985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2289174332845505210685293 858440374817064454006985)
        ·
          refine ⟨643830281112798340505239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858440374817064454006985 643830281112798340505239)
          ·
            refine ⟨965745421669197510757859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643830281112798340505239 965745421669197510757859)
            ·
              refine ⟨1448618132503796266136789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965745421669197510757859 1448618132503796266136789)
              ·
                refine ⟨33951987480557724987581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1448618132503796266136789 33951987480557724987581)
                ·
                  rfl

theorem cell22_892637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 7].length) (baseStart_892637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892637 prefixEnd_892637 := by exact prefixLift 892637
  have htrace : WordTrace (prefixWord ++ tailWord_892637) baseStart_892637 baseEnd_892637 := by
    simpa [prefixWord, tailWord_892637, baseEnd_892637] using wordTrace_append hprefix tailTrace_892637
  have hstable : (prefixWord ++ tailWord_892637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892637).length < 2 ^ (prefixWord ++ tailWord_892637).sum := by decide
  have hdescent : baseEnd_892637 < baseStart_892637 := by decide
  rcases family_descends (prefixWord ++ tailWord_892637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892648 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 5]
def baseStart_892648 : Nat := 118140960795 + 892648 * 2 ^ 59
def prefixEnd_892648 : Nat := 4983230072969 + 3 ^ 40 * 892648 * 2
def baseEnd_892648 : Nat := 101857217616606387621065

theorem tailTrace_892648 : CollatzResearch.WordTrace tailWord_892648 prefixEnd_892648 101857217616606387621065 := by
  unfold tailWord_892648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16278773635048111493087299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21705031513397481990783065 16278773635048111493087299)
  ·
    refine ⟨24418160452572167239630949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16278773635048111493087299 24418160452572167239630949)
    ·
      refine ⟨4578405084857281357430803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24418160452572167239630949 4578405084857281357430803)
      ·
        refine ⟨6867607627285922036146205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4578405084857281357430803 6867607627285922036146205)
        ·
          refine ⟨2575352860232220763554827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6867607627285922036146205 2575352860232220763554827)
          ·
            refine ⟨3863029290348331145332241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575352860232220763554827 3863029290348331145332241)
            ·
              refine ⟨2897271967761248358999181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863029290348331145332241 2897271967761248358999181)
              ·
                refine ⟨1086476987910468134624693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897271967761248358999181 1086476987910468134624693)
                ·
                  refine ⟨101857217616606387621065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1086476987910468134624693 101857217616606387621065)
                  ·
                    rfl

theorem cell22_892648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_892648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892648 prefixEnd_892648 := by exact prefixLift 892648
  have htrace : WordTrace (prefixWord ++ tailWord_892648) baseStart_892648 baseEnd_892648 := by
    simpa [prefixWord, tailWord_892648, baseEnd_892648] using wordTrace_append hprefix tailTrace_892648
  have hstable : (prefixWord ++ tailWord_892648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892648).length < 2 ^ (prefixWord ++ tailWord_892648).sum := by decide
  have hdescent : baseEnd_892648 < baseStart_892648 := by decide
  rcases family_descends (prefixWord ++ tailWord_892648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892693 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 6]
def baseStart_892693 : Nat := 118140960795 + 892693 * 2 ^ 59
def prefixEnd_892693 : Nat := 4983230072969 + 3 ^ 40 * 892693 * 2
def baseEnd_892693 : Nat := 101862352423151348496019

theorem tailTrace_892693 : CollatzResearch.WordTrace tailWord_892693 prefixEnd_892693 101862352423151348496019 := by
  unfold tailWord_892693
  simp only [CollatzResearch.WordTrace]
  refine ⟨32559188554933195671562733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21706125703288797114375155 32559188554933195671562733)
  ·
    refine ⟨12209695708099948376836025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32559188554933195671562733 12209695708099948376836025)
    ·
      refine ⟨9157271781074961282627019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12209695708099948376836025 9157271781074961282627019)
      ·
        refine ⟨13735907671612441923940529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9157271781074961282627019 13735907671612441923940529)
        ·
          refine ⟨10301930753709331442955397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13735907671612441923940529 10301930753709331442955397)
          ·
            refine ⟨1931612016320499645554137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10301930753709331442955397 1931612016320499645554137)
            ·
              refine ⟨1448709012240374734165603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931612016320499645554137 1448709012240374734165603)
              ·
                refine ⟨2173063518360562101248405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448709012240374734165603 2173063518360562101248405)
                ·
                  refine ⟨101862352423151348496019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2173063518360562101248405 101862352423151348496019)
                  ·
                    rfl

theorem cell22_892693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_892693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892693 prefixEnd_892693 := by exact prefixLift 892693
  have htrace : WordTrace (prefixWord ++ tailWord_892693) baseStart_892693 baseEnd_892693 := by
    simpa [prefixWord, tailWord_892693, baseEnd_892693] using wordTrace_append hprefix tailTrace_892693
  have hstable : (prefixWord ++ tailWord_892693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892693).length < 2 ^ (prefixWord ++ tailWord_892693).sum := by decide
  have hdescent : baseEnd_892693 < baseStart_892693 := by decide
  rcases family_descends (prefixWord ++ tailWord_892693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892759 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 2, 3]
def baseStart_892759 : Nat := 118140960795 + 892759 * 2 ^ 59
def prefixEnd_892759 : Nat := 4983230072969 + 3 ^ 40 * 892759 * 2
def baseEnd_892759 : Nat := 305609650418251873337855

theorem tailTrace_892759 : CollatzResearch.WordTrace tailWord_892759 prefixEnd_892759 305609650418251873337855 := by
  unfold tailWord_892759
  simp only [CollatzResearch.WordTrace]
  refine ⟨32561595772694088943465331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21707730515129392628976887 32561595772694088943465331)
  ·
    refine ⟨48842393659041133415197997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32561595772694088943465331 48842393659041133415197997)
    ·
      refine ⟨18315897622140425030699249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48842393659041133415197997 18315897622140425030699249)
      ·
        refine ⟨13736923216605318773024437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18315897622140425030699249 13736923216605318773024437)
        ·
          refine ⟨1287836551556748634971041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13736923216605318773024437 1287836551556748634971041)
          ·
            refine ⟨965877413667561476228281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287836551556748634971041 965877413667561476228281)
            ·
              refine ⟨724408060250671107171211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965877413667561476228281 724408060250671107171211)
              ·
                refine ⟨1086612090376006660756817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724408060250671107171211 1086612090376006660756817)
                ·
                  refine ⟨814959067782004995567613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086612090376006660756817 814959067782004995567613)
                  ·
                    refine ⟨305609650418251873337855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814959067782004995567613 305609650418251873337855)
                    ·
                      rfl

theorem cell22_892759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_892759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892759 prefixEnd_892759 := by exact prefixLift 892759
  have htrace : WordTrace (prefixWord ++ tailWord_892759) baseStart_892759 baseEnd_892759 := by
    simpa [prefixWord, tailWord_892759, baseEnd_892759] using wordTrace_append hprefix tailTrace_892759
  have hstable : (prefixWord ++ tailWord_892759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892759).length < 2 ^ (prefixWord ++ tailWord_892759).sum := by decide
  have hdescent : baseEnd_892759 < baseStart_892759 := by decide
  rcases family_descends (prefixWord ++ tailWord_892759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892804 : List Nat := [2, 3, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_892804 : Nat := 118140960795 + 892804 * 2 ^ 59
def prefixEnd_892804 : Nat := 4983230072969 + 3 ^ 40 * 892804 * 2
def baseEnd_892804 : Nat := 305625054837886755962717

theorem tailTrace_892804 : CollatzResearch.WordTrace tailWord_892804 prefixEnd_892804 305625054837886755962717 := by
  unfold tailWord_892804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16281618528765530814426733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21708824705020707752568977 16281618528765530814426733)
  ·
    refine ⟨6105606948287074055410025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16281618528765530814426733 6105606948287074055410025)
    ·
      refine ⟨4579205211215305541557519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6105606948287074055410025 4579205211215305541557519)
      ·
        refine ⟨6868807816822958312336279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579205211215305541557519 6868807816822958312336279)
        ·
          refine ⟨10303211725234437468504419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6868807816822958312336279 10303211725234437468504419)
          ·
            refine ⟨15454817587851656202756629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10303211725234437468504419 15454817587851656202756629)
            ·
              refine ⟨724444574430546384504217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15454817587851656202756629 724444574430546384504217)
              ·
                refine ⟨543333430822909788378163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724444574430546384504217 543333430822909788378163)
                ·
                  refine ⟨815000146234364682567245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543333430822909788378163 815000146234364682567245)
                  ·
                    refine ⟨305625054837886755962717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815000146234364682567245 305625054837886755962717)
                    ·
                      rfl

theorem cell22_892804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_892804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892804 prefixEnd_892804 := by exact prefixLift 892804
  have htrace : WordTrace (prefixWord ++ tailWord_892804) baseStart_892804 baseEnd_892804 := by
    simpa [prefixWord, tailWord_892804, baseEnd_892804] using wordTrace_append hprefix tailTrace_892804
  have hstable : (prefixWord ++ tailWord_892804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892804).length < 2 ^ (prefixWord ++ tailWord_892804).sum := by decide
  have hdescent : baseEnd_892804 < baseStart_892804 := by decide
  rcases family_descends (prefixWord ++ tailWord_892804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892862 : List Nat := [4, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_892862 : Nat := 118140960795 + 892862 * 2 ^ 59
def prefixEnd_892862 : Nat := 4983230072969 + 3 ^ 40 * 892862 * 2
def baseEnd_892862 : Nat := 101881636474397979337513

theorem tailTrace_892862 : CollatzResearch.WordTrace tailWord_892862 prefixEnd_892862 101881636474397979337513 := by
  unfold tailWord_892862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070669061415117191808105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21710234994213958356309893 4070669061415117191808105)
  ·
    refine ⟨3053001796061337893856079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4070669061415117191808105 3053001796061337893856079)
    ·
      refine ⟨4579502694092006840784119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3053001796061337893856079 4579502694092006840784119)
      ·
        refine ⟨6869254041138010261176179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579502694092006840784119 6869254041138010261176179)
        ·
          refine ⟨10303881061707015391764269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6869254041138010261176179 10303881061707015391764269)
          ·
            refine ⟨3863955398140130771911601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10303881061707015391764269 3863955398140130771911601)
            ·
              refine ⟨2897966548605098078933701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863955398140130771911601 2897966548605098078933701)
              ·
                refine ⟨543368727863455889800069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2897966548605098078933701 543368727863455889800069)
                ·
                  refine ⟨101881636474397979337513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543368727863455889800069 101881636474397979337513)
                  ·
                    rfl

theorem cell22_892862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_892862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892862 prefixEnd_892862 := by exact prefixLift 892862
  have htrace : WordTrace (prefixWord ++ tailWord_892862) baseStart_892862 baseEnd_892862 := by
    simpa [prefixWord, tailWord_892862, baseEnd_892862] using wordTrace_append hprefix tailTrace_892862
  have hstable : (prefixWord ++ tailWord_892862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892862).length < 2 ^ (prefixWord ++ tailWord_892862).sum := by decide
  have hdescent : baseEnd_892862 < baseStart_892862 := by decide
  rcases family_descends (prefixWord ++ tailWord_892862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892888 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_892888 : Nat := 118140960795 + 892888 * 2 ^ 59
def prefixEnd_892888 : Nat := 4983230072969 + 3 ^ 40 * 892888 * 2
def baseEnd_892888 : Nat := 305653809754538536862459

theorem tailTrace_892888 : CollatzResearch.WordTrace tailWord_892888 prefixEnd_892888 305653809754538536862459 := by
  unfold tailWord_892888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283150394613371987455659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21710867192817829316607545 16283150394613371987455659)
  ·
    refine ⟨24424725591920057981183489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16283150394613371987455659 24424725591920057981183489)
    ·
      refine ⟨18318544193940043485887617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24424725591920057981183489 18318544193940043485887617)
      ·
        refine ⟨13738908145455032614415713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18318544193940043485887617 13738908145455032614415713)
        ·
          refine ⟨10304181109091274460811785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13738908145455032614415713 10304181109091274460811785)
          ·
            refine ⟨7728135831818455845608839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10304181109091274460811785 7728135831818455845608839)
            ·
              refine ⟨11592203747727683768413259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728135831818455845608839 11592203747727683768413259)
              ·
                refine ⟨17388305621591525652619889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11592203747727683768413259 17388305621591525652619889)
                ·
                  refine ⟨13041229216193644239464917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17388305621591525652619889 13041229216193644239464917)
                  ·
                    refine ⟨305653809754538536862459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13041229216193644239464917 305653809754538536862459)
                    ·
                      rfl

theorem cell22_892888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_892888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892888 prefixEnd_892888 := by exact prefixLift 892888
  have htrace : WordTrace (prefixWord ++ tailWord_892888) baseStart_892888 baseEnd_892888 := by
    simpa [prefixWord, tailWord_892888, baseEnd_892888] using wordTrace_append hprefix tailTrace_892888
  have hstable : (prefixWord ++ tailWord_892888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892888).length < 2 ^ (prefixWord ++ tailWord_892888).sum := by decide
  have hdescent : baseEnd_892888 < baseStart_892888 := by decide
  rcases family_descends (prefixWord ++ tailWord_892888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892890 : List Nat := [3, 1, 1, 2, 5, 1, 1, 8]
def baseStart_892890 : Nat := 118140960795 + 892890 * 2 ^ 59
def prefixEnd_892890 : Nat := 4983230072969 + 3 ^ 40 * 892890 * 2
def baseEnd_892890 : Nat := 33961610488379022034717

theorem tailTrace_892890 : CollatzResearch.WordTrace tailWord_892890 prefixEnd_892890 33961610488379022034717 := by
  unfold tailWord_892890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8141593433804874579121031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21710915823479665544322749 8141593433804874579121031)
  ·
    refine ⟨12212390150707311868681547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8141593433804874579121031 12212390150707311868681547)
    ·
      refine ⟨18318585226060967803022321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12212390150707311868681547 18318585226060967803022321)
      ·
        refine ⟨13738938919545725852266741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18318585226060967803022321 13738938919545725852266741)
        ·
          refine ⟨1288025523707411798650007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13738938919545725852266741 1288025523707411798650007)
          ·
            refine ⟨1932038285561117697975011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288025523707411798650007 1932038285561117697975011)
            ·
              refine ⟨2898057428341676546962517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932038285561117697975011 2898057428341676546962517)
              ·
                refine ⟨33961610488379022034717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2898057428341676546962517 33961610488379022034717)
                ·
                  rfl

theorem cell22_892890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_892890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892890 prefixEnd_892890 := by exact prefixLift 892890
  have htrace : WordTrace (prefixWord ++ tailWord_892890) baseStart_892890 baseEnd_892890 := by
    simpa [prefixWord, tailWord_892890, baseEnd_892890] using wordTrace_append hprefix tailTrace_892890
  have hstable : (prefixWord ++ tailWord_892890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892890).length < 2 ^ (prefixWord ++ tailWord_892890).sum := by decide
  have hdescent : baseEnd_892890 < baseStart_892890 := by decide
  rcases family_descends (prefixWord ++ tailWord_892890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892909 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_892909 : Nat := 118140960795 + 892909 * 2 ^ 59
def prefixEnd_892909 : Nat := 4983230072969 + 3 ^ 40 * 892909 * 2
def baseEnd_892909 : Nat := 305660998483701482087395

theorem tailTrace_892909 : CollatzResearch.WordTrace tailWord_892909 prefixEnd_892909 305660998483701482087395 := by
  unfold tailWord_892909
  simp only [CollatzResearch.WordTrace]
  refine ⟨32567066722150664561425781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21711377814767109707617187 32567066722150664561425781)
  ·
    refine ⟨3053162505201624802633667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32567066722150664561425781 3053162505201624802633667)
    ·
      refine ⟨4579743757802437203950501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3053162505201624802633667 4579743757802437203950501)
      ·
        refine ⟨858701954587956975740719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4579743757802437203950501 858701954587956975740719)
        ·
          refine ⟨1288052931881935463611079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858701954587956975740719 1288052931881935463611079)
          ·
            refine ⟨1932079397822903195416619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288052931881935463611079 1932079397822903195416619)
            ·
              refine ⟨2898119096734354793124929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932079397822903195416619 2898119096734354793124929)
              ·
                refine ⟨2173589322550766094843697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898119096734354793124929 2173589322550766094843697)
                ·
                  refine ⟨1630191991913074571132773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2173589322550766094843697 1630191991913074571132773)
                  ·
                    refine ⟨305660998483701482087395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1630191991913074571132773 305660998483701482087395)
                    ·
                      rfl

theorem cell22_892909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_892909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892909 prefixEnd_892909 := by exact prefixLift 892909
  have htrace : WordTrace (prefixWord ++ tailWord_892909) baseStart_892909 baseEnd_892909 := by
    simpa [prefixWord, tailWord_892909, baseEnd_892909] using wordTrace_append hprefix tailTrace_892909
  have hstable : (prefixWord ++ tailWord_892909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892909).length < 2 ^ (prefixWord ++ tailWord_892909).sum := by decide
  have hdescent : baseEnd_892909 < baseStart_892909 := by decide
  rcases family_descends (prefixWord ++ tailWord_892909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_892982 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_892982 : Nat := 118140960795 + 892982 * 2 ^ 59
def prefixEnd_892982 : Nat := 4983230072969 + 3 ^ 40 * 892982 * 2
def baseEnd_892982 : Nat := 305685987875553625012171

theorem tailTrace_892982 : CollatzResearch.WordTrace tailWord_892982 prefixEnd_892982 305685987875553625012171 := by
  unfold tailWord_892982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035608078180387376802075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21713152833924132019222133 2035608078180387376802075)
  ·
    refine ⟨3053412117270581065203113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2035608078180387376802075 3053412117270581065203113)
    ·
      refine ⟨2290059087952935798902335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3053412117270581065203113 2290059087952935798902335)
      ·
        refine ⟨3435088631929403698353503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290059087952935798902335 3435088631929403698353503)
        ·
          refine ⟨5152632947894105547530255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3435088631929403698353503 5152632947894105547530255)
          ·
            refine ⟨7728949421841158321295383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152632947894105547530255 7728949421841158321295383)
            ·
              refine ⟨11593424132761737481943075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728949421841158321295383 11593424132761737481943075)
              ·
                refine ⟨17390136199142606222914613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11593424132761737481943075 17390136199142606222914613)
                ·
                  refine ⟨1630325268669619333398245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17390136199142606222914613 1630325268669619333398245)
                  ·
                    refine ⟨305685987875553625012171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1630325268669619333398245 305685987875553625012171)
                    ·
                      rfl

theorem cell22_892982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_892982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_892982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_892982 prefixEnd_892982 := by exact prefixLift 892982
  have htrace : WordTrace (prefixWord ++ tailWord_892982) baseStart_892982 baseEnd_892982 := by
    simpa [prefixWord, tailWord_892982, baseEnd_892982] using wordTrace_append hprefix tailTrace_892982
  have hstable : (prefixWord ++ tailWord_892982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_892982).length < 2 ^ (prefixWord ++ tailWord_892982).sum := by decide
  have hdescent : baseEnd_892982 < baseStart_892982 := by decide
  rcases family_descends (prefixWord ++ tailWord_892982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893012 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_893012 : Nat := 118140960795 + 893012 * 2 ^ 59
def prefixEnd_893012 : Nat := 4983230072969 + 3 ^ 40 * 893012 * 2
def baseEnd_893012 : Nat := 305696257488643546762079

theorem tailTrace_893012 : CollatzResearch.WordTrace tailWord_893012 prefixEnd_893012 305696257488643546762079 := by
  unfold tailWord_893012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16285411720388756576212645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21713882293851675434950193 16285411720388756576212645)
  ·
    refine ⟨3053514697572891858039871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16285411720388756576212645 3053514697572891858039871)
    ·
      refine ⟨4580272046359337787059807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3053514697572891858039871 4580272046359337787059807)
      ·
        refine ⟨6870408069539006680589711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4580272046359337787059807 6870408069539006680589711)
        ·
          refine ⟨10305612104308510020884567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870408069539006680589711 10305612104308510020884567)
          ·
            refine ⟨15458418156462765031326851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10305612104308510020884567 15458418156462765031326851)
            ·
              refine ⟨23187627234694147546990277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15458418156462765031326851 23187627234694147546990277)
              ·
                refine ⟨4347680106505152665060677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23187627234694147546990277 4347680106505152665060677)
                ·
                  refine ⟨815190019969716124698877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4347680106505152665060677 815190019969716124698877)
                  ·
                    refine ⟨305696257488643546762079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815190019969716124698877 305696257488643546762079)
                    ·
                      rfl

theorem cell22_893012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_893012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893012 prefixEnd_893012 := by exact prefixLift 893012
  have htrace : WordTrace (prefixWord ++ tailWord_893012) baseStart_893012 baseEnd_893012 := by
    simpa [prefixWord, tailWord_893012, baseEnd_893012] using wordTrace_append hprefix tailTrace_893012
  have hstable : (prefixWord ++ tailWord_893012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893012).length < 2 ^ (prefixWord ++ tailWord_893012).sum := by decide
  have hdescent : baseEnd_893012 < baseStart_893012 := by decide
  rcases family_descends (prefixWord ++ tailWord_893012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893029 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_893029 : Nat := 118140960795 + 893029 * 2 ^ 59
def prefixEnd_893029 : Nat := 4983230072969 + 3 ^ 40 * 893029 * 2
def baseEnd_893029 : Nat := 305702076936061169087027

theorem tailTrace_893029 : CollatzResearch.WordTrace tailWord_893029 prefixEnd_893029 305702076936061169087027 := by
  unfold tailWord_893029
  simp only [CollatzResearch.WordTrace]
  refine ⟨32571443481715925055794141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21714295654477283370529427 32571443481715925055794141)
  ·
    refine ⟨12214291305643471895922803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32571443481715925055794141 12214291305643471895922803)
    ·
      refine ⟨18321436958465207843884205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12214291305643471895922803 18321436958465207843884205)
      ·
        refine ⟨6870538859424452941456577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18321436958465207843884205 6870538859424452941456577)
        ·
          refine ⟨5152904144568339706092433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6870538859424452941456577 5152904144568339706092433)
          ·
            refine ⟨3864678108426254779569325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5152904144568339706092433 3864678108426254779569325)
            ·
              refine ⟨1449254290659845542338497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3864678108426254779569325 1449254290659845542338497)
              ·
                refine ⟨1086940717994884156753873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449254290659845542338497 1086940717994884156753873)
                ·
                  refine ⟨815205538496163117565405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086940717994884156753873 815205538496163117565405)
                  ·
                    refine ⟨305702076936061169087027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815205538496163117565405 305702076936061169087027)
                    ·
                      rfl

theorem cell22_893029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_893029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893029 prefixEnd_893029 := by exact prefixLift 893029
  have htrace : WordTrace (prefixWord ++ tailWord_893029) baseStart_893029 baseEnd_893029 := by
    simpa [prefixWord, tailWord_893029, baseEnd_893029] using wordTrace_append hprefix tailTrace_893029
  have hstable : (prefixWord ++ tailWord_893029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893029).length < 2 ^ (prefixWord ++ tailWord_893029).sum := by decide
  have hdescent : baseEnd_893029 < baseStart_893029 := by decide
  rcases family_descends (prefixWord ++ tailWord_893029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893076 : List Nat := [2, 4, 2, 3, 2, 1, 8]
def baseStart_893076 : Nat := 118140960795 + 893076 * 2 ^ 59
def prefixEnd_893076 : Nat := 4983230072969 + 3 ^ 40 * 893076 * 2
def baseEnd_893076 : Nat := 11322895036909952339329

theorem tailTrace_893076 : CollatzResearch.WordTrace tailWord_893076 prefixEnd_893076 11322895036909952339329 := by
  unfold tailWord_893076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16286578856272826041377541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21715438475030434721836721 16286578856272826041377541)
  ·
    refine ⟨3053733535551154882758289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16286578856272826041377541 3053733535551154882758289)
    ·
      refine ⟨2290300151663366162068717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3053733535551154882758289 2290300151663366162068717)
      ·
        refine ⟨858862556873762310775769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2290300151663366162068717 858862556873762310775769)
        ·
          refine ⟨644146917655321733081827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858862556873762310775769 644146917655321733081827)
          ·
            refine ⟨966220376482982599622741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644146917655321733081827 966220376482982599622741)
            ·
              refine ⟨11322895036909952339329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 966220376482982599622741 11322895036909952339329)
              ·
                rfl

theorem cell22_893076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 8].length) (baseStart_893076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893076 prefixEnd_893076 := by exact prefixLift 893076
  have htrace : WordTrace (prefixWord ++ tailWord_893076) baseStart_893076 baseEnd_893076 := by
    simpa [prefixWord, tailWord_893076, baseEnd_893076] using wordTrace_append hprefix tailTrace_893076
  have hstable : (prefixWord ++ tailWord_893076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893076).length < 2 ^ (prefixWord ++ tailWord_893076).sum := by decide
  have hdescent : baseEnd_893076 < baseStart_893076 := by decide
  rcases family_descends (prefixWord ++ tailWord_893076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893087 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 7]
def baseStart_893087 : Nat := 118140960795 + 893087 * 2 ^ 59
def prefixEnd_893087 : Nat := 4983230072969 + 3 ^ 40 * 893087 * 2
def baseEnd_893087 : Nat := 101907310507122783712283

theorem tailTrace_893087 : CollatzResearch.WordTrace tailWord_893087 prefixEnd_893087 101907310507122783712283 := by
  unfold tailWord_893087
  simp only [CollatzResearch.WordTrace]
  refine ⟨32573558915505800961405515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21715705943670533974270343 32573558915505800961405515)
  ·
    refine ⟨48860338373258701442108273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32573558915505800961405515 48860338373258701442108273)
    ·
      refine ⟨36645253779944026081581205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48860338373258701442108273 36645253779944026081581205)
      ·
        refine ⟨1717746270934876222574119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36645253779944026081581205 1717746270934876222574119)
        ·
          refine ⟨2576619406402314333861179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717746270934876222574119 2576619406402314333861179)
          ·
            refine ⟨3864929109603471500791769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576619406402314333861179 3864929109603471500791769)
            ·
              refine ⟨2898696832202603625593827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3864929109603471500791769 2898696832202603625593827)
              ·
                refine ⟨4348045248303905438390741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898696832202603625593827 4348045248303905438390741)
                ·
                  refine ⟨101907310507122783712283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4348045248303905438390741 101907310507122783712283)
                  ·
                    rfl

theorem cell22_893087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 7].length) (baseStart_893087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893087 prefixEnd_893087 := by exact prefixLift 893087
  have htrace : WordTrace (prefixWord ++ tailWord_893087) baseStart_893087 baseEnd_893087 := by
    simpa [prefixWord, tailWord_893087, baseEnd_893087] using wordTrace_append hprefix tailTrace_893087
  have hstable : (prefixWord ++ tailWord_893087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893087).length < 2 ^ (prefixWord ++ tailWord_893087).sum := by decide
  have hdescent : baseEnd_893087 < baseStart_893087 := by decide
  rcases family_descends (prefixWord ++ tailWord_893087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893115 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 8]
def baseStart_893115 : Nat := 118140960795 + 893115 * 2 ^ 59
def prefixEnd_893115 : Nat := 4983230072969 + 3 ^ 40 * 893115 * 2
def baseEnd_893115 : Nat := 101910505497861870478921

theorem tailTrace_893115 : CollatzResearch.WordTrace tailWord_893115 prefixEnd_893115 101910505497861870478921 := by
  unfold tailWord_893115
  simp only [CollatzResearch.WordTrace]
  refine ⟨32574580159404361743424799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21716386772936241162283199 32574580159404361743424799)
  ·
    refine ⟨48861870239106542615137199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32574580159404361743424799 48861870239106542615137199)
    ·
      refine ⟨73292805358659813922705799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48861870239106542615137199 73292805358659813922705799)
      ·
        refine ⟨109939208037989720884058699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73292805358659813922705799 109939208037989720884058699)
        ·
          refine ⟨164908812056984581326088049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109939208037989720884058699 164908812056984581326088049)
          ·
            refine ⟨123681609042738435994566037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164908812056984581326088049 123681609042738435994566037)
            ·
              refine ⟨5797575423878364187245283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123681609042738435994566037 5797575423878364187245283)
              ·
                refine ⟨8696363135817546280867925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797575423878364187245283 8696363135817546280867925)
                ·
                  refine ⟨101910505497861870478921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8696363135817546280867925 101910505497861870478921)
                  ·
                    rfl

theorem cell22_893115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_893115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893115 prefixEnd_893115 := by exact prefixLift 893115
  have htrace : WordTrace (prefixWord ++ tailWord_893115) baseStart_893115 baseEnd_893115 := by
    simpa [prefixWord, tailWord_893115, baseEnd_893115] using wordTrace_append hprefix tailTrace_893115
  have hstable : (prefixWord ++ tailWord_893115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893115).length < 2 ^ (prefixWord ++ tailWord_893115).sum := by decide
  have hdescent : baseEnd_893115 < baseStart_893115 := by decide
  rcases family_descends (prefixWord ++ tailWord_893115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893142 : List Nat := [5, 2, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_893142 : Nat := 118140960795 + 893142 * 2 ^ 59
def prefixEnd_893142 : Nat := 4983230072969 + 3 ^ 40 * 893142 * 2
def baseEnd_893142 : Nat := 305740759145366541011681

theorem tailTrace_893142 : CollatzResearch.WordTrace tailWord_893142 prefixEnd_893142 305740759145366541011681 := by
  unfold tailWord_893142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035972808144159084666105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21717043286871030236438453 2035972808144159084666105)
  ·
    refine ⟨1526979606108119313499579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2035972808144159084666105 1526979606108119313499579)
    ·
      refine ⟨2290469409162178970249369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526979606108119313499579 2290469409162178970249369)
      ·
        refine ⟨1717852056871634227687027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2290469409162178970249369 1717852056871634227687027)
        ·
          refine ⟨2576778085307451341530541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717852056871634227687027 2576778085307451341530541)
          ·
            refine ⟨966291781990294253073953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2576778085307451341530541 966291781990294253073953)
            ·
              refine ⟨724718836492720689805465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966291781990294253073953 724718836492720689805465)
              ·
                refine ⟨543539127369540517354099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724718836492720689805465 543539127369540517354099)
                ·
                  refine ⟨815308691054310776031149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543539127369540517354099 815308691054310776031149)
                  ·
                    refine ⟨305740759145366541011681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815308691054310776031149 305740759145366541011681)
                    ·
                      rfl

theorem cell22_893142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_893142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893142 prefixEnd_893142 := by exact prefixLift 893142
  have htrace : WordTrace (prefixWord ++ tailWord_893142) baseStart_893142 baseEnd_893142 := by
    simpa [prefixWord, tailWord_893142, baseEnd_893142] using wordTrace_append hprefix tailTrace_893142
  have hstable : (prefixWord ++ tailWord_893142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893142).length < 2 ^ (prefixWord ++ tailWord_893142).sum := by decide
  have hdescent : baseEnd_893142 < baseStart_893142 := by decide
  rcases family_descends (prefixWord ++ tailWord_893142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893162 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_893162 : Nat := 118140960795 + 893162 * 2 ^ 59
def prefixEnd_893162 : Nat := 4983230072969 + 3 ^ 40 * 893162 * 2
def baseEnd_893162 : Nat := 305747605554093155511619

theorem tailTrace_893162 : CollatzResearch.WordTrace tailWord_893162 prefixEnd_893162 305747605554093155511619 := by
  unfold tailWord_893162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8144073597558522192596435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21717529593489392513590493 8144073597558522192596435)
  ·
    refine ⟨12216110396337783288894653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8144073597558522192596435 12216110396337783288894653)
    ·
      refine ⟨4581041398626668733335495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12216110396337783288894653 4581041398626668733335495)
      ·
        refine ⟨6871562097940003100003243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581041398626668733335495 6871562097940003100003243)
        ·
          refine ⟨10307343146910004650004865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871562097940003100003243 10307343146910004650004865)
          ·
            refine ⟨7730507360182503487503649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10307343146910004650004865 7730507360182503487503649)
            ·
              refine ⟨5797880520136877615627737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7730507360182503487503649 5797880520136877615627737)
              ·
                refine ⟨4348410390102658211720803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5797880520136877615627737 4348410390102658211720803)
                ·
                  refine ⟨6522615585153987317581205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348410390102658211720803 6522615585153987317581205)
                  ·
                    refine ⟨305747605554093155511619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6522615585153987317581205 305747605554093155511619)
                    ·
                      rfl

theorem cell22_893162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_893162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893162 prefixEnd_893162 := by exact prefixLift 893162
  have htrace : WordTrace (prefixWord ++ tailWord_893162) baseStart_893162 baseEnd_893162 := by
    simpa [prefixWord, tailWord_893162, baseEnd_893162] using wordTrace_append hprefix tailTrace_893162
  have hstable : (prefixWord ++ tailWord_893162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893162).length < 2 ^ (prefixWord ++ tailWord_893162).sum := by decide
  have hdescent : baseEnd_893162 < baseStart_893162 := by decide
  rcases family_descends (prefixWord ++ tailWord_893162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893164 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_893164 : Nat := 118140960795 + 893164 * 2 ^ 59
def prefixEnd_893164 : Nat := 4983230072969 + 3 ^ 40 * 893164 * 2
def baseEnd_893164 : Nat := 305748290194965816961613

theorem tailTrace_893164 : CollatzResearch.WordTrace tailWord_893164 prefixEnd_893164 305748290194965816961613 := by
  unfold tailWord_893164
  simp only [CollatzResearch.WordTrace]
  refine ⟨16288183668113421555979273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21717578224151228741305697 16288183668113421555979273)
  ·
    refine ⟨12216137751085066166984455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16288183668113421555979273 12216137751085066166984455)
    ·
      refine ⟨18324206626627599250476683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12216137751085066166984455 18324206626627599250476683)
      ·
        refine ⟨27486309939941398875715025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18324206626627599250476683 27486309939941398875715025)
        ·
          refine ⟨20614732454956049156786269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27486309939941398875715025 20614732454956049156786269)
          ·
            refine ⟨7730524670608518433794851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20614732454956049156786269 7730524670608518433794851)
            ·
              refine ⟨11595787005912777650692277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7730524670608518433794851 11595787005912777650692277)
              ·
                refine ⟨1087105031804322904752401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11595787005912777650692277 1087105031804322904752401)
                ·
                  refine ⟨815328773853242178564301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087105031804322904752401 815328773853242178564301)
                  ·
                    refine ⟨305748290194965816961613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815328773853242178564301 305748290194965816961613)
                    ·
                      rfl

theorem cell22_893164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_893164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893164 prefixEnd_893164 := by exact prefixLift 893164
  have htrace : WordTrace (prefixWord ++ tailWord_893164) baseStart_893164 baseEnd_893164 := by
    simpa [prefixWord, tailWord_893164, baseEnd_893164] using wordTrace_append hprefix tailTrace_893164
  have hstable : (prefixWord ++ tailWord_893164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893164).length < 2 ^ (prefixWord ++ tailWord_893164).sum := by decide
  have hdescent : baseEnd_893164 < baseStart_893164 := by decide
  rcases family_descends (prefixWord ++ tailWord_893164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893267 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 6]
def baseStart_893267 : Nat := 118140960795 + 893267 * 2 ^ 59
def prefixEnd_893267 : Nat := 4983230072969 + 3 ^ 40 * 893267 * 2
def baseEnd_893267 : Nat := 101927849733302627212099

theorem tailTrace_893267 : CollatzResearch.WordTrace tailWord_893267 prefixEnd_893267 101927849733302627212099 := by
  unfold tailWord_893267
  simp only [CollatzResearch.WordTrace]
  refine ⟨32580124054853691702958055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21720082703235794468638703 32580124054853691702958055)
  ·
    refine ⟨48870186082280537554437083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32580124054853691702958055 48870186082280537554437083)
    ·
      refine ⟨73305279123420806331655625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48870186082280537554437083 73305279123420806331655625)
      ·
        refine ⟨54978959342565604748741719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73305279123420806331655625 54978959342565604748741719)
        ·
          refine ⟨82468439013848407123112579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54978959342565604748741719 82468439013848407123112579)
          ·
            refine ⟨123702658520772610684668869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82468439013848407123112579 123702658520772610684668869)
            ·
              refine ⟨23194248472644864503375413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123702658520772610684668869 23194248472644864503375413)
              ·
                refine ⟨2174460794310456047191445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23194248472644864503375413 2174460794310456047191445)
                ·
                  refine ⟨101927849733302627212099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2174460794310456047191445 101927849733302627212099)
                  ·
                    rfl

theorem cell22_893267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 6].length) (baseStart_893267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893267 prefixEnd_893267 := by exact prefixLift 893267
  have htrace : WordTrace (prefixWord ++ tailWord_893267) baseStart_893267 baseEnd_893267 := by
    simpa [prefixWord, tailWord_893267, baseEnd_893267] using wordTrace_append hprefix tailTrace_893267
  have hstable : (prefixWord ++ tailWord_893267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893267).length < 2 ^ (prefixWord ++ tailWord_893267).sum := by decide
  have hdescent : baseEnd_893267 < baseStart_893267 := by decide
  rcases family_descends (prefixWord ++ tailWord_893267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893346 : List Nat := [3, 3, 1, 2, 1, 1, 5, 6]
def baseStart_893346 : Nat := 118140960795 + 893346 * 2 ^ 59
def prefixEnd_893346 : Nat := 4983230072969 + 3 ^ 40 * 893346 * 2
def baseEnd_893346 : Nat := 33978954723819778767895

theorem tailTrace_893346 : CollatzResearch.WordTrace tailWord_893346 prefixEnd_893346 33978954723819778767895 := by
  unfold tailWord_893346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145751355391872048770973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21722003614378325463389261 8145751355391872048770973)
  ·
    refine ⟨3054656758271952018289115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8145751355391872048770973 3054656758271952018289115)
    ·
      refine ⟨4581985137407928027433673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3054656758271952018289115 4581985137407928027433673)
      ·
        refine ⟨3436488853055946020575255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4581985137407928027433673 3436488853055946020575255)
        ·
          refine ⟨5154733279583919030862883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436488853055946020575255 5154733279583919030862883)
          ·
            refine ⟨7732099919375878546294325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154733279583919030862883 7732099919375878546294325)
            ·
              refine ⟨724884367441488613715093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7732099919375878546294325 724884367441488613715093)
              ·
                refine ⟨33978954723819778767895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 724884367441488613715093 33978954723819778767895)
                ·
                  rfl

theorem cell22_893346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_893346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893346 prefixEnd_893346 := by exact prefixLift 893346
  have htrace : WordTrace (prefixWord ++ tailWord_893346) baseStart_893346 baseEnd_893346 := by
    simpa [prefixWord, tailWord_893346, baseEnd_893346] using wordTrace_append hprefix tailTrace_893346
  have hstable : (prefixWord ++ tailWord_893346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893346).length < 2 ^ (prefixWord ++ tailWord_893346).sum := by decide
  have hdescent : baseEnd_893346 < baseStart_893346 := by decide
  rcases family_descends (prefixWord ++ tailWord_893346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893354 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_893354 : Nat := 118140960795 + 893354 * 2 ^ 59
def prefixEnd_893354 : Nat := 4983230072969 + 3 ^ 40 * 893354 * 2
def baseEnd_893354 : Nat := 305813331077868654711031

theorem tailTrace_893354 : CollatzResearch.WordTrace tailWord_893354 prefixEnd_893354 305813331077868654711031 := by
  unfold tailWord_893354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145824301384626390343779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21722198137025670374250077 8145824301384626390343779)
  ·
    refine ⟨12218736452076939585515669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8145824301384626390343779 12218736452076939585515669)
    ·
      refine ⟨572753271191106543071047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12218736452076939585515669 572753271191106543071047)
      ·
        refine ⟨859129906786659814606571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572753271191106543071047 859129906786659814606571)
        ·
          refine ⟨1288694860179989721909857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859129906786659814606571 1288694860179989721909857)
          ·
            refine ⟨966521145134992291432393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288694860179989721909857 966521145134992291432393)
            ·
              refine ⟨724890858851244218574295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966521145134992291432393 724890858851244218574295)
              ·
                refine ⟨1087336288276866327861443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724890858851244218574295 1087336288276866327861443)
                ·
                  refine ⟨1631004432415299491792165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087336288276866327861443 1631004432415299491792165)
                  ·
                    refine ⟨305813331077868654711031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631004432415299491792165 305813331077868654711031)
                    ·
                      rfl

theorem cell22_893354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_893354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893354 prefixEnd_893354 := by exact prefixLift 893354
  have htrace : WordTrace (prefixWord ++ tailWord_893354) baseStart_893354 baseEnd_893354 := by
    simpa [prefixWord, tailWord_893354, baseEnd_893354] using wordTrace_append hprefix tailTrace_893354
  have hstable : (prefixWord ++ tailWord_893354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893354).length < 2 ^ (prefixWord ++ tailWord_893354).sum := by decide
  have hdescent : baseEnd_893354 < baseStart_893354 := by decide
  rcases family_descends (prefixWord ++ tailWord_893354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893429 : List Nat := [1, 3, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_893429 : Nat := 118140960795 + 893429 * 2 ^ 59
def prefixEnd_893429 : Nat := 4983230072969 + 3 ^ 40 * 893429 * 2
def baseEnd_893429 : Nat := 305839005110593459085801

theorem tailTrace_893429 : CollatzResearch.WordTrace tailWord_893429 prefixEnd_893429 305839005110593459085801 := by
  unfold tailWord_893429
  simp only [CollatzResearch.WordTrace]
  refine ⟨32586032680266793370355341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21724021786844528913570227 32586032680266793370355341)
  ·
    refine ⟨12219762255100047513883253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32586032680266793370355341 12219762255100047513883253)
    ·
      refine ⟨1145602711415629454426555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12219762255100047513883253 1145602711415629454426555)
      ·
        refine ⟨1718404067123444181639833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145602711415629454426555 1718404067123444181639833)
        ·
          refine ⟨1288803050342583136229875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718404067123444181639833 1288803050342583136229875)
          ·
            refine ⟨1933204575513874704344813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288803050342583136229875 1933204575513874704344813)
            ·
              refine ⟨724951715817703014129305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1933204575513874704344813 724951715817703014129305)
              ·
                refine ⟨543713786863277260596979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724951715817703014129305 543713786863277260596979)
                ·
                  refine ⟨815570680294915890895469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543713786863277260596979 815570680294915890895469)
                  ·
                    refine ⟨305839005110593459085801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 815570680294915890895469 305839005110593459085801)
                    ·
                      rfl

theorem cell22_893429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_893429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893429 prefixEnd_893429 := by exact prefixLift 893429
  have htrace : WordTrace (prefixWord ++ tailWord_893429) baseStart_893429 baseEnd_893429 := by
    simpa [prefixWord, tailWord_893429, baseEnd_893429] using wordTrace_append hprefix tailTrace_893429
  have hstable : (prefixWord ++ tailWord_893429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893429).length < 2 ^ (prefixWord ++ tailWord_893429).sum := by decide
  have hdescent : baseEnd_893429 < baseStart_893429 := by decide
  rcases family_descends (prefixWord ++ tailWord_893429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893434 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_893434 : Nat := 118140960795 + 893434 * 2 ^ 59
def prefixEnd_893434 : Nat := 4983230072969 + 3 ^ 40 * 893434 * 2
def baseEnd_893434 : Nat := 305840716712775112710785

theorem tailTrace_893434 : CollatzResearch.WordTrace tailWord_893434 prefixEnd_893434 305840716712775112710785 := by
  unfold tailWord_893434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146553761312169806071839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21724143363499119482858237 8146553761312169806071839)
  ·
    refine ⟨12219830641968254709107759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8146553761312169806071839 12219830641968254709107759)
    ·
      refine ⟨18329745962952382063661639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12219830641968254709107759 18329745962952382063661639)
      ·
        refine ⟨27494618944428573095492459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18329745962952382063661639 27494618944428573095492459)
        ·
          refine ⟨41241928416642859643238689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27494618944428573095492459 41241928416642859643238689)
          ·
            refine ⟨30931446312482144732429017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41241928416642859643238689 30931446312482144732429017)
            ·
              refine ⟨23198584734361608549321763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30931446312482144732429017 23198584734361608549321763)
              ·
                refine ⟨34797877101542412823982645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23198584734361608549321763 34797877101542412823982645)
                ·
                  refine ⟨3262300978269601202248373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34797877101542412823982645 3262300978269601202248373)
                  ·
                    refine ⟨305840716712775112710785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3262300978269601202248373 305840716712775112710785)
                    ·
                      rfl

theorem cell22_893434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_893434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893434 prefixEnd_893434 := by exact prefixLift 893434
  have htrace : WordTrace (prefixWord ++ tailWord_893434) baseStart_893434 baseEnd_893434 := by
    simpa [prefixWord, tailWord_893434, baseEnd_893434] using wordTrace_append hprefix tailTrace_893434
  have hstable : (prefixWord ++ tailWord_893434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893434).length < 2 ^ (prefixWord ++ tailWord_893434).sum := by decide
  have hdescent : baseEnd_893434 < baseStart_893434 := by decide
  rcases family_descends (prefixWord ++ tailWord_893434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893442 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_893442 : Nat := 118140960795 + 893442 * 2 ^ 59
def prefixEnd_893442 : Nat := 4983230072969 + 3 ^ 40 * 893442 * 2
def baseEnd_893442 : Nat := 101947818425421919503587

theorem tailTrace_893442 : CollatzResearch.WordTrace tailWord_893442 prefixEnd_893442 101947818425421919503587 := by
  unfold tailWord_893442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146626707304924147644645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21724337886146464393719053 8146626707304924147644645)
  ·
    refine ⟨1527492507619673277683371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8146626707304924147644645 1527492507619673277683371)
    ·
      refine ⟨2291238761429509916525057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1527492507619673277683371 2291238761429509916525057)
      ·
        refine ⟨1718429071072132437393793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2291238761429509916525057 1718429071072132437393793)
        ·
          refine ⟨1288821803304099328045345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718429071072132437393793 1288821803304099328045345)
          ·
            refine ⟨966616352478074496034009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288821803304099328045345 966616352478074496034009)
            ·
              refine ⟨724962264358555872025507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966616352478074496034009 724962264358555872025507)
              ·
                refine ⟨1087443396537833808038261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724962264358555872025507 1087443396537833808038261)
                ·
                  refine ⟨101947818425421919503587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1087443396537833808038261 101947818425421919503587)
                  ·
                    rfl

theorem cell22_893442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_893442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893442 prefixEnd_893442 := by exact prefixLift 893442
  have htrace : WordTrace (prefixWord ++ tailWord_893442) baseStart_893442 baseEnd_893442 := by
    simpa [prefixWord, tailWord_893442, baseEnd_893442] using wordTrace_append hprefix tailTrace_893442
  have hstable : (prefixWord ++ tailWord_893442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893442).length < 2 ^ (prefixWord ++ tailWord_893442).sum := by decide
  have hdescent : baseEnd_893442 < baseStart_893442 := by decide
  rcases family_descends (prefixWord ++ tailWord_893442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893449 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_893449 : Nat := 118140960795 + 893449 * 2 ^ 59
def prefixEnd_893449 : Nat := 4983230072969 + 3 ^ 40 * 893449 * 2
def baseEnd_893449 : Nat := 305845851519320073585739

theorem tailTrace_893449 : CollatzResearch.WordTrace tailWord_893449 prefixEnd_893449 305845851519320073585739 := by
  unfold tailWord_893449
  simp only [CollatzResearch.WordTrace]
  refine ⟨32586762140194336786083401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21724508093462891190722267 32586762140194336786083401)
  ·
    refine ⟨24440071605145752589562551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32586762140194336786083401 24440071605145752589562551)
    ·
      refine ⟨36660107407718628884343827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24440071605145752589562551 36660107407718628884343827)
      ·
        refine ⟨54990161111577943326515741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36660107407718628884343827 54990161111577943326515741)
        ·
          refine ⟨20621310416841728747443403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54990161111577943326515741 20621310416841728747443403)
          ·
            refine ⟨30931965625262593121165105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20621310416841728747443403 30931965625262593121165105)
            ·
              refine ⟨23198974218946944840873829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30931965625262593121165105 23198974218946944840873829)
              ·
                refine ⟨4349807666052552157663843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23198974218946944840873829 4349807666052552157663843)
                ·
                  refine ⟨6524711499078828236495765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349807666052552157663843 6524711499078828236495765)
                  ·
                    refine ⟨305845851519320073585739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6524711499078828236495765 305845851519320073585739)
                    ·
                      rfl

theorem cell22_893449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_893449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893449 prefixEnd_893449 := by exact prefixLift 893449
  have htrace : WordTrace (prefixWord ++ tailWord_893449) baseStart_893449 baseEnd_893449 := by
    simpa [prefixWord, tailWord_893449, baseEnd_893449] using wordTrace_append hprefix tailTrace_893449
  have hstable : (prefixWord ++ tailWord_893449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893449).length < 2 ^ (prefixWord ++ tailWord_893449).sum := by decide
  have hdescent : baseEnd_893449 < baseStart_893449 := by decide
  rcases family_descends (prefixWord ++ tailWord_893449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893466 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_893466 : Nat := 118140960795 + 893466 * 2 ^ 59
def prefixEnd_893466 : Nat := 4983230072969 + 3 ^ 40 * 893466 * 2
def baseEnd_893466 : Nat := 305851670966737695910687

theorem tailTrace_893466 : CollatzResearch.WordTrace tailWord_893466 prefixEnd_893466 305851670966737695910687 := by
  unfold tailWord_893466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146845545283187172363063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21724921454088499126301501 8146845545283187172363063)
  ·
    refine ⟨12220268317924780758544595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8146845545283187172363063 12220268317924780758544595)
    ·
      refine ⟨18330402476887171137816893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12220268317924780758544595 18330402476887171137816893)
      ·
        refine ⟨6873900928832689176681335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18330402476887171137816893 6873900928832689176681335)
        ·
          refine ⟨10310851393249033765022003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6873900928832689176681335 10310851393249033765022003)
          ·
            refine ⟨15466277089873550647533005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10310851393249033765022003 15466277089873550647533005)
            ·
              refine ⟨5799853908702581492824877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15466277089873550647533005 5799853908702581492824877)
              ·
                refine ⟨2174945215763468059809329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5799853908702581492824877 2174945215763468059809329)
                ·
                  refine ⟨1631208911822601044856997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174945215763468059809329 1631208911822601044856997)
                  ·
                    refine ⟨305851670966737695910687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631208911822601044856997 305851670966737695910687)
                    ·
                      rfl

theorem cell22_893466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_893466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893466 prefixEnd_893466 := by exact prefixLift 893466
  have htrace : WordTrace (prefixWord ++ tailWord_893466) baseStart_893466 baseEnd_893466 := by
    simpa [prefixWord, tailWord_893466, baseEnd_893466] using wordTrace_append hprefix tailTrace_893466
  have hstable : (prefixWord ++ tailWord_893466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893466).length < 2 ^ (prefixWord ++ tailWord_893466).sum := by decide
  have hdescent : baseEnd_893466 < baseStart_893466 := by decide
  rcases family_descends (prefixWord ++ tailWord_893466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893571 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 6]
def baseStart_893571 : Nat := 118140960795 + 893571 * 2 ^ 59
def prefixEnd_893571 : Nat := 4983230072969 + 3 ^ 40 * 893571 * 2
def baseEnd_893571 : Nat := 101962538204184140678455

theorem tailTrace_893571 : CollatzResearch.WordTrace tailWord_893571 prefixEnd_893571 101962538204184140678455 := by
  unfold tailWord_893571
  simp only [CollatzResearch.WordTrace]
  refine ⟨32591211845752351622024567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21727474563834901081349711 32591211845752351622024567)
  ·
    refine ⟨48886817768628527433036851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32591211845752351622024567 48886817768628527433036851)
    ·
      refine ⟨73330226652942791149555277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48886817768628527433036851 73330226652942791149555277)
      ·
        refine ⟨27498834994853546681083229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73330226652942791149555277 27498834994853546681083229)
        ·
          refine ⟨10312063123070080005406211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27498834994853546681083229 10312063123070080005406211)
          ·
            refine ⟨15468094684605120008109317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10312063123070080005406211 15468094684605120008109317)
            ·
              refine ⟨2900267753363460001520497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15468094684605120008109317 2900267753363460001520497)
              ·
                refine ⟨2175200815022595001140373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2900267753363460001520497 2175200815022595001140373)
                ·
                  refine ⟨101962538204184140678455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2175200815022595001140373 101962538204184140678455)
                  ·
                    rfl

theorem cell22_893571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 6].length) (baseStart_893571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893571 prefixEnd_893571 := by exact prefixLift 893571
  have htrace : WordTrace (prefixWord ++ tailWord_893571) baseStart_893571 baseEnd_893571 := by
    simpa [prefixWord, tailWord_893571, baseEnd_893571] using wordTrace_append hprefix tailTrace_893571
  have hstable : (prefixWord ++ tailWord_893571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893571).length < 2 ^ (prefixWord ++ tailWord_893571).sum := by decide
  have hdescent : baseEnd_893571 < baseStart_893571 := by decide
  rcases family_descends (prefixWord ++ tailWord_893571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893573 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_893573 : Nat := 118140960795 + 893573 * 2 ^ 59
def prefixEnd_893573 : Nat := 4983230072969 + 3 ^ 40 * 893573 * 2
def baseEnd_893573 : Nat := 305888299253425083485359

theorem tailTrace_893573 : CollatzResearch.WordTrace tailWord_893573 prefixEnd_893573 305888299253425083485359 := by
  unfold tailWord_893573
  simp only [CollatzResearch.WordTrace]
  refine ⟨32591284791745105963597373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21727523194496737309064915 32591284791745105963597373)
  ·
    refine ⟨12221731796904414736349015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32591284791745105963597373 12221731796904414736349015)
    ·
      refine ⟨18332597695356622104523523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12221731796904414736349015 18332597695356622104523523)
      ·
        refine ⟨27498896543034933156785285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18332597695356622104523523 27498896543034933156785285)
        ·
          refine ⟨5156043101819049966897241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27498896543034933156785285 5156043101819049966897241)
          ·
            refine ⟨3867032326364287475172931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5156043101819049966897241 3867032326364287475172931)
            ·
              refine ⟨5800548489546431212759397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867032326364287475172931 5800548489546431212759397)
              ·
                refine ⟨1087602841789955852392387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5800548489546431212759397 1087602841789955852392387)
                ·
                  refine ⟨1631404262684933778588581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087602841789955852392387 1631404262684933778588581)
                  ·
                    refine ⟨305888299253425083485359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631404262684933778588581 305888299253425083485359)
                    ·
                      rfl

theorem cell22_893573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_893573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893573 prefixEnd_893573 := by exact prefixLift 893573
  have htrace : WordTrace (prefixWord ++ tailWord_893573) baseStart_893573 baseEnd_893573 := by
    simpa [prefixWord, tailWord_893573, baseEnd_893573] using wordTrace_append hprefix tailTrace_893573
  have hstable : (prefixWord ++ tailWord_893573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893573).length < 2 ^ (prefixWord ++ tailWord_893573).sum := by decide
  have hdescent : baseEnd_893573 < baseStart_893573 := by decide
  rcases family_descends (prefixWord ++ tailWord_893573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893684 : List Nat := [2, 6, 1, 1, 2, 1, 3, 6]
def baseStart_893684 : Nat := 118140960795 + 893684 * 2 ^ 59
def prefixEnd_893684 : Nat := 4983230072969 + 3 ^ 40 * 893684 * 2
def baseEnd_893684 : Nat := 33991810757984199328891

theorem tailTrace_893684 : CollatzResearch.WordTrace tailWord_893684 prefixEnd_893684 33991810757984199328891 := by
  unfold tailWord_893684
  simp only [CollatzResearch.WordTrace]
  refine ⟨16297666647171485960444053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21730222196228647947258737 16297666647171485960444053)
  ·
    refine ⟨763953124086163404395815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16297666647171485960444053 763953124086163404395815)
    ·
      refine ⟨1145929686129245106593723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763953124086163404395815 1145929686129245106593723)
      ·
        refine ⟨1718894529193867659890585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145929686129245106593723 1718894529193867659890585)
        ·
          refine ⟨1289170896895400744917939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718894529193867659890585 1289170896895400744917939)
          ·
            refine ⟨1933756345343101117376909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289170896895400744917939 1933756345343101117376909)
            ·
              refine ⟨725158629503662919016341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1933756345343101117376909 725158629503662919016341)
              ·
                refine ⟨33991810757984199328891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 725158629503662919016341 33991810757984199328891)
                ·
                  rfl

theorem cell22_893684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 6].length) (baseStart_893684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893684 prefixEnd_893684 := by exact prefixLift 893684
  have htrace : WordTrace (prefixWord ++ tailWord_893684) baseStart_893684 baseEnd_893684 := by
    simpa [prefixWord, tailWord_893684, baseEnd_893684] using wordTrace_append hprefix tailTrace_893684
  have hstable : (prefixWord ++ tailWord_893684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893684).length < 2 ^ (prefixWord ++ tailWord_893684).sum := by decide
  have hdescent : baseEnd_893684 < baseStart_893684 := by decide
  rcases family_descends (prefixWord ++ tailWord_893684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893742 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_893742 : Nat := 118140960795 + 893742 * 2 ^ 59
def prefixEnd_893742 : Nat := 4983230072969 + 3 ^ 40 * 893742 * 2
def baseEnd_893742 : Nat := 305946151407164976009841

theorem tailTrace_893742 : CollatzResearch.WordTrace tailWord_893742 prefixEnd_893742 305946151407164976009841 := by
  unfold tailWord_893742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074681091016605978312435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21731632485421898550999653 4074681091016605978312435)
  ·
    refine ⟨6112021636524908967468653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4074681091016605978312435 6112021636524908967468653)
    ·
      refine ⟨2292008113696840862800745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6112021636524908967468653 2292008113696840862800745)
      ·
        refine ⟨1719006085272630647100559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2292008113696840862800745 1719006085272630647100559)
        ·
          refine ⟨2578509127908945970650839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719006085272630647100559 2578509127908945970650839)
          ·
            refine ⟨3867763691863418955976259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578509127908945970650839 3867763691863418955976259)
            ·
              refine ⟨5801645537795128433964389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3867763691863418955976259 5801645537795128433964389)
              ·
                refine ⟨1087808538336586581368323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5801645537795128433964389 1087808538336586581368323)
                ·
                  refine ⟨1631712807504879872052485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087808538336586581368323 1631712807504879872052485)
                  ·
                    refine ⟨305946151407164976009841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631712807504879872052485 305946151407164976009841)
                    ·
                      rfl

theorem cell22_893742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_893742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893742 prefixEnd_893742 := by exact prefixLift 893742
  have htrace : WordTrace (prefixWord ++ tailWord_893742) baseStart_893742 baseEnd_893742 := by
    simpa [prefixWord, tailWord_893742, baseEnd_893742] using wordTrace_append hprefix tailTrace_893742
  have hstable : (prefixWord ++ tailWord_893742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893742).length < 2 ^ (prefixWord ++ tailWord_893742).sum := by decide
  have hdescent : baseEnd_893742 < baseStart_893742 := by decide
  rcases family_descends (prefixWord ++ tailWord_893742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893845 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_893845 : Nat := 118140960795 + 893845 * 2 ^ 59
def prefixEnd_893845 : Nat := 4983230072969 + 3 ^ 40 * 893845 * 2
def baseEnd_893845 : Nat := 305981410412107040684525

theorem tailTrace_893845 : CollatzResearch.WordTrace tailWord_893845 prefixEnd_893845 305981410412107040684525 := by
  unfold tailWord_893845
  simp only [CollatzResearch.WordTrace]
  refine ⟨32601205446759696417498989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21734136964506464278332659 32601205446759696417498989)
  ·
    refine ⟨12225452042534886156562121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32601205446759696417498989 12225452042534886156562121)
    ·
      refine ⟨9169089031901164617421591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12225452042534886156562121 9169089031901164617421591)
      ·
        refine ⟨13753633547851746926132387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9169089031901164617421591 13753633547851746926132387)
        ·
          refine ⟨20630450321777620389198581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13753633547851746926132387 20630450321777620389198581)
          ·
            refine ⟨1934104717666651911487367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20630450321777620389198581 1934104717666651911487367)
            ·
              refine ⟨2901157076499977867231051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934104717666651911487367 2901157076499977867231051)
              ·
                refine ⟨4351735614749966800846577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901157076499977867231051 4351735614749966800846577)
                ·
                  refine ⟨3263801711062475100634933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4351735614749966800846577 3263801711062475100634933)
                  ·
                    refine ⟨305981410412107040684525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3263801711062475100634933 305981410412107040684525)
                    ·
                      rfl

theorem cell22_893845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_893845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893845 prefixEnd_893845 := by exact prefixLift 893845
  have htrace : WordTrace (prefixWord ++ tailWord_893845) baseStart_893845 baseEnd_893845 := by
    simpa [prefixWord, tailWord_893845, baseEnd_893845] using wordTrace_append hprefix tailTrace_893845
  have hstable : (prefixWord ++ tailWord_893845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893845).length < 2 ^ (prefixWord ++ tailWord_893845).sum := by decide
  have hdescent : baseEnd_893845 < baseStart_893845 := by decide
  rcases family_descends (prefixWord ++ tailWord_893845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893860 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_893860 : Nat := 118140960795 + 893860 * 2 ^ 59
def prefixEnd_893860 : Nat := 4983230072969 + 3 ^ 40 * 893860 * 2
def baseEnd_893860 : Nat := 305986545218652001559479

theorem tailTrace_893860 : CollatzResearch.WordTrace tailWord_893860 prefixEnd_893860 305986545218652001559479 := by
  unfold tailWord_893860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16300876270852676989647517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21734501694470235986196689 16300876270852676989647517)
  ·
    refine ⟨6112828601569753871117819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16300876270852676989647517 6112828601569753871117819)
    ·
      refine ⟨9169242902354630806676729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6112828601569753871117819 9169242902354630806676729)
      ·
        refine ⟨6876932176765973105007547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9169242902354630806676729 6876932176765973105007547)
        ·
          refine ⟨10315398265148959657511321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6876932176765973105007547 10315398265148959657511321)
          ·
            refine ⟨7736548698861719743133491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10315398265148959657511321 7736548698861719743133491)
            ·
              refine ⟨11604823048292579614700237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7736548698861719743133491 11604823048292579614700237)
              ·
                refine ⟨4351808643109717355512589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11604823048292579614700237 4351808643109717355512589)
                ·
                  refine ⟨1631928241166144008317221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4351808643109717355512589 1631928241166144008317221)
                  ·
                    refine ⟨305986545218652001559479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631928241166144008317221 305986545218652001559479)
                    ·
                      rfl

theorem cell22_893860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_893860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893860 prefixEnd_893860 := by exact prefixLift 893860
  have htrace : WordTrace (prefixWord ++ tailWord_893860) baseStart_893860 baseEnd_893860 := by
    simpa [prefixWord, tailWord_893860, baseEnd_893860] using wordTrace_append hprefix tailTrace_893860
  have hstable : (prefixWord ++ tailWord_893860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893860).length < 2 ^ (prefixWord ++ tailWord_893860).sum := by decide
  have hdescent : baseEnd_893860 < baseStart_893860 := by decide
  rcases family_descends (prefixWord ++ tailWord_893860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_893877 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_893877 : Nat := 118140960795 + 893877 * 2 ^ 59
def prefixEnd_893877 : Nat := 4983230072969 + 3 ^ 40 * 893877 * 2
def baseEnd_893877 : Nat := 305992364666069623884427

theorem tailTrace_893877 : CollatzResearch.WordTrace tailWord_893877 prefixEnd_893877 305992364666069623884427 := by
  unfold tailWord_893877
  simp only [CollatzResearch.WordTrace]
  refine ⟨32602372582643765882663885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21734915055095843921775923 32602372582643765882663885)
  ·
    refine ⟨12225889718491412205998957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32602372582643765882663885 12225889718491412205998957)
    ·
      refine ⟨4584708644434279577249609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12225889718491412205998957 4584708644434279577249609)
      ·
        refine ⟨3438531483325709682937207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4584708644434279577249609 3438531483325709682937207)
        ·
          refine ⟨5157797224988564524405811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438531483325709682937207 5157797224988564524405811)
          ·
            refine ⟨7736695837482846786608717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157797224988564524405811 7736695837482846786608717)
            ·
              refine ⟨2901260939056067544978269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7736695837482846786608717 2901260939056067544978269)
              ·
                refine ⟨1087972852146025329366851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2901260939056067544978269 1087972852146025329366851)
                ·
                  refine ⟨1631959278219037994050277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087972852146025329366851 1631959278219037994050277)
                  ·
                    refine ⟨305992364666069623884427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631959278219037994050277 305992364666069623884427)
                    ·
                      rfl

theorem cell22_893877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_893877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_893877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_893877 prefixEnd_893877 := by exact prefixLift 893877
  have htrace : WordTrace (prefixWord ++ tailWord_893877) baseStart_893877 baseEnd_893877 := by
    simpa [prefixWord, tailWord_893877, baseEnd_893877] using wordTrace_append hprefix tailTrace_893877
  have hstable : (prefixWord ++ tailWord_893877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_893877).length < 2 ^ (prefixWord ++ tailWord_893877).sum := by decide
  have hdescent : baseEnd_893877 < baseStart_893877 := by decide
  rcases family_descends (prefixWord ++ tailWord_893877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894012 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_894012 : Nat := 118140960795 + 894012 * 2 ^ 59
def prefixEnd_894012 : Nat := 4983230072969 + 3 ^ 40 * 894012 * 2
def baseEnd_894012 : Nat := 306038577924974271759013

theorem tailTrace_894012 : CollatzResearch.WordTrace tailWord_894012 prefixEnd_894012 306038577924974271759013 := by
  unfold tailWord_894012
  simp only [CollatzResearch.WordTrace]
  refine ⟨16303648218577341969414145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21738197624769789292552193 16303648218577341969414145)
  ·
    refine ⟨12227736163933006477060609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16303648218577341969414145 12227736163933006477060609)
    ·
      refine ⟨9170802122949754857795457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12227736163933006477060609 9170802122949754857795457)
      ·
        refine ⟨6878101592212316143346593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9170802122949754857795457 6878101592212316143346593)
        ·
          refine ⟨5158576194159237107509945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6878101592212316143346593 5158576194159237107509945)
          ·
            refine ⟨3868932145619427830632459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5158576194159237107509945 3868932145619427830632459)
            ·
              refine ⟨5803398218429141745948689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868932145619427830632459 5803398218429141745948689)
              ·
                refine ⟨4352548663821856309461517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5803398218429141745948689 4352548663821856309461517)
                ·
                  refine ⟨1632205748933196116048069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4352548663821856309461517 1632205748933196116048069)
                  ·
                    refine ⟨306038577924974271759013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1632205748933196116048069 306038577924974271759013)
                    ·
                      rfl

theorem cell22_894012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_894012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894012 prefixEnd_894012 := by exact prefixLift 894012
  have htrace : WordTrace (prefixWord ++ tailWord_894012) baseStart_894012 baseEnd_894012 := by
    simpa [prefixWord, tailWord_894012, baseEnd_894012] using wordTrace_append hprefix tailTrace_894012
  have hstable : (prefixWord ++ tailWord_894012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894012).length < 2 ^ (prefixWord ++ tailWord_894012).sum := by decide
  have hdescent : baseEnd_894012 < baseStart_894012 := by decide
  rcases family_descends (prefixWord ++ tailWord_894012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894014 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_894014 : Nat := 118140960795 + 894014 * 2 ^ 59
def prefixEnd_894014 : Nat := 4983230072969 + 3 ^ 40 * 894014 * 2
def baseEnd_894014 : Nat := 306039262565846933209007

theorem tailTrace_894014 : CollatzResearch.WordTrace tailWord_894014 prefixEnd_894014 306039262565846933209007 := by
  unfold tailWord_894014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075921172893429785050137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21738246255431625520267397 4075921172893429785050137)
  ·
    refine ⟨3056940879670072338787603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4075921172893429785050137 3056940879670072338787603)
    ·
      refine ⟨4585411319505108508181405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3056940879670072338787603 4585411319505108508181405)
      ·
        refine ⟨1719529244814415690568027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4585411319505108508181405 1719529244814415690568027)
        ·
          refine ⟨2579293867221623535852041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719529244814415690568027 2579293867221623535852041)
          ·
            refine ⟨1934470400416217651889031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2579293867221623535852041 1934470400416217651889031)
            ·
              refine ⟨2901705600624326477833547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934470400416217651889031 2901705600624326477833547)
              ·
                refine ⟨4352558400936489716750321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901705600624326477833547 4352558400936489716750321)
                ·
                  refine ⟨3264418800702367287562741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4352558400936489716750321 3264418800702367287562741)
                  ·
                    refine ⟨306039262565846933209007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3264418800702367287562741 306039262565846933209007)
                    ·
                      rfl

theorem cell22_894014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_894014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894014 prefixEnd_894014 := by exact prefixLift 894014
  have htrace : WordTrace (prefixWord ++ tailWord_894014) baseStart_894014 baseEnd_894014 := by
    simpa [prefixWord, tailWord_894014, baseEnd_894014] using wordTrace_append hprefix tailTrace_894014
  have hstable : (prefixWord ++ tailWord_894014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894014).length < 2 ^ (prefixWord ++ tailWord_894014).sum := by decide
  have hdescent : baseEnd_894014 < baseStart_894014 := by decide
  rcases family_descends (prefixWord ++ tailWord_894014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894029 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_894029 : Nat := 118140960795 + 894029 * 2 ^ 59
def prefixEnd_894029 : Nat := 4983230072969 + 3 ^ 40 * 894029 * 2
def baseEnd_894029 : Nat := 306044397372391894083961

theorem tailTrace_894029 : CollatzResearch.WordTrace tailWord_894029 prefixEnd_894029 306044397372391894083961 := by
  unfold tailWord_894029
  simp only [CollatzResearch.WordTrace]
  refine ⟨32607916478093095842197141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21738610985395397228131427 32607916478093095842197141)
  ·
    refine ⟨1528496084910613867602991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32607916478093095842197141 1528496084910613867602991)
    ·
      refine ⟨2292744127365920801404487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528496084910613867602991 2292744127365920801404487)
      ·
        refine ⟨3439116191048881202106731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292744127365920801404487 3439116191048881202106731)
        ·
          refine ⟨5158674286573321803160097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3439116191048881202106731 5158674286573321803160097)
          ·
            refine ⟨3869005714929991352370073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5158674286573321803160097 3869005714929991352370073)
            ·
              refine ⟨2901754286197493514277555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869005714929991352370073 2901754286197493514277555)
              ·
                refine ⟨4352631429296240271416333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2901754286197493514277555 4352631429296240271416333)
                ·
                  refine ⟨1632236785986090101781125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4352631429296240271416333 1632236785986090101781125)
                  ·
                    refine ⟨306044397372391894083961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1632236785986090101781125 306044397372391894083961)
                    ·
                      rfl

theorem cell22_894029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_894029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894029 prefixEnd_894029 := by exact prefixLift 894029
  have htrace : WordTrace (prefixWord ++ tailWord_894029) baseStart_894029 baseEnd_894029 := by
    simpa [prefixWord, tailWord_894029, baseEnd_894029] using wordTrace_append hprefix tailTrace_894029
  have hstable : (prefixWord ++ tailWord_894029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894029).length < 2 ^ (prefixWord ++ tailWord_894029).sum := by decide
  have hdescent : baseEnd_894029 < baseStart_894029 := by decide
  rcases family_descends (prefixWord ++ tailWord_894029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894076 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_894076 : Nat := 118140960795 + 894076 * 2 ^ 59
def prefixEnd_894076 : Nat := 4983230072969 + 3 ^ 40 * 894076 * 2
def baseEnd_894076 : Nat := 306060486432899438158817

theorem tailTrace_894076 : CollatzResearch.WordTrace tailWord_894076 prefixEnd_894076 306060486432899438158817 := by
  unfold tailWord_894076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16304815354461411434579041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21739753805948548579438721 16304815354461411434579041)
  ·
    refine ⟨12228611515846058575934281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16304815354461411434579041 12228611515846058575934281)
    ·
      refine ⟨9171458636884543931950711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12228611515846058575934281 9171458636884543931950711)
      ·
        refine ⟨13757187955326815897926067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9171458636884543931950711 13757187955326815897926067)
        ·
          refine ⟨20635781932990223846889101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757187955326815897926067 20635781932990223846889101)
          ·
            refine ⟨7738418224871333942583413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20635781932990223846889101 7738418224871333942583413)
            ·
              refine ⟨725476708581687557117195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7738418224871333942583413 725476708581687557117195)
              ·
                refine ⟨1088215062872531335675793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725476708581687557117195 1088215062872531335675793)
                ·
                  refine ⟨816161297154398501756845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1088215062872531335675793 816161297154398501756845)
                  ·
                    refine ⟨306060486432899438158817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816161297154398501756845 306060486432899438158817)
                    ·
                      rfl

theorem cell22_894076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_894076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894076 prefixEnd_894076 := by exact prefixLift 894076
  have htrace : WordTrace (prefixWord ++ tailWord_894076) baseStart_894076 baseEnd_894076 := by
    simpa [prefixWord, tailWord_894076, baseEnd_894076] using wordTrace_append hprefix tailTrace_894076
  have hstable : (prefixWord ++ tailWord_894076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894076).length < 2 ^ (prefixWord ++ tailWord_894076).sum := by decide
  have hdescent : baseEnd_894076 < baseStart_894076 := by decide
  rcases family_descends (prefixWord ++ tailWord_894076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894089 : List Nat := [1, 2, 1, 1, 4, 5, 2, 6]
def baseStart_894089 : Nat := 118140960795 + 894089 * 2 ^ 59
def prefixEnd_894089 : Nat := 4983230072969 + 3 ^ 40 * 894089 * 2
def baseEnd_894089 : Nat := 34007215177619081953753

theorem tailTrace_894089 : CollatzResearch.WordTrace tailWord_894089 prefixEnd_894089 34007215177619081953753 := by
  unfold tailWord_894089
  simp only [CollatzResearch.WordTrace]
  refine ⟨32610104857875726089381321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21740069905250484059587547 32610104857875726089381321)
  ·
    refine ⟨24457578643406794567035991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32610104857875726089381321 24457578643406794567035991)
    ·
      refine ⟨36686367965110191850553987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24457578643406794567035991 36686367965110191850553987)
      ·
        refine ⟨55029551947665287775830981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36686367965110191850553987 55029551947665287775830981)
        ·
          refine ⟨10318040990187241457968309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55029551947665287775830981 10318040990187241457968309)
          ·
            refine ⟨967316342830053886684529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10318040990187241457968309 967316342830053886684529)
            ·
              refine ⟨725487257122540415013397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967316342830053886684529 725487257122540415013397)
              ·
                refine ⟨34007215177619081953753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 725487257122540415013397 34007215177619081953753)
                ·
                  rfl

theorem cell22_894089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 6].length) (baseStart_894089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894089 prefixEnd_894089 := by exact prefixLift 894089
  have htrace : WordTrace (prefixWord ++ tailWord_894089) baseStart_894089 baseEnd_894089 := by
    simpa [prefixWord, tailWord_894089, baseEnd_894089] using wordTrace_append hprefix tailTrace_894089
  have hstable : (prefixWord ++ tailWord_894089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894089).length < 2 ^ (prefixWord ++ tailWord_894089).sum := by decide
  have hdescent : baseEnd_894089 < baseStart_894089 := by decide
  rcases family_descends (prefixWord ++ tailWord_894089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894117 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 7]
def baseStart_894117 : Nat := 118140960795 + 894117 * 2 ^ 59
def prefixEnd_894117 : Nat := 4983230072969 + 3 ^ 40 * 894117 * 2
def baseEnd_894117 : Nat := 102024840523596332627897

theorem tailTrace_894117 : CollatzResearch.WordTrace tailWord_894117 prefixEnd_894117 102024840523596332627897 := by
  unfold tailWord_894117
  simp only [CollatzResearch.WordTrace]
  refine ⟨32611126101774286871400605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21740750734516191247600403 32611126101774286871400605)
  ·
    refine ⟨12229172288165357576775227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32611126101774286871400605 12229172288165357576775227)
    ·
      refine ⟨18343758432248036365162841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12229172288165357576775227 18343758432248036365162841)
      ·
        refine ⟨13757818824186027273872131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18343758432248036365162841 13757818824186027273872131)
        ·
          refine ⟨20636728236279040910808197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13757818824186027273872131 20636728236279040910808197)
          ·
            refine ⟨3869386544302320170776537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20636728236279040910808197 3869386544302320170776537)
            ·
              refine ⟨2902039908226740128082403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3869386544302320170776537 2902039908226740128082403)
              ·
                refine ⟨4353059862340110192123605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902039908226740128082403 4353059862340110192123605)
                ·
                  refine ⟨102024840523596332627897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4353059862340110192123605 102024840523596332627897)
                  ·
                    rfl

theorem cell22_894117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_894117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894117 prefixEnd_894117 := by exact prefixLift 894117
  have htrace : WordTrace (prefixWord ++ tailWord_894117) baseStart_894117 baseEnd_894117 := by
    simpa [prefixWord, tailWord_894117, baseEnd_894117] using wordTrace_append hprefix tailTrace_894117
  have hstable : (prefixWord ++ tailWord_894117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894117).length < 2 ^ (prefixWord ++ tailWord_894117).sum := by decide
  have hdescent : baseEnd_894117 < baseStart_894117 := by decide
  rcases family_descends (prefixWord ++ tailWord_894117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894209 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_894209 : Nat := 118140960795 + 894209 * 2 ^ 59
def prefixEnd_894209 : Nat := 4983230072969 + 3 ^ 40 * 894209 * 2
def baseEnd_894209 : Nat := 306106015050931424583409

theorem tailTrace_894209 : CollatzResearch.WordTrace tailWord_894209 prefixEnd_894209 306106015050931424583409 := by
  unfold tailWord_894209
  simp only [CollatzResearch.WordTrace]
  refine ⟨32614481617440986583749681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21742987744960657722499787 32614481617440986583749681)
  ·
    refine ⟨24460861213080739937812261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32614481617440986583749681 24460861213080739937812261)
    ·
      refine ⟨4586411477452638738339799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24460861213080739937812261 4586411477452638738339799)
      ·
        refine ⟨6879617216178958107509699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586411477452638738339799 6879617216178958107509699)
        ·
          refine ⟨10319425824268437161264549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879617216178958107509699 10319425824268437161264549)
          ·
            refine ⟨1934892342050331967737103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10319425824268437161264549 1934892342050331967737103)
            ·
              refine ⟨2902338513075497951605655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1934892342050331967737103 2902338513075497951605655)
              ·
                refine ⟨4353507769613246927408483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902338513075497951605655 4353507769613246927408483)
                ·
                  refine ⟨6530261654419870391112725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4353507769613246927408483 6530261654419870391112725)
                  ·
                    refine ⟨306106015050931424583409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6530261654419870391112725 306106015050931424583409)
                    ·
                      rfl

theorem cell22_894209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_894209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894209 prefixEnd_894209 := by exact prefixLift 894209
  have htrace : WordTrace (prefixWord ++ tailWord_894209) baseStart_894209 baseEnd_894209 := by
    simpa [prefixWord, tailWord_894209, baseEnd_894209] using wordTrace_append hprefix tailTrace_894209
  have hstable : (prefixWord ++ tailWord_894209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894209).length < 2 ^ (prefixWord ++ tailWord_894209).sum := by decide
  have hdescent : baseEnd_894209 < baseStart_894209 := by decide
  rcases family_descends (prefixWord ++ tailWord_894209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894316 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_894316 : Nat := 118140960795 + 894316 * 2 ^ 59
def prefixEnd_894316 : Nat := 4983230072969 + 3 ^ 40 * 894316 * 2
def baseEnd_894316 : Nat := 306142643337618812158081

theorem tailTrace_894316 : CollatzResearch.WordTrace tailWord_894316 prefixEnd_894316 306142643337618812158081 := by
  unfold tailWord_894316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309192114026671928947401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21745589485368895905263201 16309192114026671928947401)
  ·
    refine ⟨12231894085520003946710551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16309192114026671928947401 12231894085520003946710551)
    ·
      refine ⟨18347841128280005920065827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12231894085520003946710551 18347841128280005920065827)
      ·
        refine ⟨27521761692420008880098741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18347841128280005920065827 27521761692420008880098741)
        ·
          refine ⟨2580165158664375832509257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27521761692420008880098741 2580165158664375832509257)
          ·
            refine ⟨1935123868998281874381943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580165158664375832509257 1935123868998281874381943)
            ·
              refine ⟨2902685803497422811572915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935123868998281874381943 2902685803497422811572915)
              ·
                refine ⟨4354028705246134217359373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902685803497422811572915 4354028705246134217359373)
                ·
                  refine ⟨1632760764467300331509765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4354028705246134217359373 1632760764467300331509765)
                  ·
                    refine ⟨306142643337618812158081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1632760764467300331509765 306142643337618812158081)
                    ·
                      rfl

theorem cell22_894316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_894316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894316 prefixEnd_894316 := by exact prefixLift 894316
  have htrace : WordTrace (prefixWord ++ tailWord_894316) baseStart_894316 baseEnd_894316 := by
    simpa [prefixWord, tailWord_894316, baseEnd_894316] using wordTrace_append hprefix tailTrace_894316
  have hstable : (prefixWord ++ tailWord_894316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894316).length < 2 ^ (prefixWord ++ tailWord_894316).sum := by decide
  have hdescent : baseEnd_894316 < baseStart_894316 := by decide
  rcases family_descends (prefixWord ++ tailWord_894316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894329 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_894329 : Nat := 118140960795 + 894329 * 2 ^ 59
def prefixEnd_894329 : Nat := 4983230072969 + 3 ^ 40 * 894329 * 2
def baseEnd_894329 : Nat := 306147093503291111583041

theorem tailTrace_894329 : CollatzResearch.WordTrace tailWord_894329 prefixEnd_894329 306147093503291111583041 := by
  unfold tailWord_894329
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618858377006247078118041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21745905584670831385412027 32618858377006247078118041)
  ·
    refine ⟨24464143782754685308588531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32618858377006247078118041 24464143782754685308588531)
    ·
      refine ⟨36696215674132027962882797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24464143782754685308588531 36696215674132027962882797)
      ·
        refine ⟨13761080877799510486081049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36696215674132027962882797 13761080877799510486081049)
        ·
          refine ⟨10320810658349632864560787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13761080877799510486081049 10320810658349632864560787)
          ·
            refine ⟨15481215987524449296841181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10320810658349632864560787 15481215987524449296841181)
            ·
              refine ⟨5805455995321668486315443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15481215987524449296841181 5805455995321668486315443)
              ·
                refine ⟨8708183992982502729473165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805455995321668486315443 8708183992982502729473165)
                ·
                  refine ⟨3265568997368438523552437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8708183992982502729473165 3265568997368438523552437)
                  ·
                    refine ⟨306147093503291111583041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3265568997368438523552437 306147093503291111583041)
                    ·
                      rfl

theorem cell22_894329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_894329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894329 prefixEnd_894329 := by exact prefixLift 894329
  have htrace : WordTrace (prefixWord ++ tailWord_894329) baseStart_894329 baseEnd_894329 := by
    simpa [prefixWord, tailWord_894329, baseEnd_894329] using wordTrace_append hprefix tailTrace_894329
  have hstable : (prefixWord ++ tailWord_894329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894329).length < 2 ^ (prefixWord ++ tailWord_894329).sum := by decide
  have hdescent : baseEnd_894329 < baseStart_894329 := by decide
  rcases family_descends (prefixWord ++ tailWord_894329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894331 : List Nat := [1, 1, 1, 1, 1, 6, 2, 5, 4]
def baseStart_894331 : Nat := 118140960795 + 894331 * 2 ^ 59
def prefixEnd_894331 : Nat := 4983230072969 + 3 ^ 40 * 894331 * 2
def baseEnd_894331 : Nat := 102049259381387924344345

theorem tailTrace_894331 : CollatzResearch.WordTrace tailWord_894331 prefixEnd_894331 102049259381387924344345 := by
  unfold tailWord_894331
  simp only [CollatzResearch.WordTrace]
  refine ⟨32618931322999001419690847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21745954215332667613127231 32618931322999001419690847)
  ·
    refine ⟨48928396984498502129536271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32618931322999001419690847 48928396984498502129536271)
    ·
      refine ⟨73392595476747753194304407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48928396984498502129536271 73392595476747753194304407)
      ·
        refine ⟨110088893215121629791456611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73392595476747753194304407 110088893215121629791456611)
        ·
          refine ⟨165133339822682444687184917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110088893215121629791456611 165133339822682444687184917)
          ·
            refine ⟨7740625304188239594711793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165133339822682444687184917 7740625304188239594711793)
            ·
              refine ⟨5805468978141179696033845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7740625304188239594711793 5805468978141179696033845)
              ·
                refine ⟨544262716700735596503173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5805468978141179696033845 544262716700735596503173)
                ·
                  refine ⟨102049259381387924344345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544262716700735596503173 102049259381387924344345)
                  ·
                    rfl

theorem cell22_894331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 4].length) (baseStart_894331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894331 prefixEnd_894331 := by exact prefixLift 894331
  have htrace : WordTrace (prefixWord ++ tailWord_894331) baseStart_894331 baseEnd_894331 := by
    simpa [prefixWord, tailWord_894331, baseEnd_894331] using wordTrace_append hprefix tailTrace_894331
  have hstable : (prefixWord ++ tailWord_894331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894331).length < 2 ^ (prefixWord ++ tailWord_894331).sum := by decide
  have hdescent : baseEnd_894331 < baseStart_894331 := by decide
  rcases family_descends (prefixWord ++ tailWord_894331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894333 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_894333 : Nat := 118140960795 + 894333 * 2 ^ 59
def prefixEnd_894333 : Nat := 4983230072969 + 3 ^ 40 * 894333 * 2
def baseEnd_894333 : Nat := 306148462785036434483029

theorem tailTrace_894333 : CollatzResearch.WordTrace tailWord_894333 prefixEnd_894333 306148462785036434483029 := by
  unfold tailWord_894333
  simp only [CollatzResearch.WordTrace]
  refine ⟨32619004268991755761263653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21746002845994503840842435 32619004268991755761263653)
  ·
    refine ⟨6116063300435954205236935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32619004268991755761263653 6116063300435954205236935)
    ·
      refine ⟨9174094950653931307855403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116063300435954205236935 9174094950653931307855403)
      ·
        refine ⟨13761142425980896961783105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174094950653931307855403 13761142425980896961783105)
        ·
          refine ⟨10320856819485672721337329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13761142425980896961783105 10320856819485672721337329)
          ·
            refine ⟨7740642614614254541002997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10320856819485672721337329 7740642614614254541002997)
            ·
              refine ⟨725685245120086363219031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7740642614614254541002997 725685245120086363219031)
              ·
                refine ⟨1088527867680129544828547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725685245120086363219031 1088527867680129544828547)
                ·
                  refine ⟨1632791801520194317242821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088527867680129544828547 1632791801520194317242821)
                  ·
                    refine ⟨306148462785036434483029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1632791801520194317242821 306148462785036434483029)
                    ·
                      rfl

theorem cell22_894333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_894333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894333 prefixEnd_894333 := by exact prefixLift 894333
  have htrace : WordTrace (prefixWord ++ tailWord_894333) baseStart_894333 baseEnd_894333 := by
    simpa [prefixWord, tailWord_894333, baseEnd_894333] using wordTrace_append hprefix tailTrace_894333
  have hstable : (prefixWord ++ tailWord_894333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894333).length < 2 ^ (prefixWord ++ tailWord_894333).sum := by decide
  have hdescent : baseEnd_894333 < baseStart_894333 := by decide
  rcases family_descends (prefixWord ++ tailWord_894333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894391 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 5, 3]
def baseStart_894391 : Nat := 118140960795 + 894391 * 2 ^ 59
def prefixEnd_894391 : Nat := 4983230072969 + 3 ^ 40 * 894391 * 2
def baseEnd_894391 : Nat := 306168317370343616532851

theorem tailTrace_894391 : CollatzResearch.WordTrace tailWord_894391 prefixEnd_894391 306168317370343616532851 := by
  unfold tailWord_894391
  simp only [CollatzResearch.WordTrace]
  refine ⟨32621119702781631666875027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21747413135187754444583351 32621119702781631666875027)
  ·
    refine ⟨48931679554172447500312541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32621119702781631666875027 48931679554172447500312541)
    ·
      refine ⟨18349379832814667812617203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48931679554172447500312541 18349379832814667812617203)
      ·
        refine ⟨27524069749222001718925805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18349379832814667812617203 27524069749222001718925805)
        ·
          refine ⟨10321526155958250644597177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27524069749222001718925805 10321526155958250644597177)
          ·
            refine ⟨7741144616968687983447883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10321526155958250644597177 7741144616968687983447883)
            ·
              refine ⟨11611716925453031975171825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741144616968687983447883 11611716925453031975171825)
              ·
                refine ⟨8708787694089773981378869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11611716925453031975171825 8708787694089773981378869)
                ·
                  refine ⟨816448846320916310754269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8708787694089773981378869 816448846320916310754269)
                  ·
                    refine ⟨306168317370343616532851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816448846320916310754269 306168317370343616532851)
                    ·
                      rfl

theorem cell22_894391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_894391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894391 prefixEnd_894391 := by exact prefixLift 894391
  have htrace : WordTrace (prefixWord ++ tailWord_894391) baseStart_894391 baseEnd_894391 := by
    simpa [prefixWord, tailWord_894391, baseEnd_894391] using wordTrace_append hprefix tailTrace_894391
  have hstable : (prefixWord ++ tailWord_894391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894391).length < 2 ^ (prefixWord ++ tailWord_894391).sum := by decide
  have hdescent : baseEnd_894391 < baseStart_894391 := by decide
  rcases family_descends (prefixWord ++ tailWord_894391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894408 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 3, 3]
def baseStart_894408 : Nat := 118140960795 + 894408 * 2 ^ 59
def prefixEnd_894408 : Nat := 4983230072969 + 3 ^ 40 * 894408 * 2
def baseEnd_894408 : Nat := 306174136817761238857799

theorem tailTrace_894408 : CollatzResearch.WordTrace tailWord_894408 prefixEnd_894408 306174136817761238857799 := by
  unfold tailWord_894408
  simp only [CollatzResearch.WordTrace]
  refine ⟨16310869871860021785121939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21747826495813362380162585 16310869871860021785121939)
  ·
    refine ⟨24466304807790032677682909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16310869871860021785121939 24466304807790032677682909)
    ·
      refine ⟨9174864302921262254131091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24466304807790032677682909 9174864302921262254131091)
      ·
        refine ⟨13762296454381893381196637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9174864302921262254131091 13762296454381893381196637)
        ·
          refine ⟨5160861170393210017948739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13762296454381893381196637 5160861170393210017948739)
          ·
            refine ⟨7741291755589815026923109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160861170393210017948739 7741291755589815026923109)
            ·
              refine ⟨1451492204173090317548083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7741291755589815026923109 1451492204173090317548083)
              ·
                refine ⟨2177238306259635476322125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451492204173090317548083 2177238306259635476322125)
                ·
                  refine ⟨816464364847363303620797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2177238306259635476322125 816464364847363303620797)
                  ·
                    refine ⟨306174136817761238857799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816464364847363303620797 306174136817761238857799)
                    ·
                      rfl

theorem cell22_894408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_894408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894408 prefixEnd_894408 := by exact prefixLift 894408
  have htrace : WordTrace (prefixWord ++ tailWord_894408) baseStart_894408 baseEnd_894408 := by
    simpa [prefixWord, tailWord_894408, baseEnd_894408] using wordTrace_append hprefix tailTrace_894408
  have hstable : (prefixWord ++ tailWord_894408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894408).length < 2 ^ (prefixWord ++ tailWord_894408).sum := by decide
  have hdescent : baseEnd_894408 < baseStart_894408 := by decide
  rcases family_descends (prefixWord ++ tailWord_894408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894481 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_894481 : Nat := 118140960795 + 894481 * 2 ^ 59
def prefixEnd_894481 : Nat := 4983230072969 + 3 ^ 40 * 894481 * 2
def baseEnd_894481 : Nat := 306199126209613381782575

theorem tailTrace_894481 : CollatzResearch.WordTrace tailWord_894481 prefixEnd_894481 306199126209613381782575 := by
  unfold tailWord_894481
  simp only [CollatzResearch.WordTrace]
  refine ⟨32624402272455577037651297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21749601514970384691767531 32624402272455577037651297)
  ·
    refine ⟨24468301704341682778238473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32624402272455577037651297 24468301704341682778238473)
    ·
      refine ⟨18351226278256262083678855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24468301704341682778238473 18351226278256262083678855)
      ·
        refine ⟨27526839417384393125518283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18351226278256262083678855 27526839417384393125518283)
        ·
          refine ⟨41290259126076589688277425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27526839417384393125518283 41290259126076589688277425)
          ·
            refine ⟨30967694344557442266208069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41290259126076589688277425 30967694344557442266208069)
            ·
              refine ⟨5806442689604520424914013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30967694344557442266208069 5806442689604520424914013)
              ·
                refine ⟨2177416008601695159342755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5806442689604520424914013 2177416008601695159342755)
                ·
                  refine ⟨3266124012902542739014133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177416008601695159342755 3266124012902542739014133)
                  ·
                    refine ⟨306199126209613381782575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3266124012902542739014133 306199126209613381782575)
                    ·
                      rfl

theorem cell22_894481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_894481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894481 prefixEnd_894481 := by exact prefixLift 894481
  have htrace : WordTrace (prefixWord ++ tailWord_894481) baseStart_894481 baseEnd_894481 := by
    simpa [prefixWord, tailWord_894481, baseEnd_894481] using wordTrace_append hprefix tailTrace_894481
  have hstable : (prefixWord ++ tailWord_894481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894481).length < 2 ^ (prefixWord ++ tailWord_894481).sum := by decide
  have hdescent : baseEnd_894481 < baseStart_894481 := by decide
  rcases family_descends (prefixWord ++ tailWord_894481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894485 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_894485 : Nat := 118140960795 + 894485 * 2 ^ 59
def prefixEnd_894485 : Nat := 4983230072969 + 3 ^ 40 * 894485 * 2
def baseEnd_894485 : Nat := 306200495491358704682563

theorem tailTrace_894485 : CollatzResearch.WordTrace tailWord_894485 prefixEnd_894485 306200495491358704682563 := by
  unfold tailWord_894485
  simp only [CollatzResearch.WordTrace]
  refine ⟨32624548164441085720796909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21749698776294057147197939 32624548164441085720796909)
  ·
    refine ⟨12234205561665407145298841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32624548164441085720796909 12234205561665407145298841)
    ·
      refine ⟨9175654171249055358974131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12234205561665407145298841 9175654171249055358974131)
      ·
        refine ⟨13763481256873583038461197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175654171249055358974131 13763481256873583038461197)
        ·
          refine ⟨5161305471327593639422949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13763481256873583038461197 5161305471327593639422949)
          ·
            refine ⟨967744775873923807391803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5161305471327593639422949 967744775873923807391803)
            ·
              refine ⟨1451617163810885711087705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967744775873923807391803 1451617163810885711087705)
              ·
                refine ⟨1088712872858164283315779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451617163810885711087705 1088712872858164283315779)
                ·
                  refine ⟨1633069309287246424973669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1088712872858164283315779 1633069309287246424973669)
                  ·
                    refine ⟨306200495491358704682563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1633069309287246424973669 306200495491358704682563)
                    ·
                      rfl

theorem cell22_894485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_894485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894485 prefixEnd_894485 := by exact prefixLift 894485
  have htrace : WordTrace (prefixWord ++ tailWord_894485) baseStart_894485 baseEnd_894485 := by
    simpa [prefixWord, tailWord_894485, baseEnd_894485] using wordTrace_append hprefix tailTrace_894485
  have hstable : (prefixWord ++ tailWord_894485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894485).length < 2 ^ (prefixWord ++ tailWord_894485).sum := by decide
  have hdescent : baseEnd_894485 < baseStart_894485 := by decide
  rcases family_descends (prefixWord ++ tailWord_894485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894498 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_894498 : Nat := 118140960795 + 894498 * 2 ^ 59
def prefixEnd_894498 : Nat := 4983230072969 + 3 ^ 40 * 894498 * 2
def baseEnd_894498 : Nat := 306204945657031004107523

theorem tailTrace_894498 : CollatzResearch.WordTrace tailWord_894498 prefixEnd_894498 306204945657031004107523 := by
  unfold tailWord_894498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156255578348497235255037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21750014875595992627346765 8156255578348497235255037)
  ·
    refine ⟨3058595841880686463220639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8156255578348497235255037 3058595841880686463220639)
    ·
      refine ⟨4587893762821029694830959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3058595841880686463220639 4587893762821029694830959)
      ·
        refine ⟨6881840644231544542246439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587893762821029694830959 6881840644231544542246439)
        ·
          refine ⟨10322760966347316813369659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881840644231544542246439 10322760966347316813369659)
          ·
            refine ⟨15484141449520975220054489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10322760966347316813369659 15484141449520975220054489)
            ·
              refine ⟨11613106087140731415040867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15484141449520975220054489 11613106087140731415040867)
              ·
                refine ⟨17419659130711097122561301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11613106087140731415040867 17419659130711097122561301)
                ·
                  refine ⟨816546521752082677620061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17419659130711097122561301 816546521752082677620061)
                  ·
                    refine ⟨306204945657031004107523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816546521752082677620061 306204945657031004107523)
                    ·
                      rfl

theorem cell22_894498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_894498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894498 prefixEnd_894498 := by exact prefixLift 894498
  have htrace : WordTrace (prefixWord ++ tailWord_894498) baseStart_894498 baseEnd_894498 := by
    simpa [prefixWord, tailWord_894498, baseEnd_894498] using wordTrace_append hprefix tailTrace_894498
  have hstable : (prefixWord ++ tailWord_894498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894498).length < 2 ^ (prefixWord ++ tailWord_894498).sum := by decide
  have hdescent : baseEnd_894498 < baseStart_894498 := by decide
  rcases family_descends (prefixWord ++ tailWord_894498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894515 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 2, 3]
def baseStart_894515 : Nat := 118140960795 + 894515 * 2 ^ 59
def prefixEnd_894515 : Nat := 4983230072969 + 3 ^ 40 * 894515 * 2
def baseEnd_894515 : Nat := 306210765104448626432471

theorem tailTrace_894515 : CollatzResearch.WordTrace tailWord_894515 prefixEnd_894515 306210765104448626432471 := by
  unfold tailWord_894515
  simp only [CollatzResearch.WordTrace]
  refine ⟨32625642354332400844388999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21750428236221600562925999 32625642354332400844388999)
  ·
    refine ⟨48938463531498601266583499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32625642354332400844388999 48938463531498601266583499)
    ·
      refine ⟨73407695297247901899875249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48938463531498601266583499 73407695297247901899875249)
      ·
        refine ⟨55055771472935926424906437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73407695297247901899875249 55055771472935926424906437)
        ·
          refine ⟨10322957151175486204669957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55055771472935926424906437 10322957151175486204669957)
          ·
            refine ⟨1935554465845403663375617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10322957151175486204669957 1935554465845403663375617)
            ·
              refine ⟨1451665849384052747531713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1935554465845403663375617 1451665849384052747531713)
              ·
                refine ⟨1088749387038039560648785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1451665849384052747531713 1088749387038039560648785)
                ·
                  refine ⟨816562040278529670486589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1088749387038039560648785 816562040278529670486589)
                  ·
                    refine ⟨306210765104448626432471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816562040278529670486589 306210765104448626432471)
                    ·
                      rfl

theorem cell22_894515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 3].length) (baseStart_894515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894515 prefixEnd_894515 := by exact prefixLift 894515
  have htrace : WordTrace (prefixWord ++ tailWord_894515) baseStart_894515 baseEnd_894515 := by
    simpa [prefixWord, tailWord_894515, baseEnd_894515] using wordTrace_append hprefix tailTrace_894515
  have hstable : (prefixWord ++ tailWord_894515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894515).length < 2 ^ (prefixWord ++ tailWord_894515).sum := by decide
  have hdescent : baseEnd_894515 < baseStart_894515 := by decide
  rcases family_descends (prefixWord ++ tailWord_894515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894517 : List Nat := [1, 3, 3, 1, 1, 5, 2, 2, 4]
def baseStart_894517 : Nat := 118140960795 + 894517 * 2 ^ 59
def prefixEnd_894517 : Nat := 4983230072969 + 3 ^ 40 * 894517 * 2
def baseEnd_894517 : Nat := 102070483248440429294155

theorem tailTrace_894517 : CollatzResearch.WordTrace tailWord_894517 prefixEnd_894517 102070483248440429294155 := by
  unfold tailWord_894517
  simp only [CollatzResearch.WordTrace]
  refine ⟨32625715300325155185961805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21750476866883436790641203 32625715300325155185961805)
  ·
    refine ⟨12234643237621933194735677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32625715300325155185961805 12234643237621933194735677)
    ·
      refine ⟨4587991214108224948025879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12234643237621933194735677 4587991214108224948025879)
      ·
        refine ⟨6881986821162337422038819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587991214108224948025879 6881986821162337422038819)
        ·
          refine ⟨10322980231743506133058229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881986821162337422038819 10322980231743506133058229)
          ·
            refine ⟨967779396725953699974209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10322980231743506133058229 967779396725953699974209)
            ·
              refine ⟨725834547544465274980657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967779396725953699974209 725834547544465274980657)
              ·
                refine ⟨544375910658348956235493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725834547544465274980657 544375910658348956235493)
                ·
                  refine ⟨102070483248440429294155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544375910658348956235493 102070483248440429294155)
                  ·
                    rfl

theorem cell22_894517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_894517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894517 prefixEnd_894517 := by exact prefixLift 894517
  have htrace : WordTrace (prefixWord ++ tailWord_894517) baseStart_894517 baseEnd_894517 := by
    simpa [prefixWord, tailWord_894517, baseEnd_894517] using wordTrace_append hprefix tailTrace_894517
  have hstable : (prefixWord ++ tailWord_894517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894517).length < 2 ^ (prefixWord ++ tailWord_894517).sum := by decide
  have hdescent : baseEnd_894517 < baseStart_894517 := by decide
  rcases family_descends (prefixWord ++ tailWord_894517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894586 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_894586 : Nat := 118140960795 + 894586 * 2 ^ 59
def prefixEnd_894586 : Nat := 4983230072969 + 3 ^ 40 * 894586 * 2
def baseEnd_894586 : Nat := 306235069855428107907253

theorem tailTrace_894586 : CollatzResearch.WordTrace tailWord_894586 prefixEnd_894586 306235069855428107907253 := by
  unfold tailWord_894586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157057984268794992555903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21752154624716786646815741 8157057984268794992555903)
  ·
    refine ⟨12235586976403192488833855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8157057984268794992555903 12235586976403192488833855)
    ·
      refine ⟨18353380464604788733250783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12235586976403192488833855 18353380464604788733250783)
      ·
        refine ⟨27530070696907183099876175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18353380464604788733250783 27530070696907183099876175)
        ·
          refine ⟨41295106045360774649814263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27530070696907183099876175 41295106045360774649814263)
          ·
            refine ⟨61942659068041161974721395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41295106045360774649814263 61942659068041161974721395)
            ·
              refine ⟨92913988602061742962082093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61942659068041161974721395 92913988602061742962082093)
              ·
                refine ⟨34842745725773153610780785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92913988602061742962082093 34842745725773153610780785)
                ·
                  refine ⟨26132059294329865208085589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34842745725773153610780785 26132059294329865208085589)
                  ·
                    refine ⟨306235069855428107907253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26132059294329865208085589 306235069855428107907253)
                    ·
                      rfl

theorem cell22_894586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_894586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894586 prefixEnd_894586 := by exact prefixLift 894586
  have htrace : WordTrace (prefixWord ++ tailWord_894586) baseStart_894586 baseEnd_894586 := by
    simpa [prefixWord, tailWord_894586, baseEnd_894586] using wordTrace_append hprefix tailTrace_894586
  have hstable : (prefixWord ++ tailWord_894586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894586).length < 2 ^ (prefixWord ++ tailWord_894586).sum := by decide
  have hdescent : baseEnd_894586 < baseStart_894586 := by decide
  rcases family_descends (prefixWord ++ tailWord_894586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894633 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 8, 3]
def baseStart_894633 : Nat := 118140960795 + 894633 * 2 ^ 59
def prefixEnd_894633 : Nat := 4983230072969 + 3 ^ 40 * 894633 * 2
def baseEnd_894633 : Nat := 306251158915935651982109

theorem tailTrace_894633 : CollatzResearch.WordTrace tailWord_894633 prefixEnd_894633 306251158915935651982109 := by
  unfold tailWord_894633
  simp only [CollatzResearch.WordTrace]
  refine ⟨32629946167904906997184553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21753297445269937998123035 32629946167904906997184553)
  ·
    refine ⟨24472459625928680247888415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32629946167904906997184553 24472459625928680247888415)
    ·
      refine ⟨36708689438893020371832623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24472459625928680247888415 36708689438893020371832623)
      ·
        refine ⟨55063034158339530557748935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36708689438893020371832623 55063034158339530557748935)
        ·
          refine ⟨82594551237509295836623403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55063034158339530557748935 82594551237509295836623403)
          ·
            refine ⟨123891826856263943754935105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82594551237509295836623403 123891826856263943754935105)
            ·
              refine ⟨92918870142197957816201329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123891826856263943754935105 92918870142197957816201329)
              ·
                refine ⟨69689152606648468362150997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92918870142197957816201329 69689152606648468362150997)
                ·
                  refine ⟨816669757109161738618957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 69689152606648468362150997 816669757109161738618957)
                  ·
                    refine ⟨306251158915935651982109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816669757109161738618957 306251158915935651982109)
                    ·
                      rfl

theorem cell22_894633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_894633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894633 prefixEnd_894633 := by exact prefixLift 894633
  have htrace : WordTrace (prefixWord ++ tailWord_894633) baseStart_894633 baseEnd_894633 := by
    simpa [prefixWord, tailWord_894633, baseEnd_894633] using wordTrace_append hprefix tailTrace_894633
  have hstable : (prefixWord ++ tailWord_894633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894633).length < 2 ^ (prefixWord ++ tailWord_894633).sum := by decide
  have hdescent : baseEnd_894633 < baseStart_894633 := by decide
  rcases family_descends (prefixWord ++ tailWord_894633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894693 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_894693 : Nat := 118140960795 + 894693 * 2 ^ 59
def prefixEnd_894693 : Nat := 4983230072969 + 3 ^ 40 * 894693 * 2
def baseEnd_894693 : Nat := 306271698142115495481925

theorem tailTrace_894693 : CollatzResearch.WordTrace tailWord_894693 prefixEnd_894693 306271698142115495481925 := by
  unfold tailWord_894693
  simp only [CollatzResearch.WordTrace]
  refine ⟨32632134547687537244368733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21754756365125024829579155 32632134547687537244368733)
  ·
    refine ⟨12237050455382826466638275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32632134547687537244368733 12237050455382826466638275)
    ·
      refine ⟨18355575683074239699957413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12237050455382826466638275 18355575683074239699957413)
      ·
        refine ⟨3441670440576419943742015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18355575683074239699957413 3441670440576419943742015)
        ·
          refine ⟨5162505660864629915613023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441670440576419943742015 5162505660864629915613023)
          ·
            refine ⟨7743758491296944873419535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162505660864629915613023 7743758491296944873419535)
            ·
              refine ⟨11615637736945417310129303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743758491296944873419535 11615637736945417310129303)
              ·
                refine ⟨17423456605418125965193955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11615637736945417310129303 17423456605418125965193955)
                ·
                  refine ⟨26135184908127188947790933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17423456605418125965193955 26135184908127188947790933)
                  ·
                    refine ⟨306271698142115495481925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26135184908127188947790933 306271698142115495481925)
                    ·
                      rfl

theorem cell22_894693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_894693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894693 prefixEnd_894693 := by exact prefixLift 894693
  have htrace : WordTrace (prefixWord ++ tailWord_894693) baseStart_894693 baseEnd_894693 := by
    simpa [prefixWord, tailWord_894693, baseEnd_894693] using wordTrace_append hprefix tailTrace_894693
  have hstable : (prefixWord ++ tailWord_894693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894693).length < 2 ^ (prefixWord ++ tailWord_894693).sum := by decide
  have hdescent : baseEnd_894693 < baseStart_894693 := by decide
  rcases family_descends (prefixWord ++ tailWord_894693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894770 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_894770 : Nat := 118140960795 + 894770 * 2 ^ 59
def prefixEnd_894770 : Nat := 4983230072969 + 3 ^ 40 * 894770 * 2
def baseEnd_894770 : Nat := 102099352271904320435563

theorem tailTrace_894770 : CollatzResearch.WordTrace tailWord_894770 prefixEnd_894770 102099352271904320435563 := by
  unfold tailWord_894770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8158735742102144848730441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21756628645605719596614509 8158735742102144848730441)
  ·
    refine ⟨6119051806576608636547831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8158735742102144848730441 6119051806576608636547831)
    ·
      refine ⟨9178577709864912954821747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6119051806576608636547831 9178577709864912954821747)
      ·
        refine ⟨13767866564797369432232621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178577709864912954821747 13767866564797369432232621)
        ·
          refine ⟨5162949961799013537087233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13767866564797369432232621 5162949961799013537087233)
          ·
            refine ⟨3872212471349260152815425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5162949961799013537087233 3872212471349260152815425)
            ·
              refine ⟨2904159353511945114611569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872212471349260152815425 2904159353511945114611569)
              ·
                refine ⟨2178119515133958835958677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904159353511945114611569 2178119515133958835958677)
                ·
                  refine ⟨102099352271904320435563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2178119515133958835958677 102099352271904320435563)
                  ·
                    rfl

theorem cell22_894770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_894770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894770 prefixEnd_894770 := by exact prefixLift 894770
  have htrace : WordTrace (prefixWord ++ tailWord_894770) baseStart_894770 baseEnd_894770 := by
    simpa [prefixWord, tailWord_894770, baseEnd_894770] using wordTrace_append hprefix tailTrace_894770
  have hstable : (prefixWord ++ tailWord_894770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894770).length < 2 ^ (prefixWord ++ tailWord_894770).sum := by decide
  have hdescent : baseEnd_894770 < baseStart_894770 := by decide
  rcases family_descends (prefixWord ++ tailWord_894770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894787 : List Nat := [1, 1, 1, 3, 1, 5, 3, 3, 4]
def baseStart_894787 : Nat := 118140960795 + 894787 * 2 ^ 59
def prefixEnd_894787 : Nat := 4983230072969 + 3 ^ 40 * 894787 * 2
def baseEnd_894787 : Nat := 102101292087710194543879

theorem tailTrace_894787 : CollatzResearch.WordTrace tailWord_894787 prefixEnd_894787 102101292087710194543879 := by
  unfold tailWord_894787
  simp only [CollatzResearch.WordTrace]
  refine ⟨32635563009346991298290615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21757042006231327532193743 32635563009346991298290615)
  ·
    refine ⟨48953344514020486947435923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32635563009346991298290615 48953344514020486947435923)
    ·
      refine ⟨73430016771030730421153885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48953344514020486947435923 73430016771030730421153885)
      ·
        refine ⟨27536256289136523907932707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73430016771030730421153885 27536256289136523907932707)
        ·
          refine ⟨41304384433704785861899061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27536256289136523907932707 41304384433704785861899061)
          ·
            refine ⟨3872286040659823674553037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41304384433704785861899061 3872286040659823674553037)
            ·
              refine ⟨1452107265247433877957389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3872286040659823674553037 1452107265247433877957389)
              ·
                refine ⟨544540224467787704234021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1452107265247433877957389 544540224467787704234021)
                ·
                  refine ⟨102101292087710194543879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544540224467787704234021 102101292087710194543879)
                  ·
                    rfl

theorem cell22_894787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 4].length) (baseStart_894787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894787 prefixEnd_894787 := by exact prefixLift 894787
  have htrace : WordTrace (prefixWord ++ tailWord_894787) baseStart_894787 baseEnd_894787 := by
    simpa [prefixWord, tailWord_894787, baseEnd_894787] using wordTrace_append hprefix tailTrace_894787
  have hstable : (prefixWord ++ tailWord_894787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894787).length < 2 ^ (prefixWord ++ tailWord_894787).sum := by decide
  have hdescent : baseEnd_894787 < baseStart_894787 := by decide
  rcases family_descends (prefixWord ++ tailWord_894787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894802 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_894802 : Nat := 118140960795 + 894802 * 2 ^ 59
def prefixEnd_894802 : Nat := 4983230072969 + 3 ^ 40 * 894802 * 2
def baseEnd_894802 : Nat := 306309011069675544506591

theorem tailTrace_894802 : CollatzResearch.WordTrace tailWord_894802 prefixEnd_894802 306309011069675544506591 := by
  unfold tailWord_894802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8159027526073162215021665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21757406736195099240057773 8159027526073162215021665)
  ·
    refine ⟨6119270644554871661266249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8159027526073162215021665 6119270644554871661266249)
    ·
      refine ⟨4589452983416153745949687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6119270644554871661266249 4589452983416153745949687)
      ·
        refine ⟨6884179475124230618924531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589452983416153745949687 6884179475124230618924531)
        ·
          refine ⟨10326269212686345928386797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6884179475124230618924531 10326269212686345928386797)
          ·
            refine ⟨3872350954757379723145049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10326269212686345928386797 3872350954757379723145049)
            ·
              refine ⟨2904263216068034792358787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872350954757379723145049 2904263216068034792358787)
              ·
                refine ⟨4356394824102052188538181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904263216068034792358787 4356394824102052188538181)
                ·
                  refine ⟨816824029519134785350909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4356394824102052188538181 816824029519134785350909)
                  ·
                    refine ⟨306309011069675544506591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816824029519134785350909 306309011069675544506591)
                    ·
                      rfl

theorem cell22_894802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_894802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894802 prefixEnd_894802 := by exact prefixLift 894802
  have htrace : WordTrace (prefixWord ++ tailWord_894802) baseStart_894802 baseEnd_894802 := by
    simpa [prefixWord, tailWord_894802, baseEnd_894802] using wordTrace_append hprefix tailTrace_894802
  have hstable : (prefixWord ++ tailWord_894802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894802).length < 2 ^ (prefixWord ++ tailWord_894802).sum := by decide
  have hdescent : baseEnd_894802 < baseStart_894802 := by decide
  rcases family_descends (prefixWord ++ tailWord_894802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894815 : List Nat := [1, 1, 2, 3, 1, 5, 2, 7]
def baseStart_894815 : Nat := 118140960795 + 894815 * 2 ^ 59
def prefixEnd_894815 : Nat := 4983230072969 + 3 ^ 40 * 894815 * 2
def baseEnd_894815 : Nat := 34034829026149760436839

theorem tailTrace_894815 : CollatzResearch.WordTrace tailWord_894815 prefixEnd_894815 34034829026149760436839 := by
  unfold tailWord_894815
  simp only [CollatzResearch.WordTrace]
  refine ⟨32636584253245552080309899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21757722835497034720206599 32636584253245552080309899)
  ·
    refine ⟨48954876379868328120464849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32636584253245552080309899 48954876379868328120464849)
    ·
      refine ⟨36716157284901246090348637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48954876379868328120464849 36716157284901246090348637)
      ·
        refine ⟨13768558981837967283880739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36716157284901246090348637 13768558981837967283880739)
        ·
          refine ⟨20652838472756950925821109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13768558981837967283880739 20652838472756950925821109)
          ·
            refine ⟨1936203606820964149295729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20652838472756950925821109 1936203606820964149295729)
            ·
              refine ⟨1452152705115723111971797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936203606820964149295729 1452152705115723111971797)
              ·
                refine ⟨34034829026149760436839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1452152705115723111971797 34034829026149760436839)
                ·
                  rfl

theorem cell22_894815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 7].length) (baseStart_894815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894815 prefixEnd_894815 := by exact prefixLift 894815
  have htrace : WordTrace (prefixWord ++ tailWord_894815) baseStart_894815 baseEnd_894815 := by
    simpa [prefixWord, tailWord_894815, baseEnd_894815] using wordTrace_append hprefix tailTrace_894815
  have hstable : (prefixWord ++ tailWord_894815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894815).length < 2 ^ (prefixWord ++ tailWord_894815).sum := by decide
  have hdescent : baseEnd_894815 < baseStart_894815 := by decide
  rcases family_descends (prefixWord ++ tailWord_894815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894819 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 2, 3]
def baseStart_894819 : Nat := 118140960795 + 894819 * 2 ^ 59
def prefixEnd_894819 : Nat := 4983230072969 + 3 ^ 40 * 894819 * 2
def baseEnd_894819 : Nat := 306314830517093166831539

theorem tailTrace_894819 : CollatzResearch.WordTrace tailWord_894819 prefixEnd_894819 306314830517093166831539 := by
  unfold tailWord_894819
  simp only [CollatzResearch.WordTrace]
  refine ⟨32636730145231060763455511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21757820096820707175637007 32636730145231060763455511)
  ·
    refine ⟨48955095217846591145183267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32636730145231060763455511 48955095217846591145183267)
    ·
      refine ⟨73432642826769886717774901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48955095217846591145183267 73432642826769886717774901)
      ·
        refine ⟨6884310265009676879791397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73432642826769886717774901 6884310265009676879791397)
        ·
          refine ⟨1290808174689314414960887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6884310265009676879791397 1290808174689314414960887)
          ·
            refine ⟨1936212262033971622441331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290808174689314414960887 1936212262033971622441331)
            ·
              refine ⟨2904318393050957433661997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936212262033971622441331 2904318393050957433661997)
              ·
                refine ⟨1089119397394109037623249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2904318393050957433661997 1089119397394109037623249)
                ·
                  refine ⟨816839548045581778217437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089119397394109037623249 816839548045581778217437)
                  ·
                    refine ⟨306314830517093166831539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 816839548045581778217437 306314830517093166831539)
                    ·
                      rfl

theorem cell22_894819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 3].length) (baseStart_894819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894819 prefixEnd_894819 := by exact prefixLift 894819
  have htrace : WordTrace (prefixWord ++ tailWord_894819) baseStart_894819 baseEnd_894819 := by
    simpa [prefixWord, tailWord_894819, baseEnd_894819] using wordTrace_append hprefix tailTrace_894819
  have hstable : (prefixWord ++ tailWord_894819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894819).length < 2 ^ (prefixWord ++ tailWord_894819).sum := by decide
  have hdescent : baseEnd_894819 < baseStart_894819 := by decide
  rcases family_descends (prefixWord ++ tailWord_894819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894877 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 5]
def baseStart_894877 : Nat := 118140960795 + 894877 * 2 ^ 59
def prefixEnd_894877 : Nat := 4983230072969 + 3 ^ 40 * 894877 * 2
def baseEnd_894877 : Nat := 102111561700800116293787

theorem tailTrace_894877 : CollatzResearch.WordTrace tailWord_894877 prefixEnd_894877 102111561700800116293787 := by
  unfold tailWord_894877
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638845579020936669066885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21759230386013957779377923 32638845579020936669066885)
  ·
    refine ⟨6119783546066425625450041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32638845579020936669066885 6119783546066425625450041)
    ·
      refine ⟨4589837659549819219087531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6119783546066425625450041 4589837659549819219087531)
      ·
        refine ⟨6884756489324728828631297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589837659549819219087531 6884756489324728828631297)
        ·
          refine ⟨5163567366993546621473473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6884756489324728828631297 5163567366993546621473473)
          ·
            refine ⟨3872675525245159966105105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5163567366993546621473473 3872675525245159966105105)
            ·
              refine ⟨2904506643933869974578829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872675525245159966105105 2904506643933869974578829)
              ·
                refine ⟨1089189991475201240467061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2904506643933869974578829 1089189991475201240467061)
                ·
                  refine ⟨102111561700800116293787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089189991475201240467061 102111561700800116293787)
                  ·
                    rfl

theorem cell22_894877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_894877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894877 prefixEnd_894877 := by exact prefixLift 894877
  have htrace : WordTrace (prefixWord ++ tailWord_894877) baseStart_894877 baseEnd_894877 := by
    simpa [prefixWord, tailWord_894877, baseEnd_894877] using wordTrace_append hprefix tailTrace_894877
  have hstable : (prefixWord ++ tailWord_894877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894877).length < 2 ^ (prefixWord ++ tailWord_894877).sum := by decide
  have hdescent : baseEnd_894877 < baseStart_894877 := by decide
  rcases family_descends (prefixWord ++ tailWord_894877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894905 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 8]
def baseStart_894905 : Nat := 118140960795 + 894905 * 2 ^ 59
def prefixEnd_894905 : Nat := 4983230072969 + 3 ^ 40 * 894905 * 2
def baseEnd_894905 : Nat := 102114756691539203060425

theorem tailTrace_894905 : CollatzResearch.WordTrace tailWord_894905 prefixEnd_894905 102114756691539203060425 := by
  unfold tailWord_894905
  simp only [CollatzResearch.WordTrace]
  refine ⟨32639866822919497451086169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21759911215279664967390779 32639866822919497451086169)
  ·
    refine ⟨24479900117189623088314627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32639866822919497451086169 24479900117189623088314627)
    ·
      refine ⟨36719850175784434632471941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24479900117189623088314627 36719850175784434632471941)
      ·
        refine ⟨6884971907959581493588489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36719850175784434632471941 6884971907959581493588489)
        ·
          refine ⟨5163728930969686120191367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6884971907959581493588489 5163728930969686120191367)
          ·
            refine ⟨7745593396454529180287051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163728930969686120191367 7745593396454529180287051)
            ·
              refine ⟨11618390094681793770430577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745593396454529180287051 11618390094681793770430577)
              ·
                refine ⟨8713792571011345327822933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11618390094681793770430577 8713792571011345327822933)
                ·
                  refine ⟨102114756691539203060425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8713792571011345327822933 102114756691539203060425)
                  ·
                    rfl

theorem cell22_894905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_894905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894905 prefixEnd_894905 := by exact prefixLift 894905
  have htrace : WordTrace (prefixWord ++ tailWord_894905) baseStart_894905 baseEnd_894905 := by
    simpa [prefixWord, tailWord_894905, baseEnd_894905] using wordTrace_append hprefix tailTrace_894905
  have hstable : (prefixWord ++ tailWord_894905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894905).length < 2 ^ (prefixWord ++ tailWord_894905).sum := by decide
  have hdescent : baseEnd_894905 < baseStart_894905 := by decide
  rcases family_descends (prefixWord ++ tailWord_894905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894935 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 3, 6]
def baseStart_894935 : Nat := 118140960795 + 894935 * 2 ^ 59
def prefixEnd_894935 : Nat := 4983230072969 + 3 ^ 40 * 894935 * 2
def baseEnd_894935 : Nat := 306354539687707530931183

theorem tailTrace_894935 : CollatzResearch.WordTrace tailWord_894935 prefixEnd_894935 306354539687707530931183 := by
  unfold tailWord_894935
  simp only [CollatzResearch.WordTrace]
  refine ⟨32640961012810812574678259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21760640675207208383118839 32640961012810812574678259)
  ·
    refine ⟨48961441519216218862017389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32640961012810812574678259 48961441519216218862017389)
    ·
      refine ⟨18360540569706082073256521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48961441519216218862017389 18360540569706082073256521)
      ·
        refine ⟨13770405427279561554942391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18360540569706082073256521 13770405427279561554942391)
        ·
          refine ⟨20655608140919342332413587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13770405427279561554942391 20655608140919342332413587)
          ·
            refine ⟨30983412211379013498620381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20655608140919342332413587 30983412211379013498620381)
            ·
              refine ⟨11618779579267130061982643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30983412211379013498620381 11618779579267130061982643)
              ·
                refine ⟨17428169368900695092973965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11618779579267130061982643 17428169368900695092973965)
                ·
                  refine ⟨6535563513337760659865237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17428169368900695092973965 6535563513337760659865237)
                  ·
                    refine ⟨306354539687707530931183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6535563513337760659865237 306354539687707530931183)
                    ·
                      rfl

theorem cell22_894935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_894935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894935 prefixEnd_894935 := by exact prefixLift 894935
  have htrace : WordTrace (prefixWord ++ tailWord_894935) baseStart_894935 baseEnd_894935 := by
    simpa [prefixWord, tailWord_894935, baseEnd_894935] using wordTrace_append hprefix tailTrace_894935
  have hstable : (prefixWord ++ tailWord_894935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894935).length < 2 ^ (prefixWord ++ tailWord_894935).sum := by decide
  have hdescent : baseEnd_894935 < baseStart_894935 := by decide
  rcases family_descends (prefixWord ++ tailWord_894935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894941 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_894941 : Nat := 118140960795 + 894941 * 2 ^ 59
def prefixEnd_894941 : Nat := 4983230072969 + 3 ^ 40 * 894941 * 2
def baseEnd_894941 : Nat := 306356593610325515281165

theorem tailTrace_894941 : CollatzResearch.WordTrace tailWord_894941 prefixEnd_894941 306356593610325515281165 := by
  unfold tailWord_894941
  simp only [CollatzResearch.WordTrace]
  refine ⟨32641179850789075599396677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21760786567192717066264451 32641179850789075599396677)
  ·
    refine ⟨6120221222022951674886877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32641179850789075599396677 6120221222022951674886877)
    ·
      refine ⟨2295082958258606878082579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6120221222022951674886877 2295082958258606878082579)
      ·
        refine ⟨3442624437387910317123869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295082958258606878082579 3442624437387910317123869)
        ·
          refine ⟨1290984164020466368921451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3442624437387910317123869 1290984164020466368921451)
          ·
            refine ⟨1936476246030699553382177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290984164020466368921451 1936476246030699553382177)
            ·
              refine ⟨1452357184523024665036633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936476246030699553382177 1452357184523024665036633)
              ·
                refine ⟨1089267888392268498777475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1452357184523024665036633 1089267888392268498777475)
                ·
                  refine ⟨1633901832588402748166213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089267888392268498777475 1633901832588402748166213)
                  ·
                    refine ⟨306356593610325515281165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1633901832588402748166213 306356593610325515281165)
                    ·
                      rfl

theorem cell22_894941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_894941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894941 prefixEnd_894941 := by exact prefixLift 894941
  have htrace : WordTrace (prefixWord ++ tailWord_894941) baseStart_894941 baseEnd_894941 := by
    simpa [prefixWord, tailWord_894941, baseEnd_894941] using wordTrace_append hprefix tailTrace_894941
  have hstable : (prefixWord ++ tailWord_894941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894941).length < 2 ^ (prefixWord ++ tailWord_894941).sum := by decide
  have hdescent : baseEnd_894941 < baseStart_894941 := by decide
  rcases family_descends (prefixWord ++ tailWord_894941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_894952 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_894952 : Nat := 118140960795 + 894952 * 2 ^ 59
def prefixEnd_894952 : Nat := 4983230072969 + 3 ^ 40 * 894952 * 2
def baseEnd_894952 : Nat := 306360359135125153256131

theorem tailTrace_894952 : CollatzResearch.WordTrace tailWord_894952 prefixEnd_894952 306360359135125153256131 := by
  unfold tailWord_894952
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320790526874612239023555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21761054035832816318698073 16320790526874612239023555)
  ·
    refine ⟨24481185790311918358535333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16320790526874612239023555 24481185790311918358535333)
    ·
      refine ⟨4590222335683484692225375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24481185790311918358535333 4590222335683484692225375)
      ·
        refine ⟨6885333503525227038338063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590222335683484692225375 6885333503525227038338063)
        ·
          refine ⟨10328000255287840557507095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885333503525227038338063 10328000255287840557507095)
          ·
            refine ⟨15492000382931760836260643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10328000255287840557507095 15492000382931760836260643)
            ·
              refine ⟨23238000574397641254390965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15492000382931760836260643 23238000574397641254390965)
              ·
                refine ⟨2178562553849778867599153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23238000574397641254390965 2178562553849778867599153)
                ·
                  refine ⟨1633921915387334150699365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2178562553849778867599153 1633921915387334150699365)
                  ·
                    refine ⟨306360359135125153256131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1633921915387334150699365 306360359135125153256131)
                    ·
                      rfl

theorem cell22_894952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_894952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_894952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_894952 prefixEnd_894952 := by exact prefixLift 894952
  have htrace : WordTrace (prefixWord ++ tailWord_894952) baseStart_894952 baseEnd_894952 := by
    simpa [prefixWord, tailWord_894952, baseEnd_894952] using wordTrace_append hprefix tailTrace_894952
  have hstable : (prefixWord ++ tailWord_894952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_894952).length < 2 ^ (prefixWord ++ tailWord_894952).sum := by decide
  have hdescent : baseEnd_894952 < baseStart_894952 := by decide
  rcases family_descends (prefixWord ++ tailWord_894952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895033 : List Nat := [1, 2, 1, 5, 3, 1, 1, 4, 1, 3]
def baseStart_895033 : Nat := 118140960795 + 895033 * 2 ^ 59
def prefixEnd_895033 : Nat := 4983230072969 + 3 ^ 40 * 895033 * 2
def baseEnd_895033 : Nat := 306388087090467941980883

theorem tailTrace_895033 : CollatzResearch.WordTrace tailWord_895033 prefixEnd_895033 306388087090467941980883 := by
  unfold tailWord_895033
  simp only [CollatzResearch.WordTrace]
  refine ⟨32644535366455775311745753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21763023577637183541163835 32644535366455775311745753)
  ·
    refine ⟨24483401524841831483809315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32644535366455775311745753 24483401524841831483809315)
    ·
      refine ⟨36725102287262747225713973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24483401524841831483809315 36725102287262747225713973)
      ·
        refine ⟨3442978339430882552410685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36725102287262747225713973 3442978339430882552410685)
        ·
          refine ⟨1291116877286580957154007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3442978339430882552410685 1291116877286580957154007)
          ·
            refine ⟨1936675315929871435731011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291116877286580957154007 1936675315929871435731011)
            ·
              refine ⟨2905012973894807153596517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1936675315929871435731011 2905012973894807153596517)
              ·
                refine ⟨544689932605276341299347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2905012973894807153596517 544689932605276341299347)
                ·
                  refine ⟨817034898907914511949021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544689932605276341299347 817034898907914511949021)
                  ·
                    refine ⟨306388087090467941980883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817034898907914511949021 306388087090467941980883)
                    ·
                      rfl

theorem cell22_895033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 3].length) (baseStart_895033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895033 prefixEnd_895033 := by exact prefixLift 895033
  have htrace : WordTrace (prefixWord ++ tailWord_895033) baseStart_895033 baseEnd_895033 := by
    simpa [prefixWord, tailWord_895033, baseEnd_895033] using wordTrace_append hprefix tailTrace_895033
  have hstable : (prefixWord ++ tailWord_895033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895033).length < 2 ^ (prefixWord ++ tailWord_895033).sum := by decide
  have hdescent : baseEnd_895033 < baseStart_895033 := by decide
  rcases family_descends (prefixWord ++ tailWord_895033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895046 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_895046 : Nat := 118140960795 + 895046 * 2 ^ 59
def prefixEnd_895046 : Nat := 4983230072969 + 3 ^ 40 * 895046 * 2
def baseEnd_895046 : Nat := 102130845752046747135281

theorem tailTrace_895046 : CollatzResearch.WordTrace tailWord_895046 prefixEnd_895046 102130845752046747135281 := by
  unfold tailWord_895046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020156547356521204124031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21763339676939119021312661 1020156547356521204124031)
  ·
    refine ⟨1530234821034781806186047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1020156547356521204124031 1530234821034781806186047)
    ·
      refine ⟨2295352231552172709279071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530234821034781806186047 2295352231552172709279071)
      ·
        refine ⟨3443028347328259063918607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295352231552172709279071 3443028347328259063918607)
        ·
          refine ⟨5164542520992388595877911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443028347328259063918607 5164542520992388595877911)
          ·
            refine ⟨7746813781488582893816867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164542520992388595877911 7746813781488582893816867)
            ·
              refine ⟨11620220672232874340725301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746813781488582893816867 11620220672232874340725301)
              ·
                refine ⟨1089395688021831969442997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11620220672232874340725301 1089395688021831969442997)
                ·
                  refine ⟨102130845752046747135281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089395688021831969442997 102130845752046747135281)
                  ·
                    rfl

theorem cell22_895046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_895046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895046 prefixEnd_895046 := by exact prefixLift 895046
  have htrace : WordTrace (prefixWord ++ tailWord_895046) baseStart_895046 baseEnd_895046 := by
    simpa [prefixWord, tailWord_895046, baseEnd_895046] using wordTrace_append hprefix tailTrace_895046
  have hstable : (prefixWord ++ tailWord_895046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895046).length < 2 ^ (prefixWord ++ tailWord_895046).sum := by decide
  have hdescent : baseEnd_895046 < baseStart_895046 := by decide
  rcases family_descends (prefixWord ++ tailWord_895046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895076 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_895076 : Nat := 118140960795 + 895076 * 2 ^ 59
def prefixEnd_895076 : Nat := 4983230072969 + 3 ^ 40 * 895076 * 2
def baseEnd_895076 : Nat := 306402806869230163155751

theorem tailTrace_895076 : CollatzResearch.WordTrace tailWord_895076 prefixEnd_895076 306402806869230163155751 := by
  unfold tailWord_895076
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323051852649996827780541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21764069136866662437040721 16323051852649996827780541)
  ·
    refine ⟨6121144444743748810417703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16323051852649996827780541 6121144444743748810417703)
    ·
      refine ⟨9181716667115623215626555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6121144444743748810417703 9181716667115623215626555)
      ·
        refine ⟨13772575000673434823439833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9181716667115623215626555 13772575000673434823439833)
        ·
          refine ⟨10329431250505076117579875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13772575000673434823439833 10329431250505076117579875)
          ·
            refine ⟨15494146875757614176369813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329431250505076117579875 15494146875757614176369813)
            ·
              refine ⟨726288134801138164517335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15494146875757614176369813 726288134801138164517335)
              ·
                refine ⟨1089432202201707246776003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726288134801138164517335 1089432202201707246776003)
                ·
                  refine ⟨1634148303302560870164005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1089432202201707246776003 1634148303302560870164005)
                  ·
                    refine ⟨306402806869230163155751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634148303302560870164005 306402806869230163155751)
                    ·
                      rfl

theorem cell22_895076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_895076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895076 prefixEnd_895076 := by exact prefixLift 895076
  have htrace : WordTrace (prefixWord ++ tailWord_895076) baseStart_895076 baseEnd_895076 := by
    simpa [prefixWord, tailWord_895076, baseEnd_895076] using wordTrace_append hprefix tailTrace_895076
  have hstable : (prefixWord ++ tailWord_895076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895076).length < 2 ^ (prefixWord ++ tailWord_895076).sum := by decide
  have hdescent : baseEnd_895076 < baseStart_895076 := by decide
  rcases family_descends (prefixWord ++ tailWord_895076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895089 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 4, 3]
def baseStart_895089 : Nat := 118140960795 + 895089 * 2 ^ 59
def prefixEnd_895089 : Nat := 4983230072969 + 3 ^ 40 * 895089 * 2
def baseEnd_895089 : Nat := 306407257034902462580711

theorem tailTrace_895089 : CollatzResearch.WordTrace tailWord_895089 prefixEnd_895089 306407257034902462580711 := by
  unfold tailWord_895089
  simp only [CollatzResearch.WordTrace]
  refine ⟨32646577854252896875784321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21764385236168597917189547 32646577854252896875784321)
  ·
    refine ⟨24484933390689672656838241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32646577854252896875784321 24484933390689672656838241)
    ·
      refine ⟨18363700043017254492628681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24484933390689672656838241 18363700043017254492628681)
      ·
        refine ⟨13772775032262940869471511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18363700043017254492628681 13772775032262940869471511)
        ·
          refine ⟨20659162548394411304207267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13772775032262940869471511 20659162548394411304207267)
          ·
            refine ⟨30988743822591616956310901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20659162548394411304207267 30988743822591616956310901)
            ·
              refine ⟨2905194733367964089654147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30988743822591616956310901 2905194733367964089654147)
              ·
                refine ⟨4357792100051946134481221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905194733367964089654147 4357792100051946134481221)
                ·
                  refine ⟨817086018759739900215229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4357792100051946134481221 817086018759739900215229)
                  ·
                    refine ⟨306407257034902462580711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817086018759739900215229 306407257034902462580711)
                    ·
                      rfl

theorem cell22_895089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_895089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895089 prefixEnd_895089 := by exact prefixLift 895089
  have htrace : WordTrace (prefixWord ++ tailWord_895089) baseStart_895089 baseEnd_895089 := by
    simpa [prefixWord, tailWord_895089, baseEnd_895089] using wordTrace_append hprefix tailTrace_895089
  have hstable : (prefixWord ++ tailWord_895089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895089).length < 2 ^ (prefixWord ++ tailWord_895089).sum := by decide
  have hdescent : baseEnd_895089 < baseStart_895089 := by decide
  rcases family_descends (prefixWord ++ tailWord_895089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895157 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_895157 : Nat := 118140960795 + 895157 * 2 ^ 59
def prefixEnd_895157 : Nat := 4983230072969 + 3 ^ 40 * 895157 * 2
def baseEnd_895157 : Nat := 306430534824572951880503

theorem tailTrace_895157 : CollatzResearch.WordTrace tailWord_895157 prefixEnd_895157 306430534824572951880503 := by
  unfold tailWord_895157
  simp only [CollatzResearch.WordTrace]
  refine ⟨32649058018006544489259725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21766038678671029659506483 32649058018006544489259725)
  ·
    refine ⟨12243396756752454183472397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32649058018006544489259725 12243396756752454183472397)
    ·
      refine ⟨4591273783782170318802149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12243396756752454183472397 4591273783782170318802149)
      ·
        refine ⟨860863834459156934775403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4591273783782170318802149 860863834459156934775403)
        ·
          refine ⟨1291295751688735402163105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860863834459156934775403 1291295751688735402163105)
          ·
            refine ⟨968471813766551551622329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1291295751688735402163105 968471813766551551622329)
            ·
              refine ⟨726353860324913663716747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968471813766551551622329 726353860324913663716747)
              ·
                refine ⟨1089530790487370495575121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726353860324913663716747 1089530790487370495575121)
                ·
                  refine ⟨817148092865527871681341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089530790487370495575121 817148092865527871681341)
                  ·
                    refine ⟨306430534824572951880503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817148092865527871681341 306430534824572951880503)
                    ·
                      rfl

theorem cell22_895157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_895157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895157 prefixEnd_895157 := by exact prefixLift 895157
  have htrace : WordTrace (prefixWord ++ tailWord_895157) baseStart_895157 baseEnd_895157 := by
    simpa [prefixWord, tailWord_895157, baseEnd_895157] using wordTrace_append hprefix tailTrace_895157
  have hstable : (prefixWord ++ tailWord_895157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895157).length < 2 ^ (prefixWord ++ tailWord_895157).sum := by decide
  have hdescent : baseEnd_895157 < baseStart_895157 := by decide
  rcases family_descends (prefixWord ++ tailWord_895157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895258 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_895258 : Nat := 118140960795 + 895258 * 2 ^ 59
def prefixEnd_895258 : Nat := 4983230072969 + 3 ^ 40 * 895258 * 2
def baseEnd_895258 : Nat := 306465109188642355105193

theorem tailTrace_895258 : CollatzResearch.WordTrace tailWord_895258 prefixEnd_895258 306465109188642355105193 := by
  unfold tailWord_895258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163185447660159684671607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21768494527093759159124285 8163185447660159684671607)
  ·
    refine ⟨12244778171490239527007411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163185447660159684671607 12244778171490239527007411)
    ·
      refine ⟨18367167257235359290511117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12244778171490239527007411 18367167257235359290511117)
      ·
        refine ⟨6887687721463259733941669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18367167257235359290511117 6887687721463259733941669)
        ·
          refine ⟨1291441447774361200114063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6887687721463259733941669 1291441447774361200114063)
          ·
            refine ⟨1937162171661541800171095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291441447774361200114063 1937162171661541800171095)
            ·
              refine ⟨2905743257492312700256643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937162171661541800171095 2905743257492312700256643)
              ·
                refine ⟨4358614886238469050384965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905743257492312700256643 4358614886238469050384965)
                ·
                  refine ⟨817240291169712946947181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4358614886238469050384965 817240291169712946947181)
                  ·
                    refine ⟨306465109188642355105193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817240291169712946947181 306465109188642355105193)
                    ·
                      rfl

theorem cell22_895258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_895258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895258 prefixEnd_895258 := by exact prefixLift 895258
  have htrace : WordTrace (prefixWord ++ tailWord_895258) baseStart_895258 baseEnd_895258 := by
    simpa [prefixWord, tailWord_895258, baseEnd_895258] using wordTrace_append hprefix tailTrace_895258
  have hstable : (prefixWord ++ tailWord_895258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895258).length < 2 ^ (prefixWord ++ tailWord_895258).sum := by decide
  have hdescent : baseEnd_895258 < baseStart_895258 := by decide
  rcases family_descends (prefixWord ++ tailWord_895258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895299 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 7]
def baseStart_895299 : Nat := 118140960795 + 895299 * 2 ^ 59
def prefixEnd_895299 : Nat := 4983230072969 + 3 ^ 40 * 895299 * 2
def baseEnd_895299 : Nat := 102159714775510638276689

theorem tailTrace_895299 : CollatzResearch.WordTrace tailWord_895299 prefixEnd_895299 102159714775510638276689 := by
  unfold tailWord_895299
  simp only [CollatzResearch.WordTrace]
  refine ⟨32654237183492102740928951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21769491455661401827285967 32654237183492102740928951)
  ·
    refine ⟨48981355775238154111393427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32654237183492102740928951 48981355775238154111393427)
    ·
      refine ⟨73472033662857231167090141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48981355775238154111393427 73472033662857231167090141)
      ·
        refine ⟨27552012623571461687658803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73472033662857231167090141 27552012623571461687658803)
        ·
          refine ⟨41328018935357192531488205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27552012623571461687658803 41328018935357192531488205)
          ·
            refine ⟨15498007100758947199308077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41328018935357192531488205 15498007100758947199308077)
            ·
              refine ⟨5811752662784605199740529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15498007100758947199308077 5811752662784605199740529)
              ·
                refine ⟨4358814497088453899805397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5811752662784605199740529 4358814497088453899805397)
                ·
                  refine ⟨102159714775510638276689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4358814497088453899805397 102159714775510638276689)
                  ·
                    rfl

theorem cell22_895299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_895299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895299 prefixEnd_895299 := by exact prefixLift 895299
  have htrace : WordTrace (prefixWord ++ tailWord_895299) baseStart_895299 baseEnd_895299 := by
    simpa [prefixWord, tailWord_895299, baseEnd_895299] using wordTrace_append hprefix tailTrace_895299
  have hstable : (prefixWord ++ tailWord_895299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895299).length < 2 ^ (prefixWord ++ tailWord_895299).sum := by decide
  have hdescent : baseEnd_895299 < baseStart_895299 := by decide
  rcases family_descends (prefixWord ++ tailWord_895299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895316 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 7]
def baseStart_895316 : Nat := 118140960795 + 895316 * 2 ^ 59
def prefixEnd_895316 : Nat := 4983230072969 + 3 ^ 40 * 895316 * 2
def baseEnd_895316 : Nat := 102161654591316512385005

theorem tailTrace_895316 : CollatzResearch.WordTrace tailWord_895316 prefixEnd_895316 102161654591316512385005 := by
  unfold tailWord_895316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16327428612215257322148901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21769904816287009762865201 16327428612215257322148901)
  ·
    refine ⟨3061392864790360747902919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16327428612215257322148901 3061392864790360747902919)
    ·
      refine ⟨4592089297185541121854379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3061392864790360747902919 4592089297185541121854379)
      ·
        refine ⟨6888133945778311682781569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4592089297185541121854379 6888133945778311682781569)
        ·
          refine ⟨5166100459333733762086177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6888133945778311682781569 5166100459333733762086177)
          ·
            refine ⟨3874575344500300321564633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5166100459333733762086177 3874575344500300321564633)
            ·
              refine ⟨2905931508375225241173475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874575344500300321564633 2905931508375225241173475)
              ·
                refine ⟨4358897262562837861760213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905931508375225241173475 4358897262562837861760213)
                ·
                  refine ⟨102161654591316512385005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4358897262562837861760213 102161654591316512385005)
                  ·
                    rfl

theorem cell22_895316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_895316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895316 prefixEnd_895316 := by exact prefixLift 895316
  have htrace : WordTrace (prefixWord ++ tailWord_895316) baseStart_895316 baseEnd_895316 := by
    simpa [prefixWord, tailWord_895316, baseEnd_895316] using wordTrace_append hprefix tailTrace_895316
  have hstable : (prefixWord ++ tailWord_895316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895316).length < 2 ^ (prefixWord ++ tailWord_895316).sum := by decide
  have hdescent : baseEnd_895316 < baseStart_895316 := by decide
  rcases family_descends (prefixWord ++ tailWord_895316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895326 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_895326 : Nat := 118140960795 + 895326 * 2 ^ 59
def prefixEnd_895326 : Nat := 4983230072969 + 3 ^ 40 * 895326 * 2
def baseEnd_895326 : Nat := 306488386978312844404985

theorem tailTrace_895326 : CollatzResearch.WordTrace tailWord_895326 prefixEnd_895326 306488386978312844404985 := by
  unfold tailWord_895326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081902744299285794020229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21770147969596190901441221 4081902744299285794020229)
  ·
    refine ⟨765356764556116086378793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4081902744299285794020229 765356764556116086378793)
    ·
      refine ⟨574017573417087064784095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 765356764556116086378793 574017573417087064784095)
      ·
        refine ⟨861026360125630597176143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574017573417087064784095 861026360125630597176143)
        ·
          refine ⟨1291539540188445895764215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861026360125630597176143 1291539540188445895764215)
          ·
            refine ⟨1937309310282668843646323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291539540188445895764215 1937309310282668843646323)
            ·
              refine ⟨2905963965424003265469485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937309310282668843646323 2905963965424003265469485)
              ·
                refine ⟨1089736487034001224551057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2905963965424003265469485 1089736487034001224551057)
                ·
                  refine ⟨817302365275500918413293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089736487034001224551057 817302365275500918413293)
                  ·
                    refine ⟨306488386978312844404985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817302365275500918413293 306488386978312844404985)
                    ·
                      rfl

theorem cell22_895326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_895326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895326 prefixEnd_895326 := by exact prefixLift 895326
  have htrace : WordTrace (prefixWord ++ tailWord_895326) baseStart_895326 baseEnd_895326 := by
    simpa [prefixWord, tailWord_895326, baseEnd_895326] using wordTrace_append hprefix tailTrace_895326
  have hstable : (prefixWord ++ tailWord_895326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895326).length < 2 ^ (prefixWord ++ tailWord_895326).sum := by decide
  have hdescent : baseEnd_895326 < baseStart_895326 := by decide
  rcases family_descends (prefixWord ++ tailWord_895326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895329 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_895329 : Nat := 118140960795 + 895329 * 2 ^ 59
def prefixEnd_895329 : Nat := 4983230072969 + 3 ^ 40 * 895329 * 2
def baseEnd_895329 : Nat := 306489413939621836579975

theorem tailTrace_895329 : CollatzResearch.WordTrace tailWord_895329 prefixEnd_895329 306489413939621836579975 := by
  unfold tailWord_895329
  simp only [CollatzResearch.WordTrace]
  refine ⟨32655331373383417864521041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21770220915588945243014027 32655331373383417864521041)
  ·
    refine ⟨24491498530037563398390781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32655331373383417864521041 24491498530037563398390781)
    ·
      refine ⟨9184311948764086274396543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24491498530037563398390781 9184311948764086274396543)
      ·
        refine ⟨13776467923146129411594815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9184311948764086274396543 13776467923146129411594815)
        ·
          refine ⟨20664701884719194117392223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13776467923146129411594815 20664701884719194117392223)
          ·
            refine ⟨30997052827078791176088335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20664701884719194117392223 30997052827078791176088335)
            ·
              refine ⟨46495579240618186764132503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30997052827078791176088335 46495579240618186764132503)
              ·
                refine ⟨69743368860927280146198755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46495579240618186764132503 69743368860927280146198755)
                ·
                  refine ⟨104615053291390920219298133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69743368860927280146198755 104615053291390920219298133)
                  ·
                    refine ⟨306489413939621836579975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 104615053291390920219298133 306489413939621836579975)
                    ·
                      rfl

theorem cell22_895329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_895329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895329 prefixEnd_895329 := by exact prefixLift 895329
  have htrace : WordTrace (prefixWord ++ tailWord_895329) baseStart_895329 baseEnd_895329 := by
    simpa [prefixWord, tailWord_895329, baseEnd_895329] using wordTrace_append hprefix tailTrace_895329
  have hstable : (prefixWord ++ tailWord_895329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895329).length < 2 ^ (prefixWord ++ tailWord_895329).sum := by decide
  have hdescent : baseEnd_895329 < baseStart_895329 := by decide
  rcases family_descends (prefixWord ++ tailWord_895329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895333 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 5]
def baseStart_895333 : Nat := 118140960795 + 895333 * 2 ^ 59
def prefixEnd_895333 : Nat := 4983230072969 + 3 ^ 40 * 895333 * 2
def baseEnd_895333 : Nat := 102163594407122386493321

theorem tailTrace_895333 : CollatzResearch.WordTrace tailWord_895333 prefixEnd_895333 102163594407122386493321 := by
  unfold tailWord_895333
  simp only [CollatzResearch.WordTrace]
  refine ⟨32655477265368926547666653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21770318176912617698444435 32655477265368926547666653)
  ·
    refine ⟨12245803974513347455374995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32655477265368926547666653 12245803974513347455374995)
    ·
      refine ⟨18368705961770021183062493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12245803974513347455374995 18368705961770021183062493)
      ·
        refine ⟨6888264735663757943648435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18368705961770021183062493 6888264735663757943648435)
        ·
          refine ⟨10332397103495636915472653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888264735663757943648435 10332397103495636915472653)
          ·
            refine ⟨3874648913810863843302245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10332397103495636915472653 3874648913810863843302245)
            ·
              refine ⟨726496671339536970619171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3874648913810863843302245 726496671339536970619171)
              ·
                refine ⟨1089745007009305455928757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726496671339536970619171 1089745007009305455928757)
                ·
                  refine ⟨102163594407122386493321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089745007009305455928757 102163594407122386493321)
                  ·
                    rfl

theorem cell22_895333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_895333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895333 prefixEnd_895333 := by exact prefixLift 895333
  have htrace : WordTrace (prefixWord ++ tailWord_895333) baseStart_895333 baseEnd_895333 := by
    simpa [prefixWord, tailWord_895333, baseEnd_895333] using wordTrace_append hprefix tailTrace_895333
  have hstable : (prefixWord ++ tailWord_895333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895333).length < 2 ^ (prefixWord ++ tailWord_895333).sum := by decide
  have hdescent : baseEnd_895333 < baseStart_895333 := by decide
  rcases family_descends (prefixWord ++ tailWord_895333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895391 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 1, 6]
def baseStart_895391 : Nat := 118140960795 + 895391 * 2 ^ 59
def prefixEnd_895391 : Nat := 4983230072969 + 3 ^ 40 * 895391 * 2
def baseEnd_895391 : Nat := 306510637806674341529785

theorem tailTrace_895391 : CollatzResearch.WordTrace tailWord_895391 prefixEnd_895391 306510637806674341529785 := by
  unfold tailWord_895391
  simp only [CollatzResearch.WordTrace]
  refine ⟨32657592699158802453278027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21771728466105868302185351 32657592699158802453278027)
  ·
    refine ⟨48986389048738203679917041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32657592699158802453278027 48986389048738203679917041)
    ·
      refine ⟨36739791786553652759937781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48986389048738203679917041 36739791786553652759937781)
      ·
        refine ⟨3444355479989404946244167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36739791786553652759937781 3444355479989404946244167)
        ·
          refine ⟨5166533219984107419366251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444355479989404946244167 5166533219984107419366251)
          ·
            refine ⟨7749799829976161129049377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166533219984107419366251 7749799829976161129049377)
            ·
              refine ⟨5812349872482120846787033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7749799829976161129049377 5812349872482120846787033)
              ·
                refine ⟨4359262404361590635090275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5812349872482120846787033 4359262404361590635090275)
                ·
                  refine ⟨6538893606542385952635413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359262404361590635090275 6538893606542385952635413)
                  ·
                    refine ⟨306510637806674341529785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6538893606542385952635413 306510637806674341529785)
                    ·
                      rfl

theorem cell22_895391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_895391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895391 prefixEnd_895391 := by exact prefixLift 895391
  have htrace : WordTrace (prefixWord ++ tailWord_895391) baseStart_895391 baseEnd_895391 := by
    simpa [prefixWord, tailWord_895391, baseEnd_895391] using wordTrace_append hprefix tailTrace_895391
  have hstable : (prefixWord ++ tailWord_895391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895391).length < 2 ^ (prefixWord ++ tailWord_895391).sum := by decide
  have hdescent : baseEnd_895391 < baseStart_895391 := by decide
  rcases family_descends (prefixWord ++ tailWord_895391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895489 : List Nat := [1, 2, 4, 1, 3, 2, 3, 2, 1, 3]
def baseStart_895489 : Nat := 118140960795 + 895489 * 2 ^ 59
def prefixEnd_895489 : Nat := 4983230072969 + 3 ^ 40 * 895489 * 2
def baseEnd_895489 : Nat := 306544185209434752579485

theorem tailTrace_895489 : CollatzResearch.WordTrace tailWord_895489 prefixEnd_895489 306544185209434752579485 := by
  unfold tailWord_895489
  simp only [CollatzResearch.WordTrace]
  refine ⟨32661167052803765190345521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21774111368535843460230347 32661167052803765190345521)
  ·
    refine ⟨24495875289602823892759141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32661167052803765190345521 24495875289602823892759141)
    ·
      refine ⟨4592976616800529479892339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24495875289602823892759141 4592976616800529479892339)
      ·
        refine ⟨6889464925200794219838509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4592976616800529479892339 6889464925200794219838509)
        ·
          refine ⟨2583549346950297832439441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6889464925200794219838509 2583549346950297832439441)
          ·
            refine ⟨1937662010212723374329581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583549346950297832439441 1937662010212723374329581)
            ·
              refine ⟨726623253829771265373593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1937662010212723374329581 726623253829771265373593)
              ·
                refine ⟨544967440372328449030195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726623253829771265373593 544967440372328449030195)
                ·
                  refine ⟨817451160558492673545293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544967440372328449030195 817451160558492673545293)
                  ·
                    refine ⟨306544185209434752579485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817451160558492673545293 306544185209434752579485)
                    ·
                      rfl

theorem cell22_895489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_895489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895489 prefixEnd_895489 := by exact prefixLift 895489
  have htrace : WordTrace (prefixWord ++ tailWord_895489) baseStart_895489 baseEnd_895489 := by
    simpa [prefixWord, tailWord_895489, baseEnd_895489] using wordTrace_append hprefix tailTrace_895489
  have hstable : (prefixWord ++ tailWord_895489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895489).length < 2 ^ (prefixWord ++ tailWord_895489).sum := by decide
  have hdescent : baseEnd_895489 < baseStart_895489 := by decide
  rcases family_descends (prefixWord ++ tailWord_895489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895498 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_895498 : Nat := 118140960795 + 895498 * 2 ^ 59
def prefixEnd_895498 : Nat := 4983230072969 + 3 ^ 40 * 895498 * 2
def baseEnd_895498 : Nat := 306547266093361729104457

theorem tailTrace_895498 : CollatzResearch.WordTrace tailWord_895498 prefixEnd_895498 306547266093361729104457 := by
  unfold tailWord_895498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8165373827442789931855787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21774330206514106484948765 8165373827442789931855787)
  ·
    refine ⟨12248060741164184897783681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8165373827442789931855787 12248060741164184897783681)
    ·
      refine ⟨9186045555873138673337761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12248060741164184897783681 9186045555873138673337761)
      ·
        refine ⟨6889534166904854005003321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9186045555873138673337761 6889534166904854005003321)
        ·
          refine ⟨5167150625178640503752491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6889534166904854005003321 5167150625178640503752491)
          ·
            refine ⟨7750725937767960755628737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167150625178640503752491 7750725937767960755628737)
            ·
              refine ⟨5813044453325970566721553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7750725937767960755628737 5813044453325970566721553)
              ·
                refine ⟨4359783339994477925041165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5813044453325970566721553 4359783339994477925041165)
                ·
                  refine ⟨1634918752497929221890437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4359783339994477925041165 1634918752497929221890437)
                  ·
                    refine ⟨306547266093361729104457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1634918752497929221890437 306547266093361729104457)
                    ·
                      rfl

theorem cell22_895498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_895498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895498 prefixEnd_895498 := by exact prefixLift 895498
  have htrace : WordTrace (prefixWord ++ tailWord_895498) baseStart_895498 baseEnd_895498 := by
    simpa [prefixWord, tailWord_895498, baseEnd_895498] using wordTrace_append hprefix tailTrace_895498
  have hstable : (prefixWord ++ tailWord_895498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895498).length < 2 ^ (prefixWord ++ tailWord_895498).sum := by decide
  have hdescent : baseEnd_895498 < baseStart_895498 := by decide
  rcases family_descends (prefixWord ++ tailWord_895498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895502 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_895502 : Nat := 118140960795 + 895502 * 2 ^ 59
def prefixEnd_895502 : Nat := 4983230072969 + 3 ^ 40 * 895502 * 2
def baseEnd_895502 : Nat := 102182878458369017334815

theorem tailTrace_895502 : CollatzResearch.WordTrace tailWord_895502 prefixEnd_895502 102182878458369017334815 := by
  unfold tailWord_895502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082705150219583551321095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21774427467837778940379173 4082705150219583551321095)
  ·
    refine ⟨6124057725329375326981643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082705150219583551321095 6124057725329375326981643)
    ·
      refine ⟨9186086587994062990472465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6124057725329375326981643 9186086587994062990472465)
      ·
        refine ⟨6889564940995547242854349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9186086587994062990472465 6889564940995547242854349)
        ·
          refine ⟨2583586852873330216070381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6889564940995547242854349 2583586852873330216070381)
          ·
            refine ⟨968845069827498831026393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2583586852873330216070381 968845069827498831026393)
            ·
              refine ⟨726633802370624123269795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968845069827498831026393 726633802370624123269795)
              ·
                refine ⟨1089950703555936184904693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726633802370624123269795 1089950703555936184904693)
                ·
                  refine ⟨102182878458369017334815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089950703555936184904693 102182878458369017334815)
                  ·
                    rfl

theorem cell22_895502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_895502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895502 prefixEnd_895502 := by exact prefixLift 895502
  have htrace : WordTrace (prefixWord ++ tailWord_895502) baseStart_895502 baseEnd_895502 := by
    simpa [prefixWord, tailWord_895502, baseEnd_895502] using wordTrace_append hprefix tailTrace_895502
  have hstable : (prefixWord ++ tailWord_895502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895502).length < 2 ^ (prefixWord ++ tailWord_895502).sum := by decide
  have hdescent : baseEnd_895502 < baseStart_895502 := by decide
  rcases family_descends (prefixWord ++ tailWord_895502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895540 : List Nat := [2, 5, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_895540 : Nat := 118140960795 + 895540 * 2 ^ 59
def prefixEnd_895540 : Nat := 4983230072969 + 3 ^ 40 * 895540 * 2
def baseEnd_895540 : Nat := 306561643551687619554329

theorem tailTrace_895540 : CollatzResearch.WordTrace tailWord_895540 prefixEnd_895540 306561643551687619554329 := by
  unfold tailWord_895540
  simp only [CollatzResearch.WordTrace]
  refine ⟨16331513587809500450226037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21775351450412667266968049 16331513587809500450226037)
  ·
    refine ⟨1531079398857140667208691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16331513587809500450226037 1531079398857140667208691)
    ·
      refine ⟨2296619098285711000813037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531079398857140667208691 2296619098285711000813037)
      ·
        refine ⟨861232161857141625304889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2296619098285711000813037 861232161857141625304889)
        ·
          refine ⟨645924121392856218978667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861232161857141625304889 645924121392856218978667)
          ·
            refine ⟨968886182089284328468001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645924121392856218978667 968886182089284328468001)
            ·
              refine ⟨726664636566963246351001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968886182089284328468001 726664636566963246351001)
              ·
                refine ⟨544998477425222434763251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726664636566963246351001 544998477425222434763251)
                ·
                  refine ⟨817497716137833652144877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544998477425222434763251 817497716137833652144877)
                  ·
                    refine ⟨306561643551687619554329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817497716137833652144877 306561643551687619554329)
                    ·
                      rfl

theorem cell22_895540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_895540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895540 prefixEnd_895540 := by exact prefixLift 895540
  have htrace : WordTrace (prefixWord ++ tailWord_895540) baseStart_895540 baseEnd_895540 := by
    simpa [prefixWord, tailWord_895540, baseEnd_895540] using wordTrace_append hprefix tailTrace_895540
  have hstable : (prefixWord ++ tailWord_895540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895540).length < 2 ^ (prefixWord ++ tailWord_895540).sum := by decide
  have hdescent : baseEnd_895540 < baseStart_895540 := by decide
  rcases family_descends (prefixWord ++ tailWord_895540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895543 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 2, 4]
def baseStart_895543 : Nat := 118140960795 + 895543 * 2 ^ 59
def prefixEnd_895543 : Nat := 4983230072969 + 3 ^ 40 * 895543 * 2
def baseEnd_895543 : Nat := 306562670512996611729319

theorem tailTrace_895543 : CollatzResearch.WordTrace tailWord_895543 prefixEnd_895543 306562670512996611729319 := by
  unfold tailWord_895543
  simp only [CollatzResearch.WordTrace]
  refine ⟨32663136594608132412811283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21775424396405421608540855 32663136594608132412811283)
  ·
    refine ⟨48994704891912198619216925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32663136594608132412811283 48994704891912198619216925)
    ·
      refine ⟨18373014334467074482206347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48994704891912198619216925 18373014334467074482206347)
      ·
        refine ⟨27559521501700611723309521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18373014334467074482206347 27559521501700611723309521)
        ·
          refine ⟨20669641126275458792482141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27559521501700611723309521 20669641126275458792482141)
          ·
            refine ⟨7751115422353297047180803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20669641126275458792482141 7751115422353297047180803)
            ·
              refine ⟨11626673133529945570771205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751115422353297047180803 11626673133529945570771205)
              ·
                refine ⟨2180001212536864794519601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11626673133529945570771205 2180001212536864794519601)
                ·
                  refine ⟨1635000909402648595889701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2180001212536864794519601 1635000909402648595889701)
                  ·
                    refine ⟨306562670512996611729319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635000909402648595889701 306562670512996611729319)
                    ·
                      rfl

theorem cell22_895543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_895543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895543 prefixEnd_895543 := by exact prefixLift 895543
  have htrace : WordTrace (prefixWord ++ tailWord_895543) baseStart_895543 baseEnd_895543 := by
    simpa [prefixWord, tailWord_895543, baseEnd_895543] using wordTrace_append hprefix tailTrace_895543
  have hstable : (prefixWord ++ tailWord_895543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895543).length < 2 ^ (prefixWord ++ tailWord_895543).sum := by decide
  have hdescent : baseEnd_895543 < baseStart_895543 := by decide
  rcases family_descends (prefixWord ++ tailWord_895543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895603 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 5]
def baseStart_895603 : Nat := 118140960795 + 895603 * 2 ^ 59
def prefixEnd_895603 : Nat := 4983230072969 + 3 ^ 40 * 895603 * 2
def baseEnd_895603 : Nat := 102194403246392151743045

theorem tailTrace_895603 : CollatzResearch.WordTrace tailWord_895603 prefixEnd_895603 102194403246392151743045 := by
  unfold tailWord_895603
  simp only [CollatzResearch.WordTrace]
  refine ⟨32665324974390762659995463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21776883316260508439996975 32665324974390762659995463)
  ·
    refine ⟨48997987461586143989993195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32665324974390762659995463 48997987461586143989993195)
    ·
      refine ⟨73496981192379215984989793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48997987461586143989993195 73496981192379215984989793)
      ·
        refine ⟨55122735894284411988742345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73496981192379215984989793 55122735894284411988742345)
        ·
          refine ⟨41342051920713308991556759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55122735894284411988742345 41342051920713308991556759)
          ·
            refine ⟨62013077881069963487335139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41342051920713308991556759 62013077881069963487335139)
            ·
              refine ⟨93019616821604945231002709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62013077881069963487335139 93019616821604945231002709)
              ·
                refine ⟨1090073634628182951925813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 93019616821604945231002709 1090073634628182951925813)
                ·
                  refine ⟨102194403246392151743045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090073634628182951925813 102194403246392151743045)
                  ·
                    rfl

theorem cell22_895603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 5].length) (baseStart_895603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895603 prefixEnd_895603 := by exact prefixLift 895603
  have htrace : WordTrace (prefixWord ++ tailWord_895603) baseStart_895603 baseEnd_895603 := by
    simpa [prefixWord, tailWord_895603, baseEnd_895603] using wordTrace_append hprefix tailTrace_895603
  have hstable : (prefixWord ++ tailWord_895603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895603).length < 2 ^ (prefixWord ++ tailWord_895603).sum := by decide
  have hdescent : baseEnd_895603 < baseStart_895603 := by decide
  rcases family_descends (prefixWord ++ tailWord_895603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895607 : List Nat := [1, 1, 3, 1, 1, 3, 4, 4, 1, 3]
def baseStart_895607 : Nat := 118140960795 + 895607 * 2 ^ 59
def prefixEnd_895607 : Nat := 4983230072969 + 3 ^ 40 * 895607 * 2
def baseEnd_895607 : Nat := 306584579020921778129123

theorem tailTrace_895607 : CollatzResearch.WordTrace tailWord_895607 prefixEnd_895607 306584579020921778129123 := by
  unfold tailWord_895607
  simp only [CollatzResearch.WordTrace]
  refine ⟨32665470866376271343141075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21776980577584180895427383 32665470866376271343141075)
  ·
    refine ⟨48998206299564407014711613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32665470866376271343141075 48998206299564407014711613)
    ·
      refine ⟨18374327362336652630516855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48998206299564407014711613 18374327362336652630516855)
      ·
        refine ⟨27561491043504978945775283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18374327362336652630516855 27561491043504978945775283)
        ·
          refine ⟨41342236565257468418662925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27561491043504978945775283 41342236565257468418662925)
          ·
            refine ⟨15503338711971550656998597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41342236565257468418662925 15503338711971550656998597)
            ·
              refine ⟨2906876008494665748187237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15503338711971550656998597 2906876008494665748187237)
              ·
                refine ⟨545039251592749827785107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2906876008494665748187237 545039251592749827785107)
                ·
                  refine ⟨817558877389124741677661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545039251592749827785107 817558877389124741677661)
                  ·
                    refine ⟨306584579020921778129123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817558877389124741677661 306584579020921778129123)
                    ·
                      rfl

theorem cell22_895607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_895607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895607 prefixEnd_895607 := by exact prefixLift 895607
  have htrace : WordTrace (prefixWord ++ tailWord_895607) baseStart_895607 baseEnd_895607 := by
    simpa [prefixWord, tailWord_895607, baseEnd_895607] using wordTrace_append hprefix tailTrace_895607
  have hstable : (prefixWord ++ tailWord_895607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895607).length < 2 ^ (prefixWord ++ tailWord_895607).sum := by decide
  have hdescent : baseEnd_895607 < baseStart_895607 := by decide
  rcases family_descends (prefixWord ++ tailWord_895607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895633 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_895633 : Nat := 118140960795 + 895633 * 2 ^ 59
def prefixEnd_895633 : Nat := 4983230072969 + 3 ^ 40 * 895633 * 2
def baseEnd_895633 : Nat := 306593479352266376979043

theorem tailTrace_895633 : CollatzResearch.WordTrace tailWord_895633 prefixEnd_895633 306593479352266376979043 := by
  unfold tailWord_895633
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666419164282077783587553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21777612776188051855725035 32666419164282077783587553)
  ·
    refine ⟨24499814373211558337690665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32666419164282077783587553 24499814373211558337690665)
    ·
      refine ⟨18374860779908668753267999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24499814373211558337690665 18374860779908668753267999)
      ·
        refine ⟨27562291169863003129901999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18374860779908668753267999 27562291169863003129901999)
        ·
          refine ⟨41343436754794504694852999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27562291169863003129901999 41343436754794504694852999)
          ·
            refine ⟨62015155132191757042279499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41343436754794504694852999 62015155132191757042279499)
            ·
              refine ⟨93022732698287635563419249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62015155132191757042279499 93022732698287635563419249)
              ·
                refine ⟨69767049523715726672564437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93022732698287635563419249 69767049523715726672564437)
                ·
                  refine ⟨1635165223212087343888229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 69767049523715726672564437 1635165223212087343888229)
                  ·
                    refine ⟨306593479352266376979043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635165223212087343888229 306593479352266376979043)
                    ·
                      rfl

theorem cell22_895633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_895633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895633 prefixEnd_895633 := by exact prefixLift 895633
  have htrace : WordTrace (prefixWord ++ tailWord_895633) baseStart_895633 baseEnd_895633 := by
    simpa [prefixWord, tailWord_895633, baseEnd_895633] using wordTrace_append hprefix tailTrace_895633
  have hstable : (prefixWord ++ tailWord_895633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895633).length < 2 ^ (prefixWord ++ tailWord_895633).sum := by decide
  have hdescent : baseEnd_895633 < baseStart_895633 := by decide
  rcases family_descends (prefixWord ++ tailWord_895633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895658 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_895658 : Nat := 118140960795 + 895658 * 2 ^ 59
def prefixEnd_895658 : Nat := 4983230072969 + 3 ^ 40 * 895658 * 2
def baseEnd_895658 : Nat := 306602037363174645103967

theorem tailTrace_895658 : CollatzResearch.WordTrace tailWord_895658 prefixEnd_895658 306602037363174645103967 := by
  unfold tailWord_895658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166832747297876763311907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21778220659461004702165085 8166832747297876763311907)
  ·
    refine ⟨12250249120946815144967861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8166832747297876763311907 12250249120946815144967861)
    ·
      refine ⟨1148460855088763919840737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12250249120946815144967861 1148460855088763919840737)
      ·
        refine ⟨861345641316572939880553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148460855088763919840737 861345641316572939880553)
        ·
          refine ⟨646009230987429704910415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861345641316572939880553 646009230987429704910415)
          ·
            refine ⟨969013846481144557365623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646009230987429704910415 969013846481144557365623)
            ·
              refine ⟨1453520769721716836048435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969013846481144557365623 1453520769721716836048435)
              ·
                refine ⟨2180281154582575254072653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1453520769721716836048435 2180281154582575254072653)
                ·
                  refine ⟨817605432968465720277245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2180281154582575254072653 817605432968465720277245)
                  ·
                    refine ⟨306602037363174645103967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817605432968465720277245 306602037363174645103967)
                    ·
                      rfl

theorem cell22_895658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_895658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895658 prefixEnd_895658 := by exact prefixLift 895658
  have htrace : WordTrace (prefixWord ++ tailWord_895658) baseStart_895658 baseEnd_895658 := by
    simpa [prefixWord, tailWord_895658, baseEnd_895658] using wordTrace_append hprefix tailTrace_895658
  have hstable : (prefixWord ++ tailWord_895658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895658).length < 2 ^ (prefixWord ++ tailWord_895658).sum := by decide
  have hdescent : baseEnd_895658 < baseStart_895658 := by decide
  rcases family_descends (prefixWord ++ tailWord_895658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895684 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_895684 : Nat := 118140960795 + 895684 * 2 ^ 59
def prefixEnd_895684 : Nat := 4983230072969 + 3 ^ 40 * 895684 * 2
def baseEnd_895684 : Nat := 306610937694519243953887

theorem tailTrace_895684 : CollatzResearch.WordTrace tailWord_895684 prefixEnd_895684 306610937694519243953887 := by
  unfold tailWord_895684
  simp only [CollatzResearch.WordTrace]
  refine ⟨16334139643548656746847053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21778852858064875662462737 16334139643548656746847053)
  ·
    refine ⟨6125302366330746280067645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16334139643548656746847053 6125302366330746280067645)
    ·
      refine ⟨2296988387374029855025367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6125302366330746280067645 2296988387374029855025367)
      ·
        refine ⟨3445482581061044782538051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296988387374029855025367 3445482581061044782538051)
        ·
          refine ⟨5168223871591567173807077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445482581061044782538051 5168223871591567173807077)
          ·
            refine ⟨969041975923418845088827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5168223871591567173807077 969041975923418845088827)
            ·
              refine ⟨1453562963885128267633241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969041975923418845088827 1453562963885128267633241)
              ·
                refine ⟨1090172222913846200724931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1453562963885128267633241 1090172222913846200724931)
                ·
                  refine ⟨1635258334370769301087397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090172222913846200724931 1635258334370769301087397)
                  ·
                    refine ⟨306610937694519243953887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635258334370769301087397 306610937694519243953887)
                    ·
                      rfl

theorem cell22_895684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_895684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895684 prefixEnd_895684 := by exact prefixLift 895684
  have htrace : WordTrace (prefixWord ++ tailWord_895684) baseStart_895684 baseEnd_895684 := by
    simpa [prefixWord, tailWord_895684, baseEnd_895684] using wordTrace_append hprefix tailTrace_895684
  have hstable : (prefixWord ++ tailWord_895684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895684).length < 2 ^ (prefixWord ++ tailWord_895684).sum := by decide
  have hdescent : baseEnd_895684 < baseStart_895684 := by decide
  rcases family_descends (prefixWord ++ tailWord_895684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895701 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_895701 : Nat := 118140960795 + 895701 * 2 ^ 59
def prefixEnd_895701 : Nat := 4983230072969 + 3 ^ 40 * 895701 * 2
def baseEnd_895701 : Nat := 306616757141936866278835

theorem tailTrace_895701 : CollatzResearch.WordTrace tailWord_895701 prefixEnd_895701 306616757141936866278835 := by
  unfold tailWord_895701
  simp only [CollatzResearch.WordTrace]
  refine ⟨32668899328035725397062957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21779266218690483598041971 32668899328035725397062957)
  ·
    refine ⟨12250837248013397023898609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32668899328035725397062957 12250837248013397023898609)
    ·
      refine ⟨9188127936010047767923957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12250837248013397023898609 9188127936010047767923957)
      ·
        refine ⟨861386994000941978242871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9188127936010047767923957 861386994000941978242871)
        ·
          refine ⟨1292080491001412967364307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861386994000941978242871 1292080491001412967364307)
          ·
            refine ⟨1938120736502119451046461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292080491001412967364307 1938120736502119451046461)
            ·
              refine ⟨726795276188294794142423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1938120736502119451046461 726795276188294794142423)
              ·
                refine ⟨1090192914282442191213635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726795276188294794142423 1090192914282442191213635)
                ·
                  refine ⟨1635289371423663286820453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090192914282442191213635 1635289371423663286820453)
                  ·
                    refine ⟨306616757141936866278835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1635289371423663286820453 306616757141936866278835)
                    ·
                      rfl

theorem cell22_895701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_895701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895701 prefixEnd_895701 := by exact prefixLift 895701
  have htrace : WordTrace (prefixWord ++ tailWord_895701) baseStart_895701 baseEnd_895701 := by
    simpa [prefixWord, tailWord_895701, baseEnd_895701] using wordTrace_append hprefix tailTrace_895701
  have hstable : (prefixWord ++ tailWord_895701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895701).length < 2 ^ (prefixWord ++ tailWord_895701).sum := by decide
  have hdescent : baseEnd_895701 < baseStart_895701 := by decide
  rcases family_descends (prefixWord ++ tailWord_895701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895759 : List Nat := [1, 1, 2, 1, 1, 1, 8, 3, 1, 3]
def baseStart_895759 : Nat := 118140960795 + 895759 * 2 ^ 59
def prefixEnd_895759 : Nat := 4983230072969 + 3 ^ 40 * 895759 * 2
def baseEnd_895759 : Nat := 306636611727244048328657

theorem tailTrace_895759 : CollatzResearch.WordTrace tailWord_895759 prefixEnd_895759 306636611727244048328657 := by
  unfold tailWord_895759
  simp only [CollatzResearch.WordTrace]
  refine ⟨32671014761825601302674331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21780676507883734201782887 32671014761825601302674331)
  ·
    refine ⟨49006522142738401954011497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32671014761825601302674331 49006522142738401954011497)
    ·
      refine ⟨36754891607053801465508623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49006522142738401954011497 36754891607053801465508623)
      ·
        refine ⟨55132337410580702198262935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36754891607053801465508623 55132337410580702198262935)
        ·
          refine ⟨82698506115871053297394403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55132337410580702198262935 82698506115871053297394403)
          ·
            refine ⟨124047759173806579946091605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82698506115871053297394403 124047759173806579946091605)
            ·
              refine ⟨1453684677818045858743261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 124047759173806579946091605 1453684677818045858743261)
              ·
                refine ⟨545131754181767197028723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1453684677818045858743261 545131754181767197028723)
                ·
                  refine ⟨817697631272650795543085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545131754181767197028723 817697631272650795543085)
                  ·
                    refine ⟨306636611727244048328657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817697631272650795543085 306636611727244048328657)
                    ·
                      rfl

theorem cell22_895759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 1, 3].length) (baseStart_895759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895759 prefixEnd_895759 := by exact prefixLift 895759
  have htrace : WordTrace (prefixWord ++ tailWord_895759) baseStart_895759 baseEnd_895759 := by
    simpa [prefixWord, tailWord_895759, baseEnd_895759] using wordTrace_append hprefix tailTrace_895759
  have hstable : (prefixWord ++ tailWord_895759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895759).length < 2 ^ (prefixWord ++ tailWord_895759).sum := by decide
  have hdescent : baseEnd_895759 < baseStart_895759 := by decide
  rcases family_descends (prefixWord ++ tailWord_895759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895770 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_895770 : Nat := 118140960795 + 895770 * 2 ^ 59
def prefixEnd_895770 : Nat := 4983230072969 + 3 ^ 40 * 895770 * 2
def baseEnd_895770 : Nat := 306640377252043686303623

theorem tailTrace_895770 : CollatzResearch.WordTrace tailWord_895770 prefixEnd_895770 306640377252043686303623 := by
  unfold tailWord_895770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167853991196437545331191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21780943976523833454216509 8167853991196437545331191)
  ·
    refine ⟨12251780986794656317996787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8167853991196437545331191 12251780986794656317996787)
    ·
      refine ⟨18377671480191984476995181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12251780986794656317996787 18377671480191984476995181)
      ·
        refine ⟨6891626805071994178873193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18377671480191984476995181 6891626805071994178873193)
        ·
          refine ⟨5168720103803995634154895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6891626805071994178873193 5168720103803995634154895)
          ·
            refine ⟨7753080155705993451232343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168720103803995634154895 7753080155705993451232343)
            ·
              refine ⟨11629620233558990176848515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753080155705993451232343 11629620233558990176848515)
              ·
                refine ⟨17444430350338485265272773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11629620233558990176848515 17444430350338485265272773)
                ·
                  refine ⟨3270830690688465987238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17444430350338485265272773 3270830690688465987238645)
                  ·
                    refine ⟨306640377252043686303623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3270830690688465987238645 306640377252043686303623)
                    ·
                      rfl

theorem cell22_895770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_895770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895770 prefixEnd_895770 := by exact prefixLift 895770
  have htrace : WordTrace (prefixWord ++ tailWord_895770) baseStart_895770 baseEnd_895770 := by
    simpa [prefixWord, tailWord_895770, baseEnd_895770] using wordTrace_append hprefix tailTrace_895770
  have hstable : (prefixWord ++ tailWord_895770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895770).length < 2 ^ (prefixWord ++ tailWord_895770).sum := by decide
  have hdescent : baseEnd_895770 < baseStart_895770 := by decide
  rcases family_descends (prefixWord ++ tailWord_895770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895772 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 5]
def baseStart_895772 : Nat := 118140960795 + 895772 * 2 ^ 59
def prefixEnd_895772 : Nat := 4983230072969 + 3 ^ 40 * 895772 * 2
def baseEnd_895772 : Nat := 102213687297638782584539

theorem tailTrace_895772 : CollatzResearch.WordTrace tailWord_895772 prefixEnd_895772 102213687297638782584539 := by
  unfold tailWord_895772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335744455389252261448785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21780992607185669681931713 16335744455389252261448785)
  ·
    refine ⟨12251808341541939196086589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16335744455389252261448785 12251808341541939196086589)
    ·
      refine ⟨4594428128078227198532471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12251808341541939196086589 4594428128078227198532471)
      ·
        refine ⟨6891642192117340797798707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594428128078227198532471 6891642192117340797798707)
        ·
          refine ⟨10337463288176011196698061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891642192117340797798707 10337463288176011196698061)
          ·
            refine ⟨3876548733066004198761773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10337463288176011196698061 3876548733066004198761773)
            ·
              refine ⟨1453705774899751574535665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3876548733066004198761773 1453705774899751574535665)
              ·
                refine ⟨1090279331174813680901749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1453705774899751574535665 1090279331174813680901749)
                ·
                  refine ⟨102213687297638782584539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090279331174813680901749 102213687297638782584539)
                  ·
                    rfl

theorem cell22_895772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_895772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895772 prefixEnd_895772 := by exact prefixLift 895772
  have htrace : WordTrace (prefixWord ++ tailWord_895772) baseStart_895772 baseEnd_895772 := by
    simpa [prefixWord, tailWord_895772, baseEnd_895772] using wordTrace_append hprefix tailTrace_895772
  have hstable : (prefixWord ++ tailWord_895772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895772).length < 2 ^ (prefixWord ++ tailWord_895772).sum := by decide
  have hdescent : baseEnd_895772 < baseStart_895772 := by decide
  rcases family_descends (prefixWord ++ tailWord_895772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895800 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 6]
def baseStart_895800 : Nat := 118140960795 + 895800 * 2 ^ 59
def prefixEnd_895800 : Nat := 4983230072969 + 3 ^ 40 * 895800 * 2
def baseEnd_895800 : Nat := 102216882288377869351177

theorem tailTrace_895800 : CollatzResearch.WordTrace tailWord_895800 prefixEnd_895800 102216882288377869351177 := by
  unfold tailWord_895800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16336255077338532652458427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21781673436451376869944569 16336255077338532652458427)
  ·
    refine ⟨24504382616007798978687641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16336255077338532652458427 24504382616007798978687641)
    ·
      refine ⟨18378286962005849234015731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24504382616007798978687641 18378286962005849234015731)
      ·
        refine ⟨27567430443008773851023597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18378286962005849234015731 27567430443008773851023597)
        ·
          refine ⟨10337786416128290194133849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27567430443008773851023597 10337786416128290194133849)
          ·
            refine ⟨7753339812096217645600387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10337786416128290194133849 7753339812096217645600387)
            ·
              refine ⟨11630009718144326468400581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753339812096217645600387 11630009718144326468400581)
              ·
                refine ⟨2180626822152061212825109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11630009718144326468400581 2180626822152061212825109)
                ·
                  refine ⟨102216882288377869351177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2180626822152061212825109 102216882288377869351177)
                  ·
                    rfl

theorem cell22_895800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_895800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895800 prefixEnd_895800 := by exact prefixLift 895800
  have htrace : WordTrace (prefixWord ++ tailWord_895800) baseStart_895800 baseEnd_895800 := by
    simpa [prefixWord, tailWord_895800, baseEnd_895800] using wordTrace_append hprefix tailTrace_895800
  have hstable : (prefixWord ++ tailWord_895800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895800).length < 2 ^ (prefixWord ++ tailWord_895800).sum := by decide
  have hdescent : baseEnd_895800 < baseStart_895800 := by decide
  rcases family_descends (prefixWord ++ tailWord_895800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895815 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 3, 5]
def baseStart_895815 : Nat := 118140960795 + 895815 * 2 ^ 59
def prefixEnd_895815 : Nat := 4983230072969 + 3 ^ 40 * 895815 * 2
def baseEnd_895815 : Nat := 306655781671678568928485

theorem tailTrace_895815 : CollatzResearch.WordTrace tailWord_895815 prefixEnd_895815 306655781671678568928485 := by
  unfold tailWord_895815
  simp only [CollatzResearch.WordTrace]
  refine ⟨32673057249622722866712899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21782038166415148577808599 32673057249622722866712899)
  ·
    refine ⟨49009585874434084300069349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32673057249622722866712899 49009585874434084300069349)
    ·
      refine ⟨9189297351456390806263003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49009585874434084300069349 9189297351456390806263003)
      ·
        refine ⟨13783946027184586209394505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9189297351456390806263003 13783946027184586209394505)
        ·
          refine ⟨10337959520388439657045879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13783946027184586209394505 10337959520388439657045879)
          ·
            refine ⟨15506939280582659485568819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337959520388439657045879 15506939280582659485568819)
            ·
              refine ⟨23260408920873989228353229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15506939280582659485568819 23260408920873989228353229)
              ·
                refine ⟨8722653345327745960632461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23260408920873989228353229 8722653345327745960632461)
                ·
                  refine ⟨3270995004497904735237173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8722653345327745960632461 3270995004497904735237173)
                  ·
                    refine ⟨306655781671678568928485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3270995004497904735237173 306655781671678568928485)
                    ·
                      rfl

theorem cell22_895815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_895815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895815 prefixEnd_895815 := by exact prefixLift 895815
  have htrace : WordTrace (prefixWord ++ tailWord_895815) baseStart_895815 baseEnd_895815 := by
    simpa [prefixWord, tailWord_895815, baseEnd_895815] using wordTrace_append hprefix tailTrace_895815
  have hstable : (prefixWord ++ tailWord_895815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895815).length < 2 ^ (prefixWord ++ tailWord_895815).sum := by decide
  have hdescent : baseEnd_895815 < baseStart_895815 := by decide
  rcases family_descends (prefixWord ++ tailWord_895815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895845 : List Nat := [1, 3, 1, 3, 1, 1, 3, 9]
def baseStart_895845 : Nat := 118140960795 + 895845 * 2 ^ 59
def prefixEnd_895845 : Nat := 4983230072969 + 3 ^ 40 * 895845 * 2
def baseEnd_895845 : Nat := 34074005698307610075377

theorem tailTrace_895845 : CollatzResearch.WordTrace tailWord_895845 prefixEnd_895845 34074005698307610075377 := by
  unfold tailWord_895845
  simp only [CollatzResearch.WordTrace]
  refine ⟨32674151439514037990304989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21782767626342691993536659 32674151439514037990304989)
  ·
    refine ⟨12252806789817764246364371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32674151439514037990304989 12252806789817764246364371)
    ·
      refine ⟨18379210184726646369546557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12252806789817764246364371 18379210184726646369546557)
      ·
        refine ⟨6892203819272492388579959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18379210184726646369546557 6892203819272492388579959)
        ·
          refine ⟨10338305728908738582869939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6892203819272492388579959 10338305728908738582869939)
          ·
            refine ⟨15507458593363107874304909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10338305728908738582869939 15507458593363107874304909)
            ·
              refine ⟨5815296972511165452864341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15507458593363107874304909 5815296972511165452864341)
              ·
                refine ⟨34074005698307610075377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5815296972511165452864341 34074005698307610075377)
                ·
                  rfl

theorem cell22_895845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 9].length) (baseStart_895845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895845 prefixEnd_895845 := by exact prefixLift 895845
  have htrace : WordTrace (prefixWord ++ tailWord_895845) baseStart_895845 baseEnd_895845 := by
    simpa [prefixWord, tailWord_895845, baseEnd_895845] using wordTrace_append hprefix tailTrace_895845
  have hstable : (prefixWord ++ tailWord_895845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895845).length < 2 ^ (prefixWord ++ tailWord_895845).sum := by decide
  have hdescent : baseEnd_895845 < baseStart_895845 := by decide
  rcases family_descends (prefixWord ++ tailWord_895845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895892 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_895892 : Nat := 118140960795 + 895892 * 2 ^ 59
def prefixEnd_895892 : Nat := 4983230072969 + 3 ^ 40 * 895892 * 2
def baseEnd_895892 : Nat := 306682140345276034753249

theorem tailTrace_895892 : CollatzResearch.WordTrace tailWord_895892 prefixEnd_895892 306682140345276034753249 := by
  unfold tailWord_895892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16337932835171882508632965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21783910446895843344843953 16337932835171882508632965)
  ·
    refine ⟨3063362406594727970368681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16337932835171882508632965 3063362406594727970368681)
    ·
      refine ⟨2297521804946045977776511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3063362406594727970368681 2297521804946045977776511)
      ·
        refine ⟨3446282707419068966664767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297521804946045977776511 3446282707419068966664767)
        ·
          refine ⟨5169424061128603449997151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446282707419068966664767 5169424061128603449997151)
          ·
            refine ⟨7754136091692905174995727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169424061128603449997151 7754136091692905174995727)
            ·
              refine ⟨11631204137539357762493591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754136091692905174995727 11631204137539357762493591)
              ·
                refine ⟨17446806206309036643740387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11631204137539357762493591 17446806206309036643740387)
                ·
                  refine ⟨26170209309463554965610581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17446806206309036643740387 26170209309463554965610581)
                  ·
                    refine ⟨306682140345276034753249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26170209309463554965610581 306682140345276034753249)
                    ·
                      rfl

theorem cell22_895892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_895892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895892 prefixEnd_895892 := by exact prefixLift 895892
  have htrace : WordTrace (prefixWord ++ tailWord_895892) baseStart_895892 baseEnd_895892 := by
    simpa [prefixWord, tailWord_895892, baseEnd_895892] using wordTrace_append hprefix tailTrace_895892
  have hstable : (prefixWord ++ tailWord_895892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895892).length < 2 ^ (prefixWord ++ tailWord_895892).sum := by decide
  have hdescent : baseEnd_895892 < baseStart_895892 := by decide
  rcases family_descends (prefixWord ++ tailWord_895892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895907 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 5]
def baseStart_895907 : Nat := 118140960795 + 895907 * 2 ^ 59
def prefixEnd_895907 : Nat := 4983230072969 + 3 ^ 40 * 895907 * 2
def baseEnd_895907 : Nat := 102229091717273665209401

theorem tailTrace_895907 : CollatzResearch.WordTrace tailWord_895907 prefixEnd_895907 102229091717273665209401 := by
  unfold tailWord_895907
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676412765289422579061975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21784275176859615052707983 32676412765289422579061975)
  ·
    refine ⟨49014619147934133868592963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32676412765289422579061975 49014619147934133868592963)
    ·
      refine ⟨73521928721901200802889445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49014619147934133868592963 73521928721901200802889445)
      ·
        refine ⟨13785361635356475150541771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73521928721901200802889445 13785361635356475150541771)
        ·
          refine ⟨20678042453034712725812657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13785361635356475150541771 20678042453034712725812657)
          ·
            refine ⟨15508531839776034544359493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20678042453034712725812657 15508531839776034544359493)
            ·
              refine ⟨2907849719958006477067405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15508531839776034544359493 2907849719958006477067405)
              ·
                refine ⟨1090443644984252428900277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2907849719958006477067405 1090443644984252428900277)
                ·
                  refine ⟨102229091717273665209401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090443644984252428900277 102229091717273665209401)
                  ·
                    rfl

theorem cell22_895907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 5].length) (baseStart_895907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895907 prefixEnd_895907 := by exact prefixLift 895907
  have htrace : WordTrace (prefixWord ++ tailWord_895907) baseStart_895907 baseEnd_895907 := by
    simpa [prefixWord, tailWord_895907, baseEnd_895907] using wordTrace_append hprefix tailTrace_895907
  have hstable : (prefixWord ++ tailWord_895907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895907).length < 2 ^ (prefixWord ++ tailWord_895907).sum := by decide
  have hdescent : baseEnd_895907 < baseStart_895907 := by decide
  rcases family_descends (prefixWord ++ tailWord_895907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895911 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 3, 3]
def baseStart_895911 : Nat := 118140960795 + 895911 * 2 ^ 59
def prefixEnd_895911 : Nat := 4983230072969 + 3 ^ 40 * 895911 * 2
def baseEnd_895911 : Nat := 306688644433566318528191

theorem tailTrace_895911 : CollatzResearch.WordTrace tailWord_895911 prefixEnd_895911 306688644433566318528191 := by
  unfold tailWord_895911
  simp only [CollatzResearch.WordTrace]
  refine ⟨32676558657274931262207587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21784372438183287508138391 32676558657274931262207587)
  ·
    refine ⟨49014837985912396893311381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32676558657274931262207587 49014837985912396893311381)
    ·
      refine ⟨2297570530589643604373971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49014837985912396893311381 2297570530589643604373971)
      ·
        refine ⟨3446355795884465406560957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297570530589643604373971 3446355795884465406560957)
        ·
          refine ⟨1292383423456674527460359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3446355795884465406560957 1292383423456674527460359)
          ·
            refine ⟨1938575135185011791190539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292383423456674527460359 1938575135185011791190539)
            ·
              refine ⟨2907862702777517686785809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1938575135185011791190539 2907862702777517686785809)
              ·
                refine ⟨2180897027083138265089357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907862702777517686785809 2180897027083138265089357)
                ·
                  refine ⟨817836385156176849408509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2180897027083138265089357 817836385156176849408509)
                  ·
                    refine ⟨306688644433566318528191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 817836385156176849408509 306688644433566318528191)
                    ·
                      rfl

theorem cell22_895911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_895911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895911 prefixEnd_895911 := by exact prefixLift 895911
  have htrace : WordTrace (prefixWord ++ tailWord_895911) baseStart_895911 baseEnd_895911 := by
    simpa [prefixWord, tailWord_895911, baseEnd_895911] using wordTrace_append hprefix tailTrace_895911
  have hstable : (prefixWord ++ tailWord_895911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895911).length < 2 ^ (prefixWord ++ tailWord_895911).sum := by decide
  have hdescent : baseEnd_895911 < baseStart_895911 := by decide
  rcases family_descends (prefixWord ++ tailWord_895911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_895958 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_895958 : Nat := 118140960795 + 895958 * 2 ^ 59
def prefixEnd_895958 : Nat := 4983230072969 + 3 ^ 40 * 895958 * 2
def baseEnd_895958 : Nat := 102234911164691287534349

theorem tailTrace_895958 : CollatzResearch.WordTrace tailWord_895958 prefixEnd_895958 102234911164691287534349 := by
  unfold tailWord_895958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042392055506541143073033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21785515258736438859445685 2042392055506541143073033)
  ·
    refine ⟨1531794041629905857304775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2042392055506541143073033 1531794041629905857304775)
    ·
      refine ⟨2297691062444858785957163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1531794041629905857304775 2297691062444858785957163)
      ·
        refine ⟨3446536593667288178935745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2297691062444858785957163 3446536593667288178935745)
        ·
          refine ⟨2584902445250466134201809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3446536593667288178935745 2584902445250466134201809)
          ·
            refine ⟨1938676833937849600651357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2584902445250466134201809 1938676833937849600651357)
            ·
              refine ⟨727003812726693600244259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1938676833937849600651357 727003812726693600244259)
              ·
                refine ⟨1090505719090040400366389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727003812726693600244259 1090505719090040400366389)
                ·
                  refine ⟨102234911164691287534349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090505719090040400366389 102234911164691287534349)
                  ·
                    rfl

theorem cell22_895958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_895958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_895958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_895958 prefixEnd_895958 := by exact prefixLift 895958
  have htrace : WordTrace (prefixWord ++ tailWord_895958) baseStart_895958 baseEnd_895958 := by
    simpa [prefixWord, tailWord_895958, baseEnd_895958] using wordTrace_append hprefix tailTrace_895958
  have hstable : (prefixWord ++ tailWord_895958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_895958).length < 2 ^ (prefixWord ++ tailWord_895958).sum := by decide
  have hdescent : baseEnd_895958 < baseStart_895958 := by decide
  rcases family_descends (prefixWord ++ tailWord_895958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896014 : List Nat := [4, 1, 1, 2, 2, 3, 2, 7]
def baseStart_896014 : Nat := 118140960795 + 896014 * 2 ^ 59
def prefixEnd_896014 : Nat := 4983230072969 + 3 ^ 40 * 896014 * 2
def baseEnd_896014 : Nat := 34080433715389820355875

theorem tailTrace_896014 : CollatzResearch.WordTrace tailWord_896014 prefixEnd_896014 34080433715389820355875 := by
  unfold tailWord_896014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085039421987722481650887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21786876917267853235471397 4085039421987722481650887)
  ·
    refine ⟨6127559132981583722476331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4085039421987722481650887 6127559132981583722476331)
    ·
      refine ⟨9191338699472375583714497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6127559132981583722476331 9191338699472375583714497)
      ·
        refine ⟨6893504024604281687785873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9191338699472375583714497 6893504024604281687785873)
        ·
          refine ⟨5170128018453211265839405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6893504024604281687785873 5170128018453211265839405)
          ·
            refine ⟨1938798006919954224689777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5170128018453211265839405 1938798006919954224689777)
            ·
              refine ⟨1454098505189965668517333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1938798006919954224689777 1454098505189965668517333)
              ·
                refine ⟨34080433715389820355875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1454098505189965668517333 34080433715389820355875)
                ·
                  rfl

theorem cell22_896014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_896014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896014 prefixEnd_896014 := by exact prefixLift 896014
  have htrace : WordTrace (prefixWord ++ tailWord_896014) baseStart_896014 baseEnd_896014 := by
    simpa [prefixWord, tailWord_896014, baseEnd_896014] using wordTrace_append hprefix tailTrace_896014
  have hstable : (prefixWord ++ tailWord_896014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896014).length < 2 ^ (prefixWord ++ tailWord_896014).sum := by decide
  have hdescent : baseEnd_896014 < baseStart_896014 := by decide
  rcases family_descends (prefixWord ++ tailWord_896014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896121 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 6]
def baseStart_896121 : Nat := 118140960795 + 896121 * 2 ^ 59
def prefixEnd_896121 : Nat := 4983230072969 + 3 ^ 40 * 896121 * 2
def baseEnd_896121 : Nat := 102253510575065256925849

theorem tailTrace_896121 : CollatzResearch.WordTrace tailWord_896121 prefixEnd_896121 102253510575065256925849 := by
  unfold tailWord_896121
  simp only [CollatzResearch.WordTrace]
  refine ⟨32684217986514137127352217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21789478657676091418234811 32684217986514137127352217)
  ·
    refine ⟨24513163489885602845514163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32684217986514137127352217 24513163489885602845514163)
    ·
      refine ⟨36769745234828404268271245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24513163489885602845514163 36769745234828404268271245)
      ·
        refine ⟨13788654463060651600601717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36769745234828404268271245 13788654463060651600601717)
        ·
          refine ⟨1292686355911936087556411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13788654463060651600601717 1292686355911936087556411)
          ·
            refine ⟨1939029533867904131334617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292686355911936087556411 1939029533867904131334617)
            ·
              refine ⟨1454272150400928098500963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1939029533867904131334617 1454272150400928098500963)
              ·
                refine ⟨2181408225601392147751445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454272150400928098500963 2181408225601392147751445)
                ·
                  refine ⟨102253510575065256925849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2181408225601392147751445 102253510575065256925849)
                  ·
                    rfl

theorem cell22_896121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_896121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896121 prefixEnd_896121 := by exact prefixLift 896121
  have htrace : WordTrace (prefixWord ++ tailWord_896121) baseStart_896121 baseEnd_896121 := by
    simpa [prefixWord, tailWord_896121, baseEnd_896121] using wordTrace_append hprefix tailTrace_896121
  have hstable : (prefixWord ++ tailWord_896121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896121).length < 2 ^ (prefixWord ++ tailWord_896121).sum := by decide
  have hdescent : baseEnd_896121 < baseStart_896121 := by decide
  rcases family_descends (prefixWord ++ tailWord_896121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896209 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_896209 : Nat := 118140960795 + 896209 * 2 ^ 59
def prefixEnd_896209 : Nat := 4983230072969 + 3 ^ 40 * 896209 * 2
def baseEnd_896209 : Nat := 306790655923592874577277

theorem tailTrace_896209 : CollatzResearch.WordTrace tailWord_896209 prefixEnd_896209 306790655923592874577277 := by
  unfold tailWord_896209
  simp only [CollatzResearch.WordTrace]
  refine ⟨32687427610195328156555681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21791618406796885437703787 32687427610195328156555681)
  ·
    refine ⟨24515570707646496117416761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32687427610195328156555681 24515570707646496117416761)
    ·
      refine ⟨18386678030734872088062571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24515570707646496117416761 18386678030734872088062571)
      ·
        refine ⟨27580017046102308132093857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18386678030734872088062571 27580017046102308132093857)
        ·
          refine ⟨20685012784576731099070393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27580017046102308132093857 20685012784576731099070393)
          ·
            refine ⟨15513759588432548324302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20685012784576731099070393 15513759588432548324302795)
            ·
              refine ⟨23270639382648822486454193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513759588432548324302795 23270639382648822486454193)
              ·
                refine ⟨17452979536986616864840645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23270639382648822486454193 17452979536986616864840645)
                ·
                  refine ⟨3272433663184990662157621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17452979536986616864840645 3272433663184990662157621)
                  ·
                    refine ⟨306790655923592874577277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3272433663184990662157621 306790655923592874577277)
                    ·
                      rfl

theorem cell22_896209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_896209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896209 prefixEnd_896209 := by exact prefixLift 896209
  have htrace : WordTrace (prefixWord ++ tailWord_896209) baseStart_896209 baseEnd_896209 := by
    simpa [prefixWord, tailWord_896209, baseEnd_896209] using wordTrace_append hprefix tailTrace_896209
  have hstable : (prefixWord ++ tailWord_896209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896209).length < 2 ^ (prefixWord ++ tailWord_896209).sum := by decide
  have hdescent : baseEnd_896209 < baseStart_896209 := by decide
  rcases family_descends (prefixWord ++ tailWord_896209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896273 : List Nat := [1, 2, 2, 1, 1, 4, 4, 3, 4]
def baseStart_896273 : Nat := 118140960795 + 896273 * 2 ^ 59
def prefixEnd_896273 : Nat := 4983230072969 + 3 ^ 40 * 896273 * 2
def baseEnd_896273 : Nat := 102270854810506013659027

theorem tailTrace_896273 : CollatzResearch.WordTrace tailWord_896273 prefixEnd_896273 102270854810506013659027 := by
  unfold tailWord_896273
  simp only [CollatzResearch.WordTrace]
  refine ⟨32689761881963467086885473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21793174587975644724590315 32689761881963467086885473)
  ·
    refine ⟨24517321411472600315164105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32689761881963467086885473 24517321411472600315164105)
    ·
      refine ⟨18387991058604450236373079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24517321411472600315164105 18387991058604450236373079)
      ·
        refine ⟨27581986587906675354559619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18387991058604450236373079 27581986587906675354559619)
        ·
          refine ⟨41372979881860013031839429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27581986587906675354559619 41372979881860013031839429)
          ·
            refine ⟨7757433727848752443469893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41372979881860013031839429 7757433727848752443469893)
            ·
              refine ⟨1454518823971641083150605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7757433727848752443469893 1454518823971641083150605)
              ·
                refine ⟨545444558989365406181477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1454518823971641083150605 545444558989365406181477)
                ·
                  refine ⟨102270854810506013659027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545444558989365406181477 102270854810506013659027)
                  ·
                    rfl

theorem cell22_896273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_896273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896273 prefixEnd_896273 := by exact prefixLift 896273
  have htrace : WordTrace (prefixWord ++ tailWord_896273) baseStart_896273 baseEnd_896273 := by
    simpa [prefixWord, tailWord_896273, baseEnd_896273] using wordTrace_append hprefix tailTrace_896273
  have hstable : (prefixWord ++ tailWord_896273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896273).length < 2 ^ (prefixWord ++ tailWord_896273).sum := by decide
  have hdescent : baseEnd_896273 < baseStart_896273 := by decide
  rcases family_descends (prefixWord ++ tailWord_896273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896346 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_896346 : Nat := 118140960795 + 896346 * 2 ^ 59
def prefixEnd_896346 : Nat := 4983230072969 + 3 ^ 40 * 896346 * 2
def baseEnd_896346 : Nat := 102279184607790061300619

theorem tailTrace_896346 : CollatzResearch.WordTrace tailWord_896346 prefixEnd_896346 102279184607790061300619 := by
  unfold tailWord_896346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8173106102674750138573223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21794949607132667036195261 8173106102674750138573223)
  ·
    refine ⟨12259659154012125207859835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8173106102674750138573223 12259659154012125207859835)
    ·
      refine ⟨18389488731018187811789753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12259659154012125207859835 18389488731018187811789753)
      ·
        refine ⟨13792116548263640858842315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18389488731018187811789753 13792116548263640858842315)
        ·
          refine ⟨20688174822395461288263473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13792116548263640858842315 20688174822395461288263473)
          ·
            refine ⟨15516131116796595966197605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20688174822395461288263473 15516131116796595966197605)
            ·
              refine ⟨2909274584399361743662051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15516131116796595966197605 2909274584399361743662051)
              ·
                refine ⟨4363911876599042615493077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909274584399361743662051 4363911876599042615493077)
                ·
                  refine ⟨102279184607790061300619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4363911876599042615493077 102279184607790061300619)
                  ·
                    rfl

theorem cell22_896346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_896346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896346 prefixEnd_896346 := by exact prefixLift 896346
  have htrace : WordTrace (prefixWord ++ tailWord_896346) baseStart_896346 baseEnd_896346 := by
    simpa [prefixWord, tailWord_896346, baseEnd_896346] using wordTrace_append hprefix tailTrace_896346
  have hstable : (prefixWord ++ tailWord_896346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896346).length < 2 ^ (prefixWord ++ tailWord_896346).sum := by decide
  have hdescent : baseEnd_896346 < baseStart_896346 := by decide
  rcases family_descends (prefixWord ++ tailWord_896346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896444 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_896444 : Nat := 118140960795 + 896444 * 2 ^ 59
def prefixEnd_896444 : Nat := 4983230072969 + 3 ^ 40 * 896444 * 2
def baseEnd_896444 : Nat := 306871101226130594951557

theorem tailTrace_896444 : CollatzResearch.WordTrace tailWord_896444 prefixEnd_896444 306871101226130594951557 := by
  unfold tailWord_896444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16347999382171981645680193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21797332509562642194240257 16347999382171981645680193)
  ·
    refine ⟨12260999536628986234260145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16347999382171981645680193 12260999536628986234260145)
    ·
      refine ⟨9195749652471739675695109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12260999536628986234260145 9195749652471739675695109)
      ·
        refine ⟨1724203059838451189192833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9195749652471739675695109 1724203059838451189192833)
        ·
          refine ⟨1293152294878838391894625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724203059838451189192833 1293152294878838391894625)
          ·
            refine ⟨969864221159128793920969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1293152294878838391894625 969864221159128793920969)
            ·
              refine ⟨727398165869346595440727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969864221159128793920969 727398165869346595440727)
              ·
                refine ⟨1091097248804019893161091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727398165869346595440727 1091097248804019893161091)
                ·
                  refine ⟨1636645873206029839741637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091097248804019893161091 1636645873206029839741637)
                  ·
                    refine ⟨306871101226130594951557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636645873206029839741637 306871101226130594951557)
                    ·
                      rfl

theorem cell22_896444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_896444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896444 prefixEnd_896444 := by exact prefixLift 896444
  have htrace : WordTrace (prefixWord ++ tailWord_896444) baseStart_896444 baseEnd_896444 := by
    simpa [prefixWord, tailWord_896444, baseEnd_896444] using wordTrace_append hprefix tailTrace_896444
  have hstable : (prefixWord ++ tailWord_896444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896444).length < 2 ^ (prefixWord ++ tailWord_896444).sum := by decide
  have hdescent : baseEnd_896444 < baseStart_896444 := by decide
  rcases family_descends (prefixWord ++ tailWord_896444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896525 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_896525 : Nat := 118140960795 + 896525 * 2 ^ 59
def prefixEnd_896525 : Nat := 4983230072969 + 3 ^ 40 * 896525 * 2
def baseEnd_896525 : Nat := 306898829181473383676309

theorem tailTrace_896525 : CollatzResearch.WordTrace tailWord_896525 prefixEnd_896525 306898829181473383676309 := by
  unfold tailWord_896525
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698953077050514125059029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21799302051367009416706019 32698953077050514125059029)
  ·
    refine ⟨766381712743371424806071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32698953077050514125059029 766381712743371424806071)
    ·
      refine ⟨1149572569115057137209107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766381712743371424806071 1149572569115057137209107)
      ·
        refine ⟨1724358853672585705813661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149572569115057137209107 1724358853672585705813661)
        ·
          refine ⟨646634570127219639680123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1724358853672585705813661 646634570127219639680123)
          ·
            refine ⟨969951855190829459520185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646634570127219639680123 969951855190829459520185)
            ·
              refine ⟨727463891393122094640139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969951855190829459520185 727463891393122094640139)
              ·
                refine ⟨1091195837089683141960209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727463891393122094640139 1091195837089683141960209)
                ·
                  refine ⟨818396877817262356470157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1091195837089683141960209 818396877817262356470157)
                  ·
                    refine ⟨306898829181473383676309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818396877817262356470157 306898829181473383676309)
                    ·
                      rfl

theorem cell22_896525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_896525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896525 prefixEnd_896525 := by exact prefixLift 896525
  have htrace : WordTrace (prefixWord ++ tailWord_896525) baseStart_896525 baseEnd_896525 := by
    simpa [prefixWord, tailWord_896525, baseEnd_896525] using wordTrace_append hprefix tailTrace_896525
  have hstable : (prefixWord ++ tailWord_896525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896525).length < 2 ^ (prefixWord ++ tailWord_896525).sum := by decide
  have hdescent : baseEnd_896525 < baseStart_896525 := by decide
  rcases family_descends (prefixWord ++ tailWord_896525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896543 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 6]
def baseStart_896543 : Nat := 118140960795 + 896543 * 2 ^ 59
def prefixEnd_896543 : Nat := 4983230072969 + 3 ^ 40 * 896543 * 2
def baseEnd_896543 : Nat := 102301663649775778908751

theorem tailTrace_896543 : CollatzResearch.WordTrace tailWord_896543 prefixEnd_896543 102301663649775778908751 := by
  unfold tailWord_896543
  simp only [CollatzResearch.WordTrace]
  refine ⟨32699609590985303199214283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21799739727323535466142855 32699609590985303199214283)
  ·
    refine ⟨49049414386477954798821425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32699609590985303199214283 49049414386477954798821425)
    ·
      refine ⟨36787060789858466099116069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49049414386477954798821425 36787060789858466099116069)
      ·
        refine ⟨6897573898098462393584263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36787060789858466099116069 6897573898098462393584263)
        ·
          refine ⟨10346360847147693590376395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6897573898098462393584263 10346360847147693590376395)
          ·
            refine ⟨15519541270721540385564593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10346360847147693590376395 15519541270721540385564593)
            ·
              refine ⟨11639655953041155289173445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15519541270721540385564593 11639655953041155289173445)
              ·
                refine ⟨2182435491195216616720021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11639655953041155289173445 2182435491195216616720021)
                ·
                  refine ⟨102301663649775778908751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2182435491195216616720021 102301663649775778908751)
                  ·
                    rfl

theorem cell22_896543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 6].length) (baseStart_896543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896543 prefixEnd_896543 := by exact prefixLift 896543
  have htrace : WordTrace (prefixWord ++ tailWord_896543) baseStart_896543 baseEnd_896543 := by
    simpa [prefixWord, tailWord_896543, baseEnd_896543] using wordTrace_append hprefix tailTrace_896543
  have hstable : (prefixWord ++ tailWord_896543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896543).length < 2 ^ (prefixWord ++ tailWord_896543).sum := by decide
  have hdescent : baseEnd_896543 < baseStart_896543 := by decide
  rcases family_descends (prefixWord ++ tailWord_896543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896545 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_896545 : Nat := 118140960795 + 896545 * 2 ^ 59
def prefixEnd_896545 : Nat := 4983230072969 + 3 ^ 40 * 896545 * 2
def baseEnd_896545 : Nat := 306905675590199998176247

theorem tailTrace_896545 : CollatzResearch.WordTrace tailWord_896545 prefixEnd_896545 306905675590199998176247 := by
  unfold tailWord_896545
  simp only [CollatzResearch.WordTrace]
  refine ⟨32699682536978057540787089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21799788357985371693858059 32699682536978057540787089)
  ·
    refine ⟨24524761902733543155590317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32699682536978057540787089 24524761902733543155590317)
    ·
      refine ⟨9196785713525078683346369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24524761902733543155590317 9196785713525078683346369)
      ·
        refine ⟨6897589285143809012509777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9196785713525078683346369 6897589285143809012509777)
        ·
          refine ⟨5173191963857856759382333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6897589285143809012509777 5173191963857856759382333)
          ·
            refine ⟨1939946986446696284768375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5173191963857856759382333 1939946986446696284768375)
            ·
              refine ⟨2909920479670044427152563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1939946986446696284768375 2909920479670044427152563)
              ·
                refine ⟨4364880719505066640728845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909920479670044427152563 4364880719505066640728845)
                ·
                  refine ⟨1636830269814399990273317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4364880719505066640728845 1636830269814399990273317)
                  ·
                    refine ⟨306905675590199998176247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1636830269814399990273317 306905675590199998176247)
                    ·
                      rfl

theorem cell22_896545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_896545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896545 prefixEnd_896545 := by exact prefixLift 896545
  have htrace : WordTrace (prefixWord ++ tailWord_896545) baseStart_896545 baseEnd_896545 := by
    simpa [prefixWord, tailWord_896545, baseEnd_896545] using wordTrace_append hprefix tailTrace_896545
  have hstable : (prefixWord ++ tailWord_896545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896545).length < 2 ^ (prefixWord ++ tailWord_896545).sum := by decide
  have hdescent : baseEnd_896545 < baseStart_896545 := by decide
  rcases family_descends (prefixWord ++ tailWord_896545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896560 : List Nat := [2, 1, 1, 1, 2, 3, 1, 7, 4]
def baseStart_896560 : Nat := 118140960795 + 896560 * 2 ^ 59
def prefixEnd_896560 : Nat := 4983230072969 + 3 ^ 40 * 896560 * 2
def baseEnd_896560 : Nat := 102303603465581653017067

theorem tailTrace_896560 : CollatzResearch.WordTrace tailWord_896560 prefixEnd_896560 102303603465581653017067 := by
  unfold tailWord_896560
  simp only [CollatzResearch.WordTrace]
  refine ⟨16350114815961857551291567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21800153087949143401722089 16350114815961857551291567)
  ·
    refine ⟨24525172223942786326937351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16350114815961857551291567 24525172223942786326937351)
    ·
      refine ⟨36787758335914179490406027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24525172223942786326937351 36787758335914179490406027)
      ·
        refine ⟨55181637503871269235609041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36787758335914179490406027 55181637503871269235609041)
        ·
          refine ⟨41386228127903451926706781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55181637503871269235609041 41386228127903451926706781)
          ·
            refine ⟨15519835547963794472515043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41386228127903451926706781 15519835547963794472515043)
            ·
              refine ⟨23279753321945691708772565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15519835547963794472515043 23279753321945691708772565)
              ·
                refine ⟨545619218483102149424357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23279753321945691708772565 545619218483102149424357)
                ·
                  refine ⟨102303603465581653017067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545619218483102149424357 102303603465581653017067)
                  ·
                    rfl

theorem cell22_896560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_896560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896560 prefixEnd_896560 := by exact prefixLift 896560
  have htrace : WordTrace (prefixWord ++ tailWord_896560) baseStart_896560 baseEnd_896560 := by
    simpa [prefixWord, tailWord_896560, baseEnd_896560] using wordTrace_append hprefix tailTrace_896560
  have hstable : (prefixWord ++ tailWord_896560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896560).length < 2 ^ (prefixWord ++ tailWord_896560).sum := by decide
  have hdescent : baseEnd_896560 < baseStart_896560 := by decide
  rcases family_descends (prefixWord ++ tailWord_896560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896577 : List Nat := [1, 2, 5, 1, 1, 1, 3, 4, 4]
def baseStart_896577 : Nat := 118140960795 + 896577 * 2 ^ 59
def prefixEnd_896577 : Nat := 4983230072969 + 3 ^ 40 * 896577 * 2
def baseEnd_896577 : Nat := 102305543281387527125383

theorem tailTrace_896577 : CollatzResearch.WordTrace tailWord_896577 prefixEnd_896577 102305543281387527125383 := by
  unfold tailWord_896577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700849672862127005951985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21800566448574751337301323 32700849672862127005951985)
  ·
    refine ⟨24525637254646595254463989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32700849672862127005951985 24525637254646595254463989)
    ·
      refine ⟨2299278492623118305105999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24525637254646595254463989 2299278492623118305105999)
      ·
        refine ⟨3448917738934677457658999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299278492623118305105999 3448917738934677457658999)
        ·
          refine ⟨5173376608402016186488499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448917738934677457658999 5173376608402016186488499)
          ·
            refine ⟨7760064912603024279732749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173376608402016186488499 7760064912603024279732749)
            ·
              refine ⟨2910024342226134104899781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7760064912603024279732749 2910024342226134104899781)
              ·
                refine ⟨545629564167400144668709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2910024342226134104899781 545629564167400144668709)
                ·
                  refine ⟨102305543281387527125383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545629564167400144668709 102305543281387527125383)
                  ·
                    rfl

theorem cell22_896577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_896577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896577 prefixEnd_896577 := by exact prefixLift 896577
  have htrace : WordTrace (prefixWord ++ tailWord_896577) baseStart_896577 baseEnd_896577 := by
    simpa [prefixWord, tailWord_896577, baseEnd_896577] using wordTrace_append hprefix tailTrace_896577
  have hstable : (prefixWord ++ tailWord_896577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896577).length < 2 ^ (prefixWord ++ tailWord_896577).sum := by decide
  have hdescent : baseEnd_896577 < baseStart_896577 := by decide
  rcases family_descends (prefixWord ++ tailWord_896577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896620 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_896620 : Nat := 118140960795 + 896620 * 2 ^ 59
def prefixEnd_896620 : Nat := 4983230072969 + 3 ^ 40 * 896620 * 2
def baseEnd_896620 : Nat := 306931349622924802551017

theorem tailTrace_896620 : CollatzResearch.WordTrace tailWord_896620 prefixEnd_896620 306931349622924802551017 := by
  unfold tailWord_896620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16351209005853172674883657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21801612007804230233178209 16351209005853172674883657)
  ·
    refine ⟨12263406754389879506162743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16351209005853172674883657 12263406754389879506162743)
    ·
      refine ⟨18395110131584819259244115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12263406754389879506162743 18395110131584819259244115)
      ·
        refine ⟨27592665197377228888866173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18395110131584819259244115 27592665197377228888866173)
        ·
          refine ⟨10347249449016460833324815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27592665197377228888866173 10347249449016460833324815)
          ·
            refine ⟨15520874173524691249987223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10347249449016460833324815 15520874173524691249987223)
            ·
              refine ⟨23281311260287036874980835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15520874173524691249987223 23281311260287036874980835)
              ·
                refine ⟨34921966890430555312471253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23281311260287036874980835 34921966890430555312471253)
                ·
                  refine ⟨818483598994466140136045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 34921966890430555312471253 818483598994466140136045)
                  ·
                    refine ⟨306931349622924802551017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818483598994466140136045 306931349622924802551017)
                    ·
                      rfl

theorem cell22_896620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_896620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896620 prefixEnd_896620 := by exact prefixLift 896620
  have htrace : WordTrace (prefixWord ++ tailWord_896620) baseStart_896620 baseEnd_896620 := by
    simpa [prefixWord, tailWord_896620, baseEnd_896620] using wordTrace_append hprefix tailTrace_896620
  have hstable : (prefixWord ++ tailWord_896620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896620).length < 2 ^ (prefixWord ++ tailWord_896620).sum := by decide
  have hdescent : baseEnd_896620 < baseStart_896620 := by decide
  rcases family_descends (prefixWord ++ tailWord_896620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896637 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_896637 : Nat := 118140960795 + 896637 * 2 ^ 59
def prefixEnd_896637 : Nat := 4983230072969 + 3 ^ 40 * 896637 * 2
def baseEnd_896637 : Nat := 306937169070342424875965

theorem tailTrace_896637 : CollatzResearch.WordTrace tailWord_896637 prefixEnd_896637 306937169070342424875965 := by
  unfold tailWord_896637
  simp only [CollatzResearch.WordTrace]
  refine ⟨32703038052644757253136165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21802025368429838168757443 32703038052644757253136165)
  ·
    refine ⟨6131819634870891984963031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32703038052644757253136165 6131819634870891984963031)
    ·
      refine ⟨9197729452306337977444547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6131819634870891984963031 9197729452306337977444547)
      ·
        refine ⟨13796594178459506966166821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197729452306337977444547 13796594178459506966166821)
        ·
          refine ⟨2586861408461157556156279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13796594178459506966166821 2586861408461157556156279)
          ·
            refine ⟨3880292112691736334234419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586861408461157556156279 3880292112691736334234419)
            ·
              refine ⟨5820438169037604501351629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3880292112691736334234419 5820438169037604501351629)
              ·
                refine ⟨2182664313389101688006861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820438169037604501351629 2182664313389101688006861)
                ·
                  refine ⟨818499117520913133002573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2182664313389101688006861 818499117520913133002573)
                  ·
                    refine ⟨306937169070342424875965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818499117520913133002573 306937169070342424875965)
                    ·
                      rfl

theorem cell22_896637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_896637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896637 prefixEnd_896637 := by exact prefixLift 896637
  have htrace : WordTrace (prefixWord ++ tailWord_896637) baseStart_896637 baseEnd_896637 := by
    simpa [prefixWord, tailWord_896637, baseEnd_896637] using wordTrace_append hprefix tailTrace_896637
  have hstable : (prefixWord ++ tailWord_896637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896637).length < 2 ^ (prefixWord ++ tailWord_896637).sum := by decide
  have hdescent : baseEnd_896637 < baseStart_896637 := by decide
  rcases family_descends (prefixWord ++ tailWord_896637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896744 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 2, 3]
def baseStart_896744 : Nat := 118140960795 + 896744 * 2 ^ 59
def prefixEnd_896744 : Nat := 4983230072969 + 3 ^ 40 * 896744 * 2
def baseEnd_896744 : Nat := 306973797357029812450637

theorem tailTrace_896744 : CollatzResearch.WordTrace tailWord_896744 prefixEnd_896744 306973797357029812450637 := by
  unfold tailWord_896744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353470331628557263640643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21804627108838076351520857 16353470331628557263640643)
  ·
    refine ⟨24530205497442835895460965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16353470331628557263640643 24530205497442835895460965)
    ·
      refine ⟨4599413530770531730398931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24530205497442835895460965 4599413530770531730398931)
      ·
        refine ⟨6899120296155797595598397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599413530770531730398931 6899120296155797595598397)
        ·
          refine ⟨2587170111058424098349399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6899120296155797595598397 2587170111058424098349399)
          ·
            refine ⟨3880755166587636147524099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587170111058424098349399 3880755166587636147524099)
            ·
              refine ⟨5821132749881454221286149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3880755166587636147524099 5821132749881454221286149)
              ·
                refine ⟨1091462390602772666491153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5821132749881454221286149 1091462390602772666491153)
                ·
                  refine ⟨818596792952079499868365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1091462390602772666491153 818596792952079499868365)
                  ·
                    refine ⟨306973797357029812450637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818596792952079499868365 306973797357029812450637)
                    ·
                      rfl

theorem cell22_896744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_896744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896744 prefixEnd_896744 := by exact prefixLift 896744
  have htrace : WordTrace (prefixWord ++ tailWord_896744) baseStart_896744 baseEnd_896744 := by
    simpa [prefixWord, tailWord_896744, baseEnd_896744] using wordTrace_append hprefix tailTrace_896744
  have hstable : (prefixWord ++ tailWord_896744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896744).length < 2 ^ (prefixWord ++ tailWord_896744).sum := by decide
  have hdescent : baseEnd_896744 < baseStart_896744 := by decide
  rcases family_descends (prefixWord ++ tailWord_896744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896785 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 7]
def baseStart_896785 : Nat := 118140960795 + 896785 * 2 ^ 59
def prefixEnd_896785 : Nat := 4983230072969 + 3 ^ 40 * 896785 * 2
def baseEnd_896785 : Nat := 102329277498306457391837

theorem tailTrace_896785 : CollatzResearch.WordTrace tailWord_896785 prefixEnd_896785 102329277498306457391837 := by
  unfold tailWord_896785
  simp only [CollatzResearch.WordTrace]
  refine ⟨32708436056108578529523809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21805624037405719019682539 32708436056108578529523809)
  ·
    refine ⟨24531327042081433897142857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32708436056108578529523809 24531327042081433897142857)
    ·
      refine ⟨18398495281561075422857143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24531327042081433897142857 18398495281561075422857143)
      ·
        refine ⟨27597742922341613134285715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18398495281561075422857143 27597742922341613134285715)
        ·
          refine ⟨41396614383512419701428573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27597742922341613134285715 41396614383512419701428573)
          ·
            refine ⟨15523730393817157388035715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41396614383512419701428573 15523730393817157388035715)
            ·
              refine ⟨23285595590725736082053573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15523730393817157388035715 23285595590725736082053573)
              ·
                refine ⟨4366049173261075515385045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23285595590725736082053573 4366049173261075515385045)
                ·
                  refine ⟨102329277498306457391837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4366049173261075515385045 102329277498306457391837)
                  ·
                    rfl

theorem cell22_896785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_896785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896785 prefixEnd_896785 := by exact prefixLift 896785
  have htrace : WordTrace (prefixWord ++ tailWord_896785) baseStart_896785 baseEnd_896785 := by
    simpa [prefixWord, tailWord_896785, baseEnd_896785] using wordTrace_append hprefix tailTrace_896785
  have hstable : (prefixWord ++ tailWord_896785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896785).length < 2 ^ (prefixWord ++ tailWord_896785).sum := by decide
  have hdescent : baseEnd_896785 < baseStart_896785 := by decide
  rcases family_descends (prefixWord ++ tailWord_896785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896802 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_896802 : Nat := 118140960795 + 896802 * 2 ^ 59
def prefixEnd_896802 : Nat := 4983230072969 + 3 ^ 40 * 896802 * 2
def baseEnd_896802 : Nat := 102331217314112331500153

theorem tailTrace_896802 : CollatzResearch.WordTrace tailWord_896802 prefixEnd_896802 102331217314112331500153 := by
  unfold tailWord_896802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177264024261747608223165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21806037398031326955261773 8177264024261747608223165)
  ·
    refine ⟨3066474009098155353083687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8177264024261747608223165 3066474009098155353083687)
    ·
      refine ⟨4599711013647233029625531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066474009098155353083687 4599711013647233029625531)
      ·
        refine ⟨6899566520470849544438297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599711013647233029625531 6899566520470849544438297)
        ·
          refine ⟨5174674890353137158328723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899566520470849544438297 5174674890353137158328723)
          ·
            refine ⟨7762012335529705737493085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174674890353137158328723 7762012335529705737493085)
            ·
              refine ⟨2910754625823639651559907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7762012335529705737493085 2910754625823639651559907)
              ·
                refine ⟨4366131938735459477339861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910754625823639651559907 4366131938735459477339861)
                ·
                  refine ⟨102331217314112331500153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4366131938735459477339861 102331217314112331500153)
                  ·
                    rfl

theorem cell22_896802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_896802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896802 prefixEnd_896802 := by exact prefixLift 896802
  have htrace : WordTrace (prefixWord ++ tailWord_896802) baseStart_896802 baseEnd_896802 := by
    simpa [prefixWord, tailWord_896802, baseEnd_896802] using wordTrace_append hprefix tailTrace_896802
  have hstable : (prefixWord ++ tailWord_896802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896802).length < 2 ^ (prefixWord ++ tailWord_896802).sum := by decide
  have hdescent : baseEnd_896802 < baseStart_896802 := by decide
  rcases family_descends (prefixWord ++ tailWord_896802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896817 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_896817 : Nat := 118140960795 + 896817 * 2 ^ 59
def prefixEnd_896817 : Nat := 4983230072969 + 3 ^ 40 * 896817 * 2
def baseEnd_896817 : Nat := 306998786748881955375413

theorem tailTrace_896817 : CollatzResearch.WordTrace tailWord_896817 prefixEnd_896817 306998786748881955375413 := by
  unfold tailWord_896817
  simp only [CollatzResearch.WordTrace]
  refine ⟨32709603191992647994688705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21806402127995098663125803 32709603191992647994688705)
  ·
    refine ⟨24532202393994485996016529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32709603191992647994688705 24532202393994485996016529)
    ·
      refine ⟨18399151795495864497012397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24532202393994485996016529 18399151795495864497012397)
      ·
        refine ⟨6899681923310949186379649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18399151795495864497012397 6899681923310949186379649)
        ·
          refine ⟨5174761442483211889784737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899681923310949186379649 5174761442483211889784737)
          ·
            refine ⟨3881071081862408917338553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5174761442483211889784737 3881071081862408917338553)
            ·
              refine ⟨2910803311396806688003915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881071081862408917338553 2910803311396806688003915)
              ·
                refine ⟨4366204967095210032005873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910803311396806688003915 4366204967095210032005873)
                ·
                  refine ⟨3274653725321407524004405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4366204967095210032005873 3274653725321407524004405)
                  ·
                    refine ⟨306998786748881955375413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3274653725321407524004405 306998786748881955375413)
                    ·
                      rfl

theorem cell22_896817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_896817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896817 prefixEnd_896817 := by exact prefixLift 896817
  have htrace : WordTrace (prefixWord ++ tailWord_896817) baseStart_896817 baseEnd_896817 := by
    simpa [prefixWord, tailWord_896817, baseEnd_896817] using wordTrace_append hprefix tailTrace_896817
  have hstable : (prefixWord ++ tailWord_896817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896817).length < 2 ^ (prefixWord ++ tailWord_896817).sum := by decide
  have hdescent : baseEnd_896817 < baseStart_896817 := by decide
  rcases family_descends (prefixWord ++ tailWord_896817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896849 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_896849 : Nat := 118140960795 + 896849 * 2 ^ 59
def prefixEnd_896849 : Nat := 4983230072969 + 3 ^ 40 * 896849 * 2
def baseEnd_896849 : Nat := 307009741002844538575315

theorem tailTrace_896849 : CollatzResearch.WordTrace tailWord_896849 prefixEnd_896849 307009741002844538575315 := by
  unfold tailWord_896849
  simp only [CollatzResearch.WordTrace]
  refine ⟨32710770327876717459853601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21807180218584478306569067 32710770327876717459853601)
  ·
    refine ⟨24533077745907538094890201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32710770327876717459853601 24533077745907538094890201)
    ·
      refine ⟨18399808309430653571167651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24533077745907538094890201 18399808309430653571167651)
      ·
        refine ⟨27599712464145980356751477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18399808309430653571167651 27599712464145980356751477)
        ·
          refine ⟨2587473043513685658445451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27599712464145980356751477 2587473043513685658445451)
          ·
            refine ⟨3881209565270528487668177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587473043513685658445451 3881209565270528487668177)
            ·
              refine ⟨2910907173952896365751133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881209565270528487668177 2910907173952896365751133)
              ·
                refine ⟨1091590190232336137156675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2910907173952896365751133 1091590190232336137156675)
                ·
                  refine ⟨1637385285348504205735013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1091590190232336137156675 1637385285348504205735013)
                  ·
                    refine ⟨307009741002844538575315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1637385285348504205735013 307009741002844538575315)
                    ·
                      rfl

theorem cell22_896849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_896849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896849 prefixEnd_896849 := by exact prefixLift 896849
  have htrace : WordTrace (prefixWord ++ tailWord_896849) baseStart_896849 baseEnd_896849 := by
    simpa [prefixWord, tailWord_896849, baseEnd_896849] using wordTrace_append hprefix tailTrace_896849
  have hstable : (prefixWord ++ tailWord_896849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896849).length < 2 ^ (prefixWord ++ tailWord_896849).sum := by decide
  have hdescent : baseEnd_896849 < baseStart_896849 := by decide
  rcases family_descends (prefixWord ++ tailWord_896849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896864 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 6]
def baseStart_896864 : Nat := 118140960795 + 896864 * 2 ^ 59
def prefixEnd_896864 : Nat := 4983230072969 + 3 ^ 40 * 896864 * 2
def baseEnd_896864 : Nat := 102338291936463166483423

theorem tailTrace_896864 : CollatzResearch.WordTrace tailWord_896864 prefixEnd_896864 102338291936463166483423 := by
  unfold tailWord_896864
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355658711411187510824823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21807544948548250014433097 16355658711411187510824823)
  ·
    refine ⟨24533488067116781266237235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16355658711411187510824823 24533488067116781266237235)
    ·
      refine ⟨36800232100675171899355853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24533488067116781266237235 36800232100675171899355853)
      ·
        refine ⟨13800087037753189462258445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36800232100675171899355853 13800087037753189462258445)
        ·
          refine ⟨5175032639157446048346917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13800087037753189462258445 5175032639157446048346917)
          ·
            refine ⟨970318619842021134065047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5175032639157446048346917 970318619842021134065047)
            ·
              refine ⟨1455477929763031701097571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970318619842021134065047 1455477929763031701097571)
              ·
                refine ⟨2183216894644547551646357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455477929763031701097571 2183216894644547551646357)
                ·
                  refine ⟨102338291936463166483423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2183216894644547551646357 102338291936463166483423)
                  ·
                    rfl

theorem cell22_896864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_896864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896864 prefixEnd_896864 := by exact prefixLift 896864
  have htrace : WordTrace (prefixWord ++ tailWord_896864) baseStart_896864 baseEnd_896864 := by
    simpa [prefixWord, tailWord_896864, baseEnd_896864] using wordTrace_append hprefix tailTrace_896864
  have hstable : (prefixWord ++ tailWord_896864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896864).length < 2 ^ (prefixWord ++ tailWord_896864).sum := by decide
  have hdescent : baseEnd_896864 < baseStart_896864 := by decide
  rcases family_descends (prefixWord ++ tailWord_896864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896877 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_896877 : Nat := 118140960795 + 896877 * 2 ^ 59
def prefixEnd_896877 : Nat := 4983230072969 + 3 ^ 40 * 896877 * 2
def baseEnd_896877 : Nat := 307019325975061798875229

theorem tailTrace_896877 : CollatzResearch.WordTrace tailWord_896877 prefixEnd_896877 307019325975061798875229 := by
  unfold tailWord_896877
  simp only [CollatzResearch.WordTrace]
  refine ⟨32711791571775278241872885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21807861047850185494581923 32711791571775278241872885)
  ·
    refine ⟨3066730459853932335175583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32711791571775278241872885 3066730459853932335175583)
    ·
      refine ⟨4600095689780898502763375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3066730459853932335175583 4600095689780898502763375)
      ·
        refine ⟨6900143534671347754145063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4600095689780898502763375 6900143534671347754145063)
        ·
          refine ⟨10350215302007021631217595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6900143534671347754145063 10350215302007021631217595)
          ·
            refine ⟨15525322953010532446826393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350215302007021631217595 15525322953010532446826393)
            ·
              refine ⟨11643992214757899335119795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15525322953010532446826393 11643992214757899335119795)
              ·
                refine ⟨17465988322136849002679693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11643992214757899335119795 17465988322136849002679693)
                ·
                  refine ⟨6549745620801318376004885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17465988322136849002679693 6549745620801318376004885)
                  ·
                    refine ⟨307019325975061798875229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6549745620801318376004885 307019325975061798875229)
                    ·
                      rfl

theorem cell22_896877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_896877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896877 prefixEnd_896877 := by exact prefixLift 896877
  have htrace : WordTrace (prefixWord ++ tailWord_896877) baseStart_896877 baseEnd_896877 := by
    simpa [prefixWord, tailWord_896877, baseEnd_896877] using wordTrace_append hprefix tailTrace_896877
  have hstable : (prefixWord ++ tailWord_896877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896877).length < 2 ^ (prefixWord ++ tailWord_896877).sum := by decide
  have hdescent : baseEnd_896877 < baseStart_896877 := by decide
  rcases family_descends (prefixWord ++ tailWord_896877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896952 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_896952 : Nat := 118140960795 + 896952 * 2 ^ 59
def prefixEnd_896952 : Nat := 4983230072969 + 3 ^ 40 * 896952 * 2
def baseEnd_896952 : Nat := 307045000007786603249999

theorem tailTrace_896952 : CollatzResearch.WordTrace tailWord_896952 prefixEnd_896952 307045000007786603249999 := by
  unfold tailWord_896952
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357263523251783025426555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21809684697669044033902073 16357263523251783025426555)
  ·
    refine ⟨24535895284877674538139833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16357263523251783025426555 24535895284877674538139833)
    ·
      refine ⟨18401921463658255903604875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24535895284877674538139833 18401921463658255903604875)
      ·
        refine ⟨27602882195487383855407313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18401921463658255903604875 27602882195487383855407313)
        ·
          refine ⟨20702161646615537891555485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27602882195487383855407313 20702161646615537891555485)
          ·
            refine ⟨7763310617480826709333307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20702161646615537891555485 7763310617480826709333307)
            ·
              refine ⟨11644965926221240063999961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763310617480826709333307 11644965926221240063999961)
              ·
                refine ⟨8733724444665930047999971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11644965926221240063999961 8733724444665930047999971)
                ·
                  refine ⟨13100586666998895071999957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733724444665930047999971 13100586666998895071999957)
                  ·
                    refine ⟨307045000007786603249999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13100586666998895071999957 307045000007786603249999)
                    ·
                      rfl

theorem cell22_896952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_896952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896952 prefixEnd_896952 := by exact prefixLift 896952
  have htrace : WordTrace (prefixWord ++ tailWord_896952) baseStart_896952 baseEnd_896952 := by
    simpa [prefixWord, tailWord_896952, baseEnd_896952] using wordTrace_append hprefix tailTrace_896952
  have hstable : (prefixWord ++ tailWord_896952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896952).length < 2 ^ (prefixWord ++ tailWord_896952).sum := by decide
  have hdescent : baseEnd_896952 < baseStart_896952 := by decide
  rcases family_descends (prefixWord ++ tailWord_896952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896958 : List Nat := [4, 2, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_896958 : Nat := 118140960795 + 896958 * 2 ^ 59
def prefixEnd_896958 : Nat := 4983230072969 + 3 ^ 40 * 896958 * 2
def baseEnd_896958 : Nat := 307047053930404587599981

theorem tailTrace_896958 : CollatzResearch.WordTrace tailWord_896958 prefixEnd_896958 307047053930404587599981 := by
  unfold tailWord_896958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089343235560228634446441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21809830589654552717047685 4089343235560228634446441)
  ·
    refine ⟨3067007426670171475834831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4089343235560228634446441 3067007426670171475834831)
    ·
      refine ⟨4600511140005257213752247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3067007426670171475834831 4600511140005257213752247)
      ·
        refine ⟨6900766710007885820628371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4600511140005257213752247 6900766710007885820628371)
        ·
          refine ⟨10351150065011828730942557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6900766710007885820628371 10351150065011828730942557)
          ·
            refine ⟨3881681274379435774103459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10351150065011828730942557 3881681274379435774103459)
            ·
              refine ⟨5822521911569153661155189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881681274379435774103459 5822521911569153661155189)
              ·
                refine ⟨545861429209608155733299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5822521911569153661155189 545861429209608155733299)
                ·
                  refine ⟨818792143814412233599949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545861429209608155733299 818792143814412233599949)
                  ·
                    refine ⟨307047053930404587599981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818792143814412233599949 307047053930404587599981)
                    ·
                      rfl

theorem cell22_896958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_896958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_896958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_896958 prefixEnd_896958 := by exact prefixLift 896958
  have htrace : WordTrace (prefixWord ++ tailWord_896958) baseStart_896958 baseEnd_896958 := by
    simpa [prefixWord, tailWord_896958, baseEnd_896958] using wordTrace_append hprefix tailTrace_896958
  have hstable : (prefixWord ++ tailWord_896958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896958).length < 2 ^ (prefixWord ++ tailWord_896958).sum := by decide
  have hdescent : baseEnd_896958 < baseStart_896958 := by decide
  rcases family_descends (prefixWord ++ tailWord_896958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897016 : List Nat := [2, 1, 2, 1, 1, 3, 5, 3, 4]
def baseStart_897016 : Nat := 118140960795 + 897016 * 2 ^ 59
def prefixEnd_897016 : Nat := 4983230072969 + 3 ^ 40 * 897016 * 2
def baseEnd_897016 : Nat := 102355636171903923216601

theorem tailTrace_897016 : CollatzResearch.WordTrace tailWord_897016 prefixEnd_897016 102355636171903923216601 := by
  unfold tailWord_897016
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358430659135852490591451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21811240878847803320788601 16358430659135852490591451)
  ·
    refine ⟨24537645988703778735887177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16358430659135852490591451 24537645988703778735887177)
    ·
      refine ⟨18403234491527834051915383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24537645988703778735887177 18403234491527834051915383)
      ·
        refine ⟨27604851737291751077873075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18403234491527834051915383 27604851737291751077873075)
        ·
          refine ⟨41407277605937626616809613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27604851737291751077873075 41407277605937626616809613)
          ·
            refine ⟨15527729102226609981303605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41407277605937626616809613 15527729102226609981303605)
            ·
              refine ⟨1455724603333744685747213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15527729102226609981303605 1455724603333744685747213)
              ·
                refine ⟨545896726250154257155205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1455724603333744685747213 545896726250154257155205)
                ·
                  refine ⟨102355636171903923216601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545896726250154257155205 102355636171903923216601)
                  ·
                    rfl

theorem cell22_897016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_897016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897016 prefixEnd_897016 := by exact prefixLift 897016
  have htrace : WordTrace (prefixWord ++ tailWord_897016) baseStart_897016 baseEnd_897016 := by
    simpa [prefixWord, tailWord_897016, baseEnd_897016] using wordTrace_append hprefix tailTrace_897016
  have hstable : (prefixWord ++ tailWord_897016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897016).length < 2 ^ (prefixWord ++ tailWord_897016).sum := by decide
  have hdescent : baseEnd_897016 < baseStart_897016 := by decide
  rcases family_descends (prefixWord ++ tailWord_897016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897029 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_897029 : Nat := 118140960795 + 897029 * 2 ^ 59
def prefixEnd_897029 : Nat := 4983230072969 + 3 ^ 40 * 897029 * 2
def baseEnd_897029 : Nat := 307071358681384069074763

theorem tailTrace_897029 : CollatzResearch.WordTrace tailWord_897029 prefixEnd_897029 307071358681384069074763 := by
  unfold tailWord_897029
  simp only [CollatzResearch.WordTrace]
  refine ⟨32717335467224608201406141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21811556978149738800937427 32717335467224608201406141)
  ·
    refine ⟨12269000800209228075527303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32717335467224608201406141 12269000800209228075527303)
    ·
      refine ⟨18403501200313842113290955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12269000800209228075527303 18403501200313842113290955)
      ·
        refine ⟨27605251800470763169936433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18403501200313842113290955 27605251800470763169936433)
        ·
          refine ⟨20703938850353072377452325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27605251800470763169936433 20703938850353072377452325)
          ·
            refine ⟨3881988534441201070772311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20703938850353072377452325 3881988534441201070772311)
            ·
              refine ⟨5822982801661801606158467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881988534441201070772311 5822982801661801606158467)
              ·
                refine ⟨8734474202492702409237701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822982801661801606158467 8734474202492702409237701)
                ·
                  refine ⟨1637713912967381701732069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8734474202492702409237701 1637713912967381701732069)
                  ·
                    refine ⟨307071358681384069074763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1637713912967381701732069 307071358681384069074763)
                    ·
                      rfl

theorem cell22_897029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_897029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897029 prefixEnd_897029 := by exact prefixLift 897029
  have htrace : WordTrace (prefixWord ++ tailWord_897029) baseStart_897029 baseEnd_897029 := by
    simpa [prefixWord, tailWord_897029, baseEnd_897029] using wordTrace_append hprefix tailTrace_897029
  have hstable : (prefixWord ++ tailWord_897029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897029).length < 2 ^ (prefixWord ++ tailWord_897029).sum := by decide
  have hdescent : baseEnd_897029 < baseStart_897029 := by decide
  rcases family_descends (prefixWord ++ tailWord_897029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897031 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 4, 3]
def baseStart_897031 : Nat := 118140960795 + 897031 * 2 ^ 59
def prefixEnd_897031 : Nat := 4983230072969 + 3 ^ 40 * 897031 * 2
def baseEnd_897031 : Nat := 307072043322256730524757

theorem tailTrace_897031 : CollatzResearch.WordTrace tailWord_897031 prefixEnd_897031 307072043322256730524757 := by
  unfold tailWord_897031
  simp only [CollatzResearch.WordTrace]
  refine ⟨32717408413217362542978947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21811605608811575028652631 32717408413217362542978947)
  ·
    refine ⟨49076112619826043814468421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32717408413217362542978947 49076112619826043814468421)
    ·
      refine ⟨9201771116217383215212829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49076112619826043814468421 9201771116217383215212829)
      ·
        refine ⟨3450664168581518705704811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9201771116217383215212829 3450664168581518705704811)
        ·
          refine ⟨5175996252872278058557217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450664168581518705704811 5175996252872278058557217)
          ·
            refine ⟨3881997189654208543917913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5175996252872278058557217 3881997189654208543917913)
            ·
              refine ⟨2911497892240656407938435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881997189654208543917913 2911497892240656407938435)
              ·
                refine ⟨4367246838360984611907653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911497892240656407938435 4367246838360984611907653)
                ·
                  refine ⟨818858782192684614732685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4367246838360984611907653 818858782192684614732685)
                  ·
                    refine ⟨307072043322256730524757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818858782192684614732685 307072043322256730524757)
                    ·
                      rfl

theorem cell22_897031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_897031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897031 prefixEnd_897031 := by exact prefixLift 897031
  have htrace : WordTrace (prefixWord ++ tailWord_897031) baseStart_897031 baseEnd_897031 := by
    simpa [prefixWord, tailWord_897031, baseEnd_897031] using wordTrace_append hprefix tailTrace_897031
  have hstable : (prefixWord ++ tailWord_897031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897031).length < 2 ^ (prefixWord ++ tailWord_897031).sum := by decide
  have hdescent : baseEnd_897031 < baseStart_897031 := by decide
  rcases family_descends (prefixWord ++ tailWord_897031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897110 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_897110 : Nat := 118140960795 + 897110 * 2 ^ 59
def prefixEnd_897110 : Nat := 4983230072969 + 3 ^ 40 * 897110 * 2
def baseEnd_897110 : Nat := 307099086636726857799515

theorem tailTrace_897110 : CollatzResearch.WordTrace tailWord_897110 prefixEnd_897110 307099086636726857799515 := by
  unfold tailWord_897110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045018111245697439694049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21813526519954106023403189 2045018111245697439694049)
  ·
    refine ⟨1533763583434273079770537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2045018111245697439694049 1533763583434273079770537)
    ·
      refine ⟨1150322687575704809827903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1533763583434273079770537 1150322687575704809827903)
      ·
        refine ⟨1725484031363557214741855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1150322687575704809827903 1725484031363557214741855)
        ·
          refine ⟨2588226047045335822112783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725484031363557214741855 2588226047045335822112783)
          ·
            refine ⟨3882339070568003733169175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588226047045335822112783 3882339070568003733169175)
            ·
              refine ⟨5823508605852005599753763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882339070568003733169175 5823508605852005599753763)
              ·
                refine ⟨8735262908778008399630645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823508605852005599753763 8735262908778008399630645)
                ·
                  refine ⟨818930897697938287465373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8735262908778008399630645 818930897697938287465373)
                  ·
                    refine ⟨307099086636726857799515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818930897697938287465373 307099086636726857799515)
                    ·
                      rfl

theorem cell22_897110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_897110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897110 prefixEnd_897110 := by exact prefixLift 897110
  have htrace : WordTrace (prefixWord ++ tailWord_897110) baseStart_897110 baseEnd_897110 := by
    simpa [prefixWord, tailWord_897110, baseEnd_897110] using wordTrace_append hprefix tailTrace_897110
  have hstable : (prefixWord ++ tailWord_897110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897110).length < 2 ^ (prefixWord ++ tailWord_897110).sum := by decide
  have hdescent : baseEnd_897110 < baseStart_897110 := by decide
  rcases family_descends (prefixWord ++ tailWord_897110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897181 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_897181 : Nat := 118140960795 + 897181 * 2 ^ 59
def prefixEnd_897181 : Nat := 4983230072969 + 3 ^ 40 * 897181 * 2
def baseEnd_897181 : Nat := 307123391387706339274297

theorem tailTrace_897181 : CollatzResearch.WordTrace tailWord_897181 prefixEnd_897181 307123391387706339274297 := by
  unfold tailWord_897181
  simp only [CollatzResearch.WordTrace]
  refine ⟨32722879362673938160939397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21815252908449292107292931 32722879362673938160939397)
  ·
    refine ⟨6135539880501363405176137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32722879362673938160939397 6135539880501363405176137)
    ·
      refine ⟨4601654910376022553882103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6135539880501363405176137 4601654910376022553882103)
      ·
        refine ⟨6902482365564033830823155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4601654910376022553882103 6902482365564033830823155)
        ·
          refine ⟨10353723548346050746234733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6902482365564033830823155 10353723548346050746234733)
          ·
            refine ⟨3882646330629769029838025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10353723548346050746234733 3882646330629769029838025)
            ·
              refine ⟨2911984747972326772378519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3882646330629769029838025 2911984747972326772378519)
              ·
                refine ⟨4367977121958490158567779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911984747972326772378519 4367977121958490158567779)
                ·
                  refine ⟨6551965682937735237851669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367977121958490158567779 6551965682937735237851669)
                  ·
                    refine ⟨307123391387706339274297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6551965682937735237851669 307123391387706339274297)
                    ·
                      rfl

theorem cell22_897181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_897181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897181 prefixEnd_897181 := by exact prefixLift 897181
  have htrace : WordTrace (prefixWord ++ tailWord_897181) baseStart_897181 baseEnd_897181 := by
    simpa [prefixWord, tailWord_897181, baseEnd_897181] using wordTrace_append hprefix tailTrace_897181
  have hstable : (prefixWord ++ tailWord_897181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897181).length < 2 ^ (prefixWord ++ tailWord_897181).sum := by decide
  have hdescent : baseEnd_897181 < baseStart_897181 := by decide
  rcases family_descends (prefixWord ++ tailWord_897181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897183 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 4, 3]
def baseStart_897183 : Nat := 118140960795 + 897183 * 2 ^ 59
def prefixEnd_897183 : Nat := 4983230072969 + 3 ^ 40 * 897183 * 2
def baseEnd_897183 : Nat := 307124076028579000724291

theorem tailTrace_897183 : CollatzResearch.WordTrace tailWord_897183 prefixEnd_897183 307124076028579000724291 := by
  unfold tailWord_897183
  simp only [CollatzResearch.WordTrace]
  refine ⟨32722952308666692502512203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21815301539111128335008135 32722952308666692502512203)
  ·
    refine ⟨49084428463000038753768305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32722952308666692502512203 49084428463000038753768305)
    ·
      refine ⟨36813321347250029065326229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49084428463000038753768305 36813321347250029065326229)
      ·
        refine ⟨1725624438152345112437167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36813321347250029065326229 1725624438152345112437167)
        ·
          refine ⟨2588436657228517668655751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725624438152345112437167 2588436657228517668655751)
          ·
            refine ⟨3882654985842776502983627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588436657228517668655751 3882654985842776502983627)
            ·
              refine ⟨5823982478764164754475441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882654985842776502983627 5823982478764164754475441)
              ·
                refine ⟨4367986859073123565856581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5823982478764164754475441 4367986859073123565856581)
                ·
                  refine ⟨818997536076210668598109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4367986859073123565856581 818997536076210668598109)
                  ·
                    refine ⟨307124076028579000724291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 818997536076210668598109 307124076028579000724291)
                    ·
                      rfl

theorem cell22_897183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_897183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_897183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_897183 prefixEnd_897183 := by exact prefixLift 897183
  have htrace : WordTrace (prefixWord ++ tailWord_897183) baseStart_897183 baseEnd_897183 := by
    simpa [prefixWord, tailWord_897183, baseEnd_897183] using wordTrace_append hprefix tailTrace_897183
  have hstable : (prefixWord ++ tailWord_897183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897183).length < 2 ^ (prefixWord ++ tailWord_897183).sum := by decide
  have hdescent : baseEnd_897183 < baseStart_897183 := by decide
  rcases family_descends (prefixWord ++ tailWord_897183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
