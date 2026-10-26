import V185TrunkScan23Chunk1308

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7753199 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 2, 2, 2]
def baseStart_7753199 : Nat := 118140960795 + 7753199 * 2 ^ 59
def prefixEnd_7753199 : Nat := 4983230072969 + 3 ^ 40 * 7753199 * 2
def baseEnd_7753199 : Nat := 3981117696958516306956193

theorem tailTrace_7753199 : CollatzResearch.WordTrace tailWord_7753199 prefixEnd_7753199 3981117696958516306956193 := by
  unfold tailWord_7753199
  simp only [CollatzResearch.WordTrace]
  refine ⟨282782399038491638814062651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188521599358994425876041767 282782399038491638814062651)
  ·
    refine ⟨424173598557737458221093977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282782399038491638814062651 424173598557737458221093977)
    ·
      refine ⟨318130198918303093665820483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424173598557737458221093977 318130198918303093665820483)
      ·
        refine ⟨477195298377454640498730725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318130198918303093665820483 477195298377454640498730725)
        ·
          refine ⟨89474118445772745093512011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477195298377454640498730725 89474118445772745093512011)
          ·
            refine ⟨134211177668659117640268017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89474118445772745093512011 134211177668659117640268017)
            ·
              refine ⟨100658383251494338230201013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134211177668659117640268017 100658383251494338230201013)
              ·
                refine ⟨9436723429827594209081345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100658383251494338230201013 9436723429827594209081345)
                ·
                  refine ⟨7077542572370695656811009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9436723429827594209081345 7077542572370695656811009)
                  ·
                    refine ⟨5308156929278021742608257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7077542572370695656811009 5308156929278021742608257)
                    ·
                      refine ⟨3981117696958516306956193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308156929278021742608257 3981117696958516306956193)
                      ·
                        rfl

theorem cell23_7753199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 2, 2].length) (baseStart_7753199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753199 prefixEnd_7753199 := by exact prefixLift 7753199
  have htrace : WordTrace (prefixWord ++ tailWord_7753199) baseStart_7753199 baseEnd_7753199 := by
    simpa [prefixWord, tailWord_7753199, baseEnd_7753199] using wordTrace_append hprefix tailTrace_7753199
  have hstable : (prefixWord ++ tailWord_7753199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753199).length < 2 ^ (prefixWord ++ tailWord_7753199).sum := by decide
  have hdescent : baseEnd_7753199 < baseStart_7753199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753215 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 3]
def baseStart_7753215 : Nat := 118140960795 + 7753215 * 2 ^ 59
def prefixEnd_7753215 : Nat := 4983230072969 + 3 ^ 40 * 7753215 * 2
def baseEnd_7753215 : Nat := 3981125912648988244356119

theorem tailTrace_7753215 : CollatzResearch.WordTrace tailWord_7753215 prefixEnd_7753215 3981125912648988244356119 := by
  unfold tailWord_7753215
  simp only [CollatzResearch.WordTrace]
  refine ⟨282782982606433673546645099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188521988404289115697763399 282782982606433673546645099)
  ·
    refine ⟨424174473909650510319967649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282782982606433673546645099 424174473909650510319967649)
    ·
      refine ⟨318130855432237882739975737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424174473909650510319967649 318130855432237882739975737)
      ·
        refine ⟨238598141574178412054981803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318130855432237882739975737 238598141574178412054981803)
        ·
          refine ⟨357897212361267618082472705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238598141574178412054981803 357897212361267618082472705)
          ·
            refine ⟨268422909270950713561854529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357897212361267618082472705 268422909270950713561854529)
            ·
              refine ⟨201317181953213035171390897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268422909270950713561854529 201317181953213035171390897)
              ·
                refine ⟨150987886464909776378543173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201317181953213035171390897 150987886464909776378543173)
                ·
                  refine ⟨28310228712170583070976845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150987886464909776378543173 28310228712170583070976845)
                  ·
                    refine ⟨10616335767063968651616317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28310228712170583070976845 10616335767063968651616317)
                    ·
                      refine ⟨3981125912648988244356119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10616335767063968651616317 3981125912648988244356119)
                      ·
                        rfl

theorem cell23_7753215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_7753215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753215 prefixEnd_7753215 := by exact prefixLift 7753215
  have htrace : WordTrace (prefixWord ++ tailWord_7753215) baseStart_7753215 baseEnd_7753215 := by
    simpa [prefixWord, tailWord_7753215, baseEnd_7753215] using wordTrace_append hprefix tailTrace_7753215
  have hstable : (prefixWord ++ tailWord_7753215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753215).length < 2 ^ (prefixWord ++ tailWord_7753215).sum := by decide
  have hdescent : baseEnd_7753215 < baseStart_7753215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753235 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 4, 5]
def baseStart_7753235 : Nat := 118140960795 + 7753235 * 2 ^ 59
def prefixEnd_7753235 : Nat := 4983230072969 + 3 ^ 40 * 7753235 * 2
def baseEnd_7753235 : Nat := 1327045394087359388702009

theorem tailTrace_7753235 : CollatzResearch.WordTrace tailWord_7753235 prefixEnd_7753235 1327045394087359388702009 := by
  unfold tailWord_7753235
  simp only [CollatzResearch.WordTrace]
  refine ⟨282783712066361216962373159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188522474710907477974915439 282783712066361216962373159)
  ·
    refine ⟨424175568099541825443559739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282783712066361216962373159 424175568099541825443559739)
    ·
      refine ⟨636263352149312738165339609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424175568099541825443559739 636263352149312738165339609)
      ·
        refine ⟨477197514111984553624004707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636263352149312738165339609 477197514111984553624004707)
        ·
          refine ⟨715796271167976830436007061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477197514111984553624004707 715796271167976830436007061)
          ·
            refine ⟨33552950210998913926687831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 715796271167976830436007061 33552950210998913926687831)
            ·
              refine ⟨50329425316498370890031747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33552950210998913926687831 50329425316498370890031747)
              ·
                refine ⟨75494137974747556335047621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50329425316498370890031747 75494137974747556335047621)
                ·
                  refine ⟨14155150870265166812821429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75494137974747556335047621 14155150870265166812821429)
                  ·
                    refine ⟨1327045394087359388702009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14155150870265166812821429 1327045394087359388702009)
                    ·
                      rfl

theorem cell23_7753235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 5].length) (baseStart_7753235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753235 prefixEnd_7753235 := by exact prefixLift 7753235
  have htrace : WordTrace (prefixWord ++ tailWord_7753235) baseStart_7753235 baseEnd_7753235 := by
    simpa [prefixWord, tailWord_7753235, baseEnd_7753235] using wordTrace_append hprefix tailTrace_7753235
  have hstable : (prefixWord ++ tailWord_7753235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753235).length < 2 ^ (prefixWord ++ tailWord_7753235).sum := by decide
  have hdescent : baseEnd_7753235 < baseStart_7753235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753242 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2]
def baseStart_7753242 : Nat := 118140960795 + 7753242 * 2 ^ 59
def prefixEnd_7753242 : Nat := 4983230072969 + 3 ^ 40 * 7753242 * 2
def baseEnd_7753242 : Nat := 3981139776626659638718495

theorem tailTrace_7753242 : CollatzResearch.WordTrace tailWord_7753242 prefixEnd_7753242 3981139776626659638718495 := by
  unfold tailWord_7753242
  simp only [CollatzResearch.WordTrace]
  refine ⟨70695991844333964289469495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188522644918223904771918653 70695991844333964289469495)
  ·
    refine ⟨106043987766500946434204243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70695991844333964289469495 106043987766500946434204243)
    ·
      refine ⟨159065981649751419651306365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106043987766500946434204243 159065981649751419651306365)
      ·
        refine ⟨59649743118656782369239887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159065981649751419651306365 59649743118656782369239887)
        ·
          refine ⟨89474614677985173553859831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59649743118656782369239887 89474614677985173553859831)
          ·
            refine ⟨134211922016977760330789747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89474614677985173553859831 134211922016977760330789747)
            ·
              refine ⟨201317883025466640496184621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134211922016977760330789747 201317883025466640496184621)
              ·
                refine ⟨75494206134549990186069233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201317883025466640496184621 75494206134549990186069233)
                ·
                  refine ⟨56620654600912492639551925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75494206134549990186069233 56620654600912492639551925)
                  ·
                    refine ⟨5308186368835546184957993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56620654600912492639551925 5308186368835546184957993)
                    ·
                      refine ⟨3981139776626659638718495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308186368835546184957993 3981139776626659638718495)
                      ·
                        rfl

theorem cell23_7753242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_7753242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753242 prefixEnd_7753242 := by exact prefixLift 7753242
  have htrace : WordTrace (prefixWord ++ tailWord_7753242) baseStart_7753242 baseEnd_7753242 := by
    simpa [prefixWord, tailWord_7753242, baseEnd_7753242] using wordTrace_append hprefix tailTrace_7753242
  have hstable : (prefixWord ++ tailWord_7753242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753242).length < 2 ^ (prefixWord ++ tailWord_7753242).sum := by decide
  have hdescent : baseEnd_7753242 < baseStart_7753242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753272 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_7753272 : Nat := 118140960795 + 7753272 * 2 ^ 59
def prefixEnd_7753272 : Nat := 4983230072969 + 3 ^ 40 * 7753272 * 2
def baseEnd_7753272 : Nat := 3981155181046294521343357

theorem tailTrace_7753272 : CollatzResearch.WordTrace tailWord_7753272 prefixEnd_7753272 3981155181046294521343357 := by
  unfold tailWord_7753272
  simp only [CollatzResearch.WordTrace]
  refine ⟨141392530783613586140735035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188523374378151448187646713 141392530783613586140735035)
  ·
    refine ⟨212088796175420379211102553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141392530783613586140735035 212088796175420379211102553)
    ·
      refine ⟨159066597131565284408326915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212088796175420379211102553 159066597131565284408326915)
      ·
        refine ⟨238599895697347926612490373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159066597131565284408326915 238599895697347926612490373)
        ·
          refine ⟨44737480443252736239841945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238599895697347926612490373 44737480443252736239841945)
          ·
            refine ⟨33553110332439552179881459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44737480443252736239841945 33553110332439552179881459)
            ·
              refine ⟨50329665498659328269822189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33553110332439552179881459 50329665498659328269822189)
              ·
                refine ⟨18873624561997248101183321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50329665498659328269822189 18873624561997248101183321)
                ·
                  refine ⟨14155218421497936075887491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18873624561997248101183321 14155218421497936075887491)
                  ·
                    refine ⟨21232827632246904113831237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14155218421497936075887491 21232827632246904113831237)
                    ·
                      refine ⟨3981155181046294521343357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21232827632246904113831237 3981155181046294521343357)
                      ·
                        rfl

theorem cell23_7753272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_7753272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753272 prefixEnd_7753272 := by exact prefixLift 7753272
  have htrace : WordTrace (prefixWord ++ tailWord_7753272) baseStart_7753272 baseEnd_7753272 := by
    simpa [prefixWord, tailWord_7753272, baseEnd_7753272] using wordTrace_append hprefix tailTrace_7753272
  have hstable : (prefixWord ++ tailWord_7753272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753272).length < 2 ^ (prefixWord ++ tailWord_7753272).sum := by decide
  have hdescent : baseEnd_7753272 < baseStart_7753272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753285 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_7753285 : Nat := 118140960795 + 7753285 * 2 ^ 59
def prefixEnd_7753285 : Nat := 4983230072969 + 3 ^ 40 * 7753285 * 2
def baseEnd_7753285 : Nat := 3981161856294802970480797

theorem tailTrace_7753285 : CollatzResearch.WordTrace tailWord_7753285 prefixEnd_7753285 3981161856294802970480797 := by
  unfold tailWord_7753285
  simp only [CollatzResearch.WordTrace]
  refine ⟨282785535716180075501693309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188523690477453383667795539 282785535716180075501693309)
  ·
    refine ⟨106044575893567528313134991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282785535716180075501693309 106044575893567528313134991)
    ·
      refine ⟨159066863840351292469702487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106044575893567528313134991 159066863840351292469702487)
      ·
        refine ⟨238600295760526938704553731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159066863840351292469702487 238600295760526938704553731)
        ·
          refine ⟨357900443640790408056830597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238600295760526938704553731 357900443640790408056830597)
          ·
            refine ⟨67106333182648201510655737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357900443640790408056830597 67106333182648201510655737)
            ·
              refine ⟨50329749886986151132991803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67106333182648201510655737 50329749886986151132991803)
              ·
                refine ⟨75494624830479226699487705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50329749886986151132991803 75494624830479226699487705)
                ·
                  refine ⟨56620968622859420024615779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75494624830479226699487705 56620968622859420024615779)
                  ·
                    refine ⟨84931452934289130036923669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56620968622859420024615779 84931452934289130036923669)
                    ·
                      refine ⟨3981161856294802970480797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84931452934289130036923669 3981161856294802970480797)
                      ·
                        rfl

theorem cell23_7753285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_7753285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753285 prefixEnd_7753285 := by exact prefixLift 7753285
  have htrace : WordTrace (prefixWord ++ tailWord_7753285) baseStart_7753285 baseEnd_7753285 := by
    simpa [prefixWord, tailWord_7753285, baseEnd_7753285] using wordTrace_append hprefix tailTrace_7753285
  have hstable : (prefixWord ++ tailWord_7753285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753285).length < 2 ^ (prefixWord ++ tailWord_7753285).sum := by decide
  have hdescent : baseEnd_7753285 < baseStart_7753285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753333 : List Nat := [1, 3, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7753333 : Nat := 118140960795 + 7753333 * 2 ^ 59
def prefixEnd_7753333 : Nat := 4983230072969 + 3 ^ 40 * 7753333 * 2
def baseEnd_7753333 : Nat := 1327062167788739594226859

theorem tailTrace_7753333 : CollatzResearch.WordTrace tailWord_7753333 prefixEnd_7753333 1327062167788739594226859 := by
  unfold tailWord_7753333
  simp only [CollatzResearch.WordTrace]
  refine ⟨282787286420006179699440653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188524857613337453132960435 282787286420006179699440653)
  ·
    refine ⟨106045232407502317387290245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282787286420006179699440653 106045232407502317387290245)
    ·
      refine ⟨19883481076406684510116921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106045232407502317387290245 19883481076406684510116921)
      ·
        refine ⟨14912610807305013382587691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19883481076406684510116921 14912610807305013382587691)
        ·
          refine ⟨22368916210957520073881537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14912610807305013382587691 22368916210957520073881537)
          ·
            refine ⟨16776687158218140055411153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22368916210957520073881537 16776687158218140055411153)
            ·
              refine ⟨12582515368663605041558365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16776687158218140055411153 12582515368663605041558365)
              ·
                refine ⟨4718443263248851890584387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12582515368663605041558365 4718443263248851890584387)
                ·
                  refine ⟨7077664894873277835876581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718443263248851890584387 7077664894873277835876581)
                  ·
                    refine ⟨1327062167788739594226859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7077664894873277835876581 1327062167788739594226859)
                    ·
                      rfl

theorem cell23_7753333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7753333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753333 prefixEnd_7753333 := by exact prefixLift 7753333
  have htrace : WordTrace (prefixWord ++ tailWord_7753333) baseStart_7753333 baseEnd_7753333 := by
    simpa [prefixWord, tailWord_7753333, baseEnd_7753333] using wordTrace_append hprefix tailTrace_7753333
  have hstable : (prefixWord ++ tailWord_7753333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753333).length < 2 ^ (prefixWord ++ tailWord_7753333).sum := by decide
  have hdescent : baseEnd_7753333 < baseStart_7753333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753335 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_7753335 : Nat := 118140960795 + 7753335 * 2 ^ 59
def prefixEnd_7753335 : Nat := 4983230072969 + 3 ^ 40 * 7753335 * 2
def baseEnd_7753335 : Nat := 3981187530327527774855567

theorem tailTrace_7753335 : CollatzResearch.WordTrace tailWord_7753335 prefixEnd_7753335 3981187530327527774855567 := by
  unfold tailWord_7753335
  simp only [CollatzResearch.WordTrace]
  refine ⟨282787359365998934041013459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188524906243999289360675639 282787359365998934041013459)
  ·
    refine ⟨424181039048998401061520189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282787359365998934041013459 424181039048998401061520189)
    ·
      refine ⟨159067889643374400398070071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424181039048998401061520189 159067889643374400398070071)
      ·
        refine ⟨238601834465061600597105107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159067889643374400398070071 238601834465061600597105107)
        ·
          refine ⟨357902751697592400895657661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238601834465061600597105107 357902751697592400895657661)
          ·
            refine ⟨134213531886597150335871623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357902751697592400895657661 134213531886597150335871623)
            ·
              refine ⟨201320297829895725503807435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134213531886597150335871623 201320297829895725503807435)
              ·
                refine ⟨301980446744843588255711153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201320297829895725503807435 301980446744843588255711153)
                ·
                  refine ⟨226485335058632691191783365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301980446744843588255711153 226485335058632691191783365)
                  ·
                    refine ⟨42466000323493629598459381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226485335058632691191783365 42466000323493629598459381)
                    ·
                      refine ⟨3981187530327527774855567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42466000323493629598459381 3981187530327527774855567)
                      ·
                        rfl

theorem cell23_7753335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_7753335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753335 prefixEnd_7753335 := by exact prefixLift 7753335
  have htrace : WordTrace (prefixWord ++ tailWord_7753335) baseStart_7753335 baseEnd_7753335 := by
    simpa [prefixWord, tailWord_7753335, baseEnd_7753335] using wordTrace_append hprefix tailTrace_7753335
  have hstable : (prefixWord ++ tailWord_7753335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753335).length < 2 ^ (prefixWord ++ tailWord_7753335).sum := by decide
  have hdescent : baseEnd_7753335 < baseStart_7753335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753349 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 4, 3, 2]
def baseStart_7753349 : Nat := 118140960795 + 7753349 * 2 ^ 59
def prefixEnd_7753349 : Nat := 4983230072969 + 3 ^ 40 * 7753349 * 2
def baseEnd_7753349 : Nat := 3981194719056690720080503

theorem tailTrace_7753349 : CollatzResearch.WordTrace tailWord_7753349 prefixEnd_7753349 3981194719056690720080503 := by
  unfold tailWord_7753349
  simp only [CollatzResearch.WordTrace]
  refine ⟨282787869987948214432023101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188525246658632142954682067 282787869987948214432023101)
  ·
    refine ⟨106045451245480580412008663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282787869987948214432023101 106045451245480580412008663)
    ·
      refine ⟨159068176868220870618012995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106045451245480580412008663 159068176868220870618012995)
      ·
        refine ⟨238602265302331305927019493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159068176868220870618012995 238602265302331305927019493)
        ·
          refine ⟨44737924744187119861316155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238602265302331305927019493 44737924744187119861316155)
          ·
            refine ⟨67106887116280679791974233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44737924744187119861316155 67106887116280679791974233)
            ·
              refine ⟨50330165337210509843980675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67106887116280679791974233 50330165337210509843980675)
              ·
                refine ⟨75495248005815764765971013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50330165337210509843980675 75495248005815764765971013)
                ·
                  refine ⟨14155359001090455893619565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75495248005815764765971013 14155359001090455893619565)
                  ·
                    refine ⟨5308259625408920960107337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14155359001090455893619565 5308259625408920960107337)
                    ·
                      refine ⟨3981194719056690720080503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308259625408920960107337 3981194719056690720080503)
                      ·
                        rfl

theorem cell23_7753349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_7753349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753349 prefixEnd_7753349 := by exact prefixLift 7753349
  have htrace : WordTrace (prefixWord ++ tailWord_7753349) baseStart_7753349 baseEnd_7753349 := by
    simpa [prefixWord, tailWord_7753349, baseEnd_7753349] using wordTrace_append hprefix tailTrace_7753349
  have hstable : (prefixWord ++ tailWord_7753349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753349).length < 2 ^ (prefixWord ++ tailWord_7753349).sum := by decide
  have hdescent : baseEnd_7753349 < baseStart_7753349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753356 : List Nat := [2, 2, 1, 2, 1, 1, 3, 6, 1, 1, 3]
def baseStart_7753356 : Nat := 118140960795 + 7753356 * 2 ^ 59
def prefixEnd_7753356 : Nat := 4983230072969 + 3 ^ 40 * 7753356 * 2
def baseEnd_7753356 : Nat := 3981198313421272192692971

theorem tailTrace_7753356 : CollatzResearch.WordTrace tailWord_7753356 prefixEnd_7753356 3981198313421272192692971 := by
  unfold tailWord_7753356
  simp only [CollatzResearch.WordTrace]
  refine ⟨141394062649461427313763961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188525416865948569751685281 141394062649461427313763961)
  ·
    refine ⟨106045546987096070485322971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141394062649461427313763961 106045546987096070485322971)
    ·
      refine ⟨159068320480644105727984457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106045546987096070485322971 159068320480644105727984457)
      ·
        refine ⟨119301240360483079295988343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159068320480644105727984457 119301240360483079295988343)
        ·
          refine ⟨178951860540724618943982515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119301240360483079295988343 178951860540724618943982515)
          ·
            refine ⟨268427790811086928415973773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178951860540724618943982515 268427790811086928415973773)
            ·
              refine ⟨100660421554157598155990165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268427790811086928415973773 100660421554157598155990165)
              ·
                refine ⟨4718457260351137413562039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100660421554157598155990165 4718457260351137413562039)
                ·
                  refine ⟨7077685890526706120343059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718457260351137413562039 7077685890526706120343059)
                  ·
                    refine ⟨10616528835790059180514589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7077685890526706120343059 10616528835790059180514589)
                    ·
                      refine ⟨3981198313421272192692971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10616528835790059180514589 3981198313421272192692971)
                      ·
                        rfl

theorem cell23_7753356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_7753356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753356 prefixEnd_7753356 := by exact prefixLift 7753356
  have htrace : WordTrace (prefixWord ++ tailWord_7753356) baseStart_7753356 baseEnd_7753356 := by
    simpa [prefixWord, tailWord_7753356, baseEnd_7753356] using wordTrace_append hprefix tailTrace_7753356
  have hstable : (prefixWord ++ tailWord_7753356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753356).length < 2 ^ (prefixWord ++ tailWord_7753356).sum := by decide
  have hdescent : baseEnd_7753356 < baseStart_7753356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753379 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 4]
def baseStart_7753379 : Nat := 118140960795 + 7753379 * 2 ^ 59
def prefixEnd_7753379 : Nat := 4983230072969 + 3 ^ 40 * 7753379 * 2
def baseEnd_7753379 : Nat := 3981210123476325602705365

theorem tailTrace_7753379 : CollatzResearch.WordTrace tailWord_7753379 prefixEnd_7753379 3981210123476325602705365 := by
  unfold tailWord_7753379
  simp only [CollatzResearch.WordTrace]
  refine ⟨282788964177839529555615191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188525976118559686370410127 282788964177839529555615191)
  ·
    refine ⟨424183446266759294333422787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282788964177839529555615191 424183446266759294333422787)
    ·
      refine ⟨636275169400138941500134181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424183446266759294333422787 636275169400138941500134181)
      ·
        refine ⟨119301594262526051531275159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 636275169400138941500134181 119301594262526051531275159)
        ·
          refine ⟨178952391393789077296912739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119301594262526051531275159 178952391393789077296912739)
          ·
            refine ⟨268428587090683615945369109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178952391393789077296912739 268428587090683615945369109)
            ·
              refine ⟨12582590019875794497439177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268428587090683615945369109 12582590019875794497439177)
              ·
                refine ⟨9436942514906845873079383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12582590019875794497439177 9436942514906845873079383)
                ·
                  refine ⟨14155413772360268809619075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436942514906845873079383 14155413772360268809619075)
                  ·
                    refine ⟨21233120658540403214428613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14155413772360268809619075 21233120658540403214428613)
                    ·
                      refine ⟨3981210123476325602705365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21233120658540403214428613 3981210123476325602705365)
                      ·
                        rfl

theorem cell23_7753379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_7753379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753379 prefixEnd_7753379 := by exact prefixLift 7753379
  have htrace : WordTrace (prefixWord ++ tailWord_7753379) baseStart_7753379 baseEnd_7753379 := by
    simpa [prefixWord, tailWord_7753379, baseEnd_7753379] using wordTrace_append hprefix tailTrace_7753379
  have hstable : (prefixWord ++ tailWord_7753379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753379).length < 2 ^ (prefixWord ++ tailWord_7753379).sum := by decide
  have hdescent : baseEnd_7753379 < baseStart_7753379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753384 : List Nat := [2, 1, 7, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7753384 : Nat := 118140960795 + 7753384 * 2 ^ 59
def prefixEnd_7753384 : Nat := 4983230072969 + 3 ^ 40 * 7753384 * 2
def baseEnd_7753384 : Nat := 1327070896959866027714281

theorem tailTrace_7753384 : CollatzResearch.WordTrace tailWord_7753384 prefixEnd_7753384 1327070896959866027714281 := by
  unfold tailWord_7753384
  simp only [CollatzResearch.WordTrace]
  refine ⟨141394573271410707704773603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188526097695214276939698137 141394573271410707704773603)
  ·
    refine ⟨212091859907116061557160405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141394573271410707704773603 212091859907116061557160405)
    ·
      refine ⟨4970902966573032692745947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 212091859907116061557160405 4970902966573032692745947)
      ·
        refine ⟨7456354449859549039118921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970902966573032692745947 7456354449859549039118921)
        ·
          refine ⟨5592265837394661779339191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7456354449859549039118921 5592265837394661779339191)
          ·
            refine ⟨8388398756091992669008787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592265837394661779339191 8388398756091992669008787)
            ·
              refine ⟨12582598134137989003513181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388398756091992669008787 12582598134137989003513181)
              ·
                refine ⟨4718474300301745876317443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12582598134137989003513181 4718474300301745876317443)
                ·
                  refine ⟨7077711450452618814476165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718474300301745876317443 7077711450452618814476165)
                  ·
                    refine ⟨1327070896959866027714281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7077711450452618814476165 1327070896959866027714281)
                    ·
                      rfl

theorem cell23_7753384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7753384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753384 prefixEnd_7753384 := by exact prefixLift 7753384
  have htrace : WordTrace (prefixWord ++ tailWord_7753384) baseStart_7753384 baseEnd_7753384 := by
    simpa [prefixWord, tailWord_7753384, baseEnd_7753384] using wordTrace_append hprefix tailTrace_7753384
  have hstable : (prefixWord ++ tailWord_7753384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753384).length < 2 ^ (prefixWord ++ tailWord_7753384).sum := by decide
  have hdescent : baseEnd_7753384 < baseStart_7753384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753389 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_7753389 : Nat := 118140960795 + 7753389 * 2 ^ 59
def prefixEnd_7753389 : Nat := 4983230072969 + 3 ^ 40 * 7753389 * 2
def baseEnd_7753389 : Nat := 1327071752760956854526773

theorem tailTrace_7753389 : CollatzResearch.WordTrace tailWord_7753389 prefixEnd_7753389 1327071752760956854526773 := by
  unfold tailWord_7753389
  simp only [CollatzResearch.WordTrace]
  refine ⟨282789328907803301263479221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188526219271868867508986147 282789328907803301263479221)
  ·
    refine ⟨26511499585106559493451177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282789328907803301263479221 26511499585106559493451177)
    ·
      refine ⟨19883624688829919620088383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26511499585106559493451177 19883624688829919620088383)
      ·
        refine ⟨29825437033244879430132575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19883624688829919620088383 29825437033244879430132575)
        ·
          refine ⟨44738155549867319145198863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29825437033244879430132575 44738155549867319145198863)
          ·
            refine ⟨67107233324800978717798295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44738155549867319145198863 67107233324800978717798295)
            ·
              refine ⟨100660849987201468076697443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67107233324800978717798295 100660849987201468076697443)
              ·
                refine ⟨150991274980802202115046165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100660849987201468076697443 150991274980802202115046165)
                ·
                  refine ⟨7077716014725103224142789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150991274980802202115046165 7077716014725103224142789)
                  ·
                    refine ⟨1327071752760956854526773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7077716014725103224142789 1327071752760956854526773)
                    ·
                      rfl

theorem cell23_7753389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_7753389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753389 prefixEnd_7753389 := by exact prefixLift 7753389
  have htrace : WordTrace (prefixWord ++ tailWord_7753389) baseStart_7753389 baseEnd_7753389 := by
    simpa [prefixWord, tailWord_7753389, baseEnd_7753389] using wordTrace_append hprefix tailTrace_7753389
  have hstable : (prefixWord ++ tailWord_7753389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753389).length < 2 ^ (prefixWord ++ tailWord_7753389).sum := by decide
  have hdescent : baseEnd_7753389 < baseStart_7753389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753392 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_7753392 : Nat := 118140960795 + 7753392 * 2 ^ 59
def prefixEnd_7753392 : Nat := 4983230072969 + 3 ^ 40 * 7753392 * 2
def baseEnd_7753392 : Nat := 3981216798724834051842805

theorem tailTrace_7753392 : CollatzResearch.WordTrace tailWord_7753392 prefixEnd_7753392 3981216798724834051842805 := by
  unfold tailWord_7753392
  simp only [CollatzResearch.WordTrace]
  refine ⟨141394719163396216387919215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188526292217861621850558953 141394719163396216387919215)
  ·
    refine ⟨212092078745094324581878823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141394719163396216387919215 212092078745094324581878823)
    ·
      refine ⟨318138118117641486872818235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212092078745094324581878823 318138118117641486872818235)
      ·
        refine ⟨477207177176462230309227353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318138118117641486872818235 477207177176462230309227353)
        ·
          refine ⟨357905382882346672731920515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477207177176462230309227353 357905382882346672731920515)
          ·
            refine ⟨536858074323520009097880773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357905382882346672731920515 536858074323520009097880773)
            ·
              refine ⟨100660888935660001705852645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 536858074323520009097880773 100660888935660001705852645)
              ·
                refine ⟨18873916675436250319847371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100660888935660001705852645 18873916675436250319847371)
                ·
                  refine ⟨28310875013154375479771057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18873916675436250319847371 28310875013154375479771057)
                  ·
                    refine ⟨21233156259865781609828293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28310875013154375479771057 21233156259865781609828293)
                    ·
                      refine ⟨3981216798724834051842805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21233156259865781609828293 3981216798724834051842805)
                      ·
                        rfl

theorem cell23_7753392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_7753392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753392 prefixEnd_7753392 := by exact prefixLift 7753392
  have htrace : WordTrace (prefixWord ++ tailWord_7753392) baseStart_7753392 baseEnd_7753392 := by
    simpa [prefixWord, tailWord_7753392, baseEnd_7753392] using wordTrace_append hprefix tailTrace_7753392
  have hstable : (prefixWord ++ tailWord_7753392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753392).length < 2 ^ (prefixWord ++ tailWord_7753392).sum := by decide
  have hdescent : baseEnd_7753392 < baseStart_7753392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753399 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_7753399 : Nat := 118140960795 + 7753399 * 2 ^ 59
def prefixEnd_7753399 : Nat := 4983230072969 + 3 ^ 40 * 7753399 * 2
def baseEnd_7753399 : Nat := 3981220393089415524455273

theorem tailTrace_7753399 : CollatzResearch.WordTrace tailWord_7753399 prefixEnd_7753399 3981220393089415524455273 := by
  unfold tailWord_7753399
  simp only [CollatzResearch.WordTrace]
  refine ⟨282789693637767072971343251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188526462425178048647562167 282789693637767072971343251)
  ·
    refine ⟨424184540456650609457014877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282789693637767072971343251 424184540456650609457014877)
    ·
      refine ⟨159069202671243978546380579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424184540456650609457014877 159069202671243978546380579)
      ·
        refine ⟨238603804006865967819570869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159069202671243978546380579 238603804006865967819570869)
        ·
          refine ⟨22369106625643684483084769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238603804006865967819570869 22369106625643684483084769)
          ·
            refine ⟨16776829969232763362313577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22369106625643684483084769 16776829969232763362313577)
            ·
              refine ⟨12582622476924572521735183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16776829969232763362313577 12582622476924572521735183)
              ·
                refine ⟨18873933715386858782602775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12582622476924572521735183 18873933715386858782602775)
                ·
                  refine ⟨28310900573080288173904163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18873933715386858782602775 28310900573080288173904163)
                  ·
                    refine ⟨42466350859620432260856245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28310900573080288173904163 42466350859620432260856245)
                    ·
                      refine ⟨3981220393089415524455273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42466350859620432260856245 3981220393089415524455273)
                      ·
                        rfl

theorem cell23_7753399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_7753399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753399 prefixEnd_7753399 := by exact prefixLift 7753399
  have htrace : WordTrace (prefixWord ++ tailWord_7753399) baseStart_7753399 baseEnd_7753399 := by
    simpa [prefixWord, tailWord_7753399, baseEnd_7753399] using wordTrace_append hprefix tailTrace_7753399
  have hstable : (prefixWord ++ tailWord_7753399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753399).length < 2 ^ (prefixWord ++ tailWord_7753399).sum := by decide
  have hdescent : baseEnd_7753399 < baseStart_7753399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753402 : List Nat := [3, 1, 1, 1, 2, 6, 9]
def baseStart_7753402 : Nat := 118140960795 + 7753402 * 2 ^ 59
def prefixEnd_7753402 : Nat := 4983230072969 + 3 ^ 40 * 7753402 * 2
def baseEnd_7753402 : Nat := 49150888068288629786639

theorem tailTrace_7753402 : CollatzResearch.WordTrace tailWord_7753402 prefixEnd_7753402 49150888068288629786639 := by
  unfold tailWord_7753402
  simp only [CollatzResearch.WordTrace]
  refine ⟨70697450764189051120925615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188526535371170802989134973 70697450764189051120925615)
  ·
    refine ⟨106046176146283576681388423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70697450764189051120925615 106046176146283576681388423)
    ·
      refine ⟨159069264219425365022082635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106046176146283576681388423 159069264219425365022082635)
      ·
        refine ⟨238603896329138047533123953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159069264219425365022082635 238603896329138047533123953)
        ·
          refine ⟨178952922246853535649842965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238603896329138047533123953 178952922246853535649842965)
          ·
            refine ⟨8388418230321259483586389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178952922246853535649842965 8388418230321259483586389)
            ·
              refine ⟨49150888068288629786639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8388418230321259483586389 49150888068288629786639)
              ·
                rfl

theorem cell23_7753402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 9].length) (baseStart_7753402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753402 prefixEnd_7753402 := by exact prefixLift 7753402
  have htrace : WordTrace (prefixWord ++ tailWord_7753402) baseStart_7753402 baseEnd_7753402 := by
    simpa [prefixWord, tailWord_7753402, baseEnd_7753402] using wordTrace_append hprefix tailTrace_7753402
  have hstable : (prefixWord ++ tailWord_7753402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753402).length < 2 ^ (prefixWord ++ tailWord_7753402).sum := by decide
  have hdescent : baseEnd_7753402 < baseStart_7753402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753422 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_7753422 : Nat := 118140960795 + 7753422 * 2 ^ 59
def prefixEnd_7753422 : Nat := 4983230072969 + 3 ^ 40 * 7753422 * 2
def baseEnd_7753422 : Nat := 3981232203144468934467667

theorem tailTrace_7753422 : CollatzResearch.WordTrace tailWord_7753422 prefixEnd_7753422 3981232203144468934467667 := by
  unfold tailWord_7753422
  simp only [CollatzResearch.WordTrace]
  refine ⟨35348816564585468487428815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188527021677789165266287013 35348816564585468487428815)
  ·
    refine ⟨53023224846878202731143223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35348816564585468487428815 53023224846878202731143223)
    ·
      refine ⟨79534837270317304096714835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53023224846878202731143223 79534837270317304096714835)
      ·
        refine ⟨119302255905475956145072253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79534837270317304096714835 119302255905475956145072253)
        ·
          refine ⟨44738345964553483554402095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119302255905475956145072253 44738345964553483554402095)
          ·
            refine ⟨67107518946830225331603143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44738345964553483554402095 67107518946830225331603143)
            ·
              refine ⟨100661278420245337997404715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67107518946830225331603143 100661278420245337997404715)
              ·
                refine ⟨150991917630368006996107073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100661278420245337997404715 150991917630368006996107073)
                ·
                  refine ⟨113243938222776005247080305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150991917630368006996107073 113243938222776005247080305)
                  ·
                    refine ⟨84932953667082003935310229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113243938222776005247080305 84932953667082003935310229)
                    ·
                      refine ⟨3981232203144468934467667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84932953667082003935310229 3981232203144468934467667)
                      ·
                        rfl

theorem cell23_7753422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_7753422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753422 prefixEnd_7753422 := by exact prefixLift 7753422
  have htrace : WordTrace (prefixWord ++ tailWord_7753422) baseStart_7753422 baseEnd_7753422 := by
    simpa [prefixWord, tailWord_7753422, baseEnd_7753422] using wordTrace_append hprefix tailTrace_7753422
  have hstable : (prefixWord ++ tailWord_7753422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753422).length < 2 ^ (prefixWord ++ tailWord_7753422).sum := by decide
  have hdescent : baseEnd_7753422 < baseStart_7753422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753486 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2]
def baseStart_7753486 : Nat := 118140960795 + 7753486 * 2 ^ 59
def prefixEnd_7753486 : Nat := 4983230072969 + 3 ^ 40 * 7753486 * 2
def baseEnd_7753486 : Nat := 3981265065906356684067373

theorem tailTrace_7753486 : CollatzResearch.WordTrace tailWord_7753486 prefixEnd_7753486 3981265065906356684067373 := by
  unfold tailWord_7753486
  simp only [CollatzResearch.WordTrace]
  refine ⟨35349108348556485853720039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188528577858967924553173541 35349108348556485853720039)
  ·
    refine ⟨53023662522834728780580059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35349108348556485853720039 53023662522834728780580059)
    ·
      refine ⟨79535493784252093170870089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53023662522834728780580059 79535493784252093170870089)
      ·
        refine ⟨59651620338189069878152567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79535493784252093170870089 59651620338189069878152567)
        ·
          refine ⟨89477430507283604817228851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59651620338189069878152567 89477430507283604817228851)
          ·
            refine ⟨134216145760925407225843277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89477430507283604817228851 134216145760925407225843277)
            ·
              refine ⟨50331054660347027709691229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134216145760925407225843277 50331054660347027709691229)
              ·
                refine ⟨18874145497630135391134211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50331054660347027709691229 18874145497630135391134211)
                ·
                  refine ⟨28311218246445203086701317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18874145497630135391134211 28311218246445203086701317)
                  ·
                    refine ⟨5308353421208475578756497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28311218246445203086701317 5308353421208475578756497)
                    ·
                      refine ⟨3981265065906356684067373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308353421208475578756497 3981265065906356684067373)
                      ·
                        rfl

theorem cell23_7753486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_7753486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753486 prefixEnd_7753486 := by exact prefixLift 7753486
  have htrace : WordTrace (prefixWord ++ tailWord_7753486) baseStart_7753486 baseEnd_7753486 := by
    simpa [prefixWord, tailWord_7753486, baseEnd_7753486] using wordTrace_append hprefix tailTrace_7753486
  have hstable : (prefixWord ++ tailWord_7753486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753486).length < 2 ^ (prefixWord ++ tailWord_7753486).sum := by decide
  have hdescent : baseEnd_7753486 < baseStart_7753486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753526 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_7753526 : Nat := 118140960795 + 7753526 * 2 ^ 59
def prefixEnd_7753526 : Nat := 4983230072969 + 3 ^ 40 * 7753526 * 2
def baseEnd_7753526 : Nat := 442365067236948503063021

theorem tailTrace_7753526 : CollatzResearch.WordTrace tailWord_7753526 prefixEnd_7753526 442365067236948503063021 := by
  unfold tailWord_7753526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674645356769185853826027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188529550472204649107477621 17674645356769185853826027)
  ·
    refine ⟨26511968035153778780739041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17674645356769185853826027 26511968035153778780739041)
    ·
      refine ⟨19883976026365334085554281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26511968035153778780739041 19883976026365334085554281)
      ·
        refine ⟨14912982019774000564165711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19883976026365334085554281 14912982019774000564165711)
        ·
          refine ⟨22369473029661000846248567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14912982019774000564165711 22369473029661000846248567)
          ·
            refine ⟨33554209544491501269372851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22369473029661000846248567 33554209544491501269372851)
            ·
              refine ⟨50331314316737251904059277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33554209544491501269372851 50331314316737251904059277)
              ·
                refine ⟨18874242868776469464022229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50331314316737251904059277 18874242868776469464022229)
                ·
                  refine ⟨442365067236948503063021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18874242868776469464022229 442365067236948503063021)
                  ·
                    rfl

theorem cell23_7753526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_7753526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753526 prefixEnd_7753526 := by exact prefixLift 7753526
  have htrace : WordTrace (prefixWord ++ tailWord_7753526) baseStart_7753526 baseEnd_7753526 := by
    simpa [prefixWord, tailWord_7753526, baseEnd_7753526] using wordTrace_append hprefix tailTrace_7753526
  have hstable : (prefixWord ++ tailWord_7753526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753526).length < 2 ^ (prefixWord ++ tailWord_7753526).sum := by decide
  have hdescent : baseEnd_7753526 < baseStart_7753526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753552 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 10]
def baseStart_7753552 : Nat := 118140960795 + 7753552 * 2 ^ 59
def prefixEnd_7753552 : Nat := 4983230072969 + 3 ^ 40 * 7753552 * 2
def baseEnd_7753552 : Nat := 1327099651876517808614023

theorem tailTrace_7753552 : CollatzResearch.WordTrace tailWord_7753552 prefixEnd_7753552 1327099651876517808614023 := by
  unfold tailWord_7753552
  simp only [CollatzResearch.WordTrace]
  refine ⟨141397637003106390050831455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188530182670808520067775273 141397637003106390050831455)
  ·
    refine ⟨212096455504659585076247183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141397637003106390050831455 212096455504659585076247183)
    ·
      refine ⟨318144683256989377614370775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212096455504659585076247183 318144683256989377614370775)
      ·
        refine ⟨477217024885484066421556163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318144683256989377614370775 477217024885484066421556163)
        ·
          refine ⟨715825537328226099632334245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477217024885484066421556163 715825537328226099632334245)
          ·
            refine ⟨134217288249042393681062671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 715825537328226099632334245 134217288249042393681062671)
            ·
              refine ⟨201325932373563590521594007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134217288249042393681062671 201325932373563590521594007)
              ·
                refine ⟨301988898560345385782391011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201325932373563590521594007 301988898560345385782391011)
                ·
                  refine ⟨452983347840518078673586517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301988898560345385782391011 452983347840518078673586517)
                  ·
                    refine ⟨1327099651876517808614023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 452983347840518078673586517 1327099651876517808614023)
                    ·
                      rfl

theorem cell23_7753552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_7753552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753552 prefixEnd_7753552 := by exact prefixLift 7753552
  have htrace : WordTrace (prefixWord ++ tailWord_7753552) baseStart_7753552 baseEnd_7753552 := by
    simpa [prefixWord, tailWord_7753552, baseEnd_7753552] using wordTrace_append hprefix tailTrace_7753552
  have hstable : (prefixWord ++ tailWord_7753552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753552).length < 2 ^ (prefixWord ++ tailWord_7753552).sum := by decide
  have hdescent : baseEnd_7753552 < baseStart_7753552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753576 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_7753576 : Nat := 118140960795 + 7753576 * 2 ^ 59
def prefixEnd_7753576 : Nat := 4983230072969 + 3 ^ 40 * 7753576 * 2
def baseEnd_7753576 : Nat := 3981311279165261331941959

theorem tailTrace_7753576 : CollatzResearch.WordTrace tailWord_7753576 prefixEnd_7753576 3981311279165261331941959 := by
  unfold tailWord_7753576
  simp only [CollatzResearch.WordTrace]
  refine ⟨141398074679062916100268291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188530766238750554800357721 141398074679062916100268291)
  ·
    refine ⟨212097112018594374150402437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141398074679062916100268291 212097112018594374150402437)
    ·
      refine ⟨39768208503486445153200457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212097112018594374150402437 39768208503486445153200457)
      ·
        refine ⟨29826156377614833864900343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39768208503486445153200457 29826156377614833864900343)
        ·
          refine ⟨44739234566422250797350515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29826156377614833864900343 44739234566422250797350515)
          ·
            refine ⟨67108851849633376196025773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44739234566422250797350515 67108851849633376196025773)
            ·
              refine ⟨25165819443612516073509665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67108851849633376196025773 25165819443612516073509665)
              ·
                refine ⟨18874364582709387055132249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25165819443612516073509665 18874364582709387055132249)
                ·
                  refine ⟨14155773437032040291349187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18874364582709387055132249 14155773437032040291349187)
                  ·
                    refine ⟨21233660155548060437023781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14155773437032040291349187 21233660155548060437023781)
                    ·
                      refine ⟨3981311279165261331941959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21233660155548060437023781 3981311279165261331941959)
                      ·
                        rfl

theorem cell23_7753576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_7753576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753576 prefixEnd_7753576 := by exact prefixLift 7753576
  have htrace : WordTrace (prefixWord ++ tailWord_7753576) baseStart_7753576 baseEnd_7753576 := by
    simpa [prefixWord, tailWord_7753576, baseEnd_7753576] using wordTrace_append hprefix tailTrace_7753576
  have hstable : (prefixWord ++ tailWord_7753576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753576).length < 2 ^ (prefixWord ++ tailWord_7753576).sum := by decide
  have hdescent : baseEnd_7753576 < baseStart_7753576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753633 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 6]
def baseStart_7753633 : Nat := 118140960795 + 7753633 * 2 ^ 59
def prefixEnd_7753633 : Nat := 4983230072969 + 3 ^ 40 * 7753633 * 2
def baseEnd_7753633 : Nat := 442371171951396400992133

theorem tailTrace_7753633 : CollatzResearch.WordTrace tailWord_7753633 prefixEnd_7753633 442371171951396400992133 := by
  unfold tailWord_7753633
  simp only [CollatzResearch.WordTrace]
  refine ⟨282798228318919330935361553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188532152212612887290241035 282798228318919330935361553)
  ·
    refine ⟨212098671239189498201521165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282798228318919330935361553 212098671239189498201521165)
    ·
      refine ⟨79537001714696061825570437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212098671239189498201521165 79537001714696061825570437)
      ·
        refine ⟨14913187821505511592294457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79537001714696061825570437 14913187821505511592294457)
        ·
          refine ⟨11184890866129133694220843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14913187821505511592294457 11184890866129133694220843)
          ·
            refine ⟨16777336299193700541331265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11184890866129133694220843 16777336299193700541331265)
            ·
              refine ⟨12583002224395275405998449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16777336299193700541331265 12583002224395275405998449)
              ·
                refine ⟨9437251668296456554498837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12583002224395275405998449 9437251668296456554498837)
                ·
                  refine ⟨442371171951396400992133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9437251668296456554498837 442371171951396400992133)
                  ·
                    rfl

theorem cell23_7753633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 6].length) (baseStart_7753633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753633 prefixEnd_7753633 := by exact prefixLift 7753633
  have htrace : WordTrace (prefixWord ++ tailWord_7753633) baseStart_7753633 baseEnd_7753633 := by
    simpa [prefixWord, tailWord_7753633, baseEnd_7753633] using wordTrace_append hprefix tailTrace_7753633
  have hstable : (prefixWord ++ tailWord_7753633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753633).length < 2 ^ (prefixWord ++ tailWord_7753633).sum := by decide
  have hdescent : baseEnd_7753633 < baseStart_7753633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753659 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 1, 6]
def baseStart_7753659 : Nat := 118140960795 + 7753659 * 2 ^ 59
def prefixEnd_7753659 : Nat := 4983230072969 + 3 ^ 40 * 7753659 * 2
def baseEnd_7753659 : Nat := 1327117966019861502401359

theorem tailTrace_7753659 : CollatzResearch.WordTrace tailWord_7753659 prefixEnd_7753659 1327117966019861502401359 := by
  unfold tailWord_7753659
  simp only [CollatzResearch.WordTrace]
  refine ⟨282799176616825137375808031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188532784411216758250538687 282799176616825137375808031)
  ·
    refine ⟨424198764925237706063712047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282799176616825137375808031 424198764925237706063712047)
    ·
      refine ⟨636298147387856559095568071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424198764925237706063712047 636298147387856559095568071)
      ·
        refine ⟨954447221081784838643352107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636298147387856559095568071 954447221081784838643352107)
        ·
          refine ⟨1431670831622677257965028161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954447221081784838643352107 1431670831622677257965028161)
          ·
            refine ⟨1073753123717007943473771121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431670831622677257965028161 1073753123717007943473771121)
            ·
              refine ⟨805314842787755957605328341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073753123717007943473771121 805314842787755957605328341)
              ·
                refine ⟨18874566627838030256374883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 805314842787755957605328341 18874566627838030256374883)
                ·
                  refine ⟨28311849941757045384562325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18874566627838030256374883 28311849941757045384562325)
                  ·
                    refine ⟨1327117966019861502401359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28311849941757045384562325 1327117966019861502401359)
                    ·
                      rfl

theorem cell23_7753659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 6].length) (baseStart_7753659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753659 prefixEnd_7753659 := by exact prefixLift 7753659
  have htrace : WordTrace (prefixWord ++ tailWord_7753659) baseStart_7753659 baseEnd_7753659 := by
    simpa [prefixWord, tailWord_7753659, baseEnd_7753659] using wordTrace_append hprefix tailTrace_7753659
  have hstable : (prefixWord ++ tailWord_7753659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753659).length < 2 ^ (prefixWord ++ tailWord_7753659).sum := by decide
  have hdescent : baseEnd_7753659 < baseStart_7753659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753669 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_7753669 : Nat := 118140960795 + 7753669 * 2 ^ 59
def prefixEnd_7753669 : Nat := 4983230072969 + 3 ^ 40 * 7753669 * 2
def baseEnd_7753669 : Nat := 3981359032866129468079031

theorem tailTrace_7753669 : CollatzResearch.WordTrace tailWord_7753669 prefixEnd_7753669 3981359032866129468079031 := by
  unfold tailWord_7753669
  simp only [CollatzResearch.WordTrace]
  refine ⟨282799541346788909083672061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188533027564525939389114707 282799541346788909083672061)
  ·
    refine ⟨106049828005045840906377023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282799541346788909083672061 106049828005045840906377023)
    ·
      refine ⟨159074742007568761359565535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106049828005045840906377023 159074742007568761359565535)
      ·
        refine ⟨238612113011353142039348303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159074742007568761359565535 238612113011353142039348303)
        ·
          refine ⟨357918169517029713059022455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238612113011353142039348303 357918169517029713059022455)
          ·
            refine ⟨536877254275544569588533683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357918169517029713059022455 536877254275544569588533683)
            ·
              refine ⟨805315881413316854382800525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536877254275544569588533683 805315881413316854382800525)
              ·
                refine ⟨301993455529993820393550197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805315881413316854382800525 301993455529993820393550197)
                ·
                  refine ⟨28311886455936920661895331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301993455529993820393550197 28311886455936920661895331)
                  ·
                    refine ⟨42467829683905380992842997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28311886455936920661895331 42467829683905380992842997)
                    ·
                      refine ⟨3981359032866129468079031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42467829683905380992842997 3981359032866129468079031)
                      ·
                        rfl

theorem cell23_7753669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_7753669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753669 prefixEnd_7753669 := by exact prefixLift 7753669
  have htrace : WordTrace (prefixWord ++ tailWord_7753669) baseStart_7753669 baseEnd_7753669 := by
    simpa [prefixWord, tailWord_7753669, baseEnd_7753669] using wordTrace_append hprefix tailTrace_7753669
  have hstable : (prefixWord ++ tailWord_7753669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753669).length < 2 ^ (prefixWord ++ tailWord_7753669).sum := by decide
  have hdescent : baseEnd_7753669 < baseStart_7753669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753676 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_7753676 : Nat := 118140960795 + 7753676 * 2 ^ 59
def prefixEnd_7753676 : Nat := 4983230072969 + 3 ^ 40 * 7753676 * 2
def baseEnd_7753676 : Nat := 1327120875743570313563833

theorem tailTrace_7753676 : CollatzResearch.WordTrace tailWord_7753676 prefixEnd_7753676 1327120875743570313563833 := by
  unfold tailWord_7753676
  simp only [CollatzResearch.WordTrace]
  refine ⟨141399898328881774639588441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188533197771842366186117921 141399898328881774639588441)
  ·
    refine ⟨106049923746661330979691331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141399898328881774639588441 106049923746661330979691331)
    ·
      refine ⟨159074885619991996469536997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106049923746661330979691331 159074885619991996469536997)
      ·
        refine ⟨29826541053748499338038187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159074885619991996469536997 29826541053748499338038187)
        ·
          refine ⟨44739811580622749007057281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29826541053748499338038187 44739811580622749007057281)
          ·
            refine ⟨33554858685467061755292961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44739811580622749007057281 33554858685467061755292961)
            ·
              refine ⟨25166144014100296316469721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33554858685467061755292961 25166144014100296316469721)
              ·
                refine ⟨18874608010575222237352291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25166144014100296316469721 18874608010575222237352291)
                ·
                  refine ⟨28311912015862833356028437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18874608010575222237352291 28311912015862833356028437)
                  ·
                    refine ⟨1327120875743570313563833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28311912015862833356028437 1327120875743570313563833)
                    ·
                      rfl

theorem cell23_7753676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_7753676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753676 prefixEnd_7753676 := by exact prefixLift 7753676
  have htrace : WordTrace (prefixWord ++ tailWord_7753676) baseStart_7753676 baseEnd_7753676 := by
    simpa [prefixWord, tailWord_7753676, baseEnd_7753676] using wordTrace_append hprefix tailTrace_7753676
  have hstable : (prefixWord ++ tailWord_7753676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753676).length < 2 ^ (prefixWord ++ tailWord_7753676).sum := by decide
  have hdescent : baseEnd_7753676 < baseStart_7753676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753700 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_7753700 : Nat := 118140960795 + 7753700 * 2 ^ 59
def prefixEnd_7753700 : Nat := 4983230072969 + 3 ^ 40 * 7753700 * 2
def baseEnd_7753700 : Nat := 3981374950766418846791389

theorem tailTrace_7753700 : CollatzResearch.WordTrace tailWord_7753700 prefixEnd_7753700 3981374950766418846791389 := by
  unfold tailWord_7753700
  simp only [CollatzResearch.WordTrace]
  refine ⟨141400336004838300689025277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188533781339784400918700369 141400336004838300689025277)
  ·
    refine ⟨53025126001814362758384479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141400336004838300689025277 53025126001814362758384479)
    ·
      refine ⟨79537689002721544137576719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53025126001814362758384479 79537689002721544137576719)
      ·
        refine ⟨119306533504082316206365079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79537689002721544137576719 119306533504082316206365079)
        ·
          refine ⟨178959800256123474309547619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119306533504082316206365079 178959800256123474309547619)
          ·
            refine ⟨268439700384185211464321429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178959800256123474309547619 268439700384185211464321429)
            ·
              refine ⟨12583110955508681787390067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268439700384185211464321429 12583110955508681787390067)
              ·
                refine ⟨18874666433263022681085101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12583110955508681787390067 18874666433263022681085101)
                ·
                  refine ⟨7077999912473633505406913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18874666433263022681085101 7077999912473633505406913)
                  ·
                    refine ⟨5308499934355225129055185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7077999912473633505406913 5308499934355225129055185)
                    ·
                      refine ⟨3981374950766418846791389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308499934355225129055185 3981374950766418846791389)
                      ·
                        rfl

theorem cell23_7753700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_7753700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753700 prefixEnd_7753700 := by exact prefixLift 7753700
  have htrace : WordTrace (prefixWord ++ tailWord_7753700) baseStart_7753700 baseEnd_7753700 := by
    simpa [prefixWord, tailWord_7753700, baseEnd_7753700] using wordTrace_append hprefix tailTrace_7753700
  have hstable : (prefixWord ++ tailWord_7753700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753700).length < 2 ^ (prefixWord ++ tailWord_7753700).sum := by decide
  have hdescent : baseEnd_7753700 < baseStart_7753700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753703 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_7753703 : Nat := 118140960795 + 7753703 * 2 ^ 59
def prefixEnd_7753703 : Nat := 4983230072969 + 3 ^ 40 * 7753703 * 2
def baseEnd_7753703 : Nat := 3981376491208382335053875

theorem tailTrace_7753703 : CollatzResearch.WordTrace tailWord_7753703 prefixEnd_7753703 3981376491208382335053875 := by
  unfold tailWord_7753703
  simp only [CollatzResearch.WordTrace]
  refine ⟨282800781428665732890409763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188533854285777155260273175 282800781428665732890409763)
  ·
    refine ⟨424201172142998599335614645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282800781428665732890409763 424201172142998599335614645)
    ·
      refine ⟨39768859888406118687713873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 424201172142998599335614645 39768859888406118687713873)
      ·
        refine ⟨29826644916304589015785405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39768859888406118687713873 29826644916304589015785405)
        ·
          refine ⟨11184991843614220880919527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29826644916304589015785405 11184991843614220880919527)
          ·
            refine ⟨16777487765421331321379291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11184991843614220880919527 16777487765421331321379291)
            ·
              refine ⟨25166231648131996982068937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16777487765421331321379291 25166231648131996982068937)
              ·
                refine ⟨18874673736098997736551703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25166231648131996982068937 18874673736098997736551703)
                ·
                  refine ⟨28312010604148496604827555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18874673736098997736551703 28312010604148496604827555)
                  ·
                    refine ⟨42468015906222744907241333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28312010604148496604827555 42468015906222744907241333)
                    ·
                      refine ⟨3981376491208382335053875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42468015906222744907241333 3981376491208382335053875)
                      ·
                        rfl

theorem cell23_7753703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_7753703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753703 prefixEnd_7753703 := by exact prefixLift 7753703
  have htrace : WordTrace (prefixWord ++ tailWord_7753703) baseStart_7753703 baseEnd_7753703 := by
    simpa [prefixWord, tailWord_7753703, baseEnd_7753703] using wordTrace_append hprefix tailTrace_7753703
  have hstable : (prefixWord ++ tailWord_7753703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753703).length < 2 ^ (prefixWord ++ tailWord_7753703).sum := by decide
  have hdescent : baseEnd_7753703 < baseStart_7753703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753733 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_7753733 : Nat := 118140960795 + 7753733 * 2 ^ 59
def prefixEnd_7753733 : Nat := 4983230072969 + 3 ^ 40 * 7753733 * 2
def baseEnd_7753733 : Nat := 3981391895628017217678737

theorem tailTrace_7753733 : CollatzResearch.WordTrace tailWord_7753733 prefixEnd_7753733 3981391895628017217678737 := by
  unfold tailWord_7753733
  simp only [CollatzResearch.WordTrace]
  refine ⟨282801875618557048014001853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188534583745704698676001235 282801875618557048014001853)
  ·
    refine ⟨106050703356958893005250695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282801875618557048014001853 106050703356958893005250695)
    ·
      refine ⟨159076055035438339507876043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106050703356958893005250695 159076055035438339507876043)
      ·
        refine ⟨238614082553157509261814065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159076055035438339507876043 238614082553157509261814065)
        ·
          refine ⟨178960561914868131946360549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238614082553157509261814065 178960561914868131946360549)
          ·
            refine ⟨33555105359037774739942603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178960561914868131946360549 33555105359037774739942603)
            ·
              refine ⟨50332658038556662109913905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33555105359037774739942603 50332658038556662109913905)
              ·
                refine ⟨37749493528917496582435429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50332658038556662109913905 37749493528917496582435429)
                ·
                  refine ⟨7078030036672030609206643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37749493528917496582435429 7078030036672030609206643)
                  ·
                    refine ⟨10617045055008045913809965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7078030036672030609206643 10617045055008045913809965)
                    ·
                      refine ⟨3981391895628017217678737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10617045055008045913809965 3981391895628017217678737)
                      ·
                        rfl

theorem cell23_7753733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_7753733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753733 prefixEnd_7753733 := by exact prefixLift 7753733
  have htrace : WordTrace (prefixWord ++ tailWord_7753733) baseStart_7753733 baseEnd_7753733 := by
    simpa [prefixWord, tailWord_7753733, baseEnd_7753733] using wordTrace_append hprefix tailTrace_7753733
  have hstable : (prefixWord ++ tailWord_7753733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753733).length < 2 ^ (prefixWord ++ tailWord_7753733).sum := by decide
  have hdescent : baseEnd_7753733 < baseStart_7753733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753751 : List Nat := [1, 1, 3, 5, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7753751 : Nat := 118140960795 + 7753751 * 2 ^ 59
def prefixEnd_7753751 : Nat := 4983230072969 + 3 ^ 40 * 7753751 * 2
def baseEnd_7753751 : Nat := 3981401138279798147253655

theorem tailTrace_7753751 : CollatzResearch.WordTrace tailWord_7753751 prefixEnd_7753751 3981401138279798147253655 := by
  unfold tailWord_7753751
  simp only [CollatzResearch.WordTrace]
  refine ⟨282802532132491837088157107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188535021421661224725438071 282802532132491837088157107)
  ·
    refine ⟨424203798198737755632235661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282802532132491837088157107 424203798198737755632235661)
    ·
      refine ⟨159076424324526658362088373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424203798198737755632235661 159076424324526658362088373)
      ·
        refine ⟨14913414780424374221445785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159076424324526658362088373 14913414780424374221445785)
        ·
          refine ⟨11185061085318280666084339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14913414780424374221445785 11185061085318280666084339)
          ·
            refine ⟨16777591627977420999126509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185061085318280666084339 16777591627977420999126509)
            ·
              refine ⟨6291596860491532874672441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16777591627977420999126509 6291596860491532874672441)
              ·
                refine ⟨4718697645368649656004331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6291596860491532874672441 4718697645368649656004331)
                ·
                  refine ⟨7078046468052974484006497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718697645368649656004331 7078046468052974484006497)
                  ·
                    refine ⟨5308534851039730863004873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7078046468052974484006497 5308534851039730863004873)
                    ·
                      refine ⟨3981401138279798147253655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308534851039730863004873 3981401138279798147253655)
                      ·
                        rfl

theorem cell23_7753751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7753751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753751 prefixEnd_7753751 := by exact prefixLift 7753751
  have htrace : WordTrace (prefixWord ++ tailWord_7753751) baseStart_7753751 baseEnd_7753751 := by
    simpa [prefixWord, tailWord_7753751, baseEnd_7753751] using wordTrace_append hprefix tailTrace_7753751
  have hstable : (prefixWord ++ tailWord_7753751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753751).length < 2 ^ (prefixWord ++ tailWord_7753751).sum := by decide
  have hdescent : baseEnd_7753751 < baseStart_7753751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753776 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_7753776 : Nat := 118140960795 + 7753776 * 2 ^ 59
def prefixEnd_7753776 : Nat := 4983230072969 + 3 ^ 40 * 7753776 * 2
def baseEnd_7753776 : Nat := 3981413975296160549441039

theorem tailTrace_7753776 : CollatzResearch.WordTrace tailWord_7753776 prefixEnd_7753776 3981413975296160549441039 := by
  unfold tailWord_7753776
  simp only [CollatzResearch.WordTrace]
  refine ⟨141401721978700633178908591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188535629304934177571878121 141401721978700633178908591)
  ·
    refine ⟨212102582968050949768362887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141401721978700633178908591 212102582968050949768362887)
    ·
      refine ⟨318153874452076424652544331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212102582968050949768362887 318153874452076424652544331)
      ·
        refine ⟨477230811678114636978816497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318153874452076424652544331 477230811678114636978816497)
        ·
          refine ⟨357923108758585977734112373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477230811678114636978816497 357923108758585977734112373)
          ·
            refine ⟨33555291446117435412573035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357923108758585977734112373 33555291446117435412573035)
            ·
              refine ⟨50332937169176153118859553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33555291446117435412573035 50332937169176153118859553)
              ·
                refine ⟨37749702876882114839144665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50332937169176153118859553 37749702876882114839144665)
                ·
                  refine ⟨28312277157661586129358499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37749702876882114839144665 28312277157661586129358499)
                  ·
                    refine ⟨42468415736492379194037749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28312277157661586129358499 42468415736492379194037749)
                    ·
                      refine ⟨3981413975296160549441039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42468415736492379194037749 3981413975296160549441039)
                      ·
                        rfl

theorem cell23_7753776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_7753776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753776 prefixEnd_7753776 := by exact prefixLift 7753776
  have htrace : WordTrace (prefixWord ++ tailWord_7753776) baseStart_7753776 baseEnd_7753776 := by
    simpa [prefixWord, tailWord_7753776, baseEnd_7753776] using wordTrace_append hprefix tailTrace_7753776
  have hstable : (prefixWord ++ tailWord_7753776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753776).length < 2 ^ (prefixWord ++ tailWord_7753776).sum := by decide
  have hdescent : baseEnd_7753776 < baseStart_7753776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753777 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 1, 3, 2]
def baseStart_7753777 : Nat := 118140960795 + 7753777 * 2 ^ 59
def prefixEnd_7753777 : Nat := 4983230072969 + 3 ^ 40 * 7753777 * 2
def baseEnd_7753777 : Nat := 3981414488776815045528535

theorem tailTrace_7753777 : CollatzResearch.WordTrace tailWord_7753777 prefixEnd_7753777 3981414488776815045528535 := by
  unfold tailWord_7753777
  simp only [CollatzResearch.WordTrace]
  refine ⟨282803480430397643528603585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188535653620265095685735723 282803480430397643528603585)
  ·
    refine ⟨212102610322798232646452689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282803480430397643528603585 212102610322798232646452689)
    ·
      refine ⟨159076957742098674484839517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212102610322798232646452689 159076957742098674484839517)
      ·
        refine ⟨59653859153287002931814819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159076957742098674484839517 59653859153287002931814819)
        ·
          refine ⟨89480788729930504397722229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59653859153287002931814819 89480788729930504397722229)
          ·
            refine ⟨8388823943430984787286459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89480788729930504397722229 8388823943430984787286459)
            ·
              refine ⟨12583235915146477180929689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388823943430984787286459 12583235915146477180929689)
              ·
                refine ⟨9437426936359857885697267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12583235915146477180929689 9437426936359857885697267)
                ·
                  refine ⟨14156140404539786828545901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9437426936359857885697267 14156140404539786828545901)
                  ·
                    refine ⟨5308552651702420060704713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14156140404539786828545901 5308552651702420060704713)
                    ·
                      refine ⟨3981414488776815045528535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308552651702420060704713 3981414488776815045528535)
                      ·
                        rfl

theorem cell23_7753777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_7753777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753777 prefixEnd_7753777 := by exact prefixLift 7753777
  have htrace : WordTrace (prefixWord ++ tailWord_7753777) baseStart_7753777 baseEnd_7753777 := by
    simpa [prefixWord, tailWord_7753777, baseEnd_7753777] using wordTrace_append hprefix tailTrace_7753777
  have hstable : (prefixWord ++ tailWord_7753777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753777).length < 2 ^ (prefixWord ++ tailWord_7753777).sum := by decide
  have hdescent : baseEnd_7753777 < baseStart_7753777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753786 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_7753786 : Nat := 118140960795 + 7753786 * 2 ^ 59
def prefixEnd_7753786 : Nat := 4983230072969 + 3 ^ 40 * 7753786 * 2
def baseEnd_7753786 : Nat := 3981419110102705510315993

theorem tailTrace_7753786 : CollatzResearch.WordTrace tailWord_7753786 prefixEnd_7753786 3981419110102705510315993 := by
  unfold tailWord_7753786
  simp only [CollatzResearch.WordTrace]
  refine ⟨70700952171841259516420303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188535872458243358710454141 70700952171841259516420303)
  ·
    refine ⟨106051428257761889274630455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70700952171841259516420303 106051428257761889274630455)
    ·
      refine ⟨159077142386642833911945683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106051428257761889274630455 159077142386642833911945683)
      ·
        refine ⟨238615713579964250867918525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159077142386642833911945683 238615713579964250867918525)
        ·
          refine ⟨89480892592486594075469447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238615713579964250867918525 89480892592486594075469447)
          ·
            refine ⟨134221338888729891113204171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89480892592486594075469447 134221338888729891113204171)
            ·
              refine ⟨201332008333094836669806257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134221338888729891113204171 201332008333094836669806257)
              ·
                refine ⟨150999006249821127502354693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201332008333094836669806257 150999006249821127502354693)
                ·
                  refine ⟨28312313671841461406691505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150999006249821127502354693 28312313671841461406691505)
                  ·
                    refine ⟨21234235253881096055018629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28312313671841461406691505 21234235253881096055018629)
                    ·
                      refine ⟨3981419110102705510315993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21234235253881096055018629 3981419110102705510315993)
                      ·
                        rfl

theorem cell23_7753786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_7753786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753786 prefixEnd_7753786 := by exact prefixLift 7753786
  have htrace : WordTrace (prefixWord ++ tailWord_7753786) baseStart_7753786 baseEnd_7753786 := by
    simpa [prefixWord, tailWord_7753786, baseEnd_7753786] using wordTrace_append hprefix tailTrace_7753786
  have hstable : (prefixWord ++ tailWord_7753786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753786).length < 2 ^ (prefixWord ++ tailWord_7753786).sum := by decide
  have hdescent : baseEnd_7753786 < baseStart_7753786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753793 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7753793 : Nat := 118140960795 + 7753793 * 2 ^ 59
def prefixEnd_7753793 : Nat := 4983230072969 + 3 ^ 40 * 7753793 * 2
def baseEnd_7753793 : Nat := 3981422704467286982928461

theorem tailTrace_7753793 : CollatzResearch.WordTrace tailWord_7753793 prefixEnd_7753793 3981422704467286982928461 := by
  unfold tailWord_7753793
  simp only [CollatzResearch.WordTrace]
  refine ⟨282804063998339678261186033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188536042665559785507457355 282804063998339678261186033)
  ·
    refine ⟨212103047998754758695889525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282804063998339678261186033 212103047998754758695889525)
    ·
      refine ⟨19884660749883258627739643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212103047998754758695889525 19884660749883258627739643)
      ·
        refine ⟨29826991124824887941609465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19884660749883258627739643 29826991124824887941609465)
        ·
          refine ⟨22370243343618665956207099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29826991124824887941609465 22370243343618665956207099)
          ·
            refine ⟨33555365015427998934310649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22370243343618665956207099 33555365015427998934310649)
            ·
              refine ⟨25166523761570999200732987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33555365015427998934310649 25166523761570999200732987)
              ·
                refine ⟨37749785642356498801099481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25166523761570999200732987 37749785642356498801099481)
                ·
                  refine ⟨28312339231767374100824611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37749785642356498801099481 28312339231767374100824611)
                  ·
                    refine ⟨42468508847651061151236917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28312339231767374100824611 42468508847651061151236917)
                    ·
                      refine ⟨3981422704467286982928461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42468508847651061151236917 3981422704467286982928461)
                      ·
                        rfl

theorem cell23_7753793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7753793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753793 prefixEnd_7753793 := by exact prefixLift 7753793
  have htrace : WordTrace (prefixWord ++ tailWord_7753793) baseStart_7753793 baseEnd_7753793 := by
    simpa [prefixWord, tailWord_7753793, baseEnd_7753793] using wordTrace_append hprefix tailTrace_7753793
  have hstable : (prefixWord ++ tailWord_7753793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753793).length < 2 ^ (prefixWord ++ tailWord_7753793).sum := by decide
  have hdescent : baseEnd_7753793 < baseStart_7753793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753833 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 2, 5, 2]
def baseStart_7753833 : Nat := 118140960795 + 7753833 * 2 ^ 59
def prefixEnd_7753833 : Nat := 4983230072969 + 3 ^ 40 * 7753833 * 2
def baseEnd_7753833 : Nat := 3981443243693466826428277

theorem tailTrace_7753833 : CollatzResearch.WordTrace tailWord_7753833 prefixEnd_7753833 3981443243693466826428277 := by
  unfold tailWord_7753833
  simp only [CollatzResearch.WordTrace]
  refine ⟨282805522918194765092642153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188537015278796510061761435 282805522918194765092642153)
  ·
    refine ⟨212104142188646073819481615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282805522918194765092642153 212104142188646073819481615)
    ·
      refine ⟨318156213282969110729222423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212104142188646073819481615 318156213282969110729222423)
      ·
        refine ⟨477234319924453666093833635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318156213282969110729222423 477234319924453666093833635)
        ·
          refine ⟨715851479886680499140750453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477234319924453666093833635 715851479886680499140750453)
          ·
            refine ⟨67111076239376296794445355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 715851479886680499140750453 67111076239376296794445355)
            ·
              refine ⟨100666614359064445191668033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67111076239376296794445355 100666614359064445191668033)
              ·
                refine ⟨75499960769298333893751025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100666614359064445191668033 75499960769298333893751025)
                ·
                  refine ⟨56624970576973750420313269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75499960769298333893751025 56624970576973750420313269)
                  ·
                    refine ⟨5308590991591289101904369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56624970576973750420313269 5308590991591289101904369)
                    ·
                      refine ⟨3981443243693466826428277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308590991591289101904369 3981443243693466826428277)
                      ·
                        rfl

theorem cell23_7753833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 5, 2].length) (baseStart_7753833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753833 prefixEnd_7753833 := by exact prefixLift 7753833
  have htrace : WordTrace (prefixWord ++ tailWord_7753833) baseStart_7753833 baseEnd_7753833 := by
    simpa [prefixWord, tailWord_7753833, baseEnd_7753833] using wordTrace_append hprefix tailTrace_7753833
  have hstable : (prefixWord ++ tailWord_7753833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753833).length < 2 ^ (prefixWord ++ tailWord_7753833).sum := by decide
  have hdescent : baseEnd_7753833 < baseStart_7753833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753863 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_7753863 : Nat := 118140960795 + 7753863 * 2 ^ 59
def prefixEnd_7753863 : Nat := 4983230072969 + 3 ^ 40 * 7753863 * 2
def baseEnd_7753863 : Nat := 3981458648113101709053139

theorem tailTrace_7753863 : CollatzResearch.WordTrace tailWord_7753863 prefixEnd_7753863 3981458648113101709053139 := by
  unfold tailWord_7753863
  simp only [CollatzResearch.WordTrace]
  refine ⟨282806617108086080216234243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188537744738724053477489495 282806617108086080216234243)
  ·
    refine ⟨424209925662129120324351365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282806617108086080216234243 424209925662129120324351365)
    ·
      refine ⟨79539361061649210060815881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424209925662129120324351365 79539361061649210060815881)
      ·
        refine ⟨59654520796236907545611911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79539361061649210060815881 59654520796236907545611911)
        ·
          refine ⟨89481781194355361318417867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59654520796236907545611911 89481781194355361318417867)
          ·
            refine ⟨134222671791533041977626801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89481781194355361318417867 134222671791533041977626801)
            ·
              refine ⟨100667003843649781483220101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134222671791533041977626801 100667003843649781483220101)
              ·
                refine ⟨18875063220684334028103769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100667003843649781483220101 18875063220684334028103769)
                ·
                  refine ⟨14156297415513250521077827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18875063220684334028103769 14156297415513250521077827)
                  ·
                    refine ⟨21234446123269875781616741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14156297415513250521077827 21234446123269875781616741)
                    ·
                      refine ⟨3981458648113101709053139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21234446123269875781616741 3981458648113101709053139)
                      ·
                        rfl

theorem cell23_7753863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_7753863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753863 prefixEnd_7753863 := by exact prefixLift 7753863
  have htrace : WordTrace (prefixWord ++ tailWord_7753863) baseStart_7753863 baseEnd_7753863 := by
    simpa [prefixWord, tailWord_7753863, baseEnd_7753863] using wordTrace_append hprefix tailTrace_7753863
  have hstable : (prefixWord ++ tailWord_7753863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753863).length < 2 ^ (prefixWord ++ tailWord_7753863).sum := by decide
  have hdescent : baseEnd_7753863 < baseStart_7753863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753936 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_7753936 : Nat := 118140960795 + 7753936 * 2 ^ 59
def prefixEnd_7753936 : Nat := 4983230072969 + 3 ^ 40 * 7753936 * 2
def baseEnd_7753936 : Nat := 3981496132200879923440303

theorem tailTrace_7753936 : CollatzResearch.WordTrace tailWord_7753936 prefixEnd_7753936 3981496132200879923440303 := by
  unfold tailWord_7753936
  simp only [CollatzResearch.WordTrace]
  refine ⟨141404639818410806841820831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188539519757881075789094441 141404639818410806841820831)
  ·
    refine ⟨212106959727616210262731247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141404639818410806841820831 212106959727616210262731247)
    ·
      refine ⟨318160439591424315394096871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212106959727616210262731247 318160439591424315394096871)
      ·
        refine ⟨477240659387136473091145307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318160439591424315394096871 477240659387136473091145307)
        ·
          refine ⟨715860989080704709636717961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477240659387136473091145307 715860989080704709636717961)
          ·
            refine ⟨536895741810528532227538471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715860989080704709636717961 536895741810528532227538471)
            ·
              refine ⟨805343612715792798341307707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536895741810528532227538471 805343612715792798341307707)
              ·
                refine ⟨1208015419073689197511961561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805343612715792798341307707 1208015419073689197511961561)
                ·
                  refine ⟨906011564305266898133971171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1208015419073689197511961561 906011564305266898133971171)
                  ·
                    refine ⟨1359017346457900347200956757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 906011564305266898133971171 1359017346457900347200956757)
                    ·
                      refine ⟨3981496132200879923440303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1359017346457900347200956757 3981496132200879923440303)
                      ·
                        rfl

theorem cell23_7753936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_7753936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753936 prefixEnd_7753936 := by exact prefixLift 7753936
  have htrace : WordTrace (prefixWord ++ tailWord_7753936) baseStart_7753936 baseEnd_7753936 := by
    simpa [prefixWord, tailWord_7753936, baseEnd_7753936] using wordTrace_append hprefix tailTrace_7753936
  have hstable : (prefixWord ++ tailWord_7753936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753936).length < 2 ^ (prefixWord ++ tailWord_7753936).sum := by decide
  have hdescent : baseEnd_7753936 < baseStart_7753936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753957 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 2, 3, 2]
def baseStart_7753957 : Nat := 118140960795 + 7753957 * 2 ^ 59
def prefixEnd_7753957 : Nat := 4983230072969 + 3 ^ 40 * 7753957 * 2
def baseEnd_7753957 : Nat := 3981506915294624341277707

theorem tailTrace_7753957 : CollatzResearch.WordTrace tailWord_7753957 prefixEnd_7753957 3981506915294624341277707 := by
  unfold tailWord_7753957
  simp only [CollatzResearch.WordTrace]
  refine ⟨282810045569745534270156125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188540030379830356180104083 282810045569745534270156125)
  ·
    refine ⟨106053767088654575351308547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282810045569745534270156125 106053767088654575351308547)
    ·
      refine ⟨159080650632981863026962821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106053767088654575351308547 159080650632981863026962821)
      ·
        refine ⟨29827621993684099317555529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159080650632981863026962821 29827621993684099317555529)
        ·
          refine ⟨22370716495263074488166647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29827621993684099317555529 22370716495263074488166647)
          ·
            refine ⟨33556074742894611732249971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22370716495263074488166647 33556074742894611732249971)
            ·
              refine ⟨50334112114341917598374957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33556074742894611732249971 50334112114341917598374957)
              ·
                refine ⟨18875292042878219099390609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50334112114341917598374957 18875292042878219099390609)
                ·
                  refine ⟨14156469032158664324542957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18875292042878219099390609 14156469032158664324542957)
                  ·
                    refine ⟨5308675887059499121703609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14156469032158664324542957 5308675887059499121703609)
                    ·
                      refine ⟨3981506915294624341277707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308675887059499121703609 3981506915294624341277707)
                      ·
                        rfl

theorem cell23_7753957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_7753957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753957 prefixEnd_7753957 := by exact prefixLift 7753957
  have htrace : WordTrace (prefixWord ++ tailWord_7753957) baseStart_7753957 baseEnd_7753957 := by
    simpa [prefixWord, tailWord_7753957, baseEnd_7753957] using wordTrace_append hprefix tailTrace_7753957
  have hstable : (prefixWord ++ tailWord_7753957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753957).length < 2 ^ (prefixWord ++ tailWord_7753957).sum := by decide
  have hdescent : baseEnd_7753957 < baseStart_7753957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753963 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 1, 6]
def baseStart_7753963 : Nat := 118140960795 + 7753963 * 2 ^ 59
def prefixEnd_7753963 : Nat := 4983230072969 + 3 ^ 40 * 7753963 * 2
def baseEnd_7753963 : Nat := 1327169998726183772600893

theorem tailTrace_7753963 : CollatzResearch.WordTrace tailWord_7753963 prefixEnd_7753963 1327169998726183772600893 := by
  unfold tailWord_7753963
  simp only [CollatzResearch.WordTrace]
  refine ⟨282810264407723797294874543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188540176271815864863249695 282810264407723797294874543)
  ·
    refine ⟨424215396611585695942311815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282810264407723797294874543 424215396611585695942311815)
    ·
      refine ⟨636323094917378543913467723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424215396611585695942311815 636323094917378543913467723)
      ·
        refine ⟨954484642376067815870201585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636323094917378543913467723 954484642376067815870201585)
        ·
          refine ⟨715863481782050861902651189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954484642376067815870201585 715863481782050861902651189)
          ·
            refine ⟨67112201417067268303373549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 715863481782050861902651189 67112201417067268303373549)
            ·
              refine ⟨25167075531400225613765081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67112201417067268303373549 25167075531400225613765081)
              ·
                refine ⟨18875306648550169210323811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25167075531400225613765081 18875306648550169210323811)
                ·
                  refine ⟨28312959972825253815485717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18875306648550169210323811 28312959972825253815485717)
                  ·
                    refine ⟨1327169998726183772600893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28312959972825253815485717 1327169998726183772600893)
                    ·
                      rfl

theorem cell23_7753963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 6].length) (baseStart_7753963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753963 prefixEnd_7753963 := by exact prefixLift 7753963
  have htrace : WordTrace (prefixWord ++ tailWord_7753963) baseStart_7753963 baseEnd_7753963 := by
    simpa [prefixWord, tailWord_7753963, baseEnd_7753963] using wordTrace_append hprefix tailTrace_7753963
  have hstable : (prefixWord ++ tailWord_7753963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753963).length < 2 ^ (prefixWord ++ tailWord_7753963).sum := by decide
  have hdescent : baseEnd_7753963 < baseStart_7753963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753967 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 1, 5]
def baseStart_7753967 : Nat := 118140960795 + 7753967 * 2 ^ 59
def prefixEnd_7753967 : Nat := 4983230072969 + 3 ^ 40 * 7753967 * 2
def baseEnd_7753967 : Nat := 1327170683367056434050887

theorem tailTrace_7753967 : CollatzResearch.WordTrace tailWord_7753967 prefixEnd_7753967 1327170683367056434050887 := by
  unfold tailWord_7753967
  simp only [CollatzResearch.WordTrace]
  refine ⟨282810410299709305978020155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188540273533139537318680103 282810410299709305978020155)
  ·
    refine ⟨424215615449563958967030233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282810410299709305978020155 424215615449563958967030233)
    ·
      refine ⟨318161711587172969225272675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424215615449563958967030233 318161711587172969225272675)
      ·
        refine ⟨477242567380759453837909013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318161711587172969225272675 477242567380759453837909013)
        ·
          refine ⟨22370745345973099398651985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 477242567380759453837909013 22370745345973099398651985)
          ·
            refine ⟨16778059009479824548988989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22370745345973099398651985 16778059009479824548988989)
            ·
              refine ⟨6291772128554934205870871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16778059009479824548988989 6291772128554934205870871)
              ·
                refine ⟨9437658192832401308806307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291772128554934205870871 9437658192832401308806307)
                ·
                  refine ⟨14156487289248601963209461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9437658192832401308806307 14156487289248601963209461)
                  ·
                    refine ⟨1327170683367056434050887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14156487289248601963209461 1327170683367056434050887)
                    ·
                      rfl

theorem cell23_7753967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 5].length) (baseStart_7753967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753967 prefixEnd_7753967 := by exact prefixLift 7753967
  have htrace : WordTrace (prefixWord ++ tailWord_7753967) baseStart_7753967 baseEnd_7753967 := by
    simpa [prefixWord, tailWord_7753967, baseEnd_7753967] using wordTrace_append hprefix tailTrace_7753967
  have hstable : (prefixWord ++ tailWord_7753967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753967).length < 2 ^ (prefixWord ++ tailWord_7753967).sum := by decide
  have hdescent : baseEnd_7753967 < baseStart_7753967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753983 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_7753983 : Nat := 118140960795 + 7753983 * 2 ^ 59
def prefixEnd_7753983 : Nat := 4983230072969 + 3 ^ 40 * 7753983 * 2
def baseEnd_7753983 : Nat := 3981520265791641239552587

theorem tailTrace_7753983 : CollatzResearch.WordTrace tailWord_7753983 prefixEnd_7753983 3981520265791641239552587 := by
  unfold tailWord_7753983
  simp only [CollatzResearch.WordTrace]
  refine ⟨282810993867651340710602603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188540662578434227140401735 282810993867651340710602603)
  ·
    refine ⟨424216490801477011065903905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282810993867651340710602603 424216490801477011065903905)
    ·
      refine ⟨318162368101107758299427929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424216490801477011065903905 318162368101107758299427929)
      ·
        refine ⟨238621776075830818724570947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318162368101107758299427929 238621776075830818724570947)
        ·
          refine ⟨357932664113746228086856421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238621776075830818724570947 357932664113746228086856421)
          ·
            refine ⟨67112374521327417766285579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357932664113746228086856421 67112374521327417766285579)
            ·
              refine ⟨100668561781991126649428369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67112374521327417766285579 100668561781991126649428369)
              ·
                refine ⟨75501421336493344987071277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100668561781991126649428369 75501421336493344987071277)
                ·
                  refine ⟨28313033001185004370151729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75501421336493344987071277 28313033001185004370151729)
                  ·
                    refine ⟨21234774750888753277613797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28313033001185004370151729 21234774750888753277613797)
                    ·
                      refine ⟨3981520265791641239552587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21234774750888753277613797 3981520265791641239552587)
                      ·
                        rfl

theorem cell23_7753983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_7753983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753983 prefixEnd_7753983 := by exact prefixLift 7753983
  have htrace : WordTrace (prefixWord ++ tailWord_7753983) baseStart_7753983 baseEnd_7753983 := by
    simpa [prefixWord, tailWord_7753983, baseEnd_7753983] using wordTrace_append hprefix tailTrace_7753983
  have hstable : (prefixWord ++ tailWord_7753983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753983).length < 2 ^ (prefixWord ++ tailWord_7753983).sum := by decide
  have hdescent : baseEnd_7753983 < baseStart_7753983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753987 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 3, 2, 2]
def baseStart_7753987 : Nat := 118140960795 + 7753987 * 2 ^ 59
def prefixEnd_7753987 : Nat := 4983230072969 + 3 ^ 40 * 7753987 * 2
def baseEnd_7753987 : Nat := 3981522319714259223902569

theorem tailTrace_7753987 : CollatzResearch.WordTrace tailWord_7753987 prefixEnd_7753987 3981522319714259223902569 := by
  unfold tailWord_7753987
  simp only [CollatzResearch.WordTrace]
  refine ⟨282811139759636849393748215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188540759839757899595832143 282811139759636849393748215)
  ·
    refine ⟨424216709639455274090622323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282811139759636849393748215 424216709639455274090622323)
    ·
      refine ⟨636325064459182911135933485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424216709639455274090622323 636325064459182911135933485)
      ·
        refine ⟨238621899172193591675975057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636325064459182911135933485 238621899172193591675975057)
        ·
          refine ⟨178966424379145193756981293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238621899172193591675975057 178966424379145193756981293)
          ·
            refine ⟨67112409142179447658867985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178966424379145193756981293 67112409142179447658867985)
            ·
              refine ⟨50334306856634585744150989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67112409142179447658867985 50334306856634585744150989)
              ·
                refine ⟨18875365071237969654056621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50334306856634585744150989 18875365071237969654056621)
                ·
                  refine ⟨7078261901714238620271233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18875365071237969654056621 7078261901714238620271233)
                  ·
                    refine ⟨5308696426285678965203425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7078261901714238620271233 5308696426285678965203425)
                    ·
                      refine ⟨3981522319714259223902569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308696426285678965203425 3981522319714259223902569)
                      ·
                        rfl

theorem cell23_7753987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_7753987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753987 prefixEnd_7753987 := by exact prefixLift 7753987
  have htrace : WordTrace (prefixWord ++ tailWord_7753987) baseStart_7753987 baseEnd_7753987 := by
    simpa [prefixWord, tailWord_7753987, baseEnd_7753987] using wordTrace_append hprefix tailTrace_7753987
  have hstable : (prefixWord ++ tailWord_7753987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753987).length < 2 ^ (prefixWord ++ tailWord_7753987).sum := by decide
  have hdescent : baseEnd_7753987 < baseStart_7753987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7753993 : List Nat := [1, 2, 1, 1, 3, 4, 3, 8]
def baseStart_7753993 : Nat := 118140960795 + 7753993 * 2 ^ 59
def prefixEnd_7753993 : Nat := 4983230072969 + 3 ^ 40 * 7753993 * 2
def baseEnd_7753993 : Nat := 147463903725858748163983

theorem tailTrace_7753993 : CollatzResearch.WordTrace tailWord_7753993 prefixEnd_7753993 147463903725858748163983 := by
  unfold tailWord_7753993
  simp only [CollatzResearch.WordTrace]
  refine ⟨282811358597615112418466633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188540905731743408278977755 282811358597615112418466633)
  ·
    refine ⟨212108518948211334313849975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282811358597615112418466633 212108518948211334313849975)
    ·
      refine ⟨318162778422317001470774963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212108518948211334313849975 318162778422317001470774963)
      ·
        refine ⟨477244167633475502206162445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318162778422317001470774963 477244167633475502206162445)
        ·
          refine ⟨178966562862553313327310917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477244167633475502206162445 178966562862553313327310917)
          ·
            refine ⟨33556230536728746248870797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178966562862553313327310917 33556230536728746248870797)
            ·
              refine ⟨12583586451273279843326549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33556230536728746248870797 12583586451273279843326549)
              ·
                refine ⟨147463903725858748163983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12583586451273279843326549 147463903725858748163983)
                ·
                  rfl

theorem cell23_7753993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 8].length) (baseStart_7753993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7753993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7753993 prefixEnd_7753993 := by exact prefixLift 7753993
  have htrace : WordTrace (prefixWord ++ tailWord_7753993) baseStart_7753993 baseEnd_7753993 := by
    simpa [prefixWord, tailWord_7753993, baseEnd_7753993] using wordTrace_append hprefix tailTrace_7753993
  have hstable : (prefixWord ++ tailWord_7753993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7753993).length < 2 ^ (prefixWord ++ tailWord_7753993).sum := by decide
  have hdescent : baseEnd_7753993 < baseStart_7753993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7753993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754021 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 1, 1, 4]
def baseStart_7754021 : Nat := 118140960795 + 7754021 * 2 ^ 59
def prefixEnd_7754021 : Nat := 4983230072969 + 3 ^ 40 * 7754021 * 2
def baseEnd_7754021 : Nat := 3981539778056512090877413

theorem tailTrace_7754021 : CollatzResearch.WordTrace tailWord_7754021 prefixEnd_7754021 3981539778056512090877413 := by
  unfold tailWord_7754021
  simp only [CollatzResearch.WordTrace]
  refine ⟨282812379841513673200485917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188541586561009115466990611 282812379841513673200485917)
  ·
    refine ⟨106054642440567627450182219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282812379841513673200485917 106054642440567627450182219)
    ·
      refine ⟨159081963660851441175273329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106054642440567627450182219 159081963660851441175273329)
      ·
        refine ⟨119311472745638580881454997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159081963660851441175273329 119311472745638580881454997)
        ·
          refine ⟨5592725284951808478818203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119311472745638580881454997 5592725284951808478818203)
          ·
            refine ⟨8389087927427712718227305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592725284951808478818203 8389087927427712718227305)
            ·
              refine ⟨6291815945570784538670479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8389087927427712718227305 6291815945570784538670479)
              ·
                refine ⟨9437723918356176808005719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291815945570784538670479 9437723918356176808005719)
                ·
                  refine ⟨14156585877534265212008579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9437723918356176808005719 14156585877534265212008579)
                  ·
                    refine ⟨21234878816301397818012869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14156585877534265212008579 21234878816301397818012869)
                    ·
                      refine ⟨3981539778056512090877413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21234878816301397818012869 3981539778056512090877413)
                      ·
                        rfl

theorem cell23_7754021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_7754021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754021 prefixEnd_7754021 := by exact prefixLift 7754021
  have htrace : WordTrace (prefixWord ++ tailWord_7754021) baseStart_7754021 baseEnd_7754021 := by
    simpa [prefixWord, tailWord_7754021, baseEnd_7754021] using wordTrace_append hprefix tailTrace_7754021
  have hstable : (prefixWord ++ tailWord_7754021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754021).length < 2 ^ (prefixWord ++ tailWord_7754021).sum := by decide
  have hdescent : baseEnd_7754021 < baseStart_7754021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754024 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7754024 : Nat := 118140960795 + 7754024 * 2 ^ 59
def prefixEnd_7754024 : Nat := 4983230072969 + 3 ^ 40 * 7754024 * 2
def baseEnd_7754024 : Nat := 3981541318498475579139899

theorem tailTrace_7754024 : CollatzResearch.WordTrace tailWord_7754024 prefixEnd_7754024 3981541318498475579139899 := by
  unfold tailWord_7754024
  simp only [CollatzResearch.WordTrace]
  refine ⟨141406244630251402356422563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188541659507001869808563417 141406244630251402356422563)
  ·
    refine ⟨212109366945377103534633845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141406244630251402356422563 212109366945377103534633845)
    ·
      refine ⟨19885253151129103456371923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212109366945377103534633845 19885253151129103456371923)
      ·
        refine ⟨29827879726693655184557885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19885253151129103456371923 29827879726693655184557885)
        ·
          refine ⟨11185454897510120694209207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29827879726693655184557885 11185454897510120694209207)
          ·
            refine ⟨16778182346265181041313811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185454897510120694209207 16778182346265181041313811)
            ·
              refine ⟨25167273519397771561970717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16778182346265181041313811 25167273519397771561970717)
              ·
                refine ⟨9437727569774164335739019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25167273519397771561970717 9437727569774164335739019)
                ·
                  refine ⟨14156591354661246503608529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9437727569774164335739019 14156591354661246503608529)
                  ·
                    refine ⟨10617443515995934877706397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14156591354661246503608529 10617443515995934877706397)
                    ·
                      refine ⟨3981541318498475579139899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10617443515995934877706397 3981541318498475579139899)
                      ·
                        rfl

theorem cell23_7754024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7754024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754024 prefixEnd_7754024 := by exact prefixLift 7754024
  have htrace : WordTrace (prefixWord ++ tailWord_7754024) baseStart_7754024 baseEnd_7754024 := by
    simpa [prefixWord, tailWord_7754024, baseEnd_7754024] using wordTrace_append hprefix tailTrace_7754024
  have hstable : (prefixWord ++ tailWord_7754024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754024).length < 2 ^ (prefixWord ++ tailWord_7754024).sum := by decide
  have hdescent : baseEnd_7754024 < baseStart_7754024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754037 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_7754037 : Nat := 118140960795 + 7754037 * 2 ^ 59
def prefixEnd_7754037 : Nat := 4983230072969 + 3 ^ 40 * 7754037 * 2
def baseEnd_7754037 : Nat := 3981547993746984028277339

theorem tailTrace_7754037 : CollatzResearch.WordTrace tailWord_7754037 prefixEnd_7754037 3981547993746984028277339 := by
  unfold tailWord_7754037
  simp only [CollatzResearch.WordTrace]
  refine ⟨282812963409455707933068365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188541975606303805288712243 282812963409455707933068365)
  ·
    refine ⟨106054861278545890474900637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282812963409455707933068365 106054861278545890474900637)
    ·
      refine ⟨39770572979454708928087739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106054861278545890474900637 39770572979454708928087739)
      ·
        refine ⟨59655859469182063392131609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39770572979454708928087739 59655859469182063392131609)
        ·
          refine ⟨44741894601886547544098707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59655859469182063392131609 44741894601886547544098707)
          ·
            refine ⟨67112841902829821316148061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44741894601886547544098707 67112841902829821316148061)
            ·
              refine ⟨25167315713561182993555523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67112841902829821316148061 25167315713561182993555523)
              ·
                refine ⟨37750973570341774490333285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25167315713561182993555523 37750973570341774490333285)
                ·
                  refine ⟨7078307544439082716937491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37750973570341774490333285 7078307544439082716937491)
                  ·
                    refine ⟨10617461316658624075406237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7078307544439082716937491 10617461316658624075406237)
                    ·
                      refine ⟨3981547993746984028277339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10617461316658624075406237 3981547993746984028277339)
                      ·
                        rfl

theorem cell23_7754037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_7754037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754037 prefixEnd_7754037 := by exact prefixLift 7754037
  have htrace : WordTrace (prefixWord ++ tailWord_7754037) baseStart_7754037 baseEnd_7754037 := by
    simpa [prefixWord, tailWord_7754037, baseEnd_7754037] using wordTrace_append hprefix tailTrace_7754037
  have hstable : (prefixWord ++ tailWord_7754037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754037).length < 2 ^ (prefixWord ++ tailWord_7754037).sum := by decide
  have hdescent : baseEnd_7754037 < baseStart_7754037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754064 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 1, 3, 2]
def baseStart_7754064 : Nat := 118140960795 + 7754064 * 2 ^ 59
def prefixEnd_7754064 : Nat := 4983230072969 + 3 ^ 40 * 7754064 * 2
def baseEnd_7754064 : Nat := 3981561857724655422639715

theorem tailTrace_7754064 : CollatzResearch.WordTrace tailWord_7754064 prefixEnd_7754064 3981561857724655422639715 := by
  unfold tailWord_7754064
  simp only [CollatzResearch.WordTrace]
  refine ⟨141406974090178945772150623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188542632120238594362867497 141406974090178945772150623)
  ·
    refine ⟨212110461135268418658225935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141406974090178945772150623 212110461135268418658225935)
    ·
      refine ⟨318165691702902627987338903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212110461135268418658225935 318165691702902627987338903)
      ·
        refine ⟨477248537554353941981008355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318165691702902627987338903 477248537554353941981008355)
        ·
          refine ⟨715872806331530912971512533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477248537554353941981008355 715872806331530912971512533)
          ·
            refine ⟨16778268898395255772769825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 715872806331530912971512533 16778268898395255772769825)
            ·
              refine ⟨12583701673796441829577369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16778268898395255772769825 12583701673796441829577369)
              ·
                refine ⟨9437776255347331372183027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12583701673796441829577369 9437776255347331372183027)
                ·
                  refine ⟨14156664383020997058274541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9437776255347331372183027 14156664383020997058274541)
                  ·
                    refine ⟨5308749143632873896852953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14156664383020997058274541 5308749143632873896852953)
                    ·
                      refine ⟨3981561857724655422639715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308749143632873896852953 3981561857724655422639715)
                      ·
                        rfl

theorem cell23_7754064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 3, 2].length) (baseStart_7754064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754064 prefixEnd_7754064 := by exact prefixLift 7754064
  have htrace : WordTrace (prefixWord ++ tailWord_7754064) baseStart_7754064 baseEnd_7754064 := by
    simpa [prefixWord, tailWord_7754064, baseEnd_7754064] using wordTrace_append hprefix tailTrace_7754064
  have hstable : (prefixWord ++ tailWord_7754064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754064).length < 2 ^ (prefixWord ++ tailWord_7754064).sum := by decide
  have hdescent : baseEnd_7754064 < baseStart_7754064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754078 : List Nat := [4, 4, 2, 1, 2, 1, 9]
def baseStart_7754078 : Nat := 118140960795 + 7754078 * 2 ^ 59
def prefixEnd_7754078 : Nat := 4983230072969 + 3 ^ 40 * 7754078 * 2
def baseEnd_7754078 : Nat := 49155173413010103306971

theorem tailTrace_7754078 : CollatzResearch.WordTrace tailWord_7754078 prefixEnd_7754078 49155173413010103306971 := by
  unfold tailWord_7754078
  simp only [CollatzResearch.WordTrace]
  refine ⟨35351807350288396491913861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188542972534871447956873925 35351807350288396491913861)
  ·
    refine ⟨6628463878179074342233849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35351807350288396491913861 6628463878179074342233849)
    ·
      refine ⟨4971347908634305756675387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6628463878179074342233849 4971347908634305756675387)
      ·
        refine ⟨7457021862951458635013081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4971347908634305756675387 7457021862951458635013081)
        ·
          refine ⟨5592766397213593976259811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7457021862951458635013081 5592766397213593976259811)
          ·
            refine ⟨8389149595820390964389717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592766397213593976259811 8389149595820390964389717)
            ·
              refine ⟨49155173413010103306971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8389149595820390964389717 49155173413010103306971)
              ·
                rfl

theorem cell23_7754078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 9].length) (baseStart_7754078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754078 prefixEnd_7754078 := by exact prefixLift 7754078
  have htrace : WordTrace (prefixWord ++ tailWord_7754078) baseStart_7754078 baseEnd_7754078 := by
    simpa [prefixWord, tailWord_7754078, baseEnd_7754078] using wordTrace_append hprefix tailTrace_7754078
  have hstable : (prefixWord ++ tailWord_7754078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754078).length < 2 ^ (prefixWord ++ tailWord_7754078).sum := by decide
  have hdescent : baseEnd_7754078 < baseStart_7754078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754103 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_7754103 : Nat := 118140960795 + 7754103 * 2 ^ 59
def prefixEnd_7754103 : Nat := 4983230072969 + 3 ^ 40 * 7754103 * 2
def baseEnd_7754103 : Nat := 3981581883470180770052035

theorem tailTrace_7754103 : CollatzResearch.WordTrace tailWord_7754103 prefixEnd_7754103 3981581883470180770052035 := by
  unfold tailWord_7754103
  simp only [CollatzResearch.WordTrace]
  refine ⟨282815370627216601204970963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188543580418144400803313975 282815370627216601204970963)
  ·
    refine ⟨424223055940824901807456445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282815370627216601204970963 424223055940824901807456445)
    ·
      refine ⟨159083645977809338177796167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424223055940824901807456445 159083645977809338177796167)
      ·
        refine ⟨238625468966714007266694251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159083645977809338177796167 238625468966714007266694251)
        ·
          refine ⟨357938203450071010900041377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238625468966714007266694251 357938203450071010900041377)
          ·
            refine ⟨268453652587553258175031033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357938203450071010900041377 268453652587553258175031033)
            ·
              refine ⟨201340239440664943631273275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268453652587553258175031033 201340239440664943631273275)
              ·
                refine ⟨302010359160997415446909913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201340239440664943631273275 302010359160997415446909913)
                ·
                  refine ⟨226507769370748061585182435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302010359160997415446909913 226507769370748061585182435)
                  ·
                    refine ⟨339761654056122092377773653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226507769370748061585182435 339761654056122092377773653)
                    ·
                      refine ⟨3981581883470180770052035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 339761654056122092377773653 3981581883470180770052035)
                      ·
                        rfl

theorem cell23_7754103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_7754103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754103 prefixEnd_7754103 := by exact prefixLift 7754103
  have htrace : WordTrace (prefixWord ++ tailWord_7754103) baseStart_7754103 baseEnd_7754103 := by
    simpa [prefixWord, tailWord_7754103, baseEnd_7754103] using wordTrace_append hprefix tailTrace_7754103
  have hstable : (prefixWord ++ tailWord_7754103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754103).length < 2 ^ (prefixWord ++ tailWord_7754103).sum := by decide
  have hdescent : baseEnd_7754103 < baseStart_7754103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754151 : List Nat := [1, 1, 6, 1, 1, 4, 2, 2, 5]
def baseStart_7754151 : Nat := 118140960795 + 7754151 * 2 ^ 59
def prefixEnd_7754151 : Nat := 4983230072969 + 3 ^ 40 * 7754151 * 2
def baseEnd_7754151 : Nat := 442400725615732953583535

theorem tailTrace_7754151 : CollatzResearch.WordTrace tailWord_7754151 prefixEnd_7754151 442400725615732953583535 := by
  unfold tailWord_7754151
  simp only [CollatzResearch.WordTrace]
  refine ⟨282817121331042705402718307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188544747554028470268478871 282817121331042705402718307)
  ·
    refine ⟨424225681996564058104077461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282817121331042705402718307 424225681996564058104077461)
    ·
      refine ⟨19885578843588940223628631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 424225681996564058104077461 19885578843588940223628631)
      ·
        refine ⟨29828368265383410335442947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19885578843588940223628631 29828368265383410335442947)
        ·
          refine ⟨44742552398075115503164421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29828368265383410335442947 44742552398075115503164421)
          ·
            refine ⟨8389228574639084156843329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44742552398075115503164421 8389228574639084156843329)
            ·
              refine ⟨6291921430979313117632497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8389228574639084156843329 6291921430979313117632497)
              ·
                refine ⟨4718941073234484838224373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6291921430979313117632497 4718941073234484838224373)
                ·
                  refine ⟨442400725615732953583535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4718941073234484838224373 442400725615732953583535)
                  ·
                    rfl

theorem cell23_7754151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 5].length) (baseStart_7754151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754151 prefixEnd_7754151 := by exact prefixLift 7754151
  have htrace : WordTrace (prefixWord ++ tailWord_7754151) baseStart_7754151 baseEnd_7754151 := by
    simpa [prefixWord, tailWord_7754151, baseEnd_7754151] using wordTrace_append hprefix tailTrace_7754151
  have hstable : (prefixWord ++ tailWord_7754151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754151).length < 2 ^ (prefixWord ++ tailWord_7754151).sum := by decide
  have hdescent : baseEnd_7754151 < baseStart_7754151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754167 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 1, 6, 2]
def baseStart_7754167 : Nat := 118140960795 + 7754167 * 2 ^ 59
def prefixEnd_7754167 : Nat := 4983230072969 + 3 ^ 40 * 7754167 * 2
def baseEnd_7754167 : Nat := 3981614746232068519651741

theorem tailTrace_7754167 : CollatzResearch.WordTrace tailWord_7754167 prefixEnd_7754167 3981614746232068519651741 := by
  unfold tailWord_7754167
  simp only [CollatzResearch.WordTrace]
  refine ⟨282817704898984740135300755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188545136599323160090200503 282817704898984740135300755)
  ·
    refine ⟨424226557348477110202951133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282817704898984740135300755 424226557348477110202951133)
    ·
      refine ⟨159084959005678916326106675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424226557348477110202951133 159084959005678916326106675)
      ·
        refine ⟨238627438508518374489160013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159084959005678916326106675 238627438508518374489160013)
        ·
          refine ⟨89485289440694390433435005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238627438508518374489160013 89485289440694390433435005)
          ·
            refine ⟨33556983540260396412538127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89485289440694390433435005 33556983540260396412538127)
            ·
              refine ⟨50335475310390594618807191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33556983540260396412538127 50335475310390594618807191)
              ·
                refine ⟨75503212965585891928210787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50335475310390594618807191 75503212965585891928210787)
                ·
                  refine ⟨113254819448378837892316181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75503212965585891928210787 113254819448378837892316181)
                  ·
                    refine ⟨5308819661642758026202321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113254819448378837892316181 5308819661642758026202321)
                    ·
                      refine ⟨3981614746232068519651741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308819661642758026202321 3981614746232068519651741)
                      ·
                        rfl

theorem cell23_7754167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_7754167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754167 prefixEnd_7754167 := by exact prefixLift 7754167
  have htrace : WordTrace (prefixWord ++ tailWord_7754167) baseStart_7754167 baseEnd_7754167 := by
    simpa [prefixWord, tailWord_7754167, baseEnd_7754167] using wordTrace_append hprefix tailTrace_7754167
  have hstable : (prefixWord ++ tailWord_7754167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754167).length < 2 ^ (prefixWord ++ tailWord_7754167).sum := by decide
  have hdescent : baseEnd_7754167 < baseStart_7754167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754184 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_7754184 : Nat := 118140960795 + 7754184 * 2 ^ 59
def prefixEnd_7754184 : Nat := 4983230072969 + 3 ^ 40 * 7754184 * 2
def baseEnd_7754184 : Nat := 3981623475403194953139163

theorem tailTrace_7754184 : CollatzResearch.WordTrace tailWord_7754184 prefixEnd_7754184 3981623475403194953139163 := by
  unfold tailWord_7754184
  simp only [CollatzResearch.WordTrace]
  refine ⟨141409162469961576019334803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188545549959948768025779737 141409162469961576019334803)
  ·
    refine ⟨212113743704942364029002205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141409162469961576019334803 212113743704942364029002205)
    ·
      refine ⟨79542653889353386510875827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212113743704942364029002205 79542653889353386510875827)
      ·
        refine ⟨119313980834030079766313741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79542653889353386510875827 119313980834030079766313741)
        ·
          refine ⟨44742742812761279912367653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119313980834030079766313741 44742742812761279912367653)
          ·
            refine ⟨8389264277392739983568935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44742742812761279912367653 8389264277392739983568935)
            ·
              refine ⟨12583896416089109975353403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389264277392739983568935 12583896416089109975353403)
              ·
                refine ⟨18875844624133664963030105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12583896416089109975353403 18875844624133664963030105)
                ·
                  refine ⟨14156883468100248722272579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18875844624133664963030105 14156883468100248722272579)
                  ·
                    refine ⟨21235325202150373083408869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14156883468100248722272579 21235325202150373083408869)
                    ·
                      refine ⟨3981623475403194953139163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21235325202150373083408869 3981623475403194953139163)
                      ·
                        rfl

theorem cell23_7754184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_7754184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754184 prefixEnd_7754184 := by exact prefixLift 7754184
  have htrace : WordTrace (prefixWord ++ tailWord_7754184) baseStart_7754184 baseEnd_7754184 := by
    simpa [prefixWord, tailWord_7754184, baseEnd_7754184] using wordTrace_append hprefix tailTrace_7754184
  have hstable : (prefixWord ++ tailWord_7754184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754184).length < 2 ^ (prefixWord ++ tailWord_7754184).sum := by decide
  have hdescent : baseEnd_7754184 < baseStart_7754184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754190 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_7754190 : Nat := 118140960795 + 7754190 * 2 ^ 59
def prefixEnd_7754190 : Nat := 4983230072969 + 3 ^ 40 * 7754190 * 2
def baseEnd_7754190 : Nat := 442402950698569103296015

theorem tailTrace_7754190 : CollatzResearch.WordTrace tailWord_7754190 prefixEnd_7754190 442402950698569103296015 := by
  unfold tailWord_7754190
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352317972237676882923503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188545695851934276708925349 35352317972237676882923503)
  ·
    refine ⟨53028476958356515324385255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352317972237676882923503 53028476958356515324385255)
    ·
      refine ⟨79542715437534772986577883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53028476958356515324385255 79542715437534772986577883)
      ·
        refine ⟨119314073156302159479866825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79542715437534772986577883 119314073156302159479866825)
        ·
          refine ⟨89485554867226619609900119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119314073156302159479866825 89485554867226619609900119)
          ·
            refine ⟨134228332300839929414850179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89485554867226619609900119 134228332300839929414850179)
            ·
              refine ⟨201342498451259894122275269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134228332300839929414850179 201342498451259894122275269)
              ·
                refine ⟨37751718459611230147926613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201342498451259894122275269 37751718459611230147926613)
                ·
                  refine ⟨442402950698569103296015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37751718459611230147926613 442402950698569103296015)
                  ·
                    rfl

theorem cell23_7754190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_7754190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754190 prefixEnd_7754190 := by exact prefixLift 7754190
  have htrace : WordTrace (prefixWord ++ tailWord_7754190) baseStart_7754190 baseEnd_7754190 := by
    simpa [prefixWord, tailWord_7754190, baseEnd_7754190] using wordTrace_append hprefix tailTrace_7754190
  have hstable : (prefixWord ++ tailWord_7754190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754190).length < 2 ^ (prefixWord ++ tailWord_7754190).sum := by decide
  have hdescent : baseEnd_7754190 < baseStart_7754190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754207 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 6]
def baseStart_7754207 : Nat := 118140960795 + 7754207 * 2 ^ 59
def prefixEnd_7754207 : Nat := 4983230072969 + 3 ^ 40 * 7754207 * 2
def baseEnd_7754207 : Nat := 442403920606472040350173

theorem tailTrace_7754207 : CollatzResearch.WordTrace tailWord_7754207 prefixEnd_7754207 442403920606472040350173 := by
  unfold tailWord_7754207
  simp only [CollatzResearch.WordTrace]
  refine ⟨282819163818839826966756875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188546109212559884644504583 282819163818839826966756875)
  ·
    refine ⟨424228745728259740450135313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282819163818839826966756875 424228745728259740450135313)
    ·
      refine ⟨318171559296194805337601485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424228745728259740450135313 318171559296194805337601485)
      ·
        refine ⟨119314334736073052001600557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318171559296194805337601485 119314334736073052001600557)
        ·
          refine ⟨44742875526027394500600209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119314334736073052001600557 44742875526027394500600209)
          ·
            refine ⟨33557156644520545875450157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44742875526027394500600209 33557156644520545875450157)
            ·
              refine ⟨12583933741695204703293809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33557156644520545875450157 12583933741695204703293809)
              ·
                refine ⟨9437950306271403527470357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12583933741695204703293809 9437950306271403527470357)
                ·
                  refine ⟨442403920606472040350173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9437950306271403527470357 442403920606472040350173)
                  ·
                    rfl

theorem cell23_7754207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 6].length) (baseStart_7754207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754207 prefixEnd_7754207 := by exact prefixLift 7754207
  have htrace : WordTrace (prefixWord ++ tailWord_7754207) baseStart_7754207 baseEnd_7754207 := by
    simpa [prefixWord, tailWord_7754207, baseEnd_7754207] using wordTrace_append hprefix tailTrace_7754207
  have hstable : (prefixWord ++ tailWord_7754207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754207).length < 2 ^ (prefixWord ++ tailWord_7754207).sum := by decide
  have hdescent : baseEnd_7754207 < baseStart_7754207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754227 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 3, 5, 2]
def baseStart_7754227 : Nat := 118140960795 + 7754227 * 2 ^ 59
def prefixEnd_7754227 : Nat := 4983230072969 + 3 ^ 40 * 7754227 * 2
def baseEnd_7754227 : Nat := 3981645555071338284901465

theorem tailTrace_7754227 : CollatzResearch.WordTrace tailWord_7754227 prefixEnd_7754227 3981645555071338284901465 := by
  unfold tailWord_7754227
  simp only [CollatzResearch.WordTrace]
  refine ⟨282819893278767370382484935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188546595519178246921656623 282819893278767370382484935)
  ·
    refine ⟨424229839918151055573727403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282819893278767370382484935 424229839918151055573727403)
    ·
      refine ⟨636344759877226583360591105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424229839918151055573727403 636344759877226583360591105)
      ·
        refine ⟨477258569907919937520443329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636344759877226583360591105 477258569907919937520443329)
        ·
          refine ⟨357943927430939953140332497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477258569907919937520443329 357943927430939953140332497)
          ·
            refine ⟨268457945573204964855249373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357943927430939953140332497 268457945573204964855249373)
            ·
              refine ⟨100671729589951861820718515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268457945573204964855249373 100671729589951861820718515)
              ·
                refine ⟨151007594384927792731077773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100671729589951861820718515 151007594384927792731077773)
                ·
                  refine ⟨56627847894347922274154165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151007594384927792731077773 56627847894347922274154165)
                  ·
                    refine ⟨5308860740095117713201953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56627847894347922274154165 5308860740095117713201953)
                    ·
                      refine ⟨3981645555071338284901465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308860740095117713201953 3981645555071338284901465)
                      ·
                        rfl

theorem cell23_7754227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 5, 2].length) (baseStart_7754227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754227 prefixEnd_7754227 := by exact prefixLift 7754227
  have htrace : WordTrace (prefixWord ++ tailWord_7754227) baseStart_7754227 baseEnd_7754227 := by
    simpa [prefixWord, tailWord_7754227, baseEnd_7754227] using wordTrace_append hprefix tailTrace_7754227
  have hstable : (prefixWord ++ tailWord_7754227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754227).length < 2 ^ (prefixWord ++ tailWord_7754227).sum := by decide
  have hdescent : baseEnd_7754227 < baseStart_7754227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754240 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4]
def baseStart_7754240 : Nat := 118140960795 + 7754240 * 2 ^ 59
def prefixEnd_7754240 : Nat := 4983230072969 + 3 ^ 40 * 7754240 * 2
def baseEnd_7754240 : Nat := 3981652230319846734038905

theorem tailTrace_7754240 : CollatzResearch.WordTrace tailWord_7754240 prefixEnd_7754240 3981652230319846734038905 := by
  unfold tailWord_7754240
  simp only [CollatzResearch.WordTrace]
  refine ⟨141410183713860136801354087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188546911618480182401805449 141410183713860136801354087)
  ·
    refine ⟨212115275570790205202031131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141410183713860136801354087 212115275570790205202031131)
    ·
      refine ⟨318172913356185307803046697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212115275570790205202031131 318172913356185307803046697)
      ·
        refine ⟨238629685017138980852285023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318172913356185307803046697 238629685017138980852285023)
        ·
          refine ⟨357944527525708471278427535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238629685017138980852285023 357944527525708471278427535)
          ·
            refine ⟨536916791288562706917641303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357944527525708471278427535 536916791288562706917641303)
            ·
              refine ⟨805375186932844060376461955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536916791288562706917641303 805375186932844060376461955)
              ·
                refine ⟨1208062780399266090564692933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805375186932844060376461955 1208062780399266090564692933)
                ·
                  refine ⟨226511771324862391980879925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208062780399266090564692933 226511771324862391980879925)
                  ·
                    refine ⟨21235478561705849248207493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226511771324862391980879925 21235478561705849248207493)
                    ·
                      refine ⟨3981652230319846734038905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21235478561705849248207493 3981652230319846734038905)
                      ·
                        rfl

theorem cell23_7754240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_7754240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754240 prefixEnd_7754240 := by exact prefixLift 7754240
  have htrace : WordTrace (prefixWord ++ tailWord_7754240) baseStart_7754240 baseEnd_7754240 := by
    simpa [prefixWord, tailWord_7754240, baseEnd_7754240] using wordTrace_append hprefix tailTrace_7754240
  have hstable : (prefixWord ++ tailWord_7754240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754240).length < 2 ^ (prefixWord ++ tailWord_7754240).sum := by decide
  have hdescent : baseEnd_7754240 < baseStart_7754240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754254 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_7754254 : Nat := 118140960795 + 7754254 * 2 ^ 59
def prefixEnd_7754254 : Nat := 4983230072969 + 3 ^ 40 * 7754254 * 2
def baseEnd_7754254 : Nat := 1327219806349669893087947

theorem tailTrace_7754254 : CollatzResearch.WordTrace tailWord_7754254 prefixEnd_7754254 1327219806349669893087947 := by
  unfold tailWord_7754254
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352609756208694249214727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188547252033113035995811877 35352609756208694249214727)
  ·
    refine ⟨53028914634313041373822091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352609756208694249214727 53028914634313041373822091)
    ·
      refine ⟨79543371951469562060733137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53028914634313041373822091 79543371951469562060733137)
      ·
        refine ⟨59657528963602171545549853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79543371951469562060733137 59657528963602171545549853)
        ·
          refine ⟨22371573361350814329581195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59657528963602171545549853 22371573361350814329581195)
          ·
            refine ⟨33557360042026221494371793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22371573361350814329581195 33557360042026221494371793)
            ·
              refine ⟨25168020031519666120778845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33557360042026221494371793 25168020031519666120778845)
              ·
                refine ⟨9438007511819874795292067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25168020031519666120778845 9438007511819874795292067)
                ·
                  refine ⟨14157011267729812192938101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438007511819874795292067 14157011267729812192938101)
                  ·
                    refine ⟨1327219806349669893087947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14157011267729812192938101 1327219806349669893087947)
                    ·
                      rfl

theorem cell23_7754254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_7754254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754254 prefixEnd_7754254 := by exact prefixLift 7754254
  have htrace : WordTrace (prefixWord ++ tailWord_7754254) baseStart_7754254 baseEnd_7754254 := by
    simpa [prefixWord, tailWord_7754254, baseEnd_7754254] using wordTrace_append hprefix tailTrace_7754254
  have hstable : (prefixWord ++ tailWord_7754254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754254).length < 2 ^ (prefixWord ++ tailWord_7754254).sum := by decide
  have hdescent : baseEnd_7754254 < baseStart_7754254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754277 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_7754277 : Nat := 118140960795 + 7754277 * 2 ^ 59
def prefixEnd_7754277 : Nat := 4983230072969 + 3 ^ 40 * 7754277 * 2
def baseEnd_7754277 : Nat := 3981671229104063089276235

theorem tailTrace_7754277 : CollatzResearch.WordTrace tailWord_7754277 prefixEnd_7754277 3981671229104063089276235 := by
  unfold tailWord_7754277
  simp only [CollatzResearch.WordTrace]
  refine ⟨282821716928586228921805085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188547811285724152614536723 282821716928586228921805085)
  ·
    refine ⟨106058143848219835845676907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282821716928586228921805085 106058143848219835845676907)
    ·
      refine ⟨159087215772329753768515361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106058143848219835845676907 159087215772329753768515361)
      ·
        refine ⟨119315411829247315326386521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159087215772329753768515361 119315411829247315326386521)
        ·
          refine ⟨89486558871935486494789891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119315411829247315326386521 89486558871935486494789891)
          ·
            refine ⟨134229838307903229742184837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89486558871935486494789891 134229838307903229742184837)
            ·
              refine ⟨25168094682731855576659657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134229838307903229742184837 25168094682731855576659657)
              ·
                refine ⟨18876071012048891682494743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25168094682731855576659657 18876071012048891682494743)
                ·
                  refine ⟨28314106518073337523742115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18876071012048891682494743 28314106518073337523742115)
                  ·
                    refine ⟨42471159777110006285613173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28314106518073337523742115 42471159777110006285613173)
                    ·
                      refine ⟨3981671229104063089276235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42471159777110006285613173 3981671229104063089276235)
                      ·
                        rfl

theorem cell23_7754277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_7754277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754277 prefixEnd_7754277 := by exact prefixLift 7754277
  have htrace : WordTrace (prefixWord ++ tailWord_7754277) baseStart_7754277 baseEnd_7754277 := by
    simpa [prefixWord, tailWord_7754277, baseEnd_7754277] using wordTrace_append hprefix tailTrace_7754277
  have hstable : (prefixWord ++ tailWord_7754277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754277).length < 2 ^ (prefixWord ++ tailWord_7754277).sum := by decide
  have hdescent : baseEnd_7754277 < baseStart_7754277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754325 : List Nat := [1, 3, 2, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_7754325 : Nat := 118140960795 + 7754325 * 2 ^ 59
def prefixEnd_7754325 : Nat := 4983230072969 + 3 ^ 40 * 7754325 * 2
def baseEnd_7754325 : Nat := 3981695876175478901476015

theorem tailTrace_7754325 : CollatzResearch.WordTrace tailWord_7754325 prefixEnd_7754325 3981695876175478901476015 := by
  unfold tailWord_7754325
  simp only [CollatzResearch.WordTrace]
  refine ⟨282823467632412333119552429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188548978421608222079701619 282823467632412333119552429)
  ·
    refine ⟨106058800362154624919832161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282823467632412333119552429 106058800362154624919832161)
    ·
      refine ⟨79544100271615968689874121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106058800362154624919832161 79544100271615968689874121)
      ·
        refine ⟨59658075203711976517405591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79544100271615968689874121 59658075203711976517405591)
        ·
          refine ⟨89487112805567964776108387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59658075203711976517405591 89487112805567964776108387)
          ·
            refine ⟨134230669208351947164162581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89487112805567964776108387 134230669208351947164162581)
            ·
              refine ⟨6292062619141497523320121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134230669208351947164162581 6292062619141497523320121)
              ·
                refine ⟨4719046964356123142490091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6292062619141497523320121 4719046964356123142490091)
                ·
                  refine ⟨7078570446534184713735137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719046964356123142490091 7078570446534184713735137)
                  ·
                    refine ⟨5308927834900638535301353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7078570446534184713735137 5308927834900638535301353)
                    ·
                      refine ⟨3981695876175478901476015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308927834900638535301353 3981695876175478901476015)
                      ·
                        rfl

theorem cell23_7754325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_7754325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754325 prefixEnd_7754325 := by exact prefixLift 7754325
  have htrace : WordTrace (prefixWord ++ tailWord_7754325) baseStart_7754325 baseEnd_7754325 := by
    simpa [prefixWord, tailWord_7754325, baseEnd_7754325] using wordTrace_append hprefix tailTrace_7754325
  have hstable : (prefixWord ++ tailWord_7754325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754325).length < 2 ^ (prefixWord ++ tailWord_7754325).sum := by decide
  have hdescent : baseEnd_7754325 < baseStart_7754325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754338 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7754338 : Nat := 118140960795 + 7754338 * 2 ^ 59
def prefixEnd_7754338 : Nat := 4983230072969 + 3 ^ 40 * 7754338 * 2
def baseEnd_7754338 : Nat := 3981702551423987350613455

theorem tailTrace_7754338 : CollatzResearch.WordTrace tailWord_7754338 prefixEnd_7754338 3981702551423987350613455 := by
  unfold tailWord_7754338
  simp only [CollatzResearch.WordTrace]
  refine ⟨70705985445341309084943917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188549294520910157559850445 70705985445341309084943917)
  ·
    refine ⟨26514744542002990906853969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70705985445341309084943917 26514744542002990906853969)
    ·
      refine ⟨19886058406502243180140477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26514744542002990906853969 19886058406502243180140477)
      ·
        refine ⟨7457271902438341192552679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19886058406502243180140477 7457271902438341192552679)
        ·
          refine ⟨11185907853657511788829019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457271902438341192552679 11185907853657511788829019)
          ·
            refine ⟨16778861780486267683243529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185907853657511788829019 16778861780486267683243529)
            ·
              refine ⟨12584146335364700762432647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16778861780486267683243529 12584146335364700762432647)
              ·
                refine ⟨18876219503047051143648971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12584146335364700762432647 18876219503047051143648971)
                ·
                  refine ⟨28314329254570576715473457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18876219503047051143648971 28314329254570576715473457)
                  ·
                    refine ⟨21235746940927932536605093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28314329254570576715473457 21235746940927932536605093)
                    ·
                      refine ⟨3981702551423987350613455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21235746940927932536605093 3981702551423987350613455)
                      ·
                        rfl

theorem cell23_7754338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7754338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754338 prefixEnd_7754338 := by exact prefixLift 7754338
  have htrace : WordTrace (prefixWord ++ tailWord_7754338) baseStart_7754338 baseEnd_7754338 := by
    simpa [prefixWord, tailWord_7754338, baseEnd_7754338] using wordTrace_append hprefix tailTrace_7754338
  have hstable : (prefixWord ++ tailWord_7754338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754338).length < 2 ^ (prefixWord ++ tailWord_7754338).sum := by decide
  have hdescent : baseEnd_7754338 < baseStart_7754338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754341 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_7754341 : Nat := 118140960795 + 7754341 * 2 ^ 59
def prefixEnd_7754341 : Nat := 4983230072969 + 3 ^ 40 * 7754341 * 2
def baseEnd_7754341 : Nat := 3981704091865950838875941

theorem tailTrace_7754341 : CollatzResearch.WordTrace tailWord_7754341 prefixEnd_7754341 3981704091865950838875941 := by
  unfold tailWord_7754341
  simp only [CollatzResearch.WordTrace]
  refine ⟨282824051200354367852134877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188549367466902911901423251 282824051200354367852134877)
  ·
    refine ⟨106059019200132887944550579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282824051200354367852134877 106059019200132887944550579)
    ·
      refine ⟨159088528800199331916825869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106059019200132887944550579 159088528800199331916825869)
      ·
        refine ⟨59658198300074749468809701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159088528800199331916825869 59658198300074749468809701)
        ·
          refine ⟨11185912181264015525401819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59658198300074749468809701 11185912181264015525401819)
          ·
            refine ⟨16778868271896023288102729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185912181264015525401819 16778868271896023288102729)
            ·
              refine ⟨12584151203922017466077047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16778868271896023288102729 12584151203922017466077047)
              ·
                refine ⟨18876226805883026199115571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12584151203922017466077047 18876226805883026199115571)
                ·
                  refine ⟨28314340208824539298673357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18876226805883026199115571 28314340208824539298673357)
                  ·
                    refine ⟨10617877578309202237002509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28314340208824539298673357 10617877578309202237002509)
                    ·
                      refine ⟨3981704091865950838875941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10617877578309202237002509 3981704091865950838875941)
                      ·
                        rfl

theorem cell23_7754341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_7754341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754341 prefixEnd_7754341 := by exact prefixLift 7754341
  have htrace : WordTrace (prefixWord ++ tailWord_7754341) baseStart_7754341 baseEnd_7754341 := by
    simpa [prefixWord, tailWord_7754341, baseEnd_7754341] using wordTrace_append hprefix tailTrace_7754341
  have hstable : (prefixWord ++ tailWord_7754341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754341).length < 2 ^ (prefixWord ++ tailWord_7754341).sum := by decide
  have hdescent : baseEnd_7754341 < baseStart_7754341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754367 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 3]
def baseStart_7754367 : Nat := 118140960795 + 7754367 * 2 ^ 59
def prefixEnd_7754367 : Nat := 4983230072969 + 3 ^ 40 * 7754367 * 2
def baseEnd_7754367 : Nat := 3981717442362967737150821

theorem tailTrace_7754367 : CollatzResearch.WordTrace tailWord_7754367 prefixEnd_7754367 3981717442362967737150821 := by
  unfold tailWord_7754367
  simp only [CollatzResearch.WordTrace]
  refine ⟨282824999498260174292581355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188549999665506782861720903 282824999498260174292581355)
  ·
    refine ⟨424237499247390261438872033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282824999498260174292581355 424237499247390261438872033)
    ·
      refine ⟨318178124435542696079154025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424237499247390261438872033 318178124435542696079154025)
      ·
        refine ⟨238633593326657022059365519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318178124435542696079154025 238633593326657022059365519)
        ·
          refine ⟨357950389989985533089048279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238633593326657022059365519 357950389989985533089048279)
          ·
            refine ⟨536925584984978299633572419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357950389989985533089048279 536925584984978299633572419)
            ·
              refine ⟨805388377477467449450358629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536925584984978299633572419 805388377477467449450358629)
              ·
                refine ⟨151010320777025146771942243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805388377477467449450358629 151010320777025146771942243)
                ·
                  refine ⟨226515481165537720157913365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151010320777025146771942243 226515481165537720157913365)
                  ·
                    refine ⟨10617913179634580632402189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 226515481165537720157913365 10617913179634580632402189)
                    ·
                      refine ⟨3981717442362967737150821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10617913179634580632402189 3981717442362967737150821)
                      ·
                        rfl

theorem cell23_7754367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_7754367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754367 prefixEnd_7754367 := by exact prefixLift 7754367
  have htrace : WordTrace (prefixWord ++ tailWord_7754367) baseStart_7754367 baseEnd_7754367 := by
    simpa [prefixWord, tailWord_7754367, baseEnd_7754367] using wordTrace_append hprefix tailTrace_7754367
  have hstable : (prefixWord ++ tailWord_7754367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754367).length < 2 ^ (prefixWord ++ tailWord_7754367).sum := by decide
  have hdescent : baseEnd_7754367 < baseStart_7754367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754368 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 1, 3, 2]
def baseStart_7754368 : Nat := 118140960795 + 7754368 * 2 ^ 59
def prefixEnd_7754368 : Nat := 4983230072969 + 3 ^ 40 * 7754368 * 2
def baseEnd_7754368 : Nat := 3981717955843622233238317

theorem tailTrace_7754368 : CollatzResearch.WordTrace tailWord_7754368 prefixEnd_7754368 3981717955843622233238317 := by
  unfold tailWord_7754368
  simp only [CollatzResearch.WordTrace]
  refine ⟨141412517985628275731683879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188550023980837700975578505 141412517985628275731683879)
  ·
    refine ⟨212118776978442413597525819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141412517985628275731683879 212118776978442413597525819)
    ·
      refine ⟨318178165467663620396288729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212118776978442413597525819 318178165467663620396288729)
      ·
        refine ⟨238633624100747715297216547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318178165467663620396288729 238633624100747715297216547)
        ·
          refine ⟨357950436151121572945824821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238633624100747715297216547 357950436151121572945824821)
          ·
            refine ⟨33557853389167647463671077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357950436151121572945824821 33557853389167647463671077)
            ·
              refine ⟨6292097510468933899438327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33557853389167647463671077 6292097510468933899438327)
              ·
                refine ⟨9438146265703400849157491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292097510468933899438327 9438146265703400849157491)
                ·
                  refine ⟨14157219398555101273736237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438146265703400849157491 14157219398555101273736237)
                  ·
                    refine ⟨5308957274458162977651089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14157219398555101273736237 5308957274458162977651089)
                    ·
                      refine ⟨3981717955843622233238317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308957274458162977651089 3981717955843622233238317)
                      ·
                        rfl

theorem cell23_7754368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_7754368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754368 prefixEnd_7754368 := by exact prefixLift 7754368
  have htrace : WordTrace (prefixWord ++ tailWord_7754368) baseStart_7754368 baseEnd_7754368 := by
    simpa [prefixWord, tailWord_7754368, baseEnd_7754368] using wordTrace_append hprefix tailTrace_7754368
  have hstable : (prefixWord ++ tailWord_7754368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754368).length < 2 ^ (prefixWord ++ tailWord_7754368).sum := by decide
  have hdescent : baseEnd_7754368 < baseStart_7754368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754424 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 7, 2]
def baseStart_7754424 : Nat := 118140960795 + 7754424 * 2 ^ 59
def prefixEnd_7754424 : Nat := 4983230072969 + 3 ^ 40 * 7754424 * 2
def baseEnd_7754424 : Nat := 3981746710760274014138059

theorem tailTrace_7754424 : CollatzResearch.WordTrace tailWord_7754424 prefixEnd_7754424 3981746710760274014138059 := by
  unfold tailWord_7754424
  simp only [CollatzResearch.WordTrace]
  refine ⟨141413539229526836513703163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188551385639369115351604217 141413539229526836513703163)
  ·
    refine ⟨212120308844290254770554745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141413539229526836513703163 212120308844290254770554745)
    ·
      refine ⟨159090231633217691077916059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212120308844290254770554745 159090231633217691077916059)
      ·
        refine ⟨238635347449826536616874089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159090231633217691077916059 238635347449826536616874089)
        ·
          refine ⟨178976510587369902462655567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238635347449826536616874089 178976510587369902462655567)
          ·
            refine ⟨268464765881054853693983351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178976510587369902462655567 268464765881054853693983351)
            ·
              refine ⟨402697148821582280540975027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268464765881054853693983351 402697148821582280540975027)
              ·
                refine ⟨604045723232373420811462541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402697148821582280540975027 604045723232373420811462541)
                ·
                  refine ⟨226517146212140032804298453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604045723232373420811462541 226517146212140032804298453)
                  ·
                    refine ⟨5308995614347032018850745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226517146212140032804298453 5308995614347032018850745)
                    ·
                      refine ⟨3981746710760274014138059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5308995614347032018850745 3981746710760274014138059)
                      ·
                        rfl

theorem cell23_7754424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 7, 2].length) (baseStart_7754424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754424 prefixEnd_7754424 := by exact prefixLift 7754424
  have htrace : WordTrace (prefixWord ++ tailWord_7754424) baseStart_7754424 baseEnd_7754424 := by
    simpa [prefixWord, tailWord_7754424, baseEnd_7754424] using wordTrace_append hprefix tailTrace_7754424
  have hstable : (prefixWord ++ tailWord_7754424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754424).length < 2 ^ (prefixWord ++ tailWord_7754424).sum := by decide
  have hdescent : baseEnd_7754424 < baseStart_7754424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754444 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7754444 : Nat := 118140960795 + 7754444 * 2 ^ 59
def prefixEnd_7754444 : Nat := 4983230072969 + 3 ^ 40 * 7754444 * 2
def baseEnd_7754444 : Nat := 3981756980373363935887967

theorem tailTrace_7754444 : CollatzResearch.WordTrace tailWord_7754444 prefixEnd_7754444 3981756980373363935887967 := by
  unfold tailWord_7754444
  simp only [CollatzResearch.WordTrace]
  refine ⟨141413903959490608221567193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188551871945987477628756257 141413903959490608221567193)
  ·
    refine ⟨106060427969617956166175395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141413903959490608221567193 106060427969617956166175395)
    ·
      refine ⟨159090641954426934249263093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106060427969617956166175395 159090641954426934249263093)
      ·
        refine ⟨14914747683227525085868415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159090641954426934249263093 14914747683227525085868415)
        ·
          refine ⟨22372121524841287628802623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14914747683227525085868415 22372121524841287628802623)
          ·
            refine ⟨33558182287261931443203935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22372121524841287628802623 33558182287261931443203935)
            ·
              refine ⟨50337273430892897164805903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33558182287261931443203935 50337273430892897164805903)
              ·
                refine ⟨75505910146339345747208855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50337273430892897164805903 75505910146339345747208855)
                ·
                  refine ⟨113258865219509018620813283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75505910146339345747208855 113258865219509018620813283)
                  ·
                    refine ⟨169888297829263527931219925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113258865219509018620813283 169888297829263527931219925)
                    ·
                      refine ⟨3981756980373363935887967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169888297829263527931219925 3981756980373363935887967)
                      ·
                        rfl

theorem cell23_7754444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7754444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754444 prefixEnd_7754444 := by exact prefixLift 7754444
  have htrace : WordTrace (prefixWord ++ tailWord_7754444) baseStart_7754444 baseEnd_7754444 := by
    simpa [prefixWord, tailWord_7754444, baseEnd_7754444] using wordTrace_append hprefix tailTrace_7754444
  have hstable : (prefixWord ++ tailWord_7754444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754444).length < 2 ^ (prefixWord ++ tailWord_7754444).sum := by decide
  have hdescent : baseEnd_7754444 < baseStart_7754444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754464 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 5, 4]
def baseStart_7754464 : Nat := 118140960795 + 7754464 * 2 ^ 59
def prefixEnd_7754464 : Nat := 4983230072969 + 3 ^ 40 * 7754464 * 2
def baseEnd_7754464 : Nat := 1327255749995484619212625

theorem tailTrace_7754464 : CollatzResearch.WordTrace tailWord_7754464 prefixEnd_7754464 1327255749995484619212625 := by
  unfold tailWord_7754464
  simp only [CollatzResearch.WordTrace]
  refine ⟨141414268689454379929431223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188552358252605839905908297 141414268689454379929431223)
  ·
    refine ⟨212121403034181569894146835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141414268689454379929431223 212121403034181569894146835)
    ·
      refine ⟨318182104551272354841220253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212121403034181569894146835 318182104551272354841220253)
      ·
        refine ⟨119318289206727133065457595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318182104551272354841220253 119318289206727133065457595)
        ·
          refine ⟨178977433810090699598186393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119318289206727133065457595 178977433810090699598186393)
          ·
            refine ⟨134233075357568024698639795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178977433810090699598186393 134233075357568024698639795)
            ·
              refine ⟨201349613036352037047959693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134233075357568024698639795 201349613036352037047959693)
              ·
                refine ⟨75506104888632013892984885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201349613036352037047959693 75506104888632013892984885)
                ·
                  refine ⟨7078697333309251302467333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75506104888632013892984885 7078697333309251302467333)
                  ·
                    refine ⟨1327255749995484619212625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7078697333309251302467333 1327255749995484619212625)
                    ·
                      rfl

theorem cell23_7754464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 4].length) (baseStart_7754464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754464 prefixEnd_7754464 := by exact prefixLift 7754464
  have htrace : WordTrace (prefixWord ++ tailWord_7754464) baseStart_7754464 baseEnd_7754464 := by
    simpa [prefixWord, tailWord_7754464, baseEnd_7754464] using wordTrace_append hprefix tailTrace_7754464
  have hstable : (prefixWord ++ tailWord_7754464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754464).length < 2 ^ (prefixWord ++ tailWord_7754464).sum := by decide
  have hdescent : baseEnd_7754464 < baseStart_7754464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754578 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_7754578 : Nat := 118140960795 + 7754578 * 2 ^ 59
def prefixEnd_7754578 : Nat := 4983230072969 + 3 ^ 40 * 7754578 * 2
def baseEnd_7754578 : Nat := 3981825786781066411612351

theorem tailTrace_7754578 : CollatzResearch.WordTrace tailWord_7754578 prefixEnd_7754578 3981825786781066411612351 := by
  unfold tailWord_7754578
  simp only [CollatzResearch.WordTrace]
  refine ⟨70708173825123939332128097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188555130200330504885674925 70708173825123939332128097)
  ·
    refine ⟨53031130368842954499096073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70708173825123939332128097 53031130368842954499096073)
    ·
      refine ⟨39773347776632215874322055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53031130368842954499096073 39773347776632215874322055)
      ·
        refine ⟨59660021664948323811483083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39773347776632215874322055 59660021664948323811483083)
        ·
          refine ⟨89490032497422485717224625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59660021664948323811483083 89490032497422485717224625)
          ·
            refine ⟨67117524373066864287918469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89490032497422485717224625 67117524373066864287918469)
            ·
              refine ⟨12584535819950037053984713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67117524373066864287918469 12584535819950037053984713)
              ·
                refine ⟨9438401864962527790488535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12584535819950037053984713 9438401864962527790488535)
                ·
                  refine ⟨14157602797443791685732803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438401864962527790488535 14157602797443791685732803)
                  ·
                    refine ⟨21236404196165687528599205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14157602797443791685732803 21236404196165687528599205)
                    ·
                      refine ⟨3981825786781066411612351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21236404196165687528599205 3981825786781066411612351)
                      ·
                        rfl

theorem cell23_7754578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_7754578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754578 prefixEnd_7754578 := by exact prefixLift 7754578
  have htrace : WordTrace (prefixWord ++ tailWord_7754578) baseStart_7754578 baseEnd_7754578 := by
    simpa [prefixWord, tailWord_7754578, baseEnd_7754578] using wordTrace_append hprefix tailTrace_7754578
  have hstable : (prefixWord ++ tailWord_7754578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754578).length < 2 ^ (prefixWord ++ tailWord_7754578).sum := by decide
  have hdescent : baseEnd_7754578 < baseStart_7754578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754588 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_7754588 : Nat := 118140960795 + 7754588 * 2 ^ 59
def prefixEnd_7754588 : Nat := 4983230072969 + 3 ^ 40 * 7754588 * 2
def baseEnd_7754588 : Nat := 1327276973862537124162435

theorem tailTrace_7754588 : CollatzResearch.WordTrace tailWord_7754588 prefixEnd_7754588 1327276973862537124162435 := by
  unfold tailWord_7754588
  simp only [CollatzResearch.WordTrace]
  refine ⟨141416530015229764518188209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188555373353639686024250945 141416530015229764518188209)
  ·
    refine ⟨106062397511422323388641157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141416530015229764518188209 106062397511422323388641157)
    ·
      refine ⟨19886699533391685635370217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106062397511422323388641157 19886699533391685635370217)
      ·
        refine ⟨14915024650043764226527663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19886699533391685635370217 14915024650043764226527663)
        ·
          refine ⟨22372536975065646339791495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14915024650043764226527663 22372536975065646339791495)
          ·
            refine ⟨33558805462598469509687243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22372536975065646339791495 33558805462598469509687243)
            ·
              refine ⟨50338208193897704264530865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33558805462598469509687243 50338208193897704264530865)
              ·
                refine ⟨37753656145423278198398149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50338208193897704264530865 37753656145423278198398149)
                ·
                  refine ⟨7078810527266864662199653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37753656145423278198398149 7078810527266864662199653)
                  ·
                    refine ⟨1327276973862537124162435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7078810527266864662199653 1327276973862537124162435)
                    ·
                      rfl

theorem cell23_7754588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_7754588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754588 prefixEnd_7754588 := by exact prefixLift 7754588
  have htrace : WordTrace (prefixWord ++ tailWord_7754588) baseStart_7754588 baseEnd_7754588 := by
    simpa [prefixWord, tailWord_7754588, baseEnd_7754588] using wordTrace_append hprefix tailTrace_7754588
  have hstable : (prefixWord ++ tailWord_7754588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754588).length < 2 ^ (prefixWord ++ tailWord_7754588).sum := by decide
  have hdescent : baseEnd_7754588 < baseStart_7754588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754622 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7754622 : Nat := 118140960795 + 7754622 * 2 ^ 59
def prefixEnd_7754622 : Nat := 4983230072969 + 3 ^ 40 * 7754622 * 2
def baseEnd_7754622 : Nat := 1327282793309954746487383

theorem tailTrace_7754622 : CollatzResearch.WordTrace tailWord_7754622 prefixEnd_7754622 1327282793309954746487383 := by
  unfold tailWord_7754622
  simp only [CollatzResearch.WordTrace]
  refine ⟨35354287514042044105389265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188556200074890901895409413 35354287514042044105389265)
  ·
    refine ⟨26515715635531533079041949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35354287514042044105389265 26515715635531533079041949)
    ·
      refine ⟨9943393363324324904640731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26515715635531533079041949 9943393363324324904640731)
      ·
        refine ⟨14915090044986487356961097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9943393363324324904640731 14915090044986487356961097)
        ·
          refine ⟨11186317533739865517720823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14915090044986487356961097 11186317533739865517720823)
          ·
            refine ⟨16779476300609798276581235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11186317533739865517720823 16779476300609798276581235)
            ·
              refine ⟨25169214450914697414871853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16779476300609798276581235 25169214450914697414871853)
              ·
                refine ⟨9438455419093011530576945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25169214450914697414871853 9438455419093011530576945)
                ·
                  refine ⟨7078841564319758647932709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9438455419093011530576945 7078841564319758647932709)
                  ·
                    refine ⟨1327282793309954746487383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7078841564319758647932709 1327282793309954746487383)
                    ·
                      rfl

theorem cell23_7754622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7754622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754622 prefixEnd_7754622 := by exact prefixLift 7754622
  have htrace : WordTrace (prefixWord ++ tailWord_7754622) baseStart_7754622 baseEnd_7754622 := by
    simpa [prefixWord, tailWord_7754622, baseEnd_7754622] using wordTrace_append hprefix tailTrace_7754622
  have hstable : (prefixWord ++ tailWord_7754622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754622).length < 2 ^ (prefixWord ++ tailWord_7754622).sum := by decide
  have hdescent : baseEnd_7754622 < baseStart_7754622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754624 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5]
def baseStart_7754624 : Nat := 118140960795 + 7754624 * 2 ^ 59
def prefixEnd_7754624 : Nat := 4983230072969 + 3 ^ 40 * 7754624 * 2
def baseEnd_7754624 : Nat := 3981849406891173231637139

theorem tailTrace_7754624 : CollatzResearch.WordTrace tailWord_7754624 prefixEnd_7754624 3981849406891173231637139 := by
  unfold tailWord_7754624
  simp only [CollatzResearch.WordTrace]
  refine ⟨141417186529164553592343463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188556248705552738123124617 141417186529164553592343463)
  ·
    refine ⟨212125779793746830388515195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141417186529164553592343463 212125779793746830388515195)
    ·
      refine ⟨318188669690620245582772793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212125779793746830388515195 318188669690620245582772793)
      ·
        refine ⟨238641502267965184187079595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318188669690620245582772793 238641502267965184187079595)
        ·
          refine ⟨357962253401947776280619393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238641502267965184187079595 357962253401947776280619393)
          ·
            refine ⟨268471690051460832210464545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357962253401947776280619393 268471690051460832210464545)
            ·
              refine ⟨201353767538595624157848409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268471690051460832210464545 201353767538595624157848409)
              ·
                refine ⟨151015325653946718118386307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201353767538595624157848409 151015325653946718118386307)
                ·
                  refine ⟨226522988480920077177579461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151015325653946718118386307 226522988480920077177579461)
                  ·
                    refine ⟨42473060340172514470796149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226522988480920077177579461 42473060340172514470796149)
                    ·
                      refine ⟨3981849406891173231637139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42473060340172514470796149 3981849406891173231637139)
                      ·
                        rfl

theorem cell23_7754624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_7754624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754624 prefixEnd_7754624 := by exact prefixLift 7754624
  have htrace : WordTrace (prefixWord ++ tailWord_7754624) baseStart_7754624 baseEnd_7754624 := by
    simpa [prefixWord, tailWord_7754624, baseEnd_7754624] using wordTrace_append hprefix tailTrace_7754624
  have hstable : (prefixWord ++ tailWord_7754624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754624).length < 2 ^ (prefixWord ++ tailWord_7754624).sum := by decide
  have hdescent : baseEnd_7754624 < baseStart_7754624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754663 : List Nat := [1, 1, 6, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_7754663 : Nat := 118140960795 + 7754663 * 2 ^ 59
def prefixEnd_7754663 : Nat := 4983230072969 + 3 ^ 40 * 7754663 * 2
def baseEnd_7754663 : Nat := 3981869432636698579049461

theorem tailTrace_7754663 : CollatzResearch.WordTrace tailWord_7754663 prefixEnd_7754663 3981869432636698579049461 := by
  unfold tailWord_7754663
  simp only [CollatzResearch.WordTrace]
  refine ⟨282835795505187816845356643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188557197003458544563571095 282835795505187816845356643)
  ·
    refine ⟨424253693257781725268034965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282835795505187816845356643 424253693257781725268034965)
    ·
      refine ⟨19886891871458518371939139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 424253693257781725268034965 19886891871458518371939139)
      ·
        refine ⟨29830337807187777557908709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19886891871458518371939139 29830337807187777557908709)
        ·
          refine ⟨5593188338847708292107883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29830337807187777557908709 5593188338847708292107883)
          ·
            refine ⟨8389782508271562438161825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593188338847708292107883 8389782508271562438161825)
            ·
              refine ⟨6292336881203671828621369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8389782508271562438161825 6292336881203671828621369)
              ·
                refine ⟨4719252660902753871466027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6292336881203671828621369 4719252660902753871466027)
                ·
                  refine ⟨7078878991354130807199041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719252660902753871466027 7078878991354130807199041)
                  ·
                    refine ⟨5309159243515598105399281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7078878991354130807199041 5309159243515598105399281)
                    ·
                      refine ⟨3981869432636698579049461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309159243515598105399281 3981869432636698579049461)
                      ·
                        rfl

theorem cell23_7754663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_7754663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754663 prefixEnd_7754663 := by exact prefixLift 7754663
  have htrace : WordTrace (prefixWord ++ tailWord_7754663) baseStart_7754663 baseEnd_7754663 := by
    simpa [prefixWord, tailWord_7754663, baseEnd_7754663] using wordTrace_append hprefix tailTrace_7754663
  have hstable : (prefixWord ++ tailWord_7754663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754663).length < 2 ^ (prefixWord ++ tailWord_7754663).sum := by decide
  have hdescent : baseEnd_7754663 < baseStart_7754663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754681 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7754681 : Nat := 118140960795 + 7754681 * 2 ^ 59
def prefixEnd_7754681 : Nat := 4983230072969 + 3 ^ 40 * 7754681 * 2
def baseEnd_7754681 : Nat := 3981878675288479508624377

theorem tailTrace_7754681 : CollatzResearch.WordTrace tailWord_7754681 prefixEnd_7754681 3981878675288479508624377 := by
  unfold tailWord_7754681
  simp only [CollatzResearch.WordTrace]
  refine ⟨282836452019122605919511897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188557634679415070613007931 282836452019122605919511897)
  ·
    refine ⟨212127339014341954439633923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282836452019122605919511897 212127339014341954439633923)
    ·
      refine ⟨318191008521512931659450885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212127339014341954439633923 318191008521512931659450885)
      ·
        refine ⟨59660814097783674686147041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318191008521512931659450885 59660814097783674686147041)
        ·
          refine ⟨44745610573337756014610281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59660814097783674686147041 44745610573337756014610281)
          ·
            refine ⟨33559207930003317010957711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44745610573337756014610281 33559207930003317010957711)
            ·
              refine ⟨50338811895004975516436567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33559207930003317010957711 50338811895004975516436567)
              ·
                refine ⟨75508217842507463274654851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50338811895004975516436567 75508217842507463274654851)
                ·
                  refine ⟨113262326763761194911982277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75508217842507463274654851 113262326763761194911982277)
                  ·
                    refine ⟨21236686268205224045996677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113262326763761194911982277 21236686268205224045996677)
                    ·
                      refine ⟨3981878675288479508624377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21236686268205224045996677 3981878675288479508624377)
                      ·
                        rfl

theorem cell23_7754681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7754681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754681 prefixEnd_7754681 := by exact prefixLift 7754681
  have htrace : WordTrace (prefixWord ++ tailWord_7754681) baseStart_7754681 baseEnd_7754681 := by
    simpa [prefixWord, tailWord_7754681, baseEnd_7754681] using wordTrace_append hprefix tailTrace_7754681
  have hstable : (prefixWord ++ tailWord_7754681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754681).length < 2 ^ (prefixWord ++ tailWord_7754681).sum := by decide
  have hdescent : baseEnd_7754681 < baseStart_7754681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754719 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 2, 2, 2]
def baseStart_7754719 : Nat := 118140960795 + 7754719 * 2 ^ 59
def prefixEnd_7754719 : Nat := 4983230072969 + 3 ^ 40 * 7754719 * 2
def baseEnd_7754719 : Nat := 3981898187553350359949203

theorem tailTrace_7754719 : CollatzResearch.WordTrace tailWord_7754719 prefixEnd_7754719 3981898187553350359949203 := by
  unfold tailWord_7754719
  simp only [CollatzResearch.WordTrace]
  refine ⟨282837837992984938409395211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188558558661989958939596807 282837837992984938409395211)
  ·
    refine ⟨424256756989477407614092817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282837837992984938409395211 424256756989477407614092817)
    ·
      refine ⟨318192567742108055710569613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424256756989477407614092817 318192567742108055710569613)
      ·
        refine ⟨119322212903290520891463605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318192567742108055710569613 119322212903290520891463605)
        ·
          refine ⟨11186457459683486333574713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119322212903290520891463605 11186457459683486333574713)
          ·
            refine ⟨8389843094762614750181035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11186457459683486333574713 8389843094762614750181035)
            ·
              refine ⟨12584764642143922125271553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389843094762614750181035 12584764642143922125271553)
              ·
                refine ⟨9438573481607941593953665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12584764642143922125271553 9438573481607941593953665)
                ·
                  refine ⟨7078930111205956195465249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9438573481607941593953665 7078930111205956195465249)
                  ·
                    refine ⟨5309197583404467146598937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7078930111205956195465249 5309197583404467146598937)
                    ·
                      refine ⟨3981898187553350359949203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309197583404467146598937 3981898187553350359949203)
                      ·
                        rfl

theorem cell23_7754719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_7754719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754719 prefixEnd_7754719 := by exact prefixLift 7754719
  have htrace : WordTrace (prefixWord ++ tailWord_7754719) baseStart_7754719 baseEnd_7754719 := by
    simpa [prefixWord, tailWord_7754719, baseEnd_7754719] using wordTrace_append hprefix tailTrace_7754719
  have hstable : (prefixWord ++ tailWord_7754719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754719).length < 2 ^ (prefixWord ++ tailWord_7754719).sum := by decide
  have hdescent : baseEnd_7754719 < baseStart_7754719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754721 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 4, 5]
def baseStart_7754721 : Nat := 118140960795 + 7754721 * 2 ^ 59
def prefixEnd_7754721 : Nat := 4983230072969 + 3 ^ 40 * 7754721 * 2
def baseEnd_7754721 : Nat := 1327299738171553117374731

theorem tailTrace_7754721 : CollatzResearch.WordTrace tailWord_7754721 prefixEnd_7754721 1327299738171553117374731 := by
  unfold tailWord_7754721
  simp only [CollatzResearch.WordTrace]
  refine ⟨282837910938977692750968017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188558607292651795167312011 282837910938977692750968017)
  ·
    refine ⟨212128433204233269563226013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282837910938977692750968017 212128433204233269563226013)
    ·
      refine ⟨79548162451587476086209755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212128433204233269563226013 79548162451587476086209755)
      ·
        refine ⟨119322243677381214129314633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79548162451587476086209755 119322243677381214129314633)
        ·
          refine ⟨89491682758035910596985975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119322243677381214129314633 89491682758035910596985975)
          ·
            refine ⟨134237524137053865895478963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89491682758035910596985975 134237524137053865895478963)
            ·
              refine ⟨201356286205580798843218445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134237524137053865895478963 201356286205580798843218445)
              ·
                refine ⟨75508607327092799566206917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201356286205580798843218445 75508607327092799566206917)
                ·
                  refine ⟨14157863873829899918663797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75508607327092799566206917 14157863873829899918663797)
                  ·
                    refine ⟨1327299738171553117374731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14157863873829899918663797 1327299738171553117374731)
                    ·
                      rfl

theorem cell23_7754721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_7754721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754721 prefixEnd_7754721 := by exact prefixLift 7754721
  have htrace : WordTrace (prefixWord ++ tailWord_7754721) baseStart_7754721 baseEnd_7754721 := by
    simpa [prefixWord, tailWord_7754721, baseEnd_7754721] using wordTrace_append hprefix tailTrace_7754721
  have hstable : (prefixWord ++ tailWord_7754721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754721).length < 2 ^ (prefixWord ++ tailWord_7754721).sum := by decide
  have hdescent : baseEnd_7754721 < baseStart_7754721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754725 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 7]
def baseStart_7754725 : Nat := 118140960795 + 7754725 * 2 ^ 59
def prefixEnd_7754725 : Nat := 4983230072969 + 3 ^ 40 * 7754725 * 2
def baseEnd_7754725 : Nat := 442433474270808592941575

theorem tailTrace_7754725 : CollatzResearch.WordTrace tailWord_7754725 prefixEnd_7754725 442433474270808592941575 := by
  unfold tailWord_7754725
  simp only [CollatzResearch.WordTrace]
  refine ⟨282838056830963201434113629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188558704553975467622742419 282838056830963201434113629)
  ·
    refine ⟨106064271311611200537792611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282838056830963201434113629 106064271311611200537792611)
    ·
      refine ⟨159096406967416800806688917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106064271311611200537792611 159096406967416800806688917)
      ·
        refine ⟨7457644076597662537813543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159096406967416800806688917 7457644076597662537813543)
        ·
          refine ⟨11186466114896493806720315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457644076597662537813543 11186466114896493806720315)
          ·
            refine ⟨16779699172344740710080473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11186466114896493806720315 16779699172344740710080473)
            ·
              refine ⟨12584774379258555532560355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16779699172344740710080473 12584774379258555532560355)
              ·
                refine ⟨18877161568887833298840533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12584774379258555532560355 18877161568887833298840533)
                ·
                  refine ⟨442433474270808592941575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18877161568887833298840533 442433474270808592941575)
                  ·
                    rfl

theorem cell23_7754725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_7754725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754725 prefixEnd_7754725 := by exact prefixLift 7754725
  have htrace : WordTrace (prefixWord ++ tailWord_7754725) baseStart_7754725 baseEnd_7754725 := by
    simpa [prefixWord, tailWord_7754725, baseEnd_7754725] using wordTrace_append hprefix tailTrace_7754725
  have hstable : (prefixWord ++ tailWord_7754725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754725).length < 2 ^ (prefixWord ++ tailWord_7754725).sum := by decide
  have hdescent : baseEnd_7754725 < baseStart_7754725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754728 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_7754728 : Nat := 118140960795 + 7754728 * 2 ^ 59
def prefixEnd_7754728 : Nat := 4983230072969 + 3 ^ 40 * 7754728 * 2
def baseEnd_7754728 : Nat := 3981902808879240824736661

theorem tailTrace_7754728 : CollatzResearch.WordTrace tailWord_7754728 prefixEnd_7754728 3981902808879240824736661 := by
  unfold tailWord_7754728
  simp only [CollatzResearch.WordTrace]
  refine ⟨141419083124976166473236419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188558777499968221964315225 141419083124976166473236419)
  ·
    refine ⟨212128624687464249709854629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141419083124976166473236419 212128624687464249709854629)
    ·
      refine ⟨39774117128899546820597743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212128624687464249709854629 39774117128899546820597743)
      ·
        refine ⟨59661175693349320230896615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39774117128899546820597743 59661175693349320230896615)
        ·
          refine ⟨89491763540023980346344923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59661175693349320230896615 89491763540023980346344923)
          ·
            refine ⟨134237645310035970519517385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89491763540023980346344923 134237645310035970519517385)
            ·
              refine ⟨100678233982526977889638039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134237645310035970519517385 100678233982526977889638039)
              ·
                refine ⟨151017350973790466834457059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100678233982526977889638039 151017350973790466834457059)
                ·
                  refine ⟨226526026460685700251685589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151017350973790466834457059 226526026460685700251685589)
                  ·
                    refine ⟨5309203745172321099648881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226526026460685700251685589 5309203745172321099648881)
                    ·
                      refine ⟨3981902808879240824736661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309203745172321099648881 3981902808879240824736661)
                      ·
                        rfl

theorem cell23_7754728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_7754728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754728 prefixEnd_7754728 := by exact prefixLift 7754728
  have htrace : WordTrace (prefixWord ++ tailWord_7754728) baseStart_7754728 baseEnd_7754728 := by
    simpa [prefixWord, tailWord_7754728, baseEnd_7754728] using wordTrace_append hprefix tailTrace_7754728
  have hstable : (prefixWord ++ tailWord_7754728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754728).length < 2 ^ (prefixWord ++ tailWord_7754728).sum := by decide
  have hdescent : baseEnd_7754728 < baseStart_7754728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754775 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7754775 : Nat := 118140960795 + 7754775 * 2 ^ 59
def prefixEnd_7754775 : Nat := 4983230072969 + 3 ^ 40 * 7754775 * 2
def baseEnd_7754775 : Nat := 3981926942470002140848945

theorem tailTrace_7754775 : CollatzResearch.WordTrace tailWord_7754775 prefixEnd_7754775 3981926942470002140848945 := by
  unfold tailWord_7754775
  simp only [CollatzResearch.WordTrace]
  refine ⟨282839880480782059973433779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188559920320521373315622519 282839880480782059973433779)
  ·
    refine ⟨424259820721173089960150669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282839880480782059973433779 424259820721173089960150669)
    ·
      refine ⟨159097432770439908735056501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424259820721173089960150669 159097432770439908735056501)
      ·
        refine ⟨14915384322228741443911547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159097432770439908735056501 14915384322228741443911547)
        ·
          refine ⟨22373076483343112165867321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14915384322228741443911547 22373076483343112165867321)
          ·
            refine ⟨16779807362507334124400491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22373076483343112165867321 16779807362507334124400491)
            ·
              refine ⟨25169711043761001186600737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16779807362507334124400491 25169711043761001186600737)
              ·
                refine ⟨18877283282820750889950553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25169711043761001186600737 18877283282820750889950553)
                ·
                  refine ⟨14157962462115563167462915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18877283282820750889950553 14157962462115563167462915)
                  ·
                    refine ⟨21236943693173344751194373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14157962462115563167462915 21236943693173344751194373)
                    ·
                      refine ⟨3981926942470002140848945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21236943693173344751194373 3981926942470002140848945)
                      ·
                        rfl

theorem cell23_7754775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7754775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754775 prefixEnd_7754775 := by exact prefixLift 7754775
  have htrace : WordTrace (prefixWord ++ tailWord_7754775) baseStart_7754775 baseEnd_7754775 := by
    simpa [prefixWord, tailWord_7754775, baseEnd_7754775] using wordTrace_append hprefix tailTrace_7754775
  have hstable : (prefixWord ++ tailWord_7754775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754775).length < 2 ^ (prefixWord ++ tailWord_7754775).sum := by decide
  have hdescent : baseEnd_7754775 < baseStart_7754775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754785 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 3, 4]
def baseStart_7754785 : Nat := 118140960795 + 7754785 * 2 ^ 59
def prefixEnd_7754785 : Nat := 4983230072969 + 3 ^ 40 * 7754785 * 2
def baseEnd_7754785 : Nat := 1327310692425515700574633

theorem tailTrace_7754785 : CollatzResearch.WordTrace tailWord_7754785 prefixEnd_7754785 1327310692425515700574633 := by
  unfold tailWord_7754785
  simp only [CollatzResearch.WordTrace]
  refine ⟨282840245210745831681297809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188560163473830554454198539 282840245210745831681297809)
  ·
    refine ⟨212130183908059373760973357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282840245210745831681297809 212130183908059373760973357)
    ·
      refine ⟨79548818965522265160365009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212130183908059373760973357 79548818965522265160365009)
      ·
        refine ⟨59661614224141698870273757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79548818965522265160365009 59661614224141698870273757)
        ·
          refine ⟨22373105334053137076352659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59661614224141698870273757 22373105334053137076352659)
          ·
            refine ⟨33559658001079705614528989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22373105334053137076352659 33559658001079705614528989)
            ·
              refine ⟨12584871750404889605448371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33559658001079705614528989 12584871750404889605448371)
              ·
                refine ⟨18877307625607334408172557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12584871750404889605448371 18877307625607334408172557)
                ·
                  refine ⟨7078990359602750403064709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18877307625607334408172557 7078990359602750403064709)
                  ·
                    refine ⟨1327310692425515700574633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7078990359602750403064709 1327310692425515700574633)
                    ·
                      rfl

theorem cell23_7754785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_7754785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754785 prefixEnd_7754785 := by exact prefixLift 7754785
  have htrace : WordTrace (prefixWord ++ tailWord_7754785) baseStart_7754785 baseEnd_7754785 := by
    simpa [prefixWord, tailWord_7754785, baseEnd_7754785] using wordTrace_append hprefix tailTrace_7754785
  have hstable : (prefixWord ++ tailWord_7754785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754785).length < 2 ^ (prefixWord ++ tailWord_7754785).sum := by decide
  have hdescent : baseEnd_7754785 < baseStart_7754785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754848 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4]
def baseStart_7754848 : Nat := 118140960795 + 7754848 * 2 ^ 59
def prefixEnd_7754848 : Nat := 4983230072969 + 3 ^ 40 * 7754848 * 2
def baseEnd_7754848 : Nat := 3981964426557780355236109

theorem tailTrace_7754848 : CollatzResearch.WordTrace tailWord_7754848 prefixEnd_7754848 3981964426557780355236109 := by
  unfold tailWord_7754848
  simp only [CollatzResearch.WordTrace]
  refine ⟨141421271504758796720420599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188561695339678395627227465 141421271504758796720420599)
  ·
    refine ⟨212131907257138195080630899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141421271504758796720420599 212131907257138195080630899)
    ·
      refine ⟨318197860885707292620946349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212131907257138195080630899 318197860885707292620946349)
      ·
        refine ⟨119324197832140234732854881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318197860885707292620946349 119324197832140234732854881)
        ·
          refine ⟨89493148374105176049641161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119324197832140234732854881 89493148374105176049641161)
          ·
            refine ⟨67119861280578882037230871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89493148374105176049641161 67119861280578882037230871)
            ·
              refine ⟨100679791920868323055846307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67119861280578882037230871 100679791920868323055846307)
              ·
                refine ⟨151019687881302484583769461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100679791920868323055846307 151019687881302484583769461)
                ·
                  refine ⟨14158095738872107929728387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151019687881302484583769461 14158095738872107929728387)
                  ·
                    refine ⟨21237143608308161894592581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14158095738872107929728387 21237143608308161894592581)
                    ·
                      refine ⟨3981964426557780355236109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21237143608308161894592581 3981964426557780355236109)
                      ·
                        rfl

theorem cell23_7754848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_7754848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754848 prefixEnd_7754848 := by exact prefixLift 7754848
  have htrace : WordTrace (prefixWord ++ tailWord_7754848) baseStart_7754848 baseEnd_7754848 := by
    simpa [prefixWord, tailWord_7754848, baseEnd_7754848] using wordTrace_append hprefix tailTrace_7754848
  have hstable : (prefixWord ++ tailWord_7754848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754848).length < 2 ^ (prefixWord ++ tailWord_7754848).sum := by decide
  have hdescent : baseEnd_7754848 < baseStart_7754848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754869 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7754869 : Nat := 118140960795 + 7754869 * 2 ^ 59
def prefixEnd_7754869 : Nat := 4983230072969 + 3 ^ 40 * 7754869 * 2
def baseEnd_7754869 : Nat := 3981975209651524773073513

theorem tailTrace_7754869 : CollatzResearch.WordTrace tailWord_7754869 prefixEnd_7754869 3981975209651524773073513 := by
  unfold tailWord_7754869
  simp only [CollatzResearch.WordTrace]
  refine ⟨282843308942441514027355661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188562205961627676018237107 282843308942441514027355661)
  ·
    refine ⟨106066240853415567760258373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282843308942441514027355661 106066240853415567760258373)
    ·
      refine ⟨19887420160015418955048445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106066240853415567760258373 19887420160015418955048445)
      ·
        refine ⟨7457782560005782108143167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19887420160015418955048445 7457782560005782108143167)
        ·
          refine ⟨11186673840008673162214751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457782560005782108143167 11186673840008673162214751)
          ·
            refine ⟨16780010760013009743322127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11186673840008673162214751 16780010760013009743322127)
            ·
              refine ⟨25170016140019514614983191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16780010760013009743322127 25170016140019514614983191)
              ·
                refine ⟨37755024210029271922474787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25170016140019514614983191 37755024210029271922474787)
                ·
                  refine ⟨56632536315043907883712181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37755024210029271922474787 56632536315043907883712181)
                  ·
                    refine ⟨5309300279535366364098017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56632536315043907883712181 5309300279535366364098017)
                    ·
                      refine ⟨3981975209651524773073513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309300279535366364098017 3981975209651524773073513)
                      ·
                        rfl

theorem cell23_7754869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7754869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754869 prefixEnd_7754869 := by exact prefixLift 7754869
  have htrace : WordTrace (prefixWord ++ tailWord_7754869) baseStart_7754869 baseEnd_7754869 := by
    simpa [prefixWord, tailWord_7754869, baseEnd_7754869] using wordTrace_append hprefix tailTrace_7754869
  have hstable : (prefixWord ++ tailWord_7754869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754869).length < 2 ^ (prefixWord ++ tailWord_7754869).sum := by decide
  have hdescent : baseEnd_7754869 < baseStart_7754869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754899 : List Nat := [1, 1, 1, 2, 1, 2, 6, 4, 1, 2, 2]
def baseStart_7754899 : Nat := 118140960795 + 7754899 * 2 ^ 59
def prefixEnd_7754899 : Nat := 4983230072969 + 3 ^ 40 * 7754899 * 2
def baseEnd_7754899 : Nat := 3981990614071159655698375

theorem tailTrace_7754899 : CollatzResearch.WordTrace tailWord_7754899 prefixEnd_7754899 3981990614071159655698375 := by
  unfold tailWord_7754899
  simp only [CollatzResearch.WordTrace]
  refine ⟨282844403132332829150947751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188562935421555219433965167 282844403132332829150947751)
  ·
    refine ⟨424266604698499243726421627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282844403132332829150947751 424266604698499243726421627)
    ·
      refine ⟨636399907047748865589632441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424266604698499243726421627 636399907047748865589632441)
      ·
        refine ⟨477299930285811649192224331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636399907047748865589632441 477299930285811649192224331)
        ·
          refine ⟨715949895428717473788336497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477299930285811649192224331 715949895428717473788336497)
          ·
            refine ⟨536962421571538105341252373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715949895428717473788336497 536962421571538105341252373)
            ·
              refine ⟨25170113511165848687871205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 536962421571538105341252373 25170113511165848687871205)
              ·
                refine ⟨4719396283343596628975851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25170113511165848687871205 4719396283343596628975851)
                ·
                  refine ⟨7079094425015394943463777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719396283343596628975851 7079094425015394943463777)
                  ·
                    refine ⟨5309320818761546207597833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079094425015394943463777 5309320818761546207597833)
                    ·
                      refine ⟨3981990614071159655698375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309320818761546207597833 3981990614071159655698375)
                      ·
                        rfl

theorem cell23_7754899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 2, 2].length) (baseStart_7754899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754899 prefixEnd_7754899 := by exact prefixLift 7754899
  have htrace : WordTrace (prefixWord ++ tailWord_7754899) baseStart_7754899 baseEnd_7754899 := by
    simpa [prefixWord, tailWord_7754899, baseEnd_7754899] using wordTrace_append hprefix tailTrace_7754899
  have hstable : (prefixWord ++ tailWord_7754899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754899).length < 2 ^ (prefixWord ++ tailWord_7754899).sum := by decide
  have hdescent : baseEnd_7754899 < baseStart_7754899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754919 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_7754919 : Nat := 118140960795 + 7754919 * 2 ^ 59
def prefixEnd_7754919 : Nat := 4983230072969 + 3 ^ 40 * 7754919 * 2
def baseEnd_7754919 : Nat := 3982000883684249577448283

theorem tailTrace_7754919 : CollatzResearch.WordTrace tailWord_7754919 prefixEnd_7754919 3982000883684249577448283 := by
  unfold tailWord_7754919
  simp only [CollatzResearch.WordTrace]
  refine ⟨282845132592260372566675811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188563421728173581711117207 282845132592260372566675811)
  ·
    refine ⟨424267698888390558850013717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282845132592260372566675811 424267698888390558850013717)
    ·
      refine ⟨19887548385393307446094393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 424267698888390558850013717 19887548385393307446094393)
      ·
        refine ⟨14915661289044980584570795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19887548385393307446094393 14915661289044980584570795)
        ·
          refine ⟨22373491933567470876856193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14915661289044980584570795 22373491933567470876856193)
          ·
            refine ⟨16780118950175603157642145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22373491933567470876856193 16780118950175603157642145)
            ·
              refine ⟨12585089212631702368231609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16780118950175603157642145 12585089212631702368231609)
              ·
                refine ⟨9438816909473776776173707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12585089212631702368231609 9438816909473776776173707)
                ·
                  refine ⟨14158225364210665164260561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438816909473776776173707 14158225364210665164260561)
                  ·
                    refine ⟨10618669023157998873195421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14158225364210665164260561 10618669023157998873195421)
                    ·
                      refine ⟨3982000883684249577448283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10618669023157998873195421 3982000883684249577448283)
                      ·
                        rfl

theorem cell23_7754919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_7754919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754919 prefixEnd_7754919 := by exact prefixLift 7754919
  have htrace : WordTrace (prefixWord ++ tailWord_7754919) baseStart_7754919 baseEnd_7754919 := by
    simpa [prefixWord, tailWord_7754919, baseEnd_7754919] using wordTrace_append hprefix tailTrace_7754919
  have hstable : (prefixWord ++ tailWord_7754919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754919).length < 2 ^ (prefixWord ++ tailWord_7754919).sum := by decide
  have hdescent : baseEnd_7754919 < baseStart_7754919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754922 : List Nat := [3, 1, 5, 1, 1, 1, 4, 7]
def baseStart_7754922 : Nat := 118140960795 + 7754922 * 2 ^ 59
def prefixEnd_7754922 : Nat := 4983230072969 + 3 ^ 40 * 7754922 * 2
def baseEnd_7754922 : Nat := 147481571263933817248547

theorem tailTrace_7754922 : CollatzResearch.WordTrace tailWord_7754922 prefixEnd_7754922 147481571263933817248547 := by
  unfold tailWord_7754922
  simp only [CollatzResearch.WordTrace]
  refine ⟨70711310502812376019758755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188563494674166336052690013 70711310502812376019758755)
  ·
    refine ⟨106066965754218564029638133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70711310502812376019758755 106066965754218564029638133)
    ·
      refine ⟨9943778039457990377778575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106066965754218564029638133 9943778039457990377778575)
      ·
        refine ⟨14915667059186985566667863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9943778039457990377778575 14915667059186985566667863)
        ·
          refine ⟨22373500588780478350001795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14915667059186985566667863 22373500588780478350001795)
          ·
            refine ⟨33560250883170717525002693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22373500588780478350001795 33560250883170717525002693)
            ·
              refine ⟨6292547040594509535938005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33560250883170717525002693 6292547040594509535938005)
              ·
                refine ⟨147481571263933817248547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6292547040594509535938005 147481571263933817248547)
                ·
                  rfl

theorem cell23_7754922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_7754922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754922 prefixEnd_7754922 := by exact prefixLift 7754922
  have htrace : WordTrace (prefixWord ++ tailWord_7754922) baseStart_7754922 baseEnd_7754922 := by
    simpa [prefixWord, tailWord_7754922, baseEnd_7754922] using wordTrace_append hprefix tailTrace_7754922
  have hstable : (prefixWord ++ tailWord_7754922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754922).length < 2 ^ (prefixWord ++ tailWord_7754922).sum := by decide
  have hdescent : baseEnd_7754922 < baseStart_7754922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754938 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_7754938 : Nat := 118140960795 + 7754938 * 2 ^ 59
def prefixEnd_7754938 : Nat := 4983230072969 + 3 ^ 40 * 7754938 * 2
def baseEnd_7754938 : Nat := 3982010639816685003110695

theorem tailTrace_7754938 : CollatzResearch.WordTrace tailWord_7754938 prefixEnd_7754938 3982010639816685003110695 := by
  unfold tailWord_7754938
  simp only [CollatzResearch.WordTrace]
  refine ⟨70711456394797884702904367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188563883719461025874411645 70711456394797884702904367)
  ·
    refine ⟨106067184592196827054356551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70711456394797884702904367 106067184592196827054356551)
    ·
      refine ⟨159100776888295240581534827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106067184592196827054356551 159100776888295240581534827)
      ·
        refine ⟨238651165332442860872302241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159100776888295240581534827 238651165332442860872302241)
        ·
          refine ⟨178988373999332145654226681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238651165332442860872302241 178988373999332145654226681)
          ·
            refine ⟨134241280499499109240670011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178988373999332145654226681 134241280499499109240670011)
            ·
              refine ⟨201361920749248663861005017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134241280499499109240670011 201361920749248663861005017)
              ·
                refine ⟨151021440561936497895753763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201361920749248663861005017 151021440561936497895753763)
                ·
                  refine ⟨226532160842904746843630645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151021440561936497895753763 226532160842904746843630645)
                  ·
                    refine ⟨21237390079022320016590373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226532160842904746843630645 21237390079022320016590373)
                    ·
                      refine ⟨3982010639816685003110695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21237390079022320016590373 3982010639816685003110695)
                      ·
                        rfl

theorem cell23_7754938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_7754938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754938 prefixEnd_7754938 := by exact prefixLift 7754938
  have htrace : WordTrace (prefixWord ++ tailWord_7754938) baseStart_7754938 baseEnd_7754938 := by
    simpa [prefixWord, tailWord_7754938, baseEnd_7754938] using wordTrace_append hprefix tailTrace_7754938
  have hstable : (prefixWord ++ tailWord_7754938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754938).length < 2 ^ (prefixWord ++ tailWord_7754938).sum := by decide
  have hdescent : baseEnd_7754938 < baseStart_7754938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754955 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 5, 4, 2]
def baseStart_7754955 : Nat := 118140960795 + 7754955 * 2 ^ 59
def prefixEnd_7754955 : Nat := 4983230072969 + 3 ^ 40 * 7754955 * 2
def baseEnd_7754955 : Nat := 3982019368987811436598117

theorem tailTrace_7754955 : CollatzResearch.WordTrace tailWord_7754955 prefixEnd_7754955 3982019368987811436598117 := by
  unfold tailWord_7754955
  simp only [CollatzResearch.WordTrace]
  refine ⟨282846445620129950714986319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188564297080086633809990879 282846445620129950714986319)
  ·
    refine ⟨424269668430194926072479479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282846445620129950714986319 424269668430194926072479479)
    ·
      refine ⟨636404502645292389108719219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424269668430194926072479479 636404502645292389108719219)
      ·
        refine ⟨954606753967938583663078829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636404502645292389108719219 954606753967938583663078829)
        ·
          refine ⟨357977532737976968873654561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 954606753967938583663078829 357977532737976968873654561)
          ·
            refine ⟨268483149553482726655240921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357977532737976968873654561 268483149553482726655240921)
            ·
              refine ⟨201362362165112044991430691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268483149553482726655240921 201362362165112044991430691)
              ·
                refine ⟨302043543247668067487146037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201362362165112044991430691 302043543247668067487146037)
                ·
                  refine ⟨28316582179468881326919941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302043543247668067487146037 28316582179468881326919941)
                  ·
                    refine ⟨5309359158650415248797489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28316582179468881326919941 5309359158650415248797489)
                    ·
                      refine ⟨3982019368987811436598117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309359158650415248797489 3982019368987811436598117)
                      ·
                        rfl

theorem cell23_7754955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4, 2].length) (baseStart_7754955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754955 prefixEnd_7754955 := by exact prefixLift 7754955
  have htrace : WordTrace (prefixWord ++ tailWord_7754955) baseStart_7754955 baseEnd_7754955 := by
    simpa [prefixWord, tailWord_7754955, baseEnd_7754955] using wordTrace_append hprefix tailTrace_7754955
  have hstable : (prefixWord ++ tailWord_7754955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754955).length < 2 ^ (prefixWord ++ tailWord_7754955).sum := by decide
  have hdescent : baseEnd_7754955 < baseStart_7754955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7754989 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_7754989 : Nat := 118140960795 + 7754989 * 2 ^ 59
def prefixEnd_7754989 : Nat := 4983230072969 + 3 ^ 40 * 7754989 * 2
def baseEnd_7754989 : Nat := 3982036827330064303572961

theorem tailTrace_7754989 : CollatzResearch.WordTrace tailWord_7754989 prefixEnd_7754989 3982036827330064303572961 := by
  unfold tailWord_7754989
  simp only [CollatzResearch.WordTrace]
  refine ⟨282847685702006774521724021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188565123801337849681149347 282847685702006774521724021)
  ·
    refine ⟨26516970534563135111411627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282847685702006774521724021 26516970534563135111411627)
    ·
      refine ⟨39775455801844702667117441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26516970534563135111411627 39775455801844702667117441)
      ·
        refine ⟨29831591851383527000338081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39775455801844702667117441 29831591851383527000338081)
        ·
          refine ⟨22373693888537645250253561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29831591851383527000338081 22373693888537645250253561)
          ·
            refine ⟨16780270416403233937690171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22373693888537645250253561 16780270416403233937690171)
            ·
              refine ⟨25170405624604850906535257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16780270416403233937690171 25170405624604850906535257)
              ·
                refine ⟨18877804218453638179901443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25170405624604850906535257 18877804218453638179901443)
                ·
                  refine ⟨28316706327680457269852165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18877804218453638179901443 28316706327680457269852165)
                  ·
                    refine ⟨5309382436440085738097281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28316706327680457269852165 5309382436440085738097281)
                    ·
                      refine ⟨3982036827330064303572961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309382436440085738097281 3982036827330064303572961)
                      ·
                        rfl

theorem cell23_7754989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_7754989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7754989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7754989 prefixEnd_7754989 := by exact prefixLift 7754989
  have htrace : WordTrace (prefixWord ++ tailWord_7754989) baseStart_7754989 baseEnd_7754989 := by
    simpa [prefixWord, tailWord_7754989, baseEnd_7754989] using wordTrace_append hprefix tailTrace_7754989
  have hstable : (prefixWord ++ tailWord_7754989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7754989).length < 2 ^ (prefixWord ++ tailWord_7754989).sum := by decide
  have hdescent : baseEnd_7754989 < baseStart_7754989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7754989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755006 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7755006 : Nat := 118140960795 + 7755006 * 2 ^ 59
def prefixEnd_7755006 : Nat := 4983230072969 + 3 ^ 40 * 7755006 * 2
def baseEnd_7755006 : Nat := 3982045556501190737060383

theorem tailTrace_7755006 : CollatzResearch.WordTrace tailWord_7755006 prefixEnd_7755006 3982045556501190737060383 := by
  unfold tailWord_7755006
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356038217868148303136609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188565537161963457616728581 35356038217868148303136609)
  ·
    refine ⟨26517028663401111227352457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35356038217868148303136609 26517028663401111227352457)
    ·
      refine ⟨19887771497550833420514343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26517028663401111227352457 19887771497550833420514343)
      ·
        refine ⟨29831657246326250130771515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19887771497550833420514343 29831657246326250130771515)
        ·
          refine ⟨44747485869489375196157273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29831657246326250130771515 44747485869489375196157273)
          ·
            refine ⟨33560614402117031397117955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44747485869489375196157273 33560614402117031397117955)
            ·
              refine ⟨50340921603175547095676933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33560614402117031397117955 50340921603175547095676933)
              ·
                refine ⟨9438922800595415080439425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50340921603175547095676933 9438922800595415080439425)
                ·
                  refine ⟨7079192100446561310329569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9438922800595415080439425 7079192100446561310329569)
                  ·
                    refine ⟨5309394075334920982747177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079192100446561310329569 5309394075334920982747177)
                    ·
                      refine ⟨3982045556501190737060383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309394075334920982747177 3982045556501190737060383)
                      ·
                        rfl

theorem cell23_7755006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7755006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755006 prefixEnd_7755006 := by exact prefixLift 7755006
  have htrace : WordTrace (prefixWord ++ tailWord_7755006) baseStart_7755006 baseEnd_7755006 := by
    simpa [prefixWord, tailWord_7755006, baseEnd_7755006] using wordTrace_append hprefix tailTrace_7755006
  have hstable : (prefixWord ++ tailWord_7755006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755006).length < 2 ^ (prefixWord ++ tailWord_7755006).sum := by decide
  have hdescent : baseEnd_7755006 < baseStart_7755006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755008 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 3, 7]
def baseStart_7755008 : Nat := 118140960795 + 7755008 * 2 ^ 59
def prefixEnd_7755008 : Nat := 4983230072969 + 3 ^ 40 * 7755008 * 2
def baseEnd_7755008 : Nat := 1327348861154166576411791

theorem tailTrace_7755008 : CollatzResearch.WordTrace tailWord_7755008 prefixEnd_7755008 1327348861154166576411791 := by
  unfold tailWord_7755008
  simp only [CollatzResearch.WordTrace]
  refine ⟨141424189344468970383332839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188565585792625293844443785 141424189344468970383332839)
  ·
    refine ⟨212136284016703455574999259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141424189344468970383332839 212136284016703455574999259)
    ·
      refine ⟨318204426025055183362498889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212136284016703455574999259 318204426025055183362498889)
      ·
        refine ⟨238653319518791387521874167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318204426025055183362498889 238653319518791387521874167)
        ·
          refine ⟨357979979278187081282811251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238653319518791387521874167 357979979278187081282811251)
          ·
            refine ⟨536969968917280621924216877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357979979278187081282811251 536969968917280621924216877)
            ·
              refine ⟨201363738343980233221581329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536969968917280621924216877 201363738343980233221581329)
              ·
                refine ⟨151022803757985174916185997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201363738343980233221581329 151022803757985174916185997)
                ·
                  refine ⟨56633551409244440593569749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151022803757985174916185997 56633551409244440593569749)
                  ·
                    refine ⟨1327348861154166576411791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56633551409244440593569749 1327348861154166576411791)
                    ·
                      rfl

theorem cell23_7755008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_7755008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755008 prefixEnd_7755008 := by exact prefixLift 7755008
  have htrace : WordTrace (prefixWord ++ tailWord_7755008) baseStart_7755008 baseEnd_7755008 := by
    simpa [prefixWord, tailWord_7755008, baseEnd_7755008] using wordTrace_append hprefix tailTrace_7755008
  have hstable : (prefixWord ++ tailWord_7755008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755008).length < 2 ^ (prefixWord ++ tailWord_7755008).sum := by decide
  have hdescent : baseEnd_7755008 < baseStart_7755008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755022 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_7755022 : Nat := 118140960795 + 7755022 * 2 ^ 59
def prefixEnd_7755022 : Nat := 4983230072969 + 3 ^ 40 * 7755022 * 2
def baseEnd_7755022 : Nat := 3982053772191662674460309

theorem tailTrace_7755022 : CollatzResearch.WordTrace tailWord_7755022 prefixEnd_7755022 3982053772191662674460309 := by
  unfold tailWord_7755022
  simp only [CollatzResearch.WordTrace]
  refine ⟨35356111163860902644709415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188565926207258147438450213 35356111163860902644709415)
  ·
    refine ⟨53034166745791353967064123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35356111163860902644709415 53034166745791353967064123)
    ·
      refine ⟨79551250118687030950596185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53034166745791353967064123 79551250118687030950596185)
      ·
        refine ⟨59663437589015273212947139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79551250118687030950596185 59663437589015273212947139)
        ·
          refine ⟨89495156383522909819420709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59663437589015273212947139 89495156383522909819420709)
          ·
            refine ⟨16780341821910545591141383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89495156383522909819420709 16780341821910545591141383)
            ·
              refine ⟨25170512732865818386712075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16780341821910545591141383 25170512732865818386712075)
              ·
                refine ⟨37755769099298727580068113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25170512732865818386712075 37755769099298727580068113)
                ·
                  refine ⟨28316826824474045685051085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37755769099298727580068113 28316826824474045685051085)
                  ·
                    refine ⟨10618810059177767131894157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28316826824474045685051085 10618810059177767131894157)
                    ·
                      refine ⟨3982053772191662674460309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10618810059177767131894157 3982053772191662674460309)
                      ·
                        rfl

theorem cell23_7755022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_7755022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755022 prefixEnd_7755022 := by exact prefixLift 7755022
  have htrace : WordTrace (prefixWord ++ tailWord_7755022) baseStart_7755022 baseEnd_7755022 := by
    simpa [prefixWord, tailWord_7755022, baseEnd_7755022] using wordTrace_append hprefix tailTrace_7755022
  have hstable : (prefixWord ++ tailWord_7755022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755022).length < 2 ^ (prefixWord ++ tailWord_7755022).sum := by decide
  have hdescent : baseEnd_7755022 < baseStart_7755022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755042 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_7755042 : Nat := 118140960795 + 7755042 * 2 ^ 59
def prefixEnd_7755042 : Nat := 4983230072969 + 3 ^ 40 * 7755042 * 2
def baseEnd_7755042 : Nat := 1327354680601584198736739

theorem tailTrace_7755042 : CollatzResearch.WordTrace tailWord_7755042 prefixEnd_7755042 1327354680601584198736739 := by
  unfold tailWord_7755042
  simp only [CollatzResearch.WordTrace]
  refine ⟨70712404692703691143350845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188566412513876509715602253 70712404692703691143350845)
  ·
    refine ⟨26517151759763884178756567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70712404692703691143350845 26517151759763884178756567)
    ·
      refine ⟨39775727639645826268134851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26517151759763884178756567 39775727639645826268134851)
      ·
        refine ⟨59663591459468739402202277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39775727639645826268134851 59663591459468739402202277)
        ·
          refine ⟨11186923398650388637912927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59663591459468739402202277 11186923398650388637912927)
          ·
            refine ⟨16780385097975582956869391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11186923398650388637912927 16780385097975582956869391)
            ·
              refine ⟨25170577646963374435304087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16780385097975582956869391 25170577646963374435304087)
              ·
                refine ⟨37755866470445061652956131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25170577646963374435304087 37755866470445061652956131)
                ·
                  refine ⟨56633799705667592479434197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37755866470445061652956131 56633799705667592479434197)
                  ·
                    refine ⟨1327354680601584198736739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56633799705667592479434197 1327354680601584198736739)
                    ·
                      rfl

theorem cell23_7755042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_7755042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755042 prefixEnd_7755042 := by exact prefixLift 7755042
  have htrace : WordTrace (prefixWord ++ tailWord_7755042) baseStart_7755042 baseEnd_7755042 := by
    simpa [prefixWord, tailWord_7755042, baseEnd_7755042] using wordTrace_append hprefix tailTrace_7755042
  have hstable : (prefixWord ++ tailWord_7755042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755042).length < 2 ^ (prefixWord ++ tailWord_7755042).sum := by decide
  have hdescent : baseEnd_7755042 < baseStart_7755042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755055 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 7, 4]
def baseStart_7755055 : Nat := 118140960795 + 7755055 * 2 ^ 59
def prefixEnd_7755055 : Nat := 4983230072969 + 3 ^ 40 * 7755055 * 2
def baseEnd_7755055 : Nat := 1327356905684420348449219

theorem tailTrace_7755055 : CollatzResearch.WordTrace tailWord_7755055 prefixEnd_7755055 1327356905684420348449219 := by
  unfold tailWord_7755055
  simp only [CollatzResearch.WordTrace]
  refine ⟨282850092919767667793626619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188566728613178445195751079 282850092919767667793626619)
  ·
    refine ⟨424275139379651501690439929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282850092919767667793626619 424275139379651501690439929)
    ·
      refine ⟨318206354534738626267829947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424275139379651501690439929 318206354534738626267829947)
      ·
        refine ⟨477309531802107939401744921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318206354534738626267829947 477309531802107939401744921)
        ·
          refine ⟨357982148851580954551308691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477309531802107939401744921 357982148851580954551308691)
          ·
            refine ⟨536973223277371431826963037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357982148851580954551308691 536973223277371431826963037)
            ·
              refine ⟨201364958729014286935111139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536973223277371431826963037 201364958729014286935111139)
              ·
                refine ⟨302047438093521430402666709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201364958729014286935111139 302047438093521430402666709)
                ·
                  refine ⟨7079236830316908525062501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 302047438093521430402666709 7079236830316908525062501)
                  ·
                    refine ⟨1327356905684420348449219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079236830316908525062501 1327356905684420348449219)
                    ·
                      rfl

theorem cell23_7755055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_7755055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755055 prefixEnd_7755055 := by exact prefixLift 7755055
  have htrace : WordTrace (prefixWord ++ tailWord_7755055) baseStart_7755055 baseEnd_7755055 := by
    simpa [prefixWord, tailWord_7755055, baseEnd_7755055] using wordTrace_append hprefix tailTrace_7755055
  have hstable : (prefixWord ++ tailWord_7755055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755055).length < 2 ^ (prefixWord ++ tailWord_7755055).sum := by decide
  have hdescent : baseEnd_7755055 < baseStart_7755055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755072 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 3, 4]
def baseStart_7755072 : Nat := 118140960795 + 7755072 * 2 ^ 59
def prefixEnd_7755072 : Nat := 4983230072969 + 3 ^ 40 * 7755072 * 2
def baseEnd_7755072 : Nat := 1327359815408129159611693

theorem tailTrace_7755072 : CollatzResearch.WordTrace tailWord_7755072 prefixEnd_7755072 1327359815408129159611693 := by
  unfold tailWord_7755072
  simp only [CollatzResearch.WordTrace]
  refine ⟨141425356480353039848497735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188567141973804053131330313 141425356480353039848497735)
  ·
    refine ⟨212138034720529559772746603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141425356480353039848497735 212138034720529559772746603)
    ·
      refine ⟨318207052080794339659119905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212138034720529559772746603 318207052080794339659119905)
      ·
        refine ⟨238655289060595754744339929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318207052080794339659119905 238655289060595754744339929)
        ·
          refine ⟨178991466795446816058254947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238655289060595754744339929 178991466795446816058254947)
          ·
            refine ⟨268487200193170224087382421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178991466795446816058254947 268487200193170224087382421)
            ·
              refine ⟨12585337509054854254096051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268487200193170224087382421 12585337509054854254096051)
              ·
                refine ⟨18878006263582281381144077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12585337509054854254096051 18878006263582281381144077)
                ·
                  refine ⟨7079252348843355517929029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18878006263582281381144077 7079252348843355517929029)
                  ·
                    refine ⟨1327359815408129159611693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079252348843355517929029 1327359815408129159611693)
                    ·
                      rfl

theorem cell23_7755072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 4].length) (baseStart_7755072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755072 prefixEnd_7755072 := by exact prefixLift 7755072
  have htrace : WordTrace (prefixWord ++ tailWord_7755072) baseStart_7755072 baseEnd_7755072 := by
    simpa [prefixWord, tailWord_7755072, baseEnd_7755072] using wordTrace_append hprefix tailTrace_7755072
  have hstable : (prefixWord ++ tailWord_7755072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755072).length < 2 ^ (prefixWord ++ tailWord_7755072).sum := by decide
  have hdescent : baseEnd_7755072 < baseStart_7755072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755129 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 3]
def baseStart_7755129 : Nat := 118140960795 + 7755129 * 2 ^ 59
def prefixEnd_7755129 : Nat := 4983230072969 + 3 ^ 40 * 7755129 * 2
def baseEnd_7755129 : Nat := 3982108714621693755822317

theorem tailTrace_7755129 : CollatzResearch.WordTrace tailWord_7755129 prefixEnd_7755129 3982108714621693755822317 := by
  unfold tailWord_7755129
  simp only [CollatzResearch.WordTrace]
  refine ⟨282852791921499578431820441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188568527947666385621213627 282852791921499578431820441)
  ·
    refine ⟨212139593941124683823865331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282852791921499578431820441 212139593941124683823865331)
    ·
      refine ⟨318209390911687025735797997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212139593941124683823865331 318209390911687025735797997)
      ·
        refine ⟨119328521591882634650924249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318209390911687025735797997 119328521591882634650924249)
        ·
          refine ⟨89496391193911975988193187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119328521591882634650924249 89496391193911975988193187)
          ·
            refine ⟨134244586790867963982289781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89496391193911975988193187 134244586790867963982289781)
            ·
              refine ⟨12585430011643871623339667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134244586790867963982289781 12585430011643871623339667)
              ·
                refine ⟨18878145017465807435009501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12585430011643871623339667 18878145017465807435009501)
                ·
                  refine ⟨7079304381549677788128563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18878145017465807435009501 7079304381549677788128563)
                  ·
                    refine ⟨10618956572324516682192845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7079304381549677788128563 10618956572324516682192845)
                    ·
                      refine ⟨3982108714621693755822317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10618956572324516682192845 3982108714621693755822317)
                      ·
                        rfl

theorem cell23_7755129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_7755129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755129 prefixEnd_7755129 := by exact prefixLift 7755129
  have htrace : WordTrace (prefixWord ++ tailWord_7755129) baseStart_7755129 baseEnd_7755129 := by
    simpa [prefixWord, tailWord_7755129, baseEnd_7755129] using wordTrace_append hprefix tailTrace_7755129
  have hstable : (prefixWord ++ tailWord_7755129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755129).length < 2 ^ (prefixWord ++ tailWord_7755129).sum := by decide
  have hdescent : baseEnd_7755129 < baseStart_7755129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755156 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_7755156 : Nat := 118140960795 + 7755156 * 2 ^ 59
def prefixEnd_7755156 : Nat := 4983230072969 + 3 ^ 40 * 7755156 * 2
def baseEnd_7755156 : Nat := 3982122578599365150184693

theorem tailTrace_7755156 : CollatzResearch.WordTrace tailWord_7755156 prefixEnd_7755156 3982122578599365150184693 := by
  unfold tailWord_7755156
  simp only [CollatzResearch.WordTrace]
  refine ⟨141426888346200881021526661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188569184461601174695368881 141426888346200881021526661)
  ·
    refine ⟨26517541564912665191536249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141426888346200881021526661 26517541564912665191536249)
    ·
      refine ⟨19888156173684498893652187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26517541564912665191536249 19888156173684498893652187)
      ·
        refine ⟨29832234260526748340478281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19888156173684498893652187 29832234260526748340478281)
        ·
          refine ⟨22374175695395061255358711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29832234260526748340478281 22374175695395061255358711)
          ·
            refine ⟨33561263543092591883038067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22374175695395061255358711 33561263543092591883038067)
            ·
              refine ⟨50341895314638887824557101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33561263543092591883038067 50341895314638887824557101)
              ·
                refine ⟨18878210742989582934208913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50341895314638887824557101 18878210742989582934208913)
                ·
                  refine ⟨14158658057242187200656685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18878210742989582934208913 14158658057242187200656685)
                  ·
                    refine ⟨5309496771465820200246257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14158658057242187200656685 5309496771465820200246257)
                    ·
                      refine ⟨3982122578599365150184693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309496771465820200246257 3982122578599365150184693)
                      ·
                        rfl

theorem cell23_7755156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_7755156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755156 prefixEnd_7755156 := by exact prefixLift 7755156
  have htrace : WordTrace (prefixWord ++ tailWord_7755156) baseStart_7755156 baseEnd_7755156 := by
    simpa [prefixWord, tailWord_7755156, baseEnd_7755156] using wordTrace_append hprefix tailTrace_7755156
  have hstable : (prefixWord ++ tailWord_7755156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755156).length < 2 ^ (prefixWord ++ tailWord_7755156).sum := by decide
  have hdescent : baseEnd_7755156 < baseStart_7755156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755162 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_7755162 : Nat := 118140960795 + 7755162 * 2 ^ 59
def prefixEnd_7755162 : Nat := 4983230072969 + 3 ^ 40 * 7755162 * 2
def baseEnd_7755162 : Nat := 1327375219827764042236555

theorem tailTrace_7755162 : CollatzResearch.WordTrace tailWord_7755162 prefixEnd_7755162 1327375219827764042236555 := by
  unfold tailWord_7755162
  simp only [CollatzResearch.WordTrace]
  refine ⟨70713498882595006266942935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188569330353586683378514493 70713498882595006266942935)
  ·
    refine ⟨106070248323892509400414403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70713498882595006266942935 106070248323892509400414403)
    ·
      refine ⟨159105372485838764100621605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106070248323892509400414403 159105372485838764100621605)
      ·
        refine ⟨29832257341094768268866551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159105372485838764100621605 29832257341094768268866551)
        ·
          refine ⟨44748386011642152403299827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29832257341094768268866551 44748386011642152403299827)
          ·
            refine ⟨67122579017463228604949741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44748386011642152403299827 67122579017463228604949741)
            ·
              refine ⟨25170967131548710726856153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67122579017463228604949741 25170967131548710726856153)
              ·
                refine ⟨18878225348661533045142115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25170967131548710726856153 18878225348661533045142115)
                ·
                  refine ⟨28317338022992299567713173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18878225348661533045142115 28317338022992299567713173)
                  ·
                    refine ⟨1327375219827764042236555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28317338022992299567713173 1327375219827764042236555)
                    ·
                      rfl

theorem cell23_7755162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_7755162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755162 prefixEnd_7755162 := by exact prefixLift 7755162
  have htrace : WordTrace (prefixWord ++ tailWord_7755162) baseStart_7755162 baseEnd_7755162 := by
    simpa [prefixWord, tailWord_7755162, baseEnd_7755162] using wordTrace_append hprefix tailTrace_7755162
  have hstable : (prefixWord ++ tailWord_7755162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755162).length < 2 ^ (prefixWord ++ tailWord_7755162).sum := by decide
  have hdescent : baseEnd_7755162 < baseStart_7755162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755189 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_7755189 : Nat := 118140960795 + 7755189 * 2 ^ 59
def prefixEnd_7755189 : Nat := 4983230072969 + 3 ^ 40 * 7755189 * 2
def baseEnd_7755189 : Nat := 3982139523460963521072041

theorem tailTrace_7755189 : CollatzResearch.WordTrace tailWord_7755189 prefixEnd_7755189 3982139523460963521072041 := by
  unfold tailWord_7755189
  simp only [CollatzResearch.WordTrace]
  refine ⟨282854980301282208679004621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188569986867521472452669747 282854980301282208679004621)
  ·
    refine ⟨106070617612980828254626733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282854980301282208679004621 106070617612980828254626733)
    ·
      refine ⟨39776481604867810595485025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106070617612980828254626733 39776481604867810595485025)
      ·
        refine ⟨29832361203650857946613769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39776481604867810595485025 29832361203650857946613769)
        ·
          refine ⟨22374270902738143459960327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29832361203650857946613769 22374270902738143459960327)
          ·
            refine ⟨33561406354107215189940491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22374270902738143459960327 33561406354107215189940491)
            ·
              refine ⟨50342109531160822784910737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33561406354107215189940491 50342109531160822784910737)
              ·
                refine ⟨37756582148370617088683053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50342109531160822784910737 37756582148370617088683053)
                ·
                  refine ⟨14158718305638981408256145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37756582148370617088683053 14158718305638981408256145)
                  ·
                    refine ⟨10619038729229236056192109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14158718305638981408256145 10619038729229236056192109)
                    ·
                      refine ⟨3982139523460963521072041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619038729229236056192109 3982139523460963521072041)
                      ·
                        rfl

theorem cell23_7755189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_7755189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755189 prefixEnd_7755189 := by exact prefixLift 7755189
  have htrace : WordTrace (prefixWord ++ tailWord_7755189) baseStart_7755189 baseEnd_7755189 := by
    simpa [prefixWord, tailWord_7755189, baseEnd_7755189] using wordTrace_append hprefix tailTrace_7755189
  have hstable : (prefixWord ++ tailWord_7755189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755189).length < 2 ^ (prefixWord ++ tailWord_7755189).sum := by decide
  have hdescent : baseEnd_7755189 < baseStart_7755189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755220 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 1, 1, 4]
def baseStart_7755220 : Nat := 118140960795 + 7755220 * 2 ^ 59
def prefixEnd_7755220 : Nat := 4983230072969 + 3 ^ 40 * 7755220 * 2
def baseEnd_7755220 : Nat := 3982155441361252899784399

theorem tailTrace_7755220 : CollatzResearch.WordTrace tailWord_7755220 prefixEnd_7755220 3982155441361252899784399 := by
  unfold tailWord_7755220
  simp only [CollatzResearch.WordTrace]
  refine ⟨141428055482084950486691557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188570740642779933982255409 141428055482084950486691557)
  ·
    refine ⟨26517760402890928216254667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141428055482084950486691557 26517760402890928216254667)
    ·
      refine ⟨39776640604336392324382001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26517760402890928216254667 39776640604336392324382001)
      ·
        refine ⟨29832480453252294243286501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39776640604336392324382001 29832480453252294243286501)
        ·
          refine ⟨5593590084984805170616219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29832480453252294243286501 5593590084984805170616219)
          ·
            refine ⟨8390385127477207755924329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593590084984805170616219 8390385127477207755924329)
            ·
              refine ⟨6292788845607905816943247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8390385127477207755924329 6292788845607905816943247)
              ·
                refine ⟨9439183268411858725414871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292788845607905816943247 9439183268411858725414871)
                ·
                  refine ⟨14158774902617788088122307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9439183268411858725414871 14158774902617788088122307)
                  ·
                    refine ⟨21238162353926682132183461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14158774902617788088122307 21238162353926682132183461)
                    ·
                      refine ⟨3982155441361252899784399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21238162353926682132183461 3982155441361252899784399)
                      ·
                        rfl

theorem cell23_7755220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_7755220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755220 prefixEnd_7755220 := by exact prefixLift 7755220
  have htrace : WordTrace (prefixWord ++ tailWord_7755220) baseStart_7755220 baseEnd_7755220 := by
    simpa [prefixWord, tailWord_7755220, baseEnd_7755220] using wordTrace_append hprefix tailTrace_7755220
  have hstable : (prefixWord ++ tailWord_7755220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755220).length < 2 ^ (prefixWord ++ tailWord_7755220).sum := by decide
  have hdescent : baseEnd_7755220 < baseStart_7755220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755253 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7755253 : Nat := 118140960795 + 7755253 * 2 ^ 59
def prefixEnd_7755253 : Nat := 4983230072969 + 3 ^ 40 * 7755253 * 2
def baseEnd_7755253 : Nat := 3982172386222851270671747

theorem tailTrace_7755253 : CollatzResearch.WordTrace tailWord_7755253 prefixEnd_7755253 3982172386222851270671747 := by
  unfold tailWord_7755253
  simp only [CollatzResearch.WordTrace]
  refine ⟨282857314573050347609334413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188571543048700231739556275 282857314573050347609334413)
  ·
    refine ⟨106071492964893880353500405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282857314573050347609334413 106071492964893880353500405)
    ·
      refine ⟨9944202465458801283140663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106071492964893880353500405 9944202465458801283140663)
      ·
        refine ⟨14916303698188201924710995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944202465458801283140663 14916303698188201924710995)
        ·
          refine ⟨22374455547282302887066493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916303698188201924710995 22374455547282302887066493)
          ·
            refine ⟨8390420830230863582649935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22374455547282302887066493 8390420830230863582649935)
            ·
              refine ⟨12585631245346295373974903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8390420830230863582649935 12585631245346295373974903)
              ·
                refine ⟨18878446868019443060962355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12585631245346295373974903 18878446868019443060962355)
                ·
                  refine ⟨28317670302029164591443533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18878446868019443060962355 28317670302029164591443533)
                  ·
                    refine ⟨10619126363260936721791325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28317670302029164591443533 10619126363260936721791325)
                    ·
                      refine ⟨3982172386222851270671747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619126363260936721791325 3982172386222851270671747)
                      ·
                        rfl

theorem cell23_7755253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7755253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755253 prefixEnd_7755253 := by exact prefixLift 7755253
  have htrace : WordTrace (prefixWord ++ tailWord_7755253) baseStart_7755253 baseEnd_7755253 := by
    simpa [prefixWord, tailWord_7755253, baseEnd_7755253] using wordTrace_append hprefix tailTrace_7755253
  have hstable : (prefixWord ++ tailWord_7755253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755253).length < 2 ^ (prefixWord ++ tailWord_7755253).sum := by decide
  have hdescent : baseEnd_7755253 < baseStart_7755253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755272 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_7755272 : Nat := 118140960795 + 7755272 * 2 ^ 59
def prefixEnd_7755272 : Nat := 4983230072969 + 3 ^ 40 * 7755272 * 2
def baseEnd_7755272 : Nat := 3982182142355286696334159

theorem tailTrace_7755272 : CollatzResearch.WordTrace tailWord_7755272 prefixEnd_7755272 3982182142355286696334159 := by
  unfold tailWord_7755272
  simp only [CollatzResearch.WordTrace]
  refine ⟨141429003779990756927138035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188572005039987675902850713 141429003779990756927138035)
  ·
    refine ⟨212143505669986135390707053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141429003779990756927138035 212143505669986135390707053)
    ·
      refine ⟨79553814626244800771515145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212143505669986135390707053 79553814626244800771515145)
      ·
        refine ⟨59665360969683600578636359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79553814626244800771515145 59665360969683600578636359)
        ·
          refine ⟨89498041454525400867954539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59665360969683600578636359 89498041454525400867954539)
          ·
            refine ⟨134247062181788101301931809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89498041454525400867954539 134247062181788101301931809)
            ·
              refine ⟨100685296636341075976448857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134247062181788101301931809 100685296636341075976448857)
              ·
                refine ⟨75513972477255806982336643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100685296636341075976448857 75513972477255806982336643)
                ·
                  refine ⟨113270958715883710473504965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75513972477255806982336643 113270958715883710473504965)
                  ·
                    refine ⟨21238304759228195713782181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113270958715883710473504965 21238304759228195713782181)
                    ·
                      refine ⟨3982182142355286696334159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21238304759228195713782181 3982182142355286696334159)
                      ·
                        rfl

theorem cell23_7755272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_7755272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755272 prefixEnd_7755272 := by exact prefixLift 7755272
  have htrace : WordTrace (prefixWord ++ tailWord_7755272) baseStart_7755272 baseEnd_7755272 := by
    simpa [prefixWord, tailWord_7755272, baseEnd_7755272] using wordTrace_append hprefix tailTrace_7755272
  have hstable : (prefixWord ++ tailWord_7755272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755272).length < 2 ^ (prefixWord ++ tailWord_7755272).sum := by decide
  have hdescent : baseEnd_7755272 < baseStart_7755272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755292 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_7755292 : Nat := 118140960795 + 7755292 * 2 ^ 59
def prefixEnd_7755292 : Nat := 4983230072969 + 3 ^ 40 * 7755292 * 2
def baseEnd_7755292 : Nat := 3982192411968376618084067

theorem tailTrace_7755292 : CollatzResearch.WordTrace tailWord_7755292 prefixEnd_7755292 3982192411968376618084067 := by
  unfold tailWord_7755292
  simp only [CollatzResearch.WordTrace]
  refine ⟨141429368509954528635002065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188572491346606038180002753 141429368509954528635002065)
  ·
    refine ⟨106072026382465896476251549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141429368509954528635002065 106072026382465896476251549)
    ·
      refine ⟨39777009893424711178594331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106072026382465896476251549 39777009893424711178594331)
      ·
        refine ⟨59665514840137066767891497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39777009893424711178594331 59665514840137066767891497)
        ·
          refine ⟨44749136130102800075918623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59665514840137066767891497 44749136130102800075918623)
          ·
            refine ⟨67123704195154200113877935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44749136130102800075918623 67123704195154200113877935)
            ·
              refine ⟨100685556292731300170816903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67123704195154200113877935 100685556292731300170816903)
              ·
                refine ⟨151028334439096950256225355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100685556292731300170816903 151028334439096950256225355)
                ·
                  refine ⟨226542501658645425384338033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151028334439096950256225355 226542501658645425384338033)
                  ·
                    refine ⟨169906876243984069038253525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226542501658645425384338033 169906876243984069038253525)
                    ·
                      refine ⟨3982192411968376618084067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169906876243984069038253525 3982192411968376618084067)
                      ·
                        rfl

theorem cell23_7755292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_7755292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755292 prefixEnd_7755292 := by exact prefixLift 7755292
  have htrace : WordTrace (prefixWord ++ tailWord_7755292) baseStart_7755292 baseEnd_7755292 := by
    simpa [prefixWord, tailWord_7755292, baseEnd_7755292] using wordTrace_append hprefix tailTrace_7755292
  have hstable : (prefixWord ++ tailWord_7755292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755292).length < 2 ^ (prefixWord ++ tailWord_7755292).sum := by decide
  have hdescent : baseEnd_7755292 < baseStart_7755292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755293 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_7755293 : Nat := 118140960795 + 7755293 * 2 ^ 59
def prefixEnd_7755293 : Nat := 4983230072969 + 3 ^ 40 * 7755293 * 2
def baseEnd_7755293 : Nat := 3982192925449031114171563

theorem tailTrace_7755293 : CollatzResearch.WordTrace tailWord_7755293 prefixEnd_7755293 3982192925449031114171563 := by
  unfold tailWord_7755293
  simp only [CollatzResearch.WordTrace]
  refine ⟨282858773492905434440790533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188572515661936956293860355 282858773492905434440790533)
  ·
    refine ⟨53036020029919768957648225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282858773492905434440790533 53036020029919768957648225)
    ·
      refine ⟨39777015022439826718236169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53036020029919768957648225 39777015022439826718236169)
      ·
        refine ⟨29832761266829870038677127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39777015022439826718236169 29832761266829870038677127)
        ·
          refine ⟨44749141900244805058015691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29832761266829870038677127 44749141900244805058015691)
          ·
            refine ⟨67123712850367207587023537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44749141900244805058015691 67123712850367207587023537)
            ·
              refine ⟨50342784637775405690267653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67123712850367207587023537 50342784637775405690267653)
              ·
                refine ⟨9439272119582888566925185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50342784637775405690267653 9439272119582888566925185)
                ·
                  refine ⟨7079454089687166425193889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9439272119582888566925185 7079454089687166425193889)
                  ·
                    refine ⟨5309590567265374818895417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079454089687166425193889 5309590567265374818895417)
                    ·
                      refine ⟨3982192925449031114171563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309590567265374818895417 3982192925449031114171563)
                      ·
                        rfl

theorem cell23_7755293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_7755293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755293 prefixEnd_7755293 := by exact prefixLift 7755293
  have htrace : WordTrace (prefixWord ++ tailWord_7755293) baseStart_7755293 baseEnd_7755293 := by
    simpa [prefixWord, tailWord_7755293, baseEnd_7755293] using wordTrace_append hprefix tailTrace_7755293
  have hstable : (prefixWord ++ tailWord_7755293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755293).length < 2 ^ (prefixWord ++ tailWord_7755293).sum := by decide
  have hdescent : baseEnd_7755293 < baseStart_7755293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755310 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2]
def baseStart_7755310 : Nat := 118140960795 + 7755310 * 2 ^ 59
def prefixEnd_7755310 : Nat := 4983230072969 + 3 ^ 40 * 7755310 * 2
def baseEnd_7755310 : Nat := 3982201654620157547658985

theorem tailTrace_7755310 : CollatzResearch.WordTrace tailWord_7755310 prefixEnd_7755310 3982201654620157547658985 := by
  unfold tailWord_7755310
  simp only [CollatzResearch.WordTrace]
  refine ⟨35357424191730480793019923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188572929022562564229439589 35357424191730480793019923)
  ·
    refine ⟨53036136287595721189529885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35357424191730480793019923 53036136287595721189529885)
    ·
      refine ⟨19888551107848395446073707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53036136287595721189529885 19888551107848395446073707)
      ·
        refine ⟨29832826661772593169110561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19888551107848395446073707 29832826661772593169110561)
        ·
          refine ⟨22374619996329444876832921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29832826661772593169110561 22374619996329444876832921)
          ·
            refine ⟨16780964997247083657624691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22374619996329444876832921 16780964997247083657624691)
            ·
              refine ⟨25171447495870625486437037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16780964997247083657624691 25171447495870625486437037)
              ·
                refine ⟨9439292810951484557413889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25171447495870625486437037 9439292810951484557413889)
                ·
                  refine ⟨7079469608213613418060417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9439292810951484557413889 7079469608213613418060417)
                  ·
                    refine ⟨5309602206160210063545313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079469608213613418060417 5309602206160210063545313)
                    ·
                      refine ⟨3982201654620157547658985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309602206160210063545313 3982201654620157547658985)
                      ·
                        rfl

theorem cell23_7755310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_7755310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755310 prefixEnd_7755310 := by exact prefixLift 7755310
  have htrace : WordTrace (prefixWord ++ tailWord_7755310) baseStart_7755310 baseEnd_7755310 := by
    simpa [prefixWord, tailWord_7755310, baseEnd_7755310] using wordTrace_append hprefix tailTrace_7755310
  have hstable : (prefixWord ++ tailWord_7755310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755310).length < 2 ^ (prefixWord ++ tailWord_7755310).sum := by decide
  have hdescent : baseEnd_7755310 < baseStart_7755310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755312 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 6, 5]
def baseStart_7755312 : Nat := 118140960795 + 7755312 * 2 ^ 59
def prefixEnd_7755312 : Nat := 4983230072969 + 3 ^ 40 * 7755312 * 2
def baseEnd_7755312 : Nat := 1327400893860488846611325

theorem tailTrace_7755312 : CollatzResearch.WordTrace tailWord_7755312 prefixEnd_7755312 1327400893860488846611325 := by
  unfold tailWord_7755312
  simp only [CollatzResearch.WordTrace]
  refine ⟨141429733239918300342866095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188572977653224400457154793 141429733239918300342866095)
  ·
    refine ⟨212144599859877450514299143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141429733239918300342866095 212144599859877450514299143)
    ·
      refine ⟨318216899789816175771448715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212144599859877450514299143 318216899789816175771448715)
      ·
        refine ⟨477325349684724263657173073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318216899789816175771448715 477325349684724263657173073)
        ·
          refine ⟨357994012263543197742879805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477325349684724263657173073 357994012263543197742879805)
          ·
            refine ⟨134247754598828699153579927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357994012263543197742879805 134247754598828699153579927)
            ·
              refine ⟨201371631898243048730369891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134247754598828699153579927 201371631898243048730369891)
              ·
                refine ⟨302057447847364573095554837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201371631898243048730369891 302057447847364573095554837)
                ·
                  refine ⟨14158942867845214363854133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302057447847364573095554837 14158942867845214363854133)
                  ·
                    refine ⟨1327400893860488846611325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14158942867845214363854133 1327400893860488846611325)
                    ·
                      rfl

theorem cell23_7755312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_7755312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755312 prefixEnd_7755312 := by exact prefixLift 7755312
  have htrace : WordTrace (prefixWord ++ tailWord_7755312) baseStart_7755312 baseEnd_7755312 := by
    simpa [prefixWord, tailWord_7755312, baseEnd_7755312] using wordTrace_append hprefix tailTrace_7755312
  have hstable : (prefixWord ++ tailWord_7755312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755312).length < 2 ^ (prefixWord ++ tailWord_7755312).sum := by decide
  have hdescent : baseEnd_7755312 < baseStart_7755312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755322 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_7755322 : Nat := 118140960795 + 7755322 * 2 ^ 59
def prefixEnd_7755322 : Nat := 4983230072969 + 3 ^ 40 * 7755322 * 2
def baseEnd_7755322 : Nat := 3982207816388011500708929

theorem tailTrace_7755322 : CollatzResearch.WordTrace tailWord_7755322 prefixEnd_7755322 3982207816388011500708929 := by
  unfold tailWord_7755322
  simp only [CollatzResearch.WordTrace]
  refine ⟨70714957802450093098399055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188573220806533581595730813 70714957802450093098399055)
  ·
    refine ⟨106072436703675139647598583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70714957802450093098399055 106072436703675139647598583)
    ·
      refine ⟨159108655055512709471397875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106072436703675139647598583 159108655055512709471397875)
      ·
        refine ⟨238662982583269064207096813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159108655055512709471397875 238662982583269064207096813)
        ·
          refine ⟨89498618468725899077661305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238662982583269064207096813 89498618468725899077661305)
          ·
            refine ⟨67123963851544424308245979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89498618468725899077661305 67123963851544424308245979)
            ·
              refine ⟨100685945777316636462368969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67123963851544424308245979 100685945777316636462368969)
              ·
                refine ⟨75514459332987477346776727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100685945777316636462368969 75514459332987477346776727)
                ·
                  refine ⟨113271688999481216020165091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75514459332987477346776727 113271688999481216020165091)
                  ·
                    refine ⟨169907533499221824030247637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113271688999481216020165091 169907533499221824030247637)
                    ·
                      refine ⟨3982207816388011500708929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169907533499221824030247637 3982207816388011500708929)
                      ·
                        rfl

theorem cell23_7755322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_7755322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755322 prefixEnd_7755322 := by exact prefixLift 7755322
  have htrace : WordTrace (prefixWord ++ tailWord_7755322) baseStart_7755322 baseEnd_7755322 := by
    simpa [prefixWord, tailWord_7755322, baseEnd_7755322] using wordTrace_append hprefix tailTrace_7755322
  have hstable : (prefixWord ++ tailWord_7755322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755322).length < 2 ^ (prefixWord ++ tailWord_7755322).sum := by decide
  have hdescent : baseEnd_7755322 < baseStart_7755322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755352 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_7755352 : Nat := 118140960795 + 7755352 * 2 ^ 59
def prefixEnd_7755352 : Nat := 4983230072969 + 3 ^ 40 * 7755352 * 2
def baseEnd_7755352 : Nat := 3982223220807646383333791

theorem tailTrace_7755352 : CollatzResearch.WordTrace tailWord_7755352 prefixEnd_7755352 3982223220807646383333791 := by
  unfold tailWord_7755352
  simp only [CollatzResearch.WordTrace]
  refine ⟨141430462699845843758594155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188573950266461125011458873 141430462699845843758594155)
  ·
    refine ⟨212145694049768765637891233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141430462699845843758594155 212145694049768765637891233)
    ·
      refine ⟨159109270537326574228418425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212145694049768765637891233 159109270537326574228418425)
      ·
        refine ⟨119331952902994930671313819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159109270537326574228418425 119331952902994930671313819)
        ·
          refine ⟨178997929354492396006970729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119331952902994930671313819 178997929354492396006970729)
          ·
            refine ⟨134248447015869297005228047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178997929354492396006970729 134248447015869297005228047)
            ·
              refine ⟨201372670523803945507842071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134248447015869297005228047 201372670523803945507842071)
              ·
                refine ⟨302059005785705918261763107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201372670523803945507842071 302059005785705918261763107)
                ·
                  refine ⟨453088508678558877392644661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302059005785705918261763107 453088508678558877392644661)
                  ·
                    refine ⟨42477047688614894755560437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 453088508678558877392644661 42477047688614894755560437)
                    ·
                      refine ⟨3982223220807646383333791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42477047688614894755560437 3982223220807646383333791)
                      ·
                        rfl

theorem cell23_7755352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_7755352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755352 prefixEnd_7755352 := by exact prefixLift 7755352
  have htrace : WordTrace (prefixWord ++ tailWord_7755352) baseStart_7755352 baseEnd_7755352 := by
    simpa [prefixWord, tailWord_7755352, baseEnd_7755352] using wordTrace_append hprefix tailTrace_7755352
  have hstable : (prefixWord ++ tailWord_7755352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755352).length < 2 ^ (prefixWord ++ tailWord_7755352).sum := by decide
  have hdescent : baseEnd_7755352 < baseStart_7755352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755369 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 3]
def baseStart_7755369 : Nat := 118140960795 + 7755369 * 2 ^ 59
def prefixEnd_7755369 : Nat := 4983230072969 + 3 ^ 40 * 7755369 * 2
def baseEnd_7755369 : Nat := 3982231949978772816821213

theorem tailTrace_7755369 : CollatzResearch.WordTrace tailWord_7755369 prefixEnd_7755369 3982231949978772816821213 := by
  unfold tailWord_7755369
  simp only [CollatzResearch.WordTrace]
  refine ⟨282861545440630099420557161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188574363627086732947038107 282861545440630099420557161)
  ·
    refine ⟨212146159080472574565417871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282861545440630099420557161 212146159080472574565417871)
    ·
      refine ⟨318219238620708861848126807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212146159080472574565417871 318219238620708861848126807)
      ·
        refine ⟨477328857931063292772190211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318219238620708861848126807 477328857931063292772190211)
        ·
          refine ⟨715993286896594939158285317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477328857931063292772190211 715993286896594939158285317)
          ·
            refine ⟨134248741293111551092178497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 715993286896594939158285317 134248741293111551092178497)
            ·
              refine ⟨100686555969833663319133873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134248741293111551092178497 100686555969833663319133873)
              ·
                refine ⟨75514916977375247489350405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100686555969833663319133873 75514916977375247489350405)
                ·
                  refine ⟨14159046933257858904253201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75514916977375247489350405 14159046933257858904253201)
                  ·
                    refine ⟨10619285199943394178189901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14159046933257858904253201 10619285199943394178189901)
                    ·
                      refine ⟨3982231949978772816821213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619285199943394178189901 3982231949978772816821213)
                      ·
                        rfl

theorem cell23_7755369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_7755369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755369 prefixEnd_7755369 := by exact prefixLift 7755369
  have htrace : WordTrace (prefixWord ++ tailWord_7755369) baseStart_7755369 baseEnd_7755369 := by
    simpa [prefixWord, tailWord_7755369, baseEnd_7755369] using wordTrace_append hprefix tailTrace_7755369
  have hstable : (prefixWord ++ tailWord_7755369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755369).length < 2 ^ (prefixWord ++ tailWord_7755369).sum := by decide
  have hdescent : baseEnd_7755369 < baseStart_7755369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755372 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 10]
def baseStart_7755372 : Nat := 118140960795 + 7755372 * 2 ^ 59
def prefixEnd_7755372 : Nat := 4983230072969 + 3 ^ 40 * 7755372 * 2
def baseEnd_7755372 : Nat := 442470387824526256120411

theorem tailTrace_7755372 : CollatzResearch.WordTrace tailWord_7755372 prefixEnd_7755372 442470387824526256120411 := by
  unfold tailWord_7755372
  simp only [CollatzResearch.WordTrace]
  refine ⟨141430827429809615466458185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188574436573079487288610913 141430827429809615466458185)
  ·
    refine ⟨106073120572357211599843639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141430827429809615466458185 106073120572357211599843639)
    ·
      refine ⟨159109680858535817399765459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106073120572357211599843639 159109680858535817399765459)
      ·
        refine ⟨238664521287803726099648189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159109680858535817399765459 238664521287803726099648189)
        ·
          refine ⟨89499195482926397287368071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238664521287803726099648189 89499195482926397287368071)
          ·
            refine ⟨134248793224389595931052107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89499195482926397287368071 134248793224389595931052107)
            ·
              refine ⟨201373189836584393896578161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134248793224389595931052107 201373189836584393896578161)
              ·
                refine ⟨151029892377438295422433621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201373189836584393896578161 151029892377438295422433621)
                ·
                  refine ⟨442470387824526256120411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 151029892377438295422433621 442470387824526256120411)
                  ·
                    rfl

theorem cell23_7755372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_7755372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755372 prefixEnd_7755372 := by exact prefixLift 7755372
  have htrace : WordTrace (prefixWord ++ tailWord_7755372) baseStart_7755372 baseEnd_7755372 := by
    simpa [prefixWord, tailWord_7755372, baseEnd_7755372] using wordTrace_append hprefix tailTrace_7755372
  have hstable : (prefixWord ++ tailWord_7755372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755372).length < 2 ^ (prefixWord ++ tailWord_7755372).sum := by decide
  have hdescent : baseEnd_7755372 < baseStart_7755372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755376 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 3, 4]
def baseStart_7755376 : Nat := 118140960795 + 7755376 * 2 ^ 59
def prefixEnd_7755376 : Nat := 4983230072969 + 3 ^ 40 * 7755376 * 2
def baseEnd_7755376 : Nat := 1327411848114451429811227

theorem tailTrace_7755376 : CollatzResearch.WordTrace tailWord_7755376 prefixEnd_7755376 1327411848114451429811227 := by
  unfold tailWord_7755376
  simp only [CollatzResearch.WordTrace]
  refine ⟨141430900375802369808030991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188574533834403159744041321 141430900375802369808030991)
  ·
    refine ⟨212146350563703554712046487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141430900375802369808030991 212146350563703554712046487)
    ·
      refine ⟨318219525845555332068069731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212146350563703554712046487 318219525845555332068069731)
      ·
        refine ⟨477329288768332998102104597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318219525845555332068069731 477329288768332998102104597)
        ·
          refine ⟨22374810411015609286036153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 477329288768332998102104597 22374810411015609286036153)
          ·
            refine ⟨16781107808261706964527115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22374810411015609286036153 16781107808261706964527115)
            ·
              refine ⟨25171661712392560446790673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16781107808261706964527115 25171661712392560446790673)
              ·
                refine ⟨18878746284294420335093005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25171661712392560446790673 18878746284294420335093005)
                ·
                  refine ⟨7079529856610407625659877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18878746284294420335093005 7079529856610407625659877)
                  ·
                    refine ⟨1327411848114451429811227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079529856610407625659877 1327411848114451429811227)
                    ·
                      rfl

theorem cell23_7755376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 4].length) (baseStart_7755376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755376 prefixEnd_7755376 := by exact prefixLift 7755376
  have htrace : WordTrace (prefixWord ++ tailWord_7755376) baseStart_7755376 baseEnd_7755376 := by
    simpa [prefixWord, tailWord_7755376, baseEnd_7755376] using wordTrace_append hprefix tailTrace_7755376
  have hstable : (prefixWord ++ tailWord_7755376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755376).length < 2 ^ (prefixWord ++ tailWord_7755376).sum := by decide
  have hdescent : baseEnd_7755376 < baseStart_7755376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755393 : List Nat := [1, 2, 4, 2, 1, 2, 1, 5, 1, 4]
def baseStart_7755393 : Nat := 118140960795 + 7755393 * 2 ^ 59
def prefixEnd_7755393 : Nat := 4983230072969 + 3 ^ 40 * 7755393 * 2
def baseEnd_7755393 : Nat := 1327414757838160240973701

theorem tailTrace_7755393 : CollatzResearch.WordTrace tailWord_7755393 prefixEnd_7755393 1327414757838160240973701 := by
  unfold tailWord_7755393
  simp only [CollatzResearch.WordTrace]
  refine ⟨282862420792543151519430833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188574947195028767679620555 282862420792543151519430833)
  ·
    refine ⟨212146815594407363639573125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282862420792543151519430833 212146815594407363639573125)
    ·
      refine ⟨39777527923951380682419961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212146815594407363639573125 39777527923951380682419961)
      ·
        refine ⟨29833145942963535511814971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39777527923951380682419961 29833145942963535511814971)
        ·
          refine ⟨44749718914445303267722457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29833145942963535511814971 44749718914445303267722457)
          ·
            refine ⟨33562289185833977450791843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44749718914445303267722457 33562289185833977450791843)
            ·
              refine ⟨50343433778750966176187765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33562289185833977450791843 50343433778750966176187765)
              ·
                refine ⟨4719696916757903079017603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50343433778750966176187765 4719696916757903079017603)
                ·
                  refine ⟨7079545375136854618526405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719696916757903079017603 7079545375136854618526405)
                  ·
                    refine ⟨1327414757838160240973701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079545375136854618526405 1327414757838160240973701)
                    ·
                      rfl

theorem cell23_7755393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_7755393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755393 prefixEnd_7755393 := by exact prefixLift 7755393
  have htrace : WordTrace (prefixWord ++ tailWord_7755393) baseStart_7755393 baseEnd_7755393 := by
    simpa [prefixWord, tailWord_7755393, baseEnd_7755393] using wordTrace_append hprefix tailTrace_7755393
  have hstable : (prefixWord ++ tailWord_7755393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755393).length < 2 ^ (prefixWord ++ tailWord_7755393).sum := by decide
  have hdescent : baseEnd_7755393 < baseStart_7755393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755406 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_7755406 : Nat := 118140960795 + 7755406 * 2 ^ 59
def prefixEnd_7755406 : Nat := 4983230072969 + 3 ^ 40 * 7755406 * 2
def baseEnd_7755406 : Nat := 442472327640332130228727

theorem tailTrace_7755406 : CollatzResearch.WordTrace tailWord_7755406 prefixEnd_7755406 442472327640332130228727 := by
  unfold tailWord_7755406
  simp only [CollatzResearch.WordTrace]
  refine ⟨35357861867687006842456759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188575263294330703159769381 35357861867687006842456759)
  ·
    refine ⟨53036792801530510263685139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35357861867687006842456759 53036792801530510263685139)
    ·
      refine ⟨79555189202295765395527709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53036792801530510263685139 79555189202295765395527709)
      ·
        refine ⟨29833195950860912023322891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79555189202295765395527709 29833195950860912023322891)
        ·
          refine ⟨44749793926291368034984337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29833195950860912023322891 44749793926291368034984337)
          ·
            refine ⟨33562345444718526026238253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44749793926291368034984337 33562345444718526026238253)
            ·
              refine ⟨12585879541769447259839345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33562345444718526026238253 12585879541769447259839345)
              ·
                refine ⟨9439409656327085444879509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12585879541769447259839345 9439409656327085444879509)
                ·
                  refine ⟨442472327640332130228727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9439409656327085444879509 442472327640332130228727)
                  ·
                    rfl

theorem cell23_7755406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_7755406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755406 prefixEnd_7755406 := by exact prefixLift 7755406
  have htrace : WordTrace (prefixWord ++ tailWord_7755406) baseStart_7755406 baseEnd_7755406 := by
    simpa [prefixWord, tailWord_7755406, baseEnd_7755406] using wordTrace_append hprefix tailTrace_7755406
  have hstable : (prefixWord ++ tailWord_7755406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755406).length < 2 ^ (prefixWord ++ tailWord_7755406).sum := by decide
  have hdescent : baseEnd_7755406 < baseStart_7755406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755449 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 1, 6]
def baseStart_7755449 : Nat := 118140960795 + 7755449 * 2 ^ 59
def prefixEnd_7755449 : Nat := 4983230072969 + 3 ^ 40 * 7755449 * 2
def baseEnd_7755449 : Nat := 1327424342810377501273615

theorem tailTrace_7755449 : CollatzResearch.WordTrace tailWord_7755449 prefixEnd_7755449 1327424342810377501273615 := by
  unfold tailWord_7755449
  simp only [CollatzResearch.WordTrace]
  refine ⟨282864463280340273083469401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188576308853560182055646267 282864463280340273083469401)
  ·
    refine ⟨212148347460255204812602051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282864463280340273083469401 212148347460255204812602051)
    ·
      refine ⟨318222521190382807218903077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212148347460255204812602051 318222521190382807218903077)
      ·
        refine ⟨59666722723196776353544327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318222521190382807218903077 59666722723196776353544327)
        ·
          refine ⟨89500084084795164530316491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59666722723196776353544327 89500084084795164530316491)
          ·
            refine ⟨134250126127192746795474737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89500084084795164530316491 134250126127192746795474737)
            ·
              refine ⟨100687594595394560096606053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134250126127192746795474737 100687594595394560096606053)
              ·
                refine ⟨18878923986636480018113635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100687594595394560096606053 18878923986636480018113635)
                ·
                  refine ⟨28318385979954720027170453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18878923986636480018113635 28318385979954720027170453)
                  ·
                    refine ⟨1327424342810377501273615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28318385979954720027170453 1327424342810377501273615)
                    ·
                      rfl

theorem cell23_7755449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_7755449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755449 prefixEnd_7755449 := by exact prefixLift 7755449
  have htrace : WordTrace (prefixWord ++ tailWord_7755449) baseStart_7755449 baseEnd_7755449 := by
    simpa [prefixWord, tailWord_7755449, baseEnd_7755449] using wordTrace_append hprefix tailTrace_7755449
  have hstable : (prefixWord ++ tailWord_7755449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755449).length < 2 ^ (prefixWord ++ tailWord_7755449).sum := by decide
  have hdescent : baseEnd_7755449 < baseStart_7755449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755450 : List Nat := [3, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3]
def baseStart_7755450 : Nat := 118140960795 + 7755450 * 2 ^ 59
def prefixEnd_7755450 : Nat := 4983230072969 + 3 ^ 40 * 7755450 * 2
def baseEnd_7755450 : Nat := 3982273541911786999908341

theorem tailTrace_7755450 : CollatzResearch.WordTrace tailWord_7755450 prefixEnd_7755450 3982273541911786999908341 := by
  unfold tailWord_7755450
  simp only [CollatzResearch.WordTrace]
  refine ⟨70716124938334162563563951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188576333168891100169503869 70716124938334162563563951)
  ·
    refine ⟨106074187407501243845345927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70716124938334162563563951 106074187407501243845345927)
    ·
      refine ⟨159111281111251865768018891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106074187407501243845345927 159111281111251865768018891)
      ·
        refine ⟨238666921666877798652028337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159111281111251865768018891 238666921666877798652028337)
        ·
          refine ⟨179000191250158348989021253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238666921666877798652028337 179000191250158348989021253)
          ·
            refine ⟨33562535859404690435441485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179000191250158348989021253 33562535859404690435441485)
            ·
              refine ⟨12585950947276758913290557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33562535859404690435441485 12585950947276758913290557)
              ·
                refine ⟨4719731605228784592483959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12585950947276758913290557 4719731605228784592483959)
                ·
                  refine ⟨7079597407843176888725939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719731605228784592483959 7079597407843176888725939)
                  ·
                    refine ⟨10619396111764765333088909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7079597407843176888725939 10619396111764765333088909)
                    ·
                      refine ⟨3982273541911786999908341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619396111764765333088909 3982273541911786999908341)
                      ·
                        rfl

theorem cell23_7755450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_7755450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755450 prefixEnd_7755450 := by exact prefixLift 7755450
  have htrace : WordTrace (prefixWord ++ tailWord_7755450) baseStart_7755450 baseEnd_7755450 := by
    simpa [prefixWord, tailWord_7755450, baseEnd_7755450] using wordTrace_append hprefix tailTrace_7755450
  have hstable : (prefixWord ++ tailWord_7755450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755450).length < 2 ^ (prefixWord ++ tailWord_7755450).sum := by decide
  have hdescent : baseEnd_7755450 < baseStart_7755450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755456 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4]
def baseStart_7755456 : Nat := 118140960795 + 7755456 * 2 ^ 59
def prefixEnd_7755456 : Nat := 4983230072969 + 3 ^ 40 * 7755456 * 2
def baseEnd_7755456 : Nat := 3982276622795713976433313

theorem tailTrace_7755456 : CollatzResearch.WordTrace tailWord_7755456 prefixEnd_7755456 3982276622795713976433313 := by
  unfold tailWord_7755456
  simp only [CollatzResearch.WordTrace]
  refine ⟨141432359295657456639487111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188576479060876608852649481 141432359295657456639487111)
  ·
    refine ⟨212148538943486184959230667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141432359295657456639487111 212148538943486184959230667)
    ·
      refine ⟨318222808415229277438846001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212148538943486184959230667 318222808415229277438846001)
      ·
        refine ⟨238667106311421958079134501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318222808415229277438846001 238667106311421958079134501)
        ·
          refine ⟨44750082433391617139837719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238667106311421958079134501 44750082433391617139837719)
          ·
            refine ⟨67125123650087425709756579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44750082433391617139837719 67125123650087425709756579)
            ·
              refine ⟨100687685475131138564634869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67125123650087425709756579 100687685475131138564634869)
              ·
                refine ⟨9439470513293544240434519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100687685475131138564634869 9439470513293544240434519)
                ·
                  refine ⟨14159205769940316360651779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9439470513293544240434519 14159205769940316360651779)
                  ·
                    refine ⟨21238808654910474540977669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14159205769940316360651779 21238808654910474540977669)
                    ·
                      refine ⟨3982276622795713976433313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21238808654910474540977669 3982276622795713976433313)
                      ·
                        rfl

theorem cell23_7755456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_7755456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755456 prefixEnd_7755456 := by exact prefixLift 7755456
  have htrace : WordTrace (prefixWord ++ tailWord_7755456) baseStart_7755456 baseEnd_7755456 := by
    simpa [prefixWord, tailWord_7755456, baseEnd_7755456] using wordTrace_append hprefix tailTrace_7755456
  have hstable : (prefixWord ++ tailWord_7755456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755456).length < 2 ^ (prefixWord ++ tailWord_7755456).sum := by decide
  have hdescent : baseEnd_7755456 < baseStart_7755456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755479 : List Nat := [1, 1, 3, 2, 1, 3, 4, 8]
def baseStart_7755479 : Nat := 118140960795 + 7755479 * 2 ^ 59
def prefixEnd_7755479 : Nat := 4983230072969 + 3 ^ 40 * 7755479 * 2
def baseEnd_7755479 : Nat := 147492164179658051349841

theorem tailTrace_7755479 : CollatzResearch.WordTrace tailWord_7755479 prefixEnd_7755479 147492164179658051349841 := by
  unfold tailWord_7755479
  simp only [CollatzResearch.WordTrace]
  refine ⟨282865557470231588207061491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188577038313487725471374327 282865557470231588207061491)
  ·
    refine ⟨424298336205347382310592237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282865557470231588207061491 424298336205347382310592237)
    ·
      refine ⟨159111876077005268366472089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424298336205347382310592237 159111876077005268366472089)
      ·
        refine ⟨119333907057753951274854067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159111876077005268366472089 119333907057753951274854067)
        ·
          refine ⟨179000860586630926912281101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119333907057753951274854067 179000860586630926912281101)
          ·
            refine ⟨67125322719986597592105413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179000860586630926912281101 67125322719986597592105413)
            ·
              refine ⟨12585998009997487048519765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67125322719986597592105413 12585998009997487048519765)
              ·
                refine ⟨147492164179658051349841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12585998009997487048519765 147492164179658051349841)
                ·
                  rfl

theorem cell23_7755479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 8].length) (baseStart_7755479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755479 prefixEnd_7755479 := by exact prefixLift 7755479
  have htrace : WordTrace (prefixWord ++ tailWord_7755479) baseStart_7755479 baseEnd_7755479 := by
    simpa [prefixWord, tailWord_7755479, baseEnd_7755479] using wordTrace_append hprefix tailTrace_7755479
  have hstable : (prefixWord ++ tailWord_7755479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755479).length < 2 ^ (prefixWord ++ tailWord_7755479).sum := by decide
  have hdescent : baseEnd_7755479 < baseStart_7755479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755519 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_7755519 : Nat := 118140960795 + 7755519 * 2 ^ 59
def prefixEnd_7755519 : Nat := 4983230072969 + 3 ^ 40 * 7755519 * 2
def baseEnd_7755519 : Nat := 3982308972076947229945523

theorem tailTrace_7755519 : CollatzResearch.WordTrace tailWord_7755519 prefixEnd_7755519 3982308972076947229945523 := by
  unfold tailWord_7755519
  simp only [CollatzResearch.WordTrace]
  refine ⟨282867016390086675038517611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188578010926724450025678407 282867016390086675038517611)
  ·
    refine ⟨424300524585130012557776417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282867016390086675038517611 424300524585130012557776417)
    ·
      refine ⟨318225393438847509418332313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424300524585130012557776417 318225393438847509418332313)
      ·
        refine ⟨238669045079135632063749235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318225393438847509418332313 238669045079135632063749235)
        ·
          refine ⟨358003567618703448095623853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238669045079135632063749235 358003567618703448095623853)
          ·
            refine ⟨134251337857013793035858945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358003567618703448095623853 134251337857013793035858945)
            ·
              refine ⟨100688503392760344776894209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134251337857013793035858945 100688503392760344776894209)
              ·
                refine ⟨75516377544570258582670657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100688503392760344776894209 75516377544570258582670657)
                ·
                  refine ⟨56637283158427693937002993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75516377544570258582670657 56637283158427693937002993)
                  ·
                    refine ⟨42477962368820770452752245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56637283158427693937002993 42477962368820770452752245)
                    ·
                      refine ⟨3982308972076947229945523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42477962368820770452752245 3982308972076947229945523)
                      ·
                        rfl

theorem cell23_7755519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_7755519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755519 prefixEnd_7755519 := by exact prefixLift 7755519
  have htrace : WordTrace (prefixWord ++ tailWord_7755519) baseStart_7755519 baseEnd_7755519 := by
    simpa [prefixWord, tailWord_7755519, baseEnd_7755519] using wordTrace_append hprefix tailTrace_7755519
  have hstable : (prefixWord ++ tailWord_7755519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755519).length < 2 ^ (prefixWord ++ tailWord_7755519).sum := by decide
  have hdescent : baseEnd_7755519 < baseStart_7755519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755523 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 3]
def baseStart_7755523 : Nat := 118140960795 + 7755523 * 2 ^ 59
def prefixEnd_7755523 : Nat := 4983230072969 + 3 ^ 40 * 7755523 * 2
def baseEnd_7755523 : Nat := 3982311025999565214295505

theorem tailTrace_7755523 : CollatzResearch.WordTrace tailWord_7755523 prefixEnd_7755523 3982311025999565214295505 := by
  unfold tailWord_7755523
  simp only [CollatzResearch.WordTrace]
  refine ⟨282867162282072183721663223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188578108188048122481108815 282867162282072183721663223)
  ·
    refine ⟨424300743423108275582494835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282867162282072183721663223 424300743423108275582494835)
    ·
      refine ⟨636451115134662413373742253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424300743423108275582494835 636451115134662413373742253)
      ·
        refine ⟨238669168175498405015153345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636451115134662413373742253 238669168175498405015153345)
        ·
          refine ⟨179001876131623803761365009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238669168175498405015153345 179001876131623803761365009)
          ·
            refine ⟨134251407098717852821023757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179001876131623803761365009 134251407098717852821023757)
            ·
              refine ⟨50344277662019194807883909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134251407098717852821023757 50344277662019194807883909)
              ·
                refine ⟨9439552061628599026478233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50344277662019194807883909 9439552061628599026478233)
                ·
                  refine ⟨7079664046221449269858675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9439552061628599026478233 7079664046221449269858675)
                  ·
                    refine ⟨10619496069332173904788013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7079664046221449269858675 10619496069332173904788013)
                    ·
                      refine ⟨3982311025999565214295505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619496069332173904788013 3982311025999565214295505)
                      ·
                        rfl

theorem cell23_7755523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_7755523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755523 prefixEnd_7755523 := by exact prefixLift 7755523
  have htrace : WordTrace (prefixWord ++ tailWord_7755523) baseStart_7755523 baseEnd_7755523 := by
    simpa [prefixWord, tailWord_7755523, baseEnd_7755523] using wordTrace_append hprefix tailTrace_7755523
  have hstable : (prefixWord ++ tailWord_7755523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755523).length < 2 ^ (prefixWord ++ tailWord_7755523).sum := by decide
  have hdescent : baseEnd_7755523 < baseStart_7755523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755524 : List Nat := [2, 3, 2, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7755524 : Nat := 118140960795 + 7755524 * 2 ^ 59
def prefixEnd_7755524 : Nat := 4983230072969 + 3 ^ 40 * 7755524 * 2
def baseEnd_7755524 : Nat := 3982311539480219710383001

theorem tailTrace_7755524 : CollatzResearch.WordTrace tailWord_7755524 prefixEnd_7755524 3982311539480219710383001 := by
  unfold tailWord_7755524
  simp only [CollatzResearch.WordTrace]
  refine ⟨141433599377534280446224813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188578132503379040594966417 141433599377534280446224813)
  ·
    refine ⟨53037599766575355167334305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141433599377534280446224813 53037599766575355167334305)
    ·
      refine ⟨39778199824931516375500729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53037599766575355167334305 39778199824931516375500729)
      ·
        refine ⟨29833649868698637281625547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39778199824931516375500729 29833649868698637281625547)
        ·
          refine ⟨44750474803047955922438321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29833649868698637281625547 44750474803047955922438321)
          ·
            refine ⟨33562856102285966941828741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44750474803047955922438321 33562856102285966941828741)
            ·
              refine ⟨6293035519178618801592889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33562856102285966941828741 6293035519178618801592889)
              ·
                refine ⟨4719776639383964101194667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6293035519178618801592889 4719776639383964101194667)
                ·
                  refine ⟨7079664959075946151792001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719776639383964101194667 7079664959075946151792001)
                  ·
                    refine ⟨5309748719306959613844001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079664959075946151792001 5309748719306959613844001)
                    ·
                      refine ⟨3982311539480219710383001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309748719306959613844001 3982311539480219710383001)
                      ·
                        rfl

theorem cell23_7755524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7755524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755524 prefixEnd_7755524 := by exact prefixLift 7755524
  have htrace : WordTrace (prefixWord ++ tailWord_7755524) baseStart_7755524 baseEnd_7755524 := by
    simpa [prefixWord, tailWord_7755524, baseEnd_7755524] using wordTrace_append hprefix tailTrace_7755524
  have hstable : (prefixWord ++ tailWord_7755524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755524).length < 2 ^ (prefixWord ++ tailWord_7755524).sum := by decide
  have hdescent : baseEnd_7755524 < baseStart_7755524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755574 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_7755574 : Nat := 118140960795 + 7755574 * 2 ^ 59
def prefixEnd_7755574 : Nat := 4983230072969 + 3 ^ 40 * 7755574 * 2
def baseEnd_7755574 : Nat := 3982337213512944514757771

theorem tailTrace_7755574 : CollatzResearch.WordTrace tailWord_7755574 prefixEnd_7755574 3982337213512944514757771 := by
  unfold tailWord_7755574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17679313900305463714485611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188579348269924946287846517 17679313900305463714485611)
  ·
    refine ⟨26518970850458195571728417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17679313900305463714485611 26518970850458195571728417)
    ·
      refine ⟨19889228137843646678796313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26518970850458195571728417 19889228137843646678796313)
      ·
        refine ⟨14916921103382735009097235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19889228137843646678796313 14916921103382735009097235)
        ·
          refine ⟨22375381655074102513645853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916921103382735009097235 22375381655074102513645853)
          ·
            refine ⟨8390768120652788442617195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22375381655074102513645853 8390768120652788442617195)
            ·
              refine ⟨12586152180979182663925793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8390768120652788442617195 12586152180979182663925793)
              ·
                refine ⟨9439614135734386997944345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12586152180979182663925793 9439614135734386997944345)
                ·
                  refine ⟨7079710601800790248458259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9439614135734386997944345 7079710601800790248458259)
                  ·
                    refine ⟨10619565902701185372687389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7079710601800790248458259 10619565902701185372687389)
                    ·
                      refine ⟨3982337213512944514757771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619565902701185372687389 3982337213512944514757771)
                      ·
                        rfl

theorem cell23_7755574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_7755574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755574 prefixEnd_7755574 := by exact prefixLift 7755574
  have htrace : WordTrace (prefixWord ++ tailWord_7755574) baseStart_7755574 baseEnd_7755574 := by
    simpa [prefixWord, tailWord_7755574, baseEnd_7755574] using wordTrace_append hprefix tailTrace_7755574
  have hstable : (prefixWord ++ tailWord_7755574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755574).length < 2 ^ (prefixWord ++ tailWord_7755574).sum := by decide
  have hdescent : baseEnd_7755574 < baseStart_7755574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755576 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_7755576 : Nat := 118140960795 + 7755576 * 2 ^ 59
def prefixEnd_7755576 : Nat := 4983230072969 + 3 ^ 40 * 7755576 * 2
def baseEnd_7755576 : Nat := 3982338240474253506932761

theorem tailTrace_7755576 : CollatzResearch.WordTrace tailWord_7755576 prefixEnd_7755576 3982338240474253506932761 := by
  unfold tailWord_7755576
  simp only [CollatzResearch.WordTrace]
  refine ⟨141434547675440086886671291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188579396900586782515561721 141434547675440086886671291)
  ·
    refine ⟨212151821513160130330006937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141434547675440086886671291 212151821513160130330006937)
    ·
      refine ⟨159113866134870097747505203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212151821513160130330006937 159113866134870097747505203)
      ·
        refine ⟨238670799202305146621257805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159113866134870097747505203 238670799202305146621257805)
        ·
          refine ⟨89501549700864429982971677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238670799202305146621257805 89501549700864429982971677)
          ·
            refine ⟨33563081137824161243614379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89501549700864429982971677 33563081137824161243614379)
            ·
              refine ⟨50344621706736241865421569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33563081137824161243614379 50344621706736241865421569)
              ·
                refine ⟨37758466280052181399066177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50344621706736241865421569 37758466280052181399066177)
                ·
                  refine ⟨28318849710039136049299633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37758466280052181399066177 28318849710039136049299633)
                  ·
                    refine ⟨21239137282529352036974725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28318849710039136049299633 21239137282529352036974725)
                    ·
                      refine ⟨3982338240474253506932761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21239137282529352036974725 3982338240474253506932761)
                      ·
                        rfl

theorem cell23_7755576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_7755576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755576 prefixEnd_7755576 := by exact prefixLift 7755576
  have htrace : WordTrace (prefixWord ++ tailWord_7755576) baseStart_7755576 baseEnd_7755576 := by
    simpa [prefixWord, tailWord_7755576, baseEnd_7755576] using wordTrace_append hprefix tailTrace_7755576
  have hstable : (prefixWord ++ tailWord_7755576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755576).length < 2 ^ (prefixWord ++ tailWord_7755576).sum := by decide
  have hdescent : baseEnd_7755576 < baseStart_7755576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755590 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7755590 : Nat := 118140960795 + 7755590 * 2 ^ 59
def prefixEnd_7755590 : Nat := 4983230072969 + 3 ^ 40 * 7755590 * 2
def baseEnd_7755590 : Nat := 1327448476401138817385899

theorem tailTrace_7755590 : CollatzResearch.WordTrace tailWord_7755590 prefixEnd_7755590 1327448476401138817385899 := by
  unfold tailWord_7755590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839675186650920442636007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188579737315219636109568149 8839675186650920442636007)
  ·
    refine ⟨13259512779976380663954011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839675186650920442636007 13259512779976380663954011)
    ·
      refine ⟨19889269169964570995931017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13259512779976380663954011 19889269169964570995931017)
      ·
        refine ⟨14916951877473428246948263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19889269169964570995931017 14916951877473428246948263)
        ·
          refine ⟨22375427816210142370422395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916951877473428246948263 22375427816210142370422395)
          ·
            refine ⟨33563141724315213555633593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22375427816210142370422395 33563141724315213555633593)
            ·
              refine ⟨25172356293236410166725195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33563141724315213555633593 25172356293236410166725195)
              ·
                refine ⟨37758534439854615250087793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25172356293236410166725195 37758534439854615250087793)
                ·
                  refine ⟨28318900829890961437565845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37758534439854615250087793 28318900829890961437565845)
                  ·
                    refine ⟨1327448476401138817385899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28318900829890961437565845 1327448476401138817385899)
                    ·
                      rfl

theorem cell23_7755590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7755590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755590 prefixEnd_7755590 := by exact prefixLift 7755590
  have htrace : WordTrace (prefixWord ++ tailWord_7755590) baseStart_7755590 baseEnd_7755590 := by
    simpa [prefixWord, tailWord_7755590, baseEnd_7755590] using wordTrace_append hprefix tailTrace_7755590
  have hstable : (prefixWord ++ tailWord_7755590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755590).length < 2 ^ (prefixWord ++ tailWord_7755590).sum := by decide
  have hdescent : baseEnd_7755590 < baseStart_7755590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755597 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_7755597 : Nat := 118140960795 + 7755597 * 2 ^ 59
def prefixEnd_7755597 : Nat := 4983230072969 + 3 ^ 40 * 7755597 * 2
def baseEnd_7755597 : Nat := 3982349023567997924770165

theorem tailTrace_7755597 : CollatzResearch.WordTrace tailWord_7755597 prefixEnd_7755597 3982349023567997924770165 := by
  unfold tailWord_7755597
  simp only [CollatzResearch.WordTrace]
  refine ⟨282869861283804094359857045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188579907522536062906571363 282869861283804094359857045)
  ·
    refine ⟨13259524747678316923118299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282869861283804094359857045 13259524747678316923118299)
    ·
      refine ⟨19889287121517475384677449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13259524747678316923118299 19889287121517475384677449)
      ·
        refine ⟨14916965341138106538508087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19889287121517475384677449 14916965341138106538508087)
        ·
          refine ⟨22375448011707159807762131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916965341138106538508087 22375448011707159807762131)
          ·
            refine ⟨33563172017560739711643197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22375448011707159807762131 33563172017560739711643197)
            ·
              refine ⟨12586189506585277391866199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33563172017560739711643197 12586189506585277391866199)
              ·
                refine ⟨18879284259877916087799299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12586189506585277391866199 18879284259877916087799299)
                ·
                  refine ⟨28318926389816874131698949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18879284259877916087799299 28318926389816874131698949)
                  ·
                    refine ⟨5309798698090663899693553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28318926389816874131698949 5309798698090663899693553)
                    ·
                      refine ⟨3982349023567997924770165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309798698090663899693553 3982349023567997924770165)
                      ·
                        rfl

theorem cell23_7755597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_7755597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755597 prefixEnd_7755597 := by exact prefixLift 7755597
  have htrace : WordTrace (prefixWord ++ tailWord_7755597) baseStart_7755597 baseEnd_7755597 := by
    simpa [prefixWord, tailWord_7755597, baseEnd_7755597] using wordTrace_append hprefix tailTrace_7755597
  have hstable : (prefixWord ++ tailWord_7755597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755597).length < 2 ^ (prefixWord ++ tailWord_7755597).sum := by decide
  have hdescent : baseEnd_7755597 < baseStart_7755597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755616 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 1, 7]
def baseStart_7755616 : Nat := 118140960795 + 7755616 * 2 ^ 59
def prefixEnd_7755616 : Nat := 4983230072969 + 3 ^ 40 * 7755616 * 2
def baseEnd_7755616 : Nat := 1327452926566811116810859

theorem tailTrace_7755616 : CollatzResearch.WordTrace tailWord_7755616 prefixEnd_7755616 1327452926566811116810859 := by
  unfold tailWord_7755616
  simp only [CollatzResearch.WordTrace]
  refine ⟨141435277135367630302399351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188580369513823507069865801 141435277135367630302399351)
  ·
    refine ⟨212152915703051445453599027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141435277135367630302399351 212152915703051445453599027)
    ·
      refine ⟨318229373554577168180398541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212152915703051445453599027 318229373554577168180398541)
      ·
        refine ⟨119336015082966438067649453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318229373554577168180398541 119336015082966438067649453)
        ·
          refine ⟨44751005656112414275368545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119336015082966438067649453 44751005656112414275368545)
          ·
            refine ⟨33563254242084310706526409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44751005656112414275368545 33563254242084310706526409)
            ·
              refine ⟨25172440681563233029894807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33563254242084310706526409 25172440681563233029894807)
              ·
                refine ⟨37758661022344849544842211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25172440681563233029894807 37758661022344849544842211)
                ·
                  refine ⟨56637991533517274317263317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37758661022344849544842211 56637991533517274317263317)
                  ·
                    refine ⟨1327452926566811116810859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56637991533517274317263317 1327452926566811116810859)
                    ·
                      rfl

theorem cell23_7755616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_7755616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755616 prefixEnd_7755616 := by exact prefixLift 7755616
  have htrace : WordTrace (prefixWord ++ tailWord_7755616) baseStart_7755616 baseEnd_7755616 := by
    simpa [prefixWord, tailWord_7755616, baseEnd_7755616] using wordTrace_append hprefix tailTrace_7755616
  have hstable : (prefixWord ++ tailWord_7755616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755616).length < 2 ^ (prefixWord ++ tailWord_7755616).sum := by decide
  have hdescent : baseEnd_7755616 < baseStart_7755616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755653 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 1, 6, 2]
def baseStart_7755653 : Nat := 118140960795 + 7755653 * 2 ^ 59
def prefixEnd_7755653 : Nat := 4983230072969 + 3 ^ 40 * 7755653 * 2
def baseEnd_7755653 : Nat := 3982377778484649705669907

theorem tailTrace_7755653 : CollatzResearch.WordTrace tailWord_7755653 prefixEnd_7755653 3982377778484649705669907 := by
  unfold tailWord_7755653
  simp only [CollatzResearch.WordTrace]
  refine ⟨282871903771601215923895613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188581269181067477282597075 282871903771601215923895613)
  ·
    refine ⟨106076963914350455971460855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282871903771601215923895613 106076963914350455971460855)
    ·
      refine ⟨159115445871525683957191283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106076963914350455971460855 159115445871525683957191283)
      ·
        refine ⟨238673168807288525935786925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159115445871525683957191283 238673168807288525935786925)
        ·
          refine ⟨89502438302733197225920097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238673168807288525935786925 89502438302733197225920097)
          ·
            refine ⟨67126828727049897919440073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89502438302733197225920097 67126828727049897919440073)
            ·
              refine ⟨50345121545287423439580055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67126828727049897919440073 50345121545287423439580055)
              ·
                refine ⟨75517682317931135159370083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50345121545287423439580055 75517682317931135159370083)
                ·
                  refine ⟨113276523476896702739055125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75517682317931135159370083 113276523476896702739055125)
                  ·
                    refine ⟨5309837037979532940893209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113276523476896702739055125 5309837037979532940893209)
                    ·
                      refine ⟨3982377778484649705669907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309837037979532940893209 3982377778484649705669907)
                      ·
                        rfl

theorem cell23_7755653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_7755653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755653 prefixEnd_7755653 := by exact prefixLift 7755653
  have htrace : WordTrace (prefixWord ++ tailWord_7755653) baseStart_7755653 baseEnd_7755653 := by
    simpa [prefixWord, tailWord_7755653, baseEnd_7755653] using wordTrace_append hprefix tailTrace_7755653
  have hstable : (prefixWord ++ tailWord_7755653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755653).length < 2 ^ (prefixWord ++ tailWord_7755653).sum := by decide
  have hdescent : baseEnd_7755653 < baseStart_7755653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755673 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 3]
def baseStart_7755673 : Nat := 118140960795 + 7755673 * 2 ^ 59
def prefixEnd_7755673 : Nat := 4983230072969 + 3 ^ 40 * 7755673 * 2
def baseEnd_7755673 : Nat := 3982388048097739627419815

theorem tailTrace_7755673 : CollatzResearch.WordTrace tailWord_7755673 prefixEnd_7755673 3982388048097739627419815 := by
  unfold tailWord_7755673
  simp only [CollatzResearch.WordTrace]
  refine ⟨282872633231528759339623673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188581755487685839559749115 282872633231528759339623673)
  ·
    refine ⟨212154474923646569504717755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282872633231528759339623673 212154474923646569504717755)
    ·
      refine ⟨318231712385469854257076633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212154474923646569504717755 318231712385469854257076633)
      ·
        refine ⟨238673784289102390692807475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318231712385469854257076633 238673784289102390692807475)
        ·
          refine ⟨358010676433653586039211213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238673784289102390692807475 358010676433653586039211213)
          ·
            refine ⟨134254003662620094764704205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358010676433653586039211213 134254003662620094764704205)
            ·
              refine ⟨50345251373482535536764077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134254003662620094764704205 50345251373482535536764077)
              ·
                refine ⟨18879469265055950826286529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50345251373482535536764077 18879469265055950826286529)
                ·
                  refine ⟨14159601948791963119714897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18879469265055950826286529 14159601948791963119714897)
                  ·
                    refine ⟨10619701461593972339786173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14159601948791963119714897 10619701461593972339786173)
                    ·
                      refine ⟨3982388048097739627419815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619701461593972339786173 3982388048097739627419815)
                      ·
                        rfl

theorem cell23_7755673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_7755673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755673 prefixEnd_7755673 := by exact prefixLift 7755673
  have htrace : WordTrace (prefixWord ++ tailWord_7755673) baseStart_7755673 baseEnd_7755673 := by
    simpa [prefixWord, tailWord_7755673, baseEnd_7755673] using wordTrace_append hprefix tailTrace_7755673
  have hstable : (prefixWord ++ tailWord_7755673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755673).length < 2 ^ (prefixWord ++ tailWord_7755673).sum := by decide
  have hdescent : baseEnd_7755673 < baseStart_7755673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755680 : List Nat := [2, 1, 1, 4, 1, 1, 1, 7, 1, 4]
def baseStart_7755680 : Nat := 118140960795 + 7755680 * 2 ^ 59
def prefixEnd_7755680 : Nat := 4983230072969 + 3 ^ 40 * 7755680 * 2
def baseEnd_7755680 : Nat := 1327463880820773700010761

theorem tailTrace_7755680 : CollatzResearch.WordTrace tailWord_7755680 prefixEnd_7755680 1327463880820773700010761 := by
  unfold tailWord_7755680
  simp only [CollatzResearch.WordTrace]
  refine ⟨141436444271251699767564247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188581925695002266356752329 141436444271251699767564247)
  ·
    refine ⟨212154666406877549651346371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141436444271251699767564247 212154666406877549651346371)
    ·
      refine ⟨318231999610316324477019557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212154666406877549651346371 318231999610316324477019557)
      ·
        refine ⟨59668499926934310839441167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318231999610316324477019557 59668499926934310839441167)
        ·
          refine ⟨89502749890401466259161751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59668499926934310839441167 89502749890401466259161751)
          ·
            refine ⟨134254124835602199388742627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89502749890401466259161751 134254124835602199388742627)
            ·
              refine ⟨201381187253403299083113941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134254124835602199388742627 201381187253403299083113941)
              ·
                refine ⟨4719871576251639822260483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 201381187253403299083113941 4719871576251639822260483)
                ·
                  refine ⟨7079807364377459733390725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719871576251639822260483 7079807364377459733390725)
                  ·
                    refine ⟨1327463880820773700010761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079807364377459733390725 1327463880820773700010761)
                    ·
                      rfl

theorem cell23_7755680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 4].length) (baseStart_7755680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755680 prefixEnd_7755680 := by exact prefixLift 7755680
  have htrace : WordTrace (prefixWord ++ tailWord_7755680) baseStart_7755680 baseEnd_7755680 := by
    simpa [prefixWord, tailWord_7755680, baseEnd_7755680] using wordTrace_append hprefix tailTrace_7755680
  have hstable : (prefixWord ++ tailWord_7755680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755680).length < 2 ^ (prefixWord ++ tailWord_7755680).sum := by decide
  have hdescent : baseEnd_7755680 < baseStart_7755680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755697 : List Nat := [1, 2, 2, 4, 2, 2, 1, 4, 1, 4]
def baseStart_7755697 : Nat := 118140960795 + 7755697 * 2 ^ 59
def prefixEnd_7755697 : Nat := 4983230072969 + 3 ^ 40 * 7755697 * 2
def baseEnd_7755697 : Nat := 1327466790544482511173235

theorem tailTrace_7755697 : CollatzResearch.WordTrace tailWord_7755697 prefixEnd_7755697 1327466790544482511173235 := by
  unfold tailWord_7755697
  simp only [CollatzResearch.WordTrace]
  refine ⟨282873508583441811438497345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188582339055627874292331563 282873508583441811438497345)
  ·
    refine ⟨212155131437581358578873009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282873508583441811438497345 212155131437581358578873009)
    ·
      refine ⟨159116348578186018934154757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212155131437581358578873009 159116348578186018934154757)
      ·
        refine ⟨29834315358409878550154017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159116348578186018934154757 29834315358409878550154017)
        ·
          refine ⟨22375736518807408912615513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29834315358409878550154017 22375736518807408912615513)
          ·
            refine ⟨16781802389105556684461635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22375736518807408912615513 16781802389105556684461635)
            ·
              refine ⟨25172703583658335026692453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16781802389105556684461635 25172703583658335026692453)
              ·
                refine ⟨4719881921935937817504835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25172703583658335026692453 4719881921935937817504835)
                ·
                  refine ⟨7079822882903906726257253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719881921935937817504835 7079822882903906726257253)
                  ·
                    refine ⟨1327466790544482511173235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079822882903906726257253 1327466790544482511173235)
                    ·
                      rfl

theorem cell23_7755697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_7755697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755697 prefixEnd_7755697 := by exact prefixLift 7755697
  have htrace : WordTrace (prefixWord ++ tailWord_7755697) baseStart_7755697 baseEnd_7755697 := by
    simpa [prefixWord, tailWord_7755697, baseEnd_7755697] using wordTrace_append hprefix tailTrace_7755697
  have hstable : (prefixWord ++ tailWord_7755697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755697).length < 2 ^ (prefixWord ++ tailWord_7755697).sum := by decide
  have hdescent : baseEnd_7755697 < baseStart_7755697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755720 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_7755720 : Nat := 118140960795 + 7755720 * 2 ^ 59
def prefixEnd_7755720 : Nat := 4983230072969 + 3 ^ 40 * 7755720 * 2
def baseEnd_7755720 : Nat := 3982412181688500943532099

theorem tailTrace_7755720 : CollatzResearch.WordTrace tailWord_7755720 prefixEnd_7755720 3982412181688500943532099 := by
  unfold tailWord_7755720
  simp only [CollatzResearch.WordTrace]
  refine ⟨141437173731179243183292307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188582898308238990911056409 141437173731179243183292307)
  ·
    refine ⟨212155760596768864774938461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141437173731179243183292307 212155760596768864774938461)
    ·
      refine ⟨79558410223788324290601923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212155760596768864774938461 79558410223788324290601923)
      ·
        refine ⟨119337615335682486435902885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79558410223788324290601923 119337615335682486435902885)
        ·
          refine ⟨22375802875440466206731791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119337615335682486435902885 22375802875440466206731791)
          ·
            refine ⟨33563704313160699310097687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22375802875440466206731791 33563704313160699310097687)
            ·
              refine ⟨50345556469741048965146531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33563704313160699310097687 50345556469741048965146531)
              ·
                refine ⟨75518334704611573447719797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50345556469741048965146531 75518334704611573447719797)
                ·
                  refine ⟨7079843878557335010723731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75518334704611573447719797 7079843878557335010723731)
                  ·
                    refine ⟨10619765817836002516085597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7079843878557335010723731 10619765817836002516085597)
                    ·
                      refine ⟨3982412181688500943532099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619765817836002516085597 3982412181688500943532099)
                      ·
                        rfl

theorem cell23_7755720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_7755720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755720 prefixEnd_7755720 := by exact prefixLift 7755720
  have htrace : WordTrace (prefixWord ++ tailWord_7755720) baseStart_7755720 baseEnd_7755720 := by
    simpa [prefixWord, tailWord_7755720, baseEnd_7755720] using wordTrace_append hprefix tailTrace_7755720
  have hstable : (prefixWord ++ tailWord_7755720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755720).length < 2 ^ (prefixWord ++ tailWord_7755720).sum := by decide
  have hdescent : baseEnd_7755720 < baseStart_7755720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755723 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 1, 5]
def baseStart_7755723 : Nat := 118140960795 + 7755723 * 2 ^ 59
def prefixEnd_7755723 : Nat := 4983230072969 + 3 ^ 40 * 7755723 * 2
def baseEnd_7755723 : Nat := 1327471240710154810598195

theorem tailTrace_7755723 : CollatzResearch.WordTrace tailWord_7755723 prefixEnd_7755723 1327471240710154810598195 := by
  unfold tailWord_7755723
  simp only [CollatzResearch.WordTrace]
  refine ⟨282874456881347617878943823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188582971254231745252629215 282874456881347617878943823)
  ·
    refine ⟨424311685322021426818415735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282874456881347617878943823 424311685322021426818415735)
    ·
      refine ⟨636467527983032140227623603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424311685322021426818415735 636467527983032140227623603)
      ·
        refine ⟨954701291974548210341435405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636467527983032140227623603 954701291974548210341435405)
        ·
          refine ⟨358012984490455578878038277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 954701291974548210341435405 358012984490455578878038277)
          ·
            refine ⟨67127434591960421039632177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 358012984490455578878038277 67127434591960421039632177)
            ·
              refine ⟨50345575943970315779724133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67127434591960421039632177 50345575943970315779724133)
              ·
                refine ⟨9439795489494434208698275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50345575943970315779724133 9439795489494434208698275)
                ·
                  refine ⟨14159693234241651313047413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9439795489494434208698275 14159693234241651313047413)
                  ·
                    refine ⟨1327471240710154810598195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14159693234241651313047413 1327471240710154810598195)
                    ·
                      rfl

theorem cell23_7755723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 5].length) (baseStart_7755723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755723 prefixEnd_7755723 := by exact prefixLift 7755723
  have htrace : WordTrace (prefixWord ++ tailWord_7755723) baseStart_7755723 baseEnd_7755723 := by
    simpa [prefixWord, tailWord_7755723, baseEnd_7755723] using wordTrace_append hprefix tailTrace_7755723
  have hstable : (prefixWord ++ tailWord_7755723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755723).length < 2 ^ (prefixWord ++ tailWord_7755723).sum := by decide
  have hdescent : baseEnd_7755723 < baseStart_7755723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755763 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 3]
def baseStart_7755763 : Nat := 118140960795 + 7755763 * 2 ^ 59
def prefixEnd_7755763 : Nat := 4983230072969 + 3 ^ 40 * 7755763 * 2
def baseEnd_7755763 : Nat := 3982434261356644275294401

theorem tailTrace_7755763 : CollatzResearch.WordTrace tailWord_7755763 prefixEnd_7755763 3982434261356644275294401 := by
  unfold tailWord_7755763
  simp only [CollatzResearch.WordTrace]
  refine ⟨282875915801202704710399943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188583943867468469806933295 282875915801202704710399943)
  ·
    refine ⟨424313873701804057065599915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282875915801202704710399943 424313873701804057065599915)
    ·
      refine ⟨636470810552706085598399873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424313873701804057065599915 636470810552706085598399873)
      ·
        refine ⟨477353107914529564198799905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636470810552706085598399873 477353107914529564198799905)
        ·
          refine ⟨358014830935897173149099929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477353107914529564198799905 358014830935897173149099929)
          ·
            refine ⟨268511123201922879861824947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358014830935897173149099929 268511123201922879861824947)
            ·
              refine ⟨402766684802884319792737421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268511123201922879861824947 402766684802884319792737421)
              ·
                refine ⟨151037506801081619922276533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402766684802884319792737421 151037506801081619922276533)
                ·
                  refine ⟨14159766262601401867713425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151037506801081619922276533 14159766262601401867713425)
                  ·
                    refine ⟨10619824696951051400785069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14159766262601401867713425 10619824696951051400785069)
                    ·
                      refine ⟨3982434261356644275294401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10619824696951051400785069 3982434261356644275294401)
                      ·
                        rfl

theorem cell23_7755763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_7755763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755763 prefixEnd_7755763 := by exact prefixLift 7755763
  have htrace : WordTrace (prefixWord ++ tailWord_7755763) baseStart_7755763 baseEnd_7755763 := by
    simpa [prefixWord, tailWord_7755763, baseEnd_7755763] using wordTrace_append hprefix tailTrace_7755763
  have hstable : (prefixWord ++ tailWord_7755763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755763).length < 2 ^ (prefixWord ++ tailWord_7755763).sum := by decide
  have hdescent : baseEnd_7755763 < baseStart_7755763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755777 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 3, 2, 2]
def baseStart_7755777 : Nat := 118140960795 + 7755777 * 2 ^ 59
def prefixEnd_7755777 : Nat := 4983230072969 + 3 ^ 40 * 7755777 * 2
def baseEnd_7755777 : Nat := 3982441450085807220519337

theorem tailTrace_7755777 : CollatzResearch.WordTrace tailWord_7755777 prefixEnd_7755777 3982441450085807220519337 := by
  unfold tailWord_7755777
  simp only [CollatzResearch.WordTrace]
  refine ⟨282876426423151985101409585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188584284282101323400939723 282876426423151985101409585)
  ·
    refine ⟨212157319817363988826057189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282876426423151985101409585 212157319817363988826057189)
    ·
      refine ⟨39779497465755747904885723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212157319817363988826057189 39779497465755747904885723)
      ·
        refine ⟨59669246198633621857328585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39779497465755747904885723 59669246198633621857328585)
        ·
          refine ⟨44751934648975216392996439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59669246198633621857328585 44751934648975216392996439)
          ·
            refine ⟨67127901973462824589494659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44751934648975216392996439 67127901973462824589494659)
            ·
              refine ⟨100691852960194236884241989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67127901973462824589494659 100691852960194236884241989)
              ·
                refine ⟨18879722430036419415795373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100691852960194236884241989 18879722430036419415795373)
                ·
                  refine ⟨7079895911263657280923265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18879722430036419415795373 7079895911263657280923265)
                  ·
                    refine ⟨5309921933447742960692449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079895911263657280923265 5309921933447742960692449)
                    ·
                      refine ⟨3982441450085807220519337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309921933447742960692449 3982441450085807220519337)
                      ·
                        rfl

theorem cell23_7755777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_7755777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755777 prefixEnd_7755777 := by exact prefixLift 7755777
  have htrace : WordTrace (prefixWord ++ tailWord_7755777) baseStart_7755777 baseEnd_7755777 := by
    simpa [prefixWord, tailWord_7755777, baseEnd_7755777] using wordTrace_append hprefix tailTrace_7755777
  have hstable : (prefixWord ++ tailWord_7755777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755777).length < 2 ^ (prefixWord ++ tailWord_7755777).sum := by decide
  have hdescent : baseEnd_7755777 < baseStart_7755777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755782 : List Nat := [6, 2, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7755782 : Nat := 118140960795 + 7755782 * 2 ^ 59
def prefixEnd_7755782 : Nat := 4983230072969 + 3 ^ 40 * 7755782 * 2
def baseEnd_7755782 : Nat := 1327481339163026566985605

theorem tailTrace_7755782 : CollatzResearch.WordTrace tailWord_7755782 prefixEnd_7755782 1327481339163026566985605 := by
  unfold tailWord_7755782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839894024629183467354425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188584405858755913970227733 8839894024629183467354425)
  ·
    refine ⟨6629920518471887600515819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8839894024629183467354425 6629920518471887600515819)
    ·
      refine ⟨9944880777707831400773729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6629920518471887600515819 9944880777707831400773729)
      ·
        refine ⟨7458660583280873550580297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9944880777707831400773729 7458660583280873550580297)
        ·
          refine ⟨5593995437460655162935223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7458660583280873550580297 5593995437460655162935223)
          ·
            refine ⟨8390993156190982744402835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593995437460655162935223 8390993156190982744402835)
            ·
              refine ⟨12586489734286474116604253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8390993156190982744402835 12586489734286474116604253)
              ·
                refine ⟨4719933650357427793726595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12586489734286474116604253 4719933650357427793726595)
                ·
                  refine ⟨7079900475536141690589893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719933650357427793726595 7079900475536141690589893)
                  ·
                    refine ⟨1327481339163026566985605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7079900475536141690589893 1327481339163026566985605)
                    ·
                      rfl

theorem cell23_7755782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7755782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755782 prefixEnd_7755782 := by exact prefixLift 7755782
  have htrace : WordTrace (prefixWord ++ tailWord_7755782) baseStart_7755782 baseEnd_7755782 := by
    simpa [prefixWord, tailWord_7755782, baseEnd_7755782] using wordTrace_append hprefix tailTrace_7755782
  have hstable : (prefixWord ++ tailWord_7755782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755782).length < 2 ^ (prefixWord ++ tailWord_7755782).sum := by decide
  have hdescent : baseEnd_7755782 < baseStart_7755782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755783 : List Nat := [1, 1, 4, 3, 1, 3, 1, 9]
def baseStart_7755783 : Nat := 118140960795 + 7755783 * 2 ^ 59
def prefixEnd_7755783 : Nat := 4983230072969 + 3 ^ 40 * 7755783 * 2
def baseEnd_7755783 : Nat := 147497945591471636927567

theorem tailTrace_7755783 : CollatzResearch.WordTrace tailWord_7755783 prefixEnd_7755783 147497945591471636927567 := by
  unfold tailWord_7755783
  simp only [CollatzResearch.WordTrace]
  refine ⟨282876645261130248126128003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188584430174086832084085335 282876645261130248126128003)
  ·
    refine ⟨424314967891695372189192005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282876645261130248126128003 424314967891695372189192005)
    ·
      refine ⟨79559056479692882285473501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424314967891695372189192005 79559056479692882285473501)
      ·
        refine ⟨29834646179884830857052563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79559056479692882285473501 29834646179884830857052563)
        ·
          refine ⟨44751969269827246285578845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29834646179884830857052563 44751969269827246285578845)
          ·
            refine ⟨16781988476185217357092067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44751969269827246285578845 16781988476185217357092067)
            ·
              refine ⟨25172982714277826035638101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16781988476185217357092067 25172982714277826035638101)
              ·
                refine ⟨147497945591471636927567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25172982714277826035638101 147497945591471636927567)
                ·
                  rfl

theorem cell23_7755783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 9].length) (baseStart_7755783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755783 prefixEnd_7755783 := by exact prefixLift 7755783
  have htrace : WordTrace (prefixWord ++ tailWord_7755783) baseStart_7755783 baseEnd_7755783 := by
    simpa [prefixWord, tailWord_7755783, baseEnd_7755783] using wordTrace_append hprefix tailTrace_7755783
  have hstable : (prefixWord ++ tailWord_7755783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755783).length < 2 ^ (prefixWord ++ tailWord_7755783).sum := by decide
  have hdescent : baseEnd_7755783 < baseStart_7755783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755811 : List Nat := [1, 1, 1, 4, 3, 1, 5, 2, 1, 2, 2]
def baseStart_7755811 : Nat := 118140960795 + 7755811 * 2 ^ 59
def prefixEnd_7755811 : Nat := 4983230072969 + 3 ^ 40 * 7755811 * 2
def baseEnd_7755811 : Nat := 3982458908428060087494181

theorem tailTrace_7755811 : CollatzResearch.WordTrace tailWord_7755811 prefixEnd_7755811 3982458908428060087494181 := by
  unfold tailWord_7755811
  simp only [CollatzResearch.WordTrace]
  refine ⟨282877666505028808908147287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188585111003352539272098191 282877666505028808908147287)
  ·
    refine ⟨424316499757543213362220931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282877666505028808908147287 424316499757543213362220931)
    ·
      refine ⟨636474749636314820043331397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424316499757543213362220931 636474749636314820043331397)
      ·
        refine ⟨119339015556809028758124637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 636474749636314820043331397 119339015556809028758124637)
        ·
          refine ⟨44752130833803385784296739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119339015556809028758124637 44752130833803385784296739)
          ·
            refine ⟨67128196250705078676445109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44752130833803385784296739 67128196250705078676445109)
            ·
              refine ⟨6293268398503601125916729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67128196250705078676445109 6293268398503601125916729)
              ·
                refine ⟨4719951298877700844437547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6293268398503601125916729 4719951298877700844437547)
                ·
                  refine ⟨7079926948316551266656321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719951298877700844437547 7079926948316551266656321)
                  ·
                    refine ⟨5309945211237413449992241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079926948316551266656321 5309945211237413449992241)
                    ·
                      refine ⟨3982458908428060087494181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309945211237413449992241 3982458908428060087494181)
                      ·
                        rfl

theorem cell23_7755811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_7755811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755811 prefixEnd_7755811 := by exact prefixLift 7755811
  have htrace : WordTrace (prefixWord ++ tailWord_7755811) baseStart_7755811 baseEnd_7755811 := by
    simpa [prefixWord, tailWord_7755811, baseEnd_7755811] using wordTrace_append hprefix tailTrace_7755811
  have hstable : (prefixWord ++ tailWord_7755811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755811).length < 2 ^ (prefixWord ++ tailWord_7755811).sum := by decide
  have hdescent : baseEnd_7755811 < baseStart_7755811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755837 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7755837 : Nat := 118140960795 + 7755837 * 2 ^ 59
def prefixEnd_7755837 : Nat := 4983230072969 + 3 ^ 40 * 7755837 * 2
def baseEnd_7755837 : Nat := 3982472258925076985769061

theorem tailTrace_7755837 : CollatzResearch.WordTrace tailWord_7755837 prefixEnd_7755837 3982472258925076985769061 := by
  unfold tailWord_7755837
  simp only [CollatzResearch.WordTrace]
  refine ⟨282878614802934615348593765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188585743201956410232395843 282878614802934615348593765)
  ·
    refine ⟨53039740275550240377861331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282878614802934615348593765 53039740275550240377861331)
    ·
      refine ⟨79559610413325360566791997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53039740275550240377861331 79559610413325360566791997)
      ·
        refine ⟨29834853904997010212546999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79559610413325360566791997 29834853904997010212546999)
        ·
          refine ⟨44752280857495515318820499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29834853904997010212546999 44752280857495515318820499)
          ·
            refine ⟨67128421286243272978230749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44752280857495515318820499 67128421286243272978230749)
            ·
              refine ⟨25173157982341227366836531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67128421286243272978230749 25173157982341227366836531)
              ·
                refine ⟨37759736973511841050254797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25173157982341227366836531 37759736973511841050254797)
                ·
                  refine ⟨14159901365066940393845549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37759736973511841050254797 14159901365066940393845549)
                  ·
                    refine ⟨5309963011900102647692081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14159901365066940393845549 5309963011900102647692081)
                    ·
                      refine ⟨3982472258925076985769061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309963011900102647692081 3982472258925076985769061)
                      ·
                        rfl

theorem cell23_7755837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7755837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755837 prefixEnd_7755837 := by exact prefixLift 7755837
  have htrace : WordTrace (prefixWord ++ tailWord_7755837) baseStart_7755837 baseEnd_7755837 := by
    simpa [prefixWord, tailWord_7755837, baseEnd_7755837] using wordTrace_append hprefix tailTrace_7755837
  have hstable : (prefixWord ++ tailWord_7755837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755837).length < 2 ^ (prefixWord ++ tailWord_7755837).sum := by decide
  have hdescent : baseEnd_7755837 < baseStart_7755837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755862 : List Nat := [5, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_7755862 : Nat := 118140960795 + 7755862 * 2 ^ 59
def prefixEnd_7755862 : Nat := 4983230072969 + 3 ^ 40 * 7755862 * 2
def baseEnd_7755862 : Nat := 3982485095941439387956447

theorem tailTrace_7755862 : CollatzResearch.WordTrace tailWord_7755862 prefixEnd_7755862 3982485095941439387956447 := by
  unfold tailWord_7755862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17679970414240252788640865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188586351085229363078835893 17679970414240252788640865)
  ·
    refine ⟨13259977810680189591480649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17679970414240252788640865 13259977810680189591480649)
    ·
      refine ⟨9944983358010142193610487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13259977810680189591480649 9944983358010142193610487)
      ·
        refine ⟨14917475037015213290415731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944983358010142193610487 14917475037015213290415731)
        ·
          refine ⟨22376212555522819935623597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14917475037015213290415731 22376212555522819935623597)
          ·
            refine ⟨8391079708321057475858849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22376212555522819935623597 8391079708321057475858849)
            ·
              refine ⟨6293309781240793106894137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391079708321057475858849 6293309781240793106894137)
              ·
                refine ⟨4719982335930594830170603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6293309781240793106894137 4719982335930594830170603)
                ·
                  refine ⟨7079973503895892245255905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719982335930594830170603 7079973503895892245255905)
                  ·
                    refine ⟨5309980127921919183941929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079973503895892245255905 5309980127921919183941929)
                    ·
                      refine ⟨3982485095941439387956447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309980127921919183941929 3982485095941439387956447)
                      ·
                        rfl

theorem cell23_7755862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_7755862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755862 prefixEnd_7755862 := by exact prefixLift 7755862
  have htrace : WordTrace (prefixWord ++ tailWord_7755862) baseStart_7755862 baseEnd_7755862 := by
    simpa [prefixWord, tailWord_7755862, baseEnd_7755862] using wordTrace_append hprefix tailTrace_7755862
  have hstable : (prefixWord ++ tailWord_7755862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755862).length < 2 ^ (prefixWord ++ tailWord_7755862).sum := by decide
  have hdescent : baseEnd_7755862 < baseStart_7755862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755873 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 7]
def baseStart_7755873 : Nat := 118140960795 + 7755873 * 2 ^ 59
def prefixEnd_7755873 : Nat := 4983230072969 + 3 ^ 40 * 7755873 * 2
def baseEnd_7755873 : Nat := 442498971580959871657655

theorem tailTrace_7755873 : CollatzResearch.WordTrace tailWord_7755873 prefixEnd_7755873 442498971580959871657655 := by
  unfold tailWord_7755873
  simp only [CollatzResearch.WordTrace]
  refine ⟨282879927830804193496904273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188586618553869462331269515 282879927830804193496904273)
  ·
    refine ⟨212159945873103145122678205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282879927830804193496904273 212159945873103145122678205)
    ·
      refine ⟨79559979702413679421004327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212159945873103145122678205 79559979702413679421004327)
      ·
        refine ⟨119339969553620519131506491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79559979702413679421004327 119339969553620519131506491)
        ·
          refine ⟨179009954330430778697259737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119339969553620519131506491 179009954330430778697259737)
          ·
            refine ⟨134257465747823084022944803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179009954330430778697259737 134257465747823084022944803)
            ·
              refine ⟨201386198621734626034417205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134257465747823084022944803 201386198621734626034417205)
              ·
                refine ⟨18879956120787621190726613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201386198621734626034417205 18879956120787621190726613)
                ·
                  refine ⟨442498971580959871657655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18879956120787621190726613 442498971580959871657655)
                  ·
                    rfl

theorem cell23_7755873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 7].length) (baseStart_7755873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755873 prefixEnd_7755873 := by exact prefixLift 7755873
  have htrace : WordTrace (prefixWord ++ tailWord_7755873) baseStart_7755873 baseEnd_7755873 := by
    simpa [prefixWord, tailWord_7755873, baseEnd_7755873] using wordTrace_append hprefix tailTrace_7755873
  have hstable : (prefixWord ++ tailWord_7755873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755873).length < 2 ^ (prefixWord ++ tailWord_7755873).sum := by decide
  have hdescent : baseEnd_7755873 < baseStart_7755873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755884 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 2, 2, 2]
def baseStart_7755884 : Nat := 118140960795 + 7755884 * 2 ^ 59
def prefixEnd_7755884 : Nat := 4983230072969 + 3 ^ 40 * 7755884 * 2
def baseEnd_7755884 : Nat := 3982496392515838301881345

theorem tailTrace_7755884 : CollatzResearch.WordTrace tailWord_7755884 prefixEnd_7755884 3982496392515838301881345 := by
  unfold tailWord_7755884
  simp only [CollatzResearch.WordTrace]
  refine ⟨141440164516882171187777353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188586886022509561583703137 141440164516882171187777353)
  ·
    refine ⟨106080123387661628390833015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141440164516882171187777353 106080123387661628390833015)
    ·
      refine ⟨159120185081492442586249523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106080123387661628390833015 159120185081492442586249523)
      ·
        refine ⟨238680277622238663879374285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159120185081492442586249523 238680277622238663879374285)
        ·
          refine ⟨89505104108339498954765357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238680277622238663879374285 89505104108339498954765357)
          ·
            refine ⟨33564414040627312108037009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89505104108339498954765357 33564414040627312108037009)
            ·
              refine ⟨25173310530470484081027757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33564414040627312108037009 25173310530470484081027757)
              ·
                refine ⟨9439991448926431530385409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25173310530470484081027757 9439991448926431530385409)
                ·
                  refine ⟨7079993586694823647789057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9439991448926431530385409 7079993586694823647789057)
                  ·
                    refine ⟨5309995190021117735841793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079993586694823647789057 5309995190021117735841793)
                    ·
                      refine ⟨3982496392515838301881345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5309995190021117735841793 3982496392515838301881345)
                      ·
                        rfl

theorem cell23_7755884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_7755884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755884 prefixEnd_7755884 := by exact prefixLift 7755884
  have htrace : WordTrace (prefixWord ++ tailWord_7755884) baseStart_7755884 baseEnd_7755884 := by
    simpa [prefixWord, tailWord_7755884, baseEnd_7755884] using wordTrace_append hprefix tailTrace_7755884
  have hstable : (prefixWord ++ tailWord_7755884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755884).length < 2 ^ (prefixWord ++ tailWord_7755884).sum := by decide
  have hdescent : baseEnd_7755884 < baseStart_7755884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755890 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 7]
def baseStart_7755890 : Nat := 118140960795 + 7755890 * 2 ^ 59
def prefixEnd_7755890 : Nat := 4983230072969 + 3 ^ 40 * 7755890 * 2
def baseEnd_7755890 : Nat := 442499941488862808711813

theorem tailTrace_7755890 : CollatzResearch.WordTrace tailWord_7755890 prefixEnd_7755890 442499941488862808711813 := by
  unfold tailWord_7755890
  simp only [CollatzResearch.WordTrace]
  refine ⟨70720136967935651350068281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188587031914495070266848749 70720136967935651350068281)
  ·
    refine ⟨53040102725951738512551211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70720136967935651350068281 53040102725951738512551211)
    ·
      refine ⟨79560154088927607768826817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53040102725951738512551211 79560154088927607768826817)
      ·
        refine ⟨59670115566695705826620113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79560154088927607768826817 59670115566695705826620113)
        ·
          refine ⟨44752586675021779369965085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59670115566695705826620113 44752586675021779369965085)
          ·
            refine ⟨16782220003133167263736907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44752586675021779369965085 16782220003133167263736907)
            ·
              refine ⟨25173330004699750895605361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16782220003133167263736907 25173330004699750895605361)
              ·
                refine ⟨18879997503524813171704021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25173330004699750895605361 18879997503524813171704021)
                ·
                  refine ⟨442499941488862808711813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18879997503524813171704021 442499941488862808711813)
                  ·
                    rfl

theorem cell23_7755890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_7755890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755890 prefixEnd_7755890 := by exact prefixLift 7755890
  have htrace : WordTrace (prefixWord ++ tailWord_7755890) baseStart_7755890 baseEnd_7755890 := by
    simpa [prefixWord, tailWord_7755890, baseEnd_7755890] using wordTrace_append hprefix tailTrace_7755890
  have hstable : (prefixWord ++ tailWord_7755890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755890).length < 2 ^ (prefixWord ++ tailWord_7755890).sum := by decide
  have hdescent : baseEnd_7755890 < baseStart_7755890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755907 : List Nat := [1, 1, 1, 3, 3, 4, 2, 3, 5]
def baseStart_7755907 : Nat := 118140960795 + 7755907 * 2 ^ 59
def prefixEnd_7755907 : Nat := 4983230072969 + 3 ^ 40 * 7755907 * 2
def baseEnd_7755907 : Nat := 442500911396765745765971

theorem tailTrace_7755907 : CollatzResearch.WordTrace tailWord_7755907 prefixEnd_7755907 442500911396765745765971 := by
  unfold tailWord_7755907
  simp only [CollatzResearch.WordTrace]
  refine ⟨282881167912681017303641975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188587445275120678202427983 282881167912681017303641975)
  ·
    refine ⟨424321751869021525955462963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282881167912681017303641975 424321751869021525955462963)
    ·
      refine ⟨636482627803532288933194445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424321751869021525955462963 636482627803532288933194445)
      ·
        refine ⟨238680985426324608349947917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636482627803532288933194445 238680985426324608349947917)
        ·
          refine ⟨89505369534871728131230469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238680985426324608349947917 89505369534871728131230469)
          ·
            refine ⟨16782256787788449024605713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89505369534871728131230469 16782256787788449024605713)
            ·
              refine ⟨12586692590841336768454285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16782256787788449024605713 12586692590841336768454285)
              ·
                refine ⟨4720009721565501288170357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12586692590841336768454285 4720009721565501288170357)
                ·
                  refine ⟨442500911396765745765971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4720009721565501288170357 442500911396765745765971)
                  ·
                    rfl

theorem cell23_7755907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 5].length) (baseStart_7755907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755907 prefixEnd_7755907 := by exact prefixLift 7755907
  have htrace : WordTrace (prefixWord ++ tailWord_7755907) baseStart_7755907 baseEnd_7755907 := by
    simpa [prefixWord, tailWord_7755907, baseEnd_7755907] using wordTrace_append hprefix tailTrace_7755907
  have hstable : (prefixWord ++ tailWord_7755907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755907).length < 2 ^ (prefixWord ++ tailWord_7755907).sum := by decide
  have hdescent : baseEnd_7755907 < baseStart_7755907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755918 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_7755918 : Nat := 118140960795 + 7755918 * 2 ^ 59
def prefixEnd_7755918 : Nat := 4983230072969 + 3 ^ 40 * 7755918 * 2
def baseEnd_7755918 : Nat := 3982513850858091168856189

theorem tailTrace_7755918 : CollatzResearch.WordTrace tailWord_7755918 prefixEnd_7755918 3982513850858091168856189 := by
  unfold tailWord_7755918
  simp only [CollatzResearch.WordTrace]
  refine ⟨35360196139455145772786551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188587712743760777454861605 35360196139455145772786551)
  ·
    refine ⟨53040294209182718659179827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35360196139455145772786551 53040294209182718659179827)
    ·
      refine ⟨79560441313774077988769741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53040294209182718659179827 79560441313774077988769741)
      ·
        refine ⟨29835165492665279245788653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79560441313774077988769741 29835165492665279245788653)
        ·
          refine ⟨11188187059749479717170745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29835165492665279245788653 11188187059749479717170745)
          ·
            refine ⟨8391140294812109787878059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11188187059749479717170745 8391140294812109787878059)
            ·
              refine ⟨12586710442218164681817089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391140294812109787878059 12586710442218164681817089)
              ·
                refine ⟨9440032831663623511362817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12586710442218164681817089 9440032831663623511362817)
                ·
                  refine ⟨7080024623747717633522113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9440032831663623511362817 7080024623747717633522113)
                  ·
                    refine ⟨5310018467810788225141585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7080024623747717633522113 5310018467810788225141585)
                    ·
                      refine ⟨3982513850858091168856189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310018467810788225141585 3982513850858091168856189)
                      ·
                        rfl

theorem cell23_7755918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_7755918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755918 prefixEnd_7755918 := by exact prefixLift 7755918
  have htrace : WordTrace (prefixWord ++ tailWord_7755918) baseStart_7755918 baseEnd_7755918 := by
    simpa [prefixWord, tailWord_7755918, baseEnd_7755918] using wordTrace_append hprefix tailTrace_7755918
  have hstable : (prefixWord ++ tailWord_7755918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755918).length < 2 ^ (prefixWord ++ tailWord_7755918).sum := by decide
  have hdescent : baseEnd_7755918 < baseStart_7755918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755924 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 7]
def baseStart_7755924 : Nat := 118140960795 + 7755924 * 2 ^ 59
def prefixEnd_7755924 : Nat := 4983230072969 + 3 ^ 40 * 7755924 * 2
def baseEnd_7755924 : Nat := 442501881304668682820129

theorem tailTrace_7755924 : CollatzResearch.WordTrace tailWord_7755924 prefixEnd_7755924 442501881304668682820129 := by
  unfold tailWord_7755924
  simp only [CollatzResearch.WordTrace]
  refine ⟨141440893976809714603505413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188587858635746286138007217 141440893976809714603505413)
  ·
    refine ⟨26520167620651821488157265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141440893976809714603505413 26520167620651821488157265)
    ·
      refine ⟨19890125715488866116117949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26520167620651821488157265 19890125715488866116117949)
      ·
        refine ⟨7458797143308324793544231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19890125715488866116117949 7458797143308324793544231)
        ·
          refine ⟨11188195714962487190316347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458797143308324793544231 11188195714962487190316347)
          ·
            refine ⟨16782293572443730785474521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11188195714962487190316347 16782293572443730785474521)
            ·
              refine ⟨12586720179332798089105891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16782293572443730785474521 12586720179332798089105891)
              ·
                refine ⟨18880080268999197133658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12586720179332798089105891 18880080268999197133658837)
                ·
                  refine ⟨442501881304668682820129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18880080268999197133658837 442501881304668682820129)
                  ·
                    rfl

theorem cell23_7755924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_7755924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755924 prefixEnd_7755924 := by exact prefixLift 7755924
  have htrace : WordTrace (prefixWord ++ tailWord_7755924) baseStart_7755924 baseEnd_7755924 := by
    simpa [prefixWord, tailWord_7755924, baseEnd_7755924] using wordTrace_append hprefix tailTrace_7755924
  have hstable : (prefixWord ++ tailWord_7755924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755924).length < 2 ^ (prefixWord ++ tailWord_7755924).sum := by decide
  have hdescent : baseEnd_7755924 < baseStart_7755924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755960 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_7755960 : Nat := 118140960795 + 7755960 * 2 ^ 59
def prefixEnd_7755960 : Nat := 4983230072969 + 3 ^ 40 * 7755960 * 2
def baseEnd_7755960 : Nat := 3982535417045580004530995

theorem tailTrace_7755960 : CollatzResearch.WordTrace tailWord_7755960 prefixEnd_7755960 3982535417045580004530995 := by
  unfold tailWord_7755960
  simp only [CollatzResearch.WordTrace]
  refine ⟨141441550490744503677660667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188588733987659338236880889 141441550490744503677660667)
  ·
    refine ⟨212162325736116755516491001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141441550490744503677660667 212162325736116755516491001)
    ·
      refine ⟨159121744302087566637368251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212162325736116755516491001 159121744302087566637368251)
      ·
        refine ⟨238682616453131349956052377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159121744302087566637368251 238682616453131349956052377)
        ·
          refine ⟨179011962339848512467039283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238682616453131349956052377 179011962339848512467039283)
          ·
            refine ⟨268517943509772768700558925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179011962339848512467039283 268517943509772768700558925)
            ·
              refine ⟨100694228816164788262709597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268517943509772768700558925 100694228816164788262709597)
              ·
                refine ⟨37760335806061795598516099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100694228816164788262709597 37760335806061795598516099)
                ·
                  refine ⟨56640503709092693397774149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37760335806061795598516099 56640503709092693397774149)
                  ·
                    refine ⟨10620094445454880012082653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56640503709092693397774149 10620094445454880012082653)
                    ·
                      refine ⟨3982535417045580004530995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10620094445454880012082653 3982535417045580004530995)
                      ·
                        rfl

theorem cell23_7755960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_7755960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755960 prefixEnd_7755960 := by exact prefixLift 7755960
  have htrace : WordTrace (prefixWord ++ tailWord_7755960) baseStart_7755960 baseEnd_7755960 := by
    simpa [prefixWord, tailWord_7755960, baseEnd_7755960] using wordTrace_append hprefix tailTrace_7755960
  have hstable : (prefixWord ++ tailWord_7755960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755960).length < 2 ^ (prefixWord ++ tailWord_7755960).sum := by decide
  have hdescent : baseEnd_7755960 < baseStart_7755960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7755963 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 10]
def baseStart_7755963 : Nat := 118140960795 + 7755963 * 2 ^ 59
def prefixEnd_7755963 : Nat := 4983230072969 + 3 ^ 40 * 7755963 * 2
def baseEnd_7755963 : Nat := 442504106387504832532609

theorem tailTrace_7755963 : CollatzResearch.WordTrace tailWord_7755963 prefixEnd_7755963 442504106387504832532609 := by
  unfold tailWord_7755963
  simp only [CollatzResearch.WordTrace]
  refine ⟨282883210400478138867680543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188588806933652092578453695 282883210400478138867680543)
  ·
    refine ⟨424324815600717208301520815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282883210400478138867680543 424324815600717208301520815)
    ·
      refine ⟨636487223401075812452281223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424324815600717208301520815 636487223401075812452281223)
      ·
        refine ⟨954730835101613718678421835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636487223401075812452281223 954730835101613718678421835)
        ·
          refine ⟨1432096252652420578017632753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954730835101613718678421835 1432096252652420578017632753)
          ·
            refine ⟨1074072189489315433513224565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432096252652420578017632753 1074072189489315433513224565)
            ·
              refine ⟨100694267764623321891864803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1074072189489315433513224565 100694267764623321891864803)
              ·
                refine ⟨151041401646934982837797205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100694267764623321891864803 151041401646934982837797205)
                ·
                  refine ⟨442504106387504832532609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 151041401646934982837797205 442504106387504832532609)
                  ·
                    rfl

theorem cell23_7755963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 10].length) (baseStart_7755963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7755963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7755963 prefixEnd_7755963 := by exact prefixLift 7755963
  have htrace : WordTrace (prefixWord ++ tailWord_7755963) baseStart_7755963 baseEnd_7755963 := by
    simpa [prefixWord, tailWord_7755963, baseEnd_7755963] using wordTrace_append hprefix tailTrace_7755963
  have hstable : (prefixWord ++ tailWord_7755963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7755963).length < 2 ^ (prefixWord ++ tailWord_7755963).sum := by decide
  have hdescent : baseEnd_7755963 < baseStart_7755963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7755963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756017 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 1, 5, 2]
def baseStart_7756017 : Nat := 118140960795 + 7756017 * 2 ^ 59
def prefixEnd_7756017 : Nat := 4983230072969 + 3 ^ 40 * 7756017 * 2
def baseEnd_7756017 : Nat := 3982564685442886281518233

theorem tailTrace_7756017 : CollatzResearch.WordTrace tailWord_7756017 prefixEnd_7756017 3982564685442886281518233 := by
  unfold tailWord_7756017
  simp only [CollatzResearch.WordTrace]
  refine ⟨282885179942282506090146305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188590119961521670726764203 282885179942282506090146305)
  ·
    refine ⟨212163884956711879567609729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282885179942282506090146305 212163884956711879567609729)
    ·
      refine ⟨159122913717533909675707297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212163884956711879567609729 159122913717533909675707297)
      ·
        refine ⟨119342185288150432256780473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159122913717533909675707297 119342185288150432256780473)
        ·
          refine ⟨89506638966112824192585355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119342185288150432256780473 89506638966112824192585355)
          ·
            refine ⟨134259958449169236288878033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89506638966112824192585355 134259958449169236288878033)
            ·
              refine ⟨100694968836876927216658525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134259958449169236288878033 100694968836876927216658525)
              ·
                refine ⟨37760613313828847706246947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100694968836876927216658525 37760613313828847706246947)
                ·
                  refine ⟨56640919970743271559370421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37760613313828847706246947 56640919970743271559370421)
                  ·
                    refine ⟨5310086247257181708690977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56640919970743271559370421 5310086247257181708690977)
                    ·
                      refine ⟨3982564685442886281518233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310086247257181708690977 3982564685442886281518233)
                      ·
                        rfl

theorem cell23_7756017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_7756017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756017 prefixEnd_7756017 := by exact prefixLift 7756017
  have htrace : WordTrace (prefixWord ++ tailWord_7756017) baseStart_7756017 baseEnd_7756017 := by
    simpa [prefixWord, tailWord_7756017, baseEnd_7756017] using wordTrace_append hprefix tailTrace_7756017
  have hstable : (prefixWord ++ tailWord_7756017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756017).length < 2 ^ (prefixWord ++ tailWord_7756017).sum := by decide
  have hdescent : baseEnd_7756017 < baseStart_7756017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756041 : List Nat := [1, 2, 1, 1, 3, 5, 1, 4, 1, 1, 3]
def baseStart_7756041 : Nat := 118140960795 + 7756041 * 2 ^ 59
def prefixEnd_7756041 : Nat := 4983230072969 + 3 ^ 40 * 7756041 * 2
def baseEnd_7756041 : Nat := 3982577008978594187618123

theorem tailTrace_7756041 : CollatzResearch.WordTrace tailWord_7756041 prefixEnd_7756041 3982577008978594187618123 := by
  unfold tailWord_7756041
  simp only [CollatzResearch.WordTrace]
  refine ⟨282886055294195558189019977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188590703529463705459346651 282886055294195558189019977)
  ·
    refine ⟨212164541470646668641764983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282886055294195558189019977 212164541470646668641764983)
    ·
      refine ⟨318246812205970002962647475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212164541470646668641764983 318246812205970002962647475)
      ·
        refine ⟨477370218308955004443971213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318246812205970002962647475 477370218308955004443971213)
        ·
          refine ⟨179013831865858126666489205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477370218308955004443971213 179013831865858126666489205)
          ·
            refine ⟨16782546737424199374983363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179013831865858126666489205 16782546737424199374983363)
            ·
              refine ⟨25173820106136299062475045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16782546737424199374983363 25173820106136299062475045)
              ·
                refine ⟨4720091269900556074214071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25173820106136299062475045 4720091269900556074214071)
                ·
                  refine ⟨7080136904850834111321107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720091269900556074214071 7080136904850834111321107)
                  ·
                    refine ⟨10620205357276251166981661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7080136904850834111321107 10620205357276251166981661)
                    ·
                      refine ⟨3982577008978594187618123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10620205357276251166981661 3982577008978594187618123)
                      ·
                        rfl

theorem cell23_7756041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 1, 3].length) (baseStart_7756041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756041 prefixEnd_7756041 := by exact prefixLift 7756041
  have htrace : WordTrace (prefixWord ++ tailWord_7756041) baseStart_7756041 baseEnd_7756041 := by
    simpa [prefixWord, tailWord_7756041, baseEnd_7756041] using wordTrace_append hprefix tailTrace_7756041
  have hstable : (prefixWord ++ tailWord_7756041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756041).length < 2 ^ (prefixWord ++ tailWord_7756041).sum := by decide
  have hdescent : baseEnd_7756041 < baseStart_7756041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756067 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 3]
def baseStart_7756067 : Nat := 118140960795 + 7756067 * 2 ^ 59
def prefixEnd_7756067 : Nat := 4983230072969 + 3 ^ 40 * 7756067 * 2
def baseEnd_7756067 : Nat := 3982590359475611085893003

theorem tailTrace_7756067 : CollatzResearch.WordTrace tailWord_7756067 prefixEnd_7756067 3982590359475611085893003 := by
  unfold tailWord_7756067
  simp only [CollatzResearch.WordTrace]
  refine ⟨282887003592101364629466455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188591335728067576419644303 282887003592101364629466455)
  ·
    refine ⟨424330505388152046944199683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282887003592101364629466455 424330505388152046944199683)
    ·
      refine ⟨636495758082228070416299525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424330505388152046944199683 636495758082228070416299525)
      ·
        refine ⟨119342954640417763203056161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 636495758082228070416299525 119342954640417763203056161)
        ·
          refine ⟨89507215980313322402292121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119342954640417763203056161 89507215980313322402292121)
          ·
            refine ⟨67130411985234991801719091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89507215980313322402292121 67130411985234991801719091)
            ·
              refine ⟨100695617977852487702578637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67130411985234991801719091 100695617977852487702578637)
              ·
                refine ⟨37760856741694682888466989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100695617977852487702578637 37760856741694682888466989)
                ·
                  refine ⟨14160321278135506083175121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37760856741694682888466989 14160321278135506083175121)
                  ·
                    refine ⟨10620240958601629562381341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14160321278135506083175121 10620240958601629562381341)
                    ·
                      refine ⟨3982590359475611085893003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10620240958601629562381341 3982590359475611085893003)
                      ·
                        rfl

theorem cell23_7756067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_7756067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756067 prefixEnd_7756067 := by exact prefixLift 7756067
  have htrace : WordTrace (prefixWord ++ tailWord_7756067) baseStart_7756067 baseEnd_7756067 := by
    simpa [prefixWord, tailWord_7756067, baseEnd_7756067] using wordTrace_append hprefix tailTrace_7756067
  have hstable : (prefixWord ++ tailWord_7756067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756067).length < 2 ^ (prefixWord ++ tailWord_7756067).sum := by decide
  have hdescent : baseEnd_7756067 < baseStart_7756067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756107 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 7, 2]
def baseStart_7756107 : Nat := 118140960795 + 7756107 * 2 ^ 59
def prefixEnd_7756107 : Nat := 4983230072969 + 3 ^ 40 * 7756107 * 2
def baseEnd_7756107 : Nat := 3982610898701790929392819

theorem tailTrace_7756107 : CollatzResearch.WordTrace tailWord_7756107 prefixEnd_7756107 3982610898701790929392819 := by
  unfold tailWord_7756107
  simp only [CollatzResearch.WordTrace]
  refine ⟨282888462511956451460922575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188592308341304300973948383 282888462511956451460922575)
  ·
    refine ⟨424332693767934677191383863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282888462511956451460922575 424332693767934677191383863)
    ·
      refine ⟨636499040651902015787075795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424332693767934677191383863 636499040651902015787075795)
      ·
        refine ⟨954748560977853023680613693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636499040651902015787075795 954748560977853023680613693)
        ·
          refine ⟨358030710366694883880230135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 954748560977853023680613693 358030710366694883880230135)
          ·
            refine ⟨537046065550042325820345203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358030710366694883880230135 537046065550042325820345203)
            ·
              refine ⟨805569098325063488730517805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537046065550042325820345203 805569098325063488730517805)
              ·
                refine ⟨302088411871898808273944177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805569098325063488730517805 302088411871898808273944177)
                ·
                  refine ⟨226566308903924106205458133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302088411871898808273944177 226566308903924106205458133)
                  ·
                    refine ⟨5310147864935721239190425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226566308903924106205458133 5310147864935721239190425)
                    ·
                      refine ⟨3982610898701790929392819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310147864935721239190425 3982610898701790929392819)
                      ·
                        rfl

theorem cell23_7756107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7, 2].length) (baseStart_7756107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756107 prefixEnd_7756107 := by exact prefixLift 7756107
  have htrace : WordTrace (prefixWord ++ tailWord_7756107) baseStart_7756107 baseEnd_7756107 := by
    simpa [prefixWord, tailWord_7756107, baseEnd_7756107] using wordTrace_append hprefix tailTrace_7756107
  have hstable : (prefixWord ++ tailWord_7756107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756107).length < 2 ^ (prefixWord ++ tailWord_7756107).sum := by decide
  have hdescent : baseEnd_7756107 < baseStart_7756107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756114 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_7756114 : Nat := 118140960795 + 7756114 * 2 ^ 59
def prefixEnd_7756114 : Nat := 4983230072969 + 3 ^ 40 * 7756114 * 2
def baseEnd_7756114 : Nat := 3982614493066372402005287

theorem tailTrace_7756114 : CollatzResearch.WordTrace tailWord_7756114 prefixEnd_7756114 3982614493066372402005287 := by
  unfold tailWord_7756114
  simp only [CollatzResearch.WordTrace]
  refine ⟨70722179455732772914106849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188592478548620727770951597 70722179455732772914106849)
  ·
    refine ⟨53041634591799579685580137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70722179455732772914106849 53041634591799579685580137)
    ·
      refine ⟨39781225943849684764185103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53041634591799579685580137 39781225943849684764185103)
      ·
        refine ⟨59671838915774527146277655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39781225943849684764185103 59671838915774527146277655)
        ·
          refine ⟨89507758373661790719416483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59671838915774527146277655 89507758373661790719416483)
          ·
            refine ⟨134261637560492686079124725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89507758373661790719416483 134261637560492686079124725)
            ·
              refine ⟨12587028521296189319917943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134261637560492686079124725 12587028521296189319917943)
              ·
                refine ⟨18880542781944283979876915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12587028521296189319917943 18880542781944283979876915)
                ·
                  refine ⟨28320814172916425969815373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18880542781944283979876915 28320814172916425969815373)
                  ·
                    refine ⟨10620305314843659738680765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28320814172916425969815373 10620305314843659738680765)
                    ·
                      refine ⟨3982614493066372402005287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10620305314843659738680765 3982614493066372402005287)
                      ·
                        rfl

theorem cell23_7756114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_7756114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756114 prefixEnd_7756114 := by exact prefixLift 7756114
  have htrace : WordTrace (prefixWord ++ tailWord_7756114) baseStart_7756114 baseEnd_7756114 := by
    simpa [prefixWord, tailWord_7756114, baseEnd_7756114] using wordTrace_append hprefix tailTrace_7756114
  have hstable : (prefixWord ++ tailWord_7756114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756114).length < 2 ^ (prefixWord ++ tailWord_7756114).sum := by decide
  have hdescent : baseEnd_7756114 < baseStart_7756114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756120 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_7756120 : Nat := 118140960795 + 7756120 * 2 ^ 59
def prefixEnd_7756120 : Nat := 4983230072969 + 3 ^ 40 * 7756120 * 2
def baseEnd_7756120 : Nat := 3982617573950299378530259

theorem tailTrace_7756120 : CollatzResearch.WordTrace tailWord_7756120 prefixEnd_7756120 3982617573950299378530259 := by
  unfold tailWord_7756120
  simp only [CollatzResearch.WordTrace]
  refine ⟨141444468330454677340572907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188592624440606236454097209 141444468330454677340572907)
  ·
    refine ⟨212166702495682016010859361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141444468330454677340572907 212166702495682016010859361)
    ·
      refine ⟨159125026871761512008144521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212166702495682016010859361 159125026871761512008144521)
      ·
        refine ⟨119343770153821134006108391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159125026871761512008144521 119343770153821134006108391)
        ·
          refine ⟨179015655230731701009162587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119343770153821134006108391 179015655230731701009162587)
          ·
            refine ⟨268523482846097551513743881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179015655230731701009162587 268523482846097551513743881)
            ·
              refine ⟨201392612134573163635307911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268523482846097551513743881 201392612134573163635307911)
              ·
                refine ⟨302088918201859745452961867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201392612134573163635307911 302088918201859745452961867)
                ·
                  refine ⟨453133377302789618179442801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302088918201859745452961867 453133377302789618179442801)
                  ·
                    refine ⟨339850032977092213634582101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 453133377302789618179442801 339850032977092213634582101)
                    ·
                      refine ⟨3982617573950299378530259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 339850032977092213634582101 3982617573950299378530259)
                      ·
                        rfl

theorem cell23_7756120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_7756120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756120 prefixEnd_7756120 := by exact prefixLift 7756120
  have htrace : WordTrace (prefixWord ++ tailWord_7756120) baseStart_7756120 baseEnd_7756120 := by
    simpa [prefixWord, tailWord_7756120, baseEnd_7756120] using wordTrace_append hprefix tailTrace_7756120
  have hstable : (prefixWord ++ tailWord_7756120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756120).length < 2 ^ (prefixWord ++ tailWord_7756120).sum := by decide
  have hdescent : baseEnd_7756120 < baseStart_7756120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756126 : List Nat := [4, 4, 2, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7756126 : Nat := 118140960795 + 7756126 * 2 ^ 59
def prefixEnd_7756126 : Nat := 4983230072969 + 3 ^ 40 * 7756126 * 2
def baseEnd_7756126 : Nat := 3982620654834226355055233

theorem tailTrace_7756126 : CollatzResearch.WordTrace tailWord_7756126 prefixEnd_7756126 3982620654834226355055233 := by
  unfold tailWord_7756126
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361144437360952213233029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188592770332591745137242821 35361144437360952213233029)
  ·
    refine ⟨6630214582005178539981193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35361144437360952213233029 6630214582005178539981193)
    ·
      refine ⟨4972660936503883904985895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6630214582005178539981193 4972660936503883904985895)
      ·
        refine ⟨7458991404755825857478843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4972660936503883904985895 7458991404755825857478843)
        ·
          refine ⟨11188487107133738786218265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458991404755825857478843 11188487107133738786218265)
          ·
            refine ⟨8391365330350304089663699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11188487107133738786218265 8391365330350304089663699)
            ·
              refine ⟨12587047995525456134495549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391365330350304089663699 12587047995525456134495549)
              ·
                refine ⟨4720142998322046050435831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12587047995525456134495549 4720142998322046050435831)
                ·
                  refine ⟨7080214497483069075653747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720142998322046050435831 7080214497483069075653747)
                  ·
                    refine ⟨10620321746224603613480621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7080214497483069075653747 10620321746224603613480621)
                    ·
                      refine ⟨3982620654834226355055233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10620321746224603613480621 3982620654834226355055233)
                      ·
                        rfl

theorem cell23_7756126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7756126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756126 prefixEnd_7756126 := by exact prefixLift 7756126
  have htrace : WordTrace (prefixWord ++ tailWord_7756126) baseStart_7756126 baseEnd_7756126 := by
    simpa [prefixWord, tailWord_7756126, baseEnd_7756126] using wordTrace_append hprefix tailTrace_7756126
  have hstable : (prefixWord ++ tailWord_7756126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756126).length < 2 ^ (prefixWord ++ tailWord_7756126).sum := by decide
  have hdescent : baseEnd_7756126 < baseStart_7756126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756141 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_7756141 : Nat := 118140960795 + 7756141 * 2 ^ 59
def prefixEnd_7756141 : Nat := 4983230072969 + 3 ^ 40 * 7756141 * 2
def baseEnd_7756141 : Nat := 3982628357044043796367663

theorem tailTrace_7756141 : CollatzResearch.WordTrace tailWord_7756141 prefixEnd_7756141 3982628357044043796367663 := by
  unfold tailWord_7756141
  simp only [CollatzResearch.WordTrace]
  refine ⟨282889702593833275267660277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188593135062555516845106851 282889702593833275267660277)
  ·
    refine ⟨26520909618171869556343151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282889702593833275267660277 26520909618171869556343151)
    ·
      refine ⟨39781364427257804334514727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26520909618171869556343151 39781364427257804334514727)
      ·
        refine ⟨59672046640886706501772091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39781364427257804334514727 59672046640886706501772091)
        ·
          refine ⟨89508069961330059752658137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59672046640886706501772091 89508069961330059752658137)
          ·
            refine ⟨67131052470997544814493603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89508069961330059752658137 67131052470997544814493603)
            ·
              refine ⟨100696578706496317221740405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67131052470997544814493603 100696578706496317221740405)
              ·
                refine ⟨9440304253734029739538163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100696578706496317221740405 9440304253734029739538163)
                ·
                  refine ⟨14160456380601044609307245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9440304253734029739538163 14160456380601044609307245)
                  ·
                    refine ⟨5310171142725391728490217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14160456380601044609307245 5310171142725391728490217)
                    ·
                      refine ⟨3982628357044043796367663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310171142725391728490217 3982628357044043796367663)
                      ·
                        rfl

theorem cell23_7756141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_7756141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756141 prefixEnd_7756141 := by exact prefixLift 7756141
  have htrace : WordTrace (prefixWord ++ tailWord_7756141) baseStart_7756141 baseEnd_7756141 := by
    simpa [prefixWord, tailWord_7756141, baseEnd_7756141] using wordTrace_append hprefix tailTrace_7756141
  have hstable : (prefixWord ++ tailWord_7756141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756141).length < 2 ^ (prefixWord ++ tailWord_7756141).sum := by decide
  have hdescent : baseEnd_7756141 < baseStart_7756141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756167 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_7756167 : Nat := 118140960795 + 7756167 * 2 ^ 59
def prefixEnd_7756167 : Nat := 4983230072969 + 3 ^ 40 * 7756167 * 2
def baseEnd_7756167 : Nat := 3982641707541060694642543

theorem tailTrace_7756167 : CollatzResearch.WordTrace tailWord_7756167 prefixEnd_7756167 3982641707541060694642543 := by
  unfold tailWord_7756167
  simp only [CollatzResearch.WordTrace]
  refine ⟨282890650891739081708106755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188593767261159387805404503 282890650891739081708106755)
  ·
    refine ⟨424335976337608622562160133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282890650891739081708106755 424335976337608622562160133)
    ·
      refine ⟨79562995563301616730405025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 424335976337608622562160133 79562995563301616730405025)
      ·
        refine ⟨59672246672476212547803769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79562995563301616730405025 59672246672476212547803769)
        ·
          refine ⟨44754185004357159410852827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59672246672476212547803769 44754185004357159410852827)
          ·
            refine ⟨67131277506535739116279241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44754185004357159410852827 67131277506535739116279241)
            ·
              refine ⟨50348458129901804337209431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67131277506535739116279241 50348458129901804337209431)
              ·
                refine ⟨75522687194852706505814147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50348458129901804337209431 75522687194852706505814147)
                ·
                  refine ⟨113284030792279059758721221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75522687194852706505814147 113284030792279059758721221)
                  ·
                    refine ⟨21240755773552323704760229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113284030792279059758721221 21240755773552323704760229)
                    ·
                      refine ⟨3982641707541060694642543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21240755773552323704760229 3982641707541060694642543)
                      ·
                        rfl

theorem cell23_7756167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_7756167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756167 prefixEnd_7756167 := by exact prefixLift 7756167
  have htrace : WordTrace (prefixWord ++ tailWord_7756167) baseStart_7756167 baseEnd_7756167 := by
    simpa [prefixWord, tailWord_7756167, baseEnd_7756167] using wordTrace_append hprefix tailTrace_7756167
  have hstable : (prefixWord ++ tailWord_7756167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756167).length < 2 ^ (prefixWord ++ tailWord_7756167).sum := by decide
  have hdescent : baseEnd_7756167 < baseStart_7756167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756174 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7756174 : Nat := 118140960795 + 7756174 * 2 ^ 59
def prefixEnd_7756174 : Nat := 4983230072969 + 3 ^ 40 * 7756174 * 2
def baseEnd_7756174 : Nat := 3982645301905642167255011

theorem tailTrace_7756174 : CollatzResearch.WordTrace tailWord_7756174 prefixEnd_7756174 3982645301905642167255011 := by
  unfold tailWord_7756174
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361363275339215237951447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188593937468475814602407717 35361363275339215237951447)
  ·
    refine ⟨53042044913008822856927171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35361363275339215237951447 53042044913008822856927171)
    ·
      refine ⟨79563067369513234285390757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53042044913008822856927171 79563067369513234285390757)
      ·
        refine ⟨14918075131783731428510767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79563067369513234285390757 14918075131783731428510767)
        ·
          refine ⟨22377112697675597142766151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14918075131783731428510767 22377112697675597142766151)
          ·
            refine ⟨33565669046513395714149227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22377112697675597142766151 33565669046513395714149227)
            ·
              refine ⟨50348503569770093571223841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33565669046513395714149227 50348503569770093571223841)
              ·
                refine ⟨37761377677327570178417881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50348503569770093571223841 37761377677327570178417881)
                ·
                  refine ⟨28321033257995677633813411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37761377677327570178417881 28321033257995677633813411)
                  ·
                    refine ⟨42481549886993516450720117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28321033257995677633813411 42481549886993516450720117)
                    ·
                      refine ⟨3982645301905642167255011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42481549886993516450720117 3982645301905642167255011)
                      ·
                        rfl

theorem cell23_7756174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7756174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756174 prefixEnd_7756174 := by exact prefixLift 7756174
  have htrace : WordTrace (prefixWord ++ tailWord_7756174) baseStart_7756174 baseEnd_7756174 := by
    simpa [prefixWord, tailWord_7756174, baseEnd_7756174] using wordTrace_append hprefix tailTrace_7756174
  have hstable : (prefixWord ++ tailWord_7756174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756174).length < 2 ^ (prefixWord ++ tailWord_7756174).sum := by decide
  have hdescent : baseEnd_7756174 < baseStart_7756174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756227 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4]
def baseStart_7756227 : Nat := 118140960795 + 7756227 * 2 ^ 59
def prefixEnd_7756227 : Nat := 4983230072969 + 3 ^ 40 * 7756227 * 2
def baseEnd_7756227 : Nat := 3982672516380330459892267

theorem tailTrace_7756227 : CollatzResearch.WordTrace tailWord_7756227 prefixEnd_7756227 3982672516380330459892267 := by
  unfold tailWord_7756227
  simp only [CollatzResearch.WordTrace]
  refine ⟨282892839271521711955290935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188595226181014474636860623 282892839271521711955290935)
  ·
    refine ⟨424339258907282567932936403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282892839271521711955290935 424339258907282567932936403)
    ·
      refine ⟨636508888360923851899404605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424339258907282567932936403 636508888360923851899404605)
      ·
        refine ⟨238690833135346444462276727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 636508888360923851899404605 238690833135346444462276727)
        ·
          refine ⟨358036249703019666693415091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238690833135346444462276727 358036249703019666693415091)
          ·
            refine ⟨537054374554529500040122637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358036249703019666693415091 537054374554529500040122637)
            ·
              refine ⟨201395390457948562515045989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537054374554529500040122637 201395390457948562515045989)
              ·
                refine ⟨37761635710865355471571123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201395390457948562515045989 37761635710865355471571123)
                ·
                  refine ⟨56642453566298033207356685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37761635710865355471571123 56642453566298033207356685)
                  ·
                    refine ⟨21240920087361762452758757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56642453566298033207356685 21240920087361762452758757)
                    ·
                      refine ⟨3982672516380330459892267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21240920087361762452758757 3982672516380330459892267)
                      ·
                        rfl

theorem cell23_7756227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_7756227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756227 prefixEnd_7756227 := by exact prefixLift 7756227
  have htrace : WordTrace (prefixWord ++ tailWord_7756227) baseStart_7756227 baseEnd_7756227 := by
    simpa [prefixWord, tailWord_7756227, baseEnd_7756227] using wordTrace_append hprefix tailTrace_7756227
  have hstable : (prefixWord ++ tailWord_7756227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756227).length < 2 ^ (prefixWord ++ tailWord_7756227).sum := by decide
  have hdescent : baseEnd_7756227 < baseStart_7756227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756257 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7756257 : Nat := 118140960795 + 7756257 * 2 ^ 59
def prefixEnd_7756257 : Nat := 4983230072969 + 3 ^ 40 * 7756257 * 2
def baseEnd_7756257 : Nat := 3982687920799965342517129

theorem tailTrace_7756257 : CollatzResearch.WordTrace tailWord_7756257 prefixEnd_7756257 3982687920799965342517129 := by
  unfold tailWord_7756257
  simp only [CollatzResearch.WordTrace]
  refine ⟨282893933461413027078883025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188595955640942018052588683 282893933461413027078883025)
  ·
    refine ⟨212170450096059770309162269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282893933461413027078883025 212170450096059770309162269)
    ·
      refine ⟨79563918786022413865935851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212170450096059770309162269 79563918786022413865935851)
      ·
        refine ⟨119345878179033620798903777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79563918786022413865935851 119345878179033620798903777)
        ·
          refine ⟨89509408634275215599177833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119345878179033620798903777 89509408634275215599177833)
          ·
            refine ⟨67132056475706411699383375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89509408634275215599177833 67132056475706411699383375)
            ·
              refine ⟨100698084713559617549075063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67132056475706411699383375 100698084713559617549075063)
              ·
                refine ⟨151047127070339426323612595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100698084713559617549075063 151047127070339426323612595)
                ·
                  refine ⟨226570690605509139485418893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151047127070339426323612595 226570690605509139485418893)
                  ·
                    refine ⟨84964008977065927307032085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226570690605509139485418893 84964008977065927307032085)
                    ·
                      refine ⟨3982687920799965342517129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84964008977065927307032085 3982687920799965342517129)
                      ·
                        rfl

theorem cell23_7756257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7756257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756257 prefixEnd_7756257 := by exact prefixLift 7756257
  have htrace : WordTrace (prefixWord ++ tailWord_7756257) baseStart_7756257 baseEnd_7756257 := by
    simpa [prefixWord, tailWord_7756257, baseEnd_7756257] using wordTrace_append hprefix tailTrace_7756257
  have hstable : (prefixWord ++ tailWord_7756257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756257).length < 2 ^ (prefixWord ++ tailWord_7756257).sum := by decide
  have hdescent : baseEnd_7756257 < baseStart_7756257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756267 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 8]
def baseStart_7756267 : Nat := 118140960795 + 7756267 * 2 ^ 59
def prefixEnd_7756267 : Nat := 4983230072969 + 3 ^ 40 * 7756267 * 2
def baseEnd_7756267 : Nat := 442521450622945589265787

theorem tailTrace_7756267 : CollatzResearch.WordTrace tailWord_7756267 prefixEnd_7756267 442521450622945589265787 := by
  unfold tailWord_7756267
  simp only [CollatzResearch.WordTrace]
  refine ⟨282894298191376798786747055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188596198794251199191164703 282894298191376798786747055)
  ·
    refine ⟨424341447287065198180120583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282894298191376798786747055 424341447287065198180120583)
    ·
      refine ⟨636512170930597797270180875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424341447287065198180120583 636512170930597797270180875)
      ·
        refine ⟨954768256395896695905271313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636512170930597797270180875 954768256395896695905271313)
        ·
          refine ⟨716076192296922521928953485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954768256395896695905271313 716076192296922521928953485)
          ·
            refine ⟨268528572111345945723357557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 716076192296922521928953485 268528572111345945723357557)
            ·
              refine ⟨25174553635438682411564771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268528572111345945723357557 25174553635438682411564771)
              ·
                refine ⟨37761830453158023617347157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25174553635438682411564771 37761830453158023617347157)
                ·
                  refine ⟨442521450622945589265787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37761830453158023617347157 442521450622945589265787)
                  ·
                    rfl

theorem cell23_7756267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 8].length) (baseStart_7756267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756267 prefixEnd_7756267 := by exact prefixLift 7756267
  have htrace : WordTrace (prefixWord ++ tailWord_7756267) baseStart_7756267 baseEnd_7756267 := by
    simpa [prefixWord, tailWord_7756267, baseEnd_7756267] using wordTrace_append hprefix tailTrace_7756267
  have hstable : (prefixWord ++ tailWord_7756267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756267).length < 2 ^ (prefixWord ++ tailWord_7756267).sum := by decide
  have hdescent : baseEnd_7756267 < baseStart_7756267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756287 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_7756287 : Nat := 118140960795 + 7756287 * 2 ^ 59
def prefixEnd_7756287 : Nat := 4983230072969 + 3 ^ 40 * 7756287 * 2
def baseEnd_7756287 : Nat := 3982703325219600225141991

theorem tailTrace_7756287 : CollatzResearch.WordTrace tailWord_7756287 prefixEnd_7756287 3982703325219600225141991 := by
  unfold tailWord_7756287
  simp only [CollatzResearch.WordTrace]
  refine ⟨282895027651304342202475115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188596685100869561468316743 282895027651304342202475115)
  ·
    refine ⟨424342541476956513303712673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282895027651304342202475115 424342541476956513303712673)
    ·
      refine ⟨318256906107717384977784505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424342541476956513303712673 318256906107717384977784505)
      ·
        refine ⟨238692679580788038733338379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318256906107717384977784505 238692679580788038733338379)
        ·
          refine ⟨358039019371182058100007569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238692679580788038733338379 358039019371182058100007569)
          ·
            refine ⟨268529264528386543575005677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358039019371182058100007569 268529264528386543575005677)
            ·
              refine ⟨100698474198144953840627129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268529264528386543575005677 100698474198144953840627129)
              ·
                refine ⟨75523855648608715380470347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100698474198144953840627129 75523855648608715380470347)
                ·
                  refine ⟨113285783472913073070705521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75523855648608715380470347 113285783472913073070705521)
                  ·
                    refine ⟨84964337604684804803029141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113285783472913073070705521 84964337604684804803029141)
                    ·
                      refine ⟨3982703325219600225141991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84964337604684804803029141 3982703325219600225141991)
                      ·
                        rfl

theorem cell23_7756287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_7756287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756287 prefixEnd_7756287 := by exact prefixLift 7756287
  have htrace : WordTrace (prefixWord ++ tailWord_7756287) baseStart_7756287 baseEnd_7756287 := by
    simpa [prefixWord, tailWord_7756287, baseEnd_7756287] using wordTrace_append hprefix tailTrace_7756287
  have hstable : (prefixWord ++ tailWord_7756287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756287).length < 2 ^ (prefixWord ++ tailWord_7756287).sum := by decide
  have hdescent : baseEnd_7756287 < baseStart_7756287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756344 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 1, 6]
def baseStart_7756344 : Nat := 118140960795 + 7756344 * 2 ^ 59
def prefixEnd_7756344 : Nat := 4983230072969 + 3 ^ 40 * 7756344 * 2
def baseEnd_7756344 : Nat := 1327577531205635500709743

theorem tailTrace_7756344 : CollatzResearch.WordTrace tailWord_7756344 prefixEnd_7756344 1327577531205635500709743 := by
  unfold tailWord_7756344
  simp only [CollatzResearch.WordTrace]
  refine ⟨141448553306048920468650043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188598071074731893958200057 141448553306048920468650043)
  ·
    refine ⟨212172829959073380702975065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141448553306048920468650043 212172829959073380702975065)
    ·
      refine ⟨159129622469305035527231299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212172829959073380702975065 159129622469305035527231299)
      ·
        refine ⟨238694433703957553290846949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159129622469305035527231299 238694433703957553290846949)
        ·
          refine ⟨44755206319492041242033803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238694433703957553290846949 44755206319492041242033803)
          ·
            refine ⟨67132809479238061863050705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44755206319492041242033803 67132809479238061863050705)
            ·
              refine ⟨50349607109428546397288029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67132809479238061863050705 50349607109428546397288029)
              ·
                refine ⟨18881102666035704898983011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50349607109428546397288029 18881102666035704898983011)
                ·
                  refine ⟨28321653999053557348474517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18881102666035704898983011 28321653999053557348474517)
                  ·
                    refine ⟨1327577531205635500709743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28321653999053557348474517 1327577531205635500709743)
                    ·
                      rfl

theorem cell23_7756344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_7756344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756344 prefixEnd_7756344 := by exact prefixLift 7756344
  have htrace : WordTrace (prefixWord ++ tailWord_7756344) baseStart_7756344 baseEnd_7756344 := by
    simpa [prefixWord, tailWord_7756344, baseEnd_7756344] using wordTrace_append hprefix tailTrace_7756344
  have hstable : (prefixWord ++ tailWord_7756344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756344).length < 2 ^ (prefixWord ++ tailWord_7756344).sum := by decide
  have hdescent : baseEnd_7756344 < baseStart_7756344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756348 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_7756348 : Nat := 118140960795 + 7756348 * 2 ^ 59
def prefixEnd_7756348 : Nat := 4983230072969 + 3 ^ 40 * 7756348 * 2
def baseEnd_7756348 : Nat := 1327578215846508162159737

theorem tailTrace_7756348 : CollatzResearch.WordTrace tailWord_7756348 prefixEnd_7756348 1327578215846508162159737 := by
  unfold tailWord_7756348
  simp only [CollatzResearch.WordTrace]
  refine ⟨141448626252041674810222849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188598168336055566413630465 141448626252041674810222849)
  ·
    refine ⟨106086469689031256107667137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141448626252041674810222849 106086469689031256107667137)
    ·
      refine ⟨79564852266773442080750353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106086469689031256107667137 79564852266773442080750353)
      ·
        refine ⟨59673639200080081560562765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79564852266773442080750353 59673639200080081560562765)
        ·
          refine ⟨22377614700030030585211037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59673639200080081560562765 22377614700030030585211037)
          ·
            refine ⟨8391605512511261469454139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22377614700030030585211037 8391605512511261469454139)
            ·
              refine ⟨12587408268766892204181209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391605512511261469454139 12587408268766892204181209)
              ·
                refine ⟨9440556201575169153135907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12587408268766892204181209 9440556201575169153135907)
                ·
                  refine ⟨14160834302362753729703861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9440556201575169153135907 14160834302362753729703861)
                  ·
                    refine ⟨1327578215846508162159737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14160834302362753729703861 1327578215846508162159737)
                    ·
                      rfl

theorem cell23_7756348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_7756348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756348 prefixEnd_7756348 := by exact prefixLift 7756348
  have htrace : WordTrace (prefixWord ++ tailWord_7756348) baseStart_7756348 baseEnd_7756348 := by
    simpa [prefixWord, tailWord_7756348, baseEnd_7756348] using wordTrace_append hprefix tailTrace_7756348
  have hstable : (prefixWord ++ tailWord_7756348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756348).length < 2 ^ (prefixWord ++ tailWord_7756348).sum := by decide
  have hdescent : baseEnd_7756348 < baseStart_7756348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756365 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_7756365 : Nat := 118140960795 + 7756365 * 2 ^ 59
def prefixEnd_7756365 : Nat := 4983230072969 + 3 ^ 40 * 7756365 * 2
def baseEnd_7756365 : Nat := 1327581125570216973322211

theorem tailTrace_7756365 : CollatzResearch.WordTrace tailWord_7756365 prefixEnd_7756365 1327581125570216973322211 := by
  unfold tailWord_7756365
  simp only [CollatzResearch.WordTrace]
  refine ⟨282897872545021761523814549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188598581696681174349209699 282897872545021761523814549)
  ·
    refine ⟨13260837775547895071428807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282897872545021761523814549 13260837775547895071428807)
    ·
      refine ⟨19891256663321842607143211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13260837775547895071428807 19891256663321842607143211)
      ·
        refine ⟨29836884994982763910714817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19891256663321842607143211 29836884994982763910714817)
        ·
          refine ⟨22377663746237072933036113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29836884994982763910714817 22377663746237072933036113)
          ·
            refine ⟨16783247809677804699777085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22377663746237072933036113 16783247809677804699777085)
            ·
              refine ⟨6293717928629176762416407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16783247809677804699777085 6293717928629176762416407)
              ·
                refine ⟨9440576892943765143624611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293717928629176762416407 9440576892943765143624611)
                ·
                  refine ⟨14160865339415647715436917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9440576892943765143624611 14160865339415647715436917)
                  ·
                    refine ⟨1327581125570216973322211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14160865339415647715436917 1327581125570216973322211)
                    ·
                      rfl

theorem cell23_7756365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_7756365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756365 prefixEnd_7756365 := by exact prefixLift 7756365
  have htrace : WordTrace (prefixWord ++ tailWord_7756365) baseStart_7756365 baseEnd_7756365 := by
    simpa [prefixWord, tailWord_7756365, baseEnd_7756365] using wordTrace_append hprefix tailTrace_7756365
  have hstable : (prefixWord ++ tailWord_7756365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756365).length < 2 ^ (prefixWord ++ tailWord_7756365).sum := by decide
  have hdescent : baseEnd_7756365 < baseStart_7756365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756398 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_7756398 : Nat := 118140960795 + 7756398 * 2 ^ 59
def prefixEnd_7756398 : Nat := 4983230072969 + 3 ^ 40 * 7756398 * 2
def baseEnd_7756398 : Nat := 3982760321572249290853981

theorem tailTrace_7756398 : CollatzResearch.WordTrace tailWord_7756398 prefixEnd_7756398 3982760321572249290853981 := by
  unfold tailWord_7756398
  simp only [CollatzResearch.WordTrace]
  refine ⟨35362384519237776019970731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188599384102601472106510565 35362384519237776019970731)
  ·
    refine ⟨53043576778856664029956097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35362384519237776019970731 53043576778856664029956097)
    ·
      refine ⟨39782682584142498022467073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53043576778856664029956097 39782682584142498022467073)
      ·
        refine ⟨29837011938106873516850305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39782682584142498022467073 29837011938106873516850305)
        ·
          refine ⟨22377758953580155137637729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29837011938106873516850305 22377758953580155137637729)
          ·
            refine ⟨16783319215185116353228297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22377758953580155137637729 16783319215185116353228297)
            ·
              refine ⟨12587489411388837264921223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16783319215185116353228297 12587489411388837264921223)
              ·
                refine ⟨18881234117083255897381835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12587489411388837264921223 18881234117083255897381835)
                ·
                  refine ⟨28321851175624883846072753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18881234117083255897381835 28321851175624883846072753)
                  ·
                    refine ⟨21241388381718662884554565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28321851175624883846072753 21241388381718662884554565)
                    ·
                      refine ⟨3982760321572249290853981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21241388381718662884554565 3982760321572249290853981)
                      ·
                        rfl

theorem cell23_7756398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_7756398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756398 prefixEnd_7756398 := by exact prefixLift 7756398
  have htrace : WordTrace (prefixWord ++ tailWord_7756398) baseStart_7756398 baseEnd_7756398 := by
    simpa [prefixWord, tailWord_7756398, baseEnd_7756398] using wordTrace_append hprefix tailTrace_7756398
  have hstable : (prefixWord ++ tailWord_7756398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756398).length < 2 ^ (prefixWord ++ tailWord_7756398).sum := by decide
  have hdescent : baseEnd_7756398 < baseStart_7756398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756401 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_7756401 : Nat := 118140960795 + 7756401 * 2 ^ 59
def prefixEnd_7756401 : Nat := 4983230072969 + 3 ^ 40 * 7756401 * 2
def baseEnd_7756401 : Nat := 3982761862014212779116467

theorem tailTrace_7756401 : CollatzResearch.WordTrace tailWord_7756401 prefixEnd_7756401 3982761862014212779116467 := by
  unfold tailWord_7756401
  simp only [CollatzResearch.WordTrace]
  refine ⟨282899185572891339672125057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188599457048594226448083371 282899185572891339672125057)
  ·
    refine ⟨212174389179668504754093793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282899185572891339672125057 212174389179668504754093793)
    ·
      refine ⟨159130791884751378565570345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212174389179668504754093793 159130791884751378565570345)
      ·
        refine ⟨119348093913563533924177759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159130791884751378565570345 119348093913563533924177759)
        ·
          refine ⟨179022140870345300886266639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119348093913563533924177759 179022140870345300886266639)
          ·
            refine ⟨268533211305517951329399959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179022140870345300886266639 268533211305517951329399959)
            ·
              refine ⟨402799816958276926994099939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268533211305517951329399959 402799816958276926994099939)
              ·
                refine ⟨604199725437415390491149909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402799816958276926994099939 604199725437415390491149909)
                ·
                  refine ⟨7080465532469711607318163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 604199725437415390491149909 7080465532469711607318163)
                  ·
                    refine ⟨10620698298704567410977245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7080465532469711607318163 10620698298704567410977245)
                    ·
                      refine ⟨3982761862014212779116467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10620698298704567410977245 3982761862014212779116467)
                      ·
                        rfl

theorem cell23_7756401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_7756401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756401 prefixEnd_7756401 := by exact prefixLift 7756401
  have htrace : WordTrace (prefixWord ++ tailWord_7756401) baseStart_7756401 baseEnd_7756401 := by
    simpa [prefixWord, tailWord_7756401, baseEnd_7756401] using wordTrace_append hprefix tailTrace_7756401
  have hstable : (prefixWord ++ tailWord_7756401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756401).length < 2 ^ (prefixWord ++ tailWord_7756401).sum := by decide
  have hdescent : baseEnd_7756401 < baseStart_7756401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756462 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7756462 : Nat := 118140960795 + 7756462 * 2 ^ 59
def prefixEnd_7756462 : Nat := 4983230072969 + 3 ^ 40 * 7756462 * 2
def baseEnd_7756462 : Nat := 3982793184334137040453687

theorem tailTrace_7756462 : CollatzResearch.WordTrace tailWord_7756462 prefixEnd_7756462 3982793184334137040453687 := by
  unfold tailWord_7756462
  simp only [CollatzResearch.WordTrace]
  refine ⟨35362676303208793386261955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188600940283780231393397093 35362676303208793386261955)
  ·
    refine ⟨53044014454813190079392933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35362676303208793386261955 53044014454813190079392933)
    ·
      refine ⟨9945752710277473139886175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53044014454813190079392933 9945752710277473139886175)
      ·
        refine ⟨14918629065416209709829263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9945752710277473139886175 14918629065416209709829263)
        ·
          refine ⟨22377943598124314564743895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14918629065416209709829263 22377943598124314564743895)
          ·
            refine ⟨33566915397186471847115843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22377943598124314564743895 33566915397186471847115843)
            ·
              refine ⟨50350373095779707770673765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33566915397186471847115843 50350373095779707770673765)
              ·
                refine ⟨9440694955458695207001331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50350373095779707770673765 9440694955458695207001331)
                ·
                  refine ⟨14161042433188042810501997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9440694955458695207001331 14161042433188042810501997)
                  ·
                    refine ⟨5310390912445516053938249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14161042433188042810501997 5310390912445516053938249)
                    ·
                      refine ⟨3982793184334137040453687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310390912445516053938249 3982793184334137040453687)
                      ·
                        rfl

theorem cell23_7756462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7756462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756462 prefixEnd_7756462 := by exact prefixLift 7756462
  have htrace : WordTrace (prefixWord ++ tailWord_7756462) baseStart_7756462 baseEnd_7756462 := by
    simpa [prefixWord, tailWord_7756462, baseEnd_7756462] using wordTrace_append hprefix tailTrace_7756462
  have hstable : (prefixWord ++ tailWord_7756462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756462).length < 2 ^ (prefixWord ++ tailWord_7756462).sum := by decide
  have hdescent : baseEnd_7756462 < baseStart_7756462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756548 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7756548 : Nat := 118140960795 + 7756548 * 2 ^ 59
def prefixEnd_7756548 : Nat := 4983230072969 + 3 ^ 40 * 7756548 * 2
def baseEnd_7756548 : Nat := 3982837343670423703978291

theorem tailTrace_7756548 : CollatzResearch.WordTrace tailWord_7756548 prefixEnd_7756548 3982837343670423703978291 := by
  unfold tailWord_7756548
  simp only [CollatzResearch.WordTrace]
  refine ⟨141452273551679391888863149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188603031402239189185150865 141452273551679391888863149)
  ·
    refine ⟨53044602581879771958323681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141452273551679391888863149 53044602581879771958323681)
    ·
      refine ⟨39783451936409828968742761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53044602581879771958323681 39783451936409828968742761)
      ·
        refine ⟨29837588952307371726557071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39783451936409828968742761 29837588952307371726557071)
        ·
          refine ⟨44756383428461057589835607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29837588952307371726557071 44756383428461057589835607)
          ·
            refine ⟨67134575142691586384753411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44756383428461057589835607 67134575142691586384753411)
            ·
              refine ⟨100701862714037379577130117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67134575142691586384753411 100701862714037379577130117)
              ·
                refine ⟨18881599258882008670711897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100701862714037379577130117 18881599258882008670711897)
                ·
                  refine ⟨14161199444161506503033923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18881599258882008670711897 14161199444161506503033923)
                  ·
                    refine ⟨21241799166242259754550885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14161199444161506503033923 21241799166242259754550885)
                    ·
                      refine ⟨3982837343670423703978291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21241799166242259754550885 3982837343670423703978291)
                      ·
                        rfl

theorem cell23_7756548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7756548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756548 prefixEnd_7756548 := by exact prefixLift 7756548
  have htrace : WordTrace (prefixWord ++ tailWord_7756548) baseStart_7756548 baseEnd_7756548 := by
    simpa [prefixWord, tailWord_7756548, baseEnd_7756548] using wordTrace_append hprefix tailTrace_7756548
  have hstable : (prefixWord ++ tailWord_7756548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756548).length < 2 ^ (prefixWord ++ tailWord_7756548).sum := by decide
  have hdescent : baseEnd_7756548 < baseStart_7756548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756558 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_7756558 : Nat := 118140960795 + 7756558 * 2 ^ 59
def prefixEnd_7756558 : Nat := 4983230072969 + 3 ^ 40 * 7756558 * 2
def baseEnd_7756558 : Nat := 1327614159492322888284415

theorem tailTrace_7756558 : CollatzResearch.WordTrace tailWord_7756558 prefixEnd_7756558 1327614159492322888284415 := by
  unfold tailWord_7756558
  simp only [CollatzResearch.WordTrace]
  refine ⟨35363113979165319435698791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188603274555548370323726885 35363113979165319435698791)
  ·
    refine ⟨53044670968747979153548187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35363113979165319435698791 53044670968747979153548187)
    ·
      refine ⟨79567006453121968730322281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53044670968747979153548187 79567006453121968730322281)
      ·
        refine ⟨59675254839841476547741711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79567006453121968730322281 59675254839841476547741711)
        ·
          refine ⟨89512882259762214821612567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59675254839841476547741711 89512882259762214821612567)
          ·
            refine ⟨134269323389643322232418851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89512882259762214821612567 134269323389643322232418851)
            ·
              refine ⟨201403985084464983348628277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134269323389643322232418851 201403985084464983348628277)
              ·
                refine ⟨18881623601668592188933901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201403985084464983348628277 18881623601668592188933901)
                ·
                  refine ⟨7080608850625722070850213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18881623601668592188933901 7080608850625722070850213)
                  ·
                    refine ⟨1327614159492322888284415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7080608850625722070850213 1327614159492322888284415)
                    ·
                      rfl

theorem cell23_7756558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_7756558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756558 prefixEnd_7756558 := by exact prefixLift 7756558
  have htrace : WordTrace (prefixWord ++ tailWord_7756558) baseStart_7756558 baseEnd_7756558 := by
    simpa [prefixWord, tailWord_7756558, baseEnd_7756558] using wordTrace_append hprefix tailTrace_7756558
  have hstable : (prefixWord ++ tailWord_7756558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756558).length < 2 ^ (prefixWord ++ tailWord_7756558).sum := by decide
  have hdescent : baseEnd_7756558 < baseStart_7756558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756655 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 5, 2, 2]
def baseStart_7756655 : Nat := 118140960795 + 7756655 * 2 ^ 59
def prefixEnd_7756655 : Nat := 4983230072969 + 3 ^ 40 * 7756655 * 2
def baseEnd_7756655 : Nat := 3982892286100454785340299

theorem tailTrace_7756655 : CollatzResearch.WordTrace tailWord_7756655 prefixEnd_7756655 3982892286100454785340299 := by
  unfold tailWord_7756655
  simp only [CollatzResearch.WordTrace]
  refine ⟨282908449713971141051871419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188605633142647427367914279 282908449713971141051871419)
  ·
    refine ⟨424362674570956711577807129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282908449713971141051871419 424362674570956711577807129)
    ·
      refine ⟨318272005928217533683355347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424362674570956711577807129 318272005928217533683355347)
      ·
        refine ⟨477408008892326300525033021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318272005928217533683355347 477408008892326300525033021)
        ·
          refine ⟨179028003334622362696887383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477408008892326300525033021 179028003334622362696887383)
          ·
            refine ⟨268542005001933544045331075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179028003334622362696887383 268542005001933544045331075)
            ·
              refine ⟨402813007502900316067996613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268542005001933544045331075 402813007502900316067996613)
              ·
                refine ⟨75527438906793809262749365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402813007502900316067996613 75527438906793809262749365)
                ·
                  refine ⟨7080697397511919618382753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75527438906793809262749365 7080697397511919618382753)
                  ·
                    refine ⟨5310523048133939713787065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7080697397511919618382753 5310523048133939713787065)
                    ·
                      refine ⟨3982892286100454785340299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310523048133939713787065 3982892286100454785340299)
                      ·
                        rfl

theorem cell23_7756655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 2, 2].length) (baseStart_7756655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756655 prefixEnd_7756655 := by exact prefixLift 7756655
  have htrace : WordTrace (prefixWord ++ tailWord_7756655) baseStart_7756655 baseEnd_7756655 := by
    simpa [prefixWord, tailWord_7756655, baseEnd_7756655] using wordTrace_append hprefix tailTrace_7756655
  have hstable : (prefixWord ++ tailWord_7756655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756655).length < 2 ^ (prefixWord ++ tailWord_7756655).sum := by decide
  have hdescent : baseEnd_7756655 < baseStart_7756655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756658 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_7756658 : Nat := 118140960795 + 7756658 * 2 ^ 59
def prefixEnd_7756658 : Nat := 4983230072969 + 3 ^ 40 * 7756658 * 2
def baseEnd_7756658 : Nat := 3982893826542418273602785

theorem tailTrace_7756658 : CollatzResearch.WordTrace tailWord_7756658 prefixEnd_7756658 3982893826542418273602785 := by
  unfold tailWord_7756658
  simp only [CollatzResearch.WordTrace]
  refine ⟨70727139783240068141057657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188605706088640181709487085 70727139783240068141057657)
  ·
    refine ⟨53045354837430051105793243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70727139783240068141057657 53045354837430051105793243)
    ·
      refine ⟨79568032256145076658689865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53045354837430051105793243 79568032256145076658689865)
      ·
        refine ⟨59676024192108807494017399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79568032256145076658689865 59676024192108807494017399)
        ·
          refine ⟨89514036288163211241026099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59676024192108807494017399 89514036288163211241026099)
          ·
            refine ⟨134271054432244816861539149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89514036288163211241026099 134271054432244816861539149)
            ·
              refine ⟨50351645412091806323077181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134271054432244816861539149 50351645412091806323077181)
              ·
                refine ⟨18881867029534427371153943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50351645412091806323077181 18881867029534427371153943)
                ·
                  refine ⟨28322800544301641056730915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18881867029534427371153943 28322800544301641056730915)
                  ·
                    refine ⟨42484200816452461585096373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28322800544301641056730915 42484200816452461585096373)
                    ·
                      refine ⟨3982893826542418273602785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42484200816452461585096373 3982893826542418273602785)
                      ·
                        rfl

theorem cell23_7756658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_7756658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756658 prefixEnd_7756658 := by exact prefixLift 7756658
  have htrace : WordTrace (prefixWord ++ tailWord_7756658) baseStart_7756658 baseEnd_7756658 := by
    simpa [prefixWord, tailWord_7756658, baseEnd_7756658] using wordTrace_append hprefix tailTrace_7756658
  have hstable : (prefixWord ++ tailWord_7756658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756658).length < 2 ^ (prefixWord ++ tailWord_7756658).sum := by decide
  have hdescent : baseEnd_7756658 < baseStart_7756658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756682 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_7756682 : Nat := 118140960795 + 7756682 * 2 ^ 59
def prefixEnd_7756682 : Nat := 4983230072969 + 3 ^ 40 * 7756682 * 2
def baseEnd_7756682 : Nat := 1327635383359375393234225

theorem tailTrace_7756682 : CollatzResearch.WordTrace tailWord_7756682 prefixEnd_7756682 1327635383359375393234225 := by
  unfold tailWord_7756682
  simp only [CollatzResearch.WordTrace]
  refine ⟨70727358621218331165776075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188606289656582216442069533 70727358621218331165776075)
  ·
    refine ⟨106091037931827496748664113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70727358621218331165776075 106091037931827496748664113)
    ·
      refine ⟨79568278448870622561498085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106091037931827496748664113 79568278448870622561498085)
      ·
        refine ⟨14919052209163241730280891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79568278448870622561498085 14919052209163241730280891)
        ·
          refine ⟨22378578313744862595421337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14919052209163241730280891 22378578313744862595421337)
          ·
            refine ⟨16783933735308646946566003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22378578313744862595421337 16783933735308646946566003)
            ·
              refine ⟨25175900602962970419849005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16783933735308646946566003 25175900602962970419849005)
              ·
                refine ⟨9440962726111113907443377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25175900602962970419849005 9440962726111113907443377)
                ·
                  refine ⟨7080722044583335430582533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9440962726111113907443377 7080722044583335430582533)
                  ·
                    refine ⟨1327635383359375393234225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7080722044583335430582533 1327635383359375393234225)
                    ·
                      rfl

theorem cell23_7756682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_7756682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756682 prefixEnd_7756682 := by exact prefixLift 7756682
  have htrace : WordTrace (prefixWord ++ tailWord_7756682) baseStart_7756682 baseEnd_7756682 := by
    simpa [prefixWord, tailWord_7756682, baseEnd_7756682] using wordTrace_append hprefix tailTrace_7756682
  have hstable : (prefixWord ++ tailWord_7756682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756682).length < 2 ^ (prefixWord ++ tailWord_7756682).sum := by decide
  have hdescent : baseEnd_7756682 < baseStart_7756682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756691 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 4, 7]
def baseStart_7756691 : Nat := 118140960795 + 7756691 * 2 ^ 59
def prefixEnd_7756691 : Nat := 4983230072969 + 3 ^ 40 * 7756691 * 2
def baseEnd_7756691 : Nat := 1327636923801338881496711

theorem tailTrace_7756691 : CollatzResearch.WordTrace tailWord_7756691 prefixEnd_7756691 1327636923801338881496711 := by
  unfold tailWord_7756691
  simp only [CollatzResearch.WordTrace]
  refine ⟨282909762741840719200181927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188606508494560479466787951 282909762741840719200181927)
  ·
    refine ⟨424364644112761078800272891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282909762741840719200181927 424364644112761078800272891)
    ·
      refine ⟨636546966169141618200409337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424364644112761078800272891 636546966169141618200409337)
      ·
        refine ⟨477410224626856213650307003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636546966169141618200409337 477410224626856213650307003)
        ·
          refine ⟨716115336940284320475460505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477410224626856213650307003 716115336940284320475460505)
          ·
            refine ⟨537086502705213240356595379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716115336940284320475460505 537086502705213240356595379)
            ·
              refine ⟨805629754057819860534893069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537086502705213240356595379 805629754057819860534893069)
              ·
                refine ⟨302111157771682447700584901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805629754057819860534893069 302111157771682447700584901)
                ·
                  refine ⟨56645842082190458943859669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 302111157771682447700584901 56645842082190458943859669)
                  ·
                    refine ⟨1327636923801338881496711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56645842082190458943859669 1327636923801338881496711)
                    ·
                      rfl

theorem cell23_7756691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 7].length) (baseStart_7756691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756691 prefixEnd_7756691 := by exact prefixLift 7756691
  have htrace : WordTrace (prefixWord ++ tailWord_7756691) baseStart_7756691 baseEnd_7756691 := by
    simpa [prefixWord, tailWord_7756691, baseEnd_7756691] using wordTrace_append hprefix tailTrace_7756691
  have hstable : (prefixWord ++ tailWord_7756691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756691).length < 2 ^ (prefixWord ++ tailWord_7756691).sum := by decide
  have hdescent : baseEnd_7756691 < baseStart_7756691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756705 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7756705 : Nat := 118140960795 + 7756705 * 2 ^ 59
def prefixEnd_7756705 : Nat := 4983230072969 + 3 ^ 40 * 7756705 * 2
def baseEnd_7756705 : Nat := 3982917960133179589715069

theorem tailTrace_7756705 : CollatzResearch.WordTrace tailWord_7756705 prefixEnd_7756705 3982917960133179589715069 := by
  unfold tailWord_7756705
  simp only [CollatzResearch.WordTrace]
  refine ⟨282910273363789999591191569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188606848909193333060794379 282910273363789999591191569)
  ·
    refine ⟨212182705022842499693393677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282910273363789999591191569 212182705022842499693393677)
    ·
      refine ⟨79568514383565937385022629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212182705022842499693393677 79568514383565937385022629)
      ·
        refine ⟨14919096446918613259691743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79568514383565937385022629 14919096446918613259691743)
        ·
          refine ⟨22378644670377919889537615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14919096446918613259691743 22378644670377919889537615)
          ·
            refine ⟨33567967005566879834306423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22378644670377919889537615 33567967005566879834306423)
            ·
              refine ⟨50351950508350319751459635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33567967005566879834306423 50351950508350319751459635)
              ·
                refine ⟨75527925762525479627189453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50351950508350319751459635 75527925762525479627189453)
                ·
                  refine ⟨28322972160947054860196045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75527925762525479627189453 28322972160947054860196045)
                  ·
                    refine ⟨10621114560355145572573517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28322972160947054860196045 10621114560355145572573517)
                    ·
                      refine ⟨3982917960133179589715069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10621114560355145572573517 3982917960133179589715069)
                      ·
                        rfl

theorem cell23_7756705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7756705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756705 prefixEnd_7756705 := by exact prefixLift 7756705
  have htrace : WordTrace (prefixWord ++ tailWord_7756705) baseStart_7756705 baseEnd_7756705 := by
    simpa [prefixWord, tailWord_7756705, baseEnd_7756705] using wordTrace_append hprefix tailTrace_7756705
  have hstable : (prefixWord ++ tailWord_7756705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756705).length < 2 ^ (prefixWord ++ tailWord_7756705).sum := by decide
  have hdescent : baseEnd_7756705 < baseStart_7756705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756728 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_7756728 : Nat := 118140960795 + 7756728 * 2 ^ 59
def prefixEnd_7756728 : Nat := 4983230072969 + 3 ^ 40 * 7756728 * 2
def baseEnd_7756728 : Nat := 3982929770188232999727463

theorem tailTrace_7756728 : CollatzResearch.WordTrace tailWord_7756728 prefixEnd_7756728 3982929770188232999727463 := by
  unfold tailWord_7756728
  simp only [CollatzResearch.WordTrace]
  refine ⟨141455556121353337259639419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188607408161804449679519225 141455556121353337259639419)
  ·
    refine ⟨212183334182030005889459129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141455556121353337259639419 212183334182030005889459129)
    ·
      refine ⟨159137500636522504417094347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212183334182030005889459129 159137500636522504417094347)
      ·
        refine ⟨238706250954783756625641521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159137500636522504417094347 238706250954783756625641521)
        ·
          refine ⟨179029688216087817469231141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238706250954783756625641521 179029688216087817469231141)
          ·
            refine ⟨33568066540516465775480839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179029688216087817469231141 33568066540516465775480839)
            ·
              refine ⟨50352099810774698663221259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33568066540516465775480839 50352099810774698663221259)
              ·
                refine ⟨75528149716162047994831889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50352099810774698663221259 75528149716162047994831889)
                ·
                  refine ⟨56646112287121535996123917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75528149716162047994831889 56646112287121535996123917)
                  ·
                    refine ⟨21242292107670575998546469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56646112287121535996123917 21242292107670575998546469)
                    ·
                      refine ⟨3982929770188232999727463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21242292107670575998546469 3982929770188232999727463)
                      ·
                        rfl

theorem cell23_7756728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_7756728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756728 prefixEnd_7756728 := by exact prefixLift 7756728
  have htrace : WordTrace (prefixWord ++ tailWord_7756728) baseStart_7756728 baseEnd_7756728 := by
    simpa [prefixWord, tailWord_7756728, baseEnd_7756728] using wordTrace_append hprefix tailTrace_7756728
  have hstable : (prefixWord ++ tailWord_7756728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756728).length < 2 ^ (prefixWord ++ tailWord_7756728).sum := by decide
  have hdescent : baseEnd_7756728 < baseStart_7756728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756762 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2]
def baseStart_7756762 : Nat := 118140960795 + 7756762 * 2 ^ 59
def prefixEnd_7756762 : Nat := 4983230072969 + 3 ^ 40 * 7756762 * 2
def baseEnd_7756762 : Nat := 3982947228530485866702307

theorem tailTrace_7756762 : CollatzResearch.WordTrace tailWord_7756762 prefixEnd_7756762 3982947228530485866702307 := by
  unfold tailWord_7756762
  simp only [CollatzResearch.WordTrace]
  refine ⟨70728088081145874581504135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188608234883055665550677693 70728088081145874581504135)
  ·
    refine ⟨106092132121718811872256203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70728088081145874581504135 106092132121718811872256203)
    ·
      refine ⟨159138198182578217808384305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106092132121718811872256203 159138198182578217808384305)
      ·
        refine ⟨119353648636933663356288229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159138198182578217808384305 119353648636933663356288229)
        ·
          refine ⟨22378809119425061879304043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119353648636933663356288229 22378809119425061879304043)
          ·
            refine ⟨33568213679137592818956065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22378809119425061879304043 33568213679137592818956065)
            ·
              refine ⟨25176160259353194614217049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33568213679137592818956065 25176160259353194614217049)
              ·
                refine ⟨18882120194514895960662787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25176160259353194614217049 18882120194514895960662787)
                ·
                  refine ⟨28323180291772343940994181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18882120194514895960662787 28323180291772343940994181)
                  ·
                    refine ⟨5310596304707314488936409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28323180291772343940994181 5310596304707314488936409)
                    ·
                      refine ⟨3982947228530485866702307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310596304707314488936409 3982947228530485866702307)
                      ·
                        rfl

theorem cell23_7756762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_7756762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756762 prefixEnd_7756762 := by exact prefixLift 7756762
  have htrace : WordTrace (prefixWord ++ tailWord_7756762) baseStart_7756762 baseEnd_7756762 := by
    simpa [prefixWord, tailWord_7756762, baseEnd_7756762] using wordTrace_append hprefix tailTrace_7756762
  have hstable : (prefixWord ++ tailWord_7756762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756762).length < 2 ^ (prefixWord ++ tailWord_7756762).sum := by decide
  have hdescent : baseEnd_7756762 < baseStart_7756762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756773 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7756773 : Nat := 118140960795 + 7756773 * 2 ^ 59
def prefixEnd_7756773 : Nat := 4983230072969 + 3 ^ 40 * 7756773 * 2
def baseEnd_7756773 : Nat := 3982952876817685323664757

theorem tailTrace_7756773 : CollatzResearch.WordTrace tailWord_7756773 prefixEnd_7756773 3982952876817685323664757 := by
  unfold tailWord_7756773
  simp only [CollatzResearch.WordTrace]
  refine ⟨282912753527543647204666973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188608502351695764803111315 282912753527543647204666973)
  ·
    refine ⟨106092282572828867701750115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282912753527543647204666973 106092282572828867701750115)
    ·
      refine ⟨159138423859243301552625173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106092282572828867701750115 159138423859243301552625173)
      ·
        refine ⟨7459613618402029760279305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159138423859243301552625173 7459613618402029760279305)
        ·
          refine ⟨5594710213801522320209479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7459613618402029760279305 5594710213801522320209479)
          ·
            refine ⟨8392065320702283480314219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594710213801522320209479 8392065320702283480314219)
            ·
              refine ⟨12588097981053425220471329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8392065320702283480314219 12588097981053425220471329)
              ·
                refine ⟨9441073485790068915353497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588097981053425220471329 9441073485790068915353497)
                ·
                  refine ⟨7080805114342551686515123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441073485790068915353497 7080805114342551686515123)
                  ·
                    refine ⟨10621207671513827529772685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7080805114342551686515123 10621207671513827529772685)
                    ·
                      refine ⟨3982952876817685323664757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10621207671513827529772685 3982952876817685323664757)
                      ·
                        rfl

theorem cell23_7756773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7756773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756773 prefixEnd_7756773 := by exact prefixLift 7756773
  have htrace : WordTrace (prefixWord ++ tailWord_7756773) baseStart_7756773 baseEnd_7756773 := by
    simpa [prefixWord, tailWord_7756773, baseEnd_7756773] using wordTrace_append hprefix tailTrace_7756773
  have hstable : (prefixWord ++ tailWord_7756773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756773).length < 2 ^ (prefixWord ++ tailWord_7756773).sum := by decide
  have hdescent : baseEnd_7756773 < baseStart_7756773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756775 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7756775 : Nat := 118140960795 + 7756775 * 2 ^ 59
def prefixEnd_7756775 : Nat := 4983230072969 + 3 ^ 40 * 7756775 * 2
def baseEnd_7756775 : Nat := 3982953903778994315839747

theorem tailTrace_7756775 : CollatzResearch.WordTrace tailWord_7756775 prefixEnd_7756775 3982953903778994315839747 := by
  unfold tailWord_7756775
  simp only [CollatzResearch.WordTrace]
  refine ⟨282912826473536401546239779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188608550982357601030826519 282912826473536401546239779)
  ·
    refine ⟨424369239710304602319359669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282912826473536401546239779 424369239710304602319359669)
    ·
      refine ⟨39784616222841056467439969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 424369239710304602319359669 39784616222841056467439969)
      ·
        refine ⟨29838462167130792350579977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39784616222841056467439969 29838462167130792350579977)
        ·
          refine ⟨22378846625348094262934983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29838462167130792350579977 22378846625348094262934983)
          ·
            refine ⟨33568269938022141394402475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22378846625348094262934983 33568269938022141394402475)
            ·
              refine ⟨50352404907033212091603713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33568269938022141394402475 50352404907033212091603713)
              ·
                refine ⟨37764303680274909068702785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50352404907033212091603713 37764303680274909068702785)
                ·
                  refine ⟨28323227760206181801527089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37764303680274909068702785 28323227760206181801527089)
                  ·
                    refine ⟨21242420820154636351145317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28323227760206181801527089 21242420820154636351145317)
                    ·
                      refine ⟨3982953903778994315839747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21242420820154636351145317 3982953903778994315839747)
                      ·
                        rfl

theorem cell23_7756775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7756775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756775 prefixEnd_7756775 := by exact prefixLift 7756775
  have htrace : WordTrace (prefixWord ++ tailWord_7756775) baseStart_7756775 baseEnd_7756775 := by
    simpa [prefixWord, tailWord_7756775, baseEnd_7756775] using wordTrace_append hprefix tailTrace_7756775
  have hstable : (prefixWord ++ tailWord_7756775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756775).length < 2 ^ (prefixWord ++ tailWord_7756775).sum := by decide
  have hdescent : baseEnd_7756775 < baseStart_7756775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756785 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 7]
def baseStart_7756785 : Nat := 118140960795 + 7756785 * 2 ^ 59
def prefixEnd_7756785 : Nat := 4983230072969 + 3 ^ 40 * 7756785 * 2
def baseEnd_7756785 : Nat := 442551004287282141857189

theorem tailTrace_7756785 : CollatzResearch.WordTrace tailWord_7756785 prefixEnd_7756785 442551004287282141857189 := by
  unfold tailWord_7756785
  simp only [CollatzResearch.WordTrace]
  refine ⟨282913191203500173254103809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188608794135666782169402539 282913191203500173254103809)
  ·
    refine ⟨212184893402625129940577857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282913191203500173254103809 212184893402625129940577857)
    ·
      refine ⟨159138670051968847455433393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212184893402625129940577857 159138670051968847455433393)
      ·
        refine ⟨119354002538976635591575045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159138670051968847455433393 119354002538976635591575045)
        ·
          refine ⟨22378875476058119173420321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119354002538976635591575045 22378875476058119173420321)
          ·
            refine ⟨16784156607043589380065241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22378875476058119173420321 16784156607043589380065241)
            ·
              refine ⟨12588117455282692035048931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16784156607043589380065241 12588117455282692035048931)
              ·
                refine ⟨18882176182924038052573397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12588117455282692035048931 18882176182924038052573397)
                ·
                  refine ⟨442551004287282141857189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18882176182924038052573397 442551004287282141857189)
                  ·
                    rfl

theorem cell23_7756785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 7].length) (baseStart_7756785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756785 prefixEnd_7756785 := by exact prefixLift 7756785
  have htrace : WordTrace (prefixWord ++ tailWord_7756785) baseStart_7756785 baseEnd_7756785 := by
    simpa [prefixWord, tailWord_7756785, baseEnd_7756785] using wordTrace_append hprefix tailTrace_7756785
  have hstable : (prefixWord ++ tailWord_7756785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756785).length < 2 ^ (prefixWord ++ tailWord_7756785).sum := by decide
  have hdescent : baseEnd_7756785 < baseStart_7756785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756796 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_7756796 : Nat := 118140960795 + 7756796 * 2 ^ 59
def prefixEnd_7756796 : Nat := 4983230072969 + 3 ^ 40 * 7756796 * 2
def baseEnd_7756796 : Nat := 3982964686872738733677151

theorem tailTrace_7756796 : CollatzResearch.WordTrace tailWord_7756796 prefixEnd_7756796 3982964686872738733677151 := by
  unfold tailWord_7756796
  simp only [CollatzResearch.WordTrace]
  refine ⟨141456796203230161066377121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188609061604306881421836161 141456796203230161066377121)
  ·
    refine ⟨106092597152422620799782841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141456796203230161066377121 106092597152422620799782841)
    ·
      refine ⟨79569447864316965599837131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106092597152422620799782841 79569447864316965599837131)
      ·
        refine ⟨119354171796475448399755697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79569447864316965599837131 119354171796475448399755697)
        ·
          refine ⟨89515628847356586299816773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119354171796475448399755697 89515628847356586299816773)
          ·
            refine ⟨16784180408879359931215645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89515628847356586299816773 16784180408879359931215645)
            ·
              refine ⟨6294067653329759974205867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16784180408879359931215645 6294067653329759974205867)
              ·
                refine ⟨9441101479994639961308801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294067653329759974205867 9441101479994639961308801)
                ·
                  refine ⟨7080826109995979970981601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441101479994639961308801 7080826109995979970981601)
                  ·
                    refine ⟨5310619582496984978236201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7080826109995979970981601 5310619582496984978236201)
                    ·
                      refine ⟨3982964686872738733677151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310619582496984978236201 3982964686872738733677151)
                      ·
                        rfl

theorem cell23_7756796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_7756796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756796 prefixEnd_7756796 := by exact prefixLift 7756796
  have htrace : WordTrace (prefixWord ++ tailWord_7756796) baseStart_7756796 baseEnd_7756796 := by
    simpa [prefixWord, tailWord_7756796, baseEnd_7756796] using wordTrace_append hprefix tailTrace_7756796
  have hstable : (prefixWord ++ tailWord_7756796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756796).length < 2 ^ (prefixWord ++ tailWord_7756796).sum := by decide
  have hdescent : baseEnd_7756796 < baseStart_7756796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756835 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 4]
def baseStart_7756835 : Nat := 118140960795 + 7756835 * 2 ^ 59
def prefixEnd_7756835 : Nat := 4983230072969 + 3 ^ 40 * 7756835 * 2
def baseEnd_7756835 : Nat := 3982984712618264081089471

theorem tailTrace_7756835 : CollatzResearch.WordTrace tailWord_7756835 prefixEnd_7756835 3982984712618264081089471 := by
  unfold tailWord_7756835
  simp only [CollatzResearch.WordTrace]
  refine ⟨282915014853319031793423959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188610009902212687862282639 282915014853319031793423959)
  ·
    refine ⟨424372522279978547690135939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282915014853319031793423959 424372522279978547690135939)
    ·
      refine ⟨636558783419967821535203909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424372522279978547690135939 636558783419967821535203909)
      ·
        refine ⟨119354771891243966537850733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 636558783419967821535203909 119354771891243966537850733)
        ·
          refine ⟨44758039459216487451694025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119354771891243966537850733 44758039459216487451694025)
          ·
            refine ⟨33568529594412365588770519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44758039459216487451694025 33568529594412365588770519)
            ·
              refine ⟨50352794391618548383155779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33568529594412365588770519 50352794391618548383155779)
              ·
                refine ⟨75529191587427822574733669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50352794391618548383155779 75529191587427822574733669)
                ·
                  refine ⟨14161723422642716732762563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75529191587427822574733669 14161723422642716732762563)
                  ·
                    refine ⟨21242585133964075099143845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14161723422642716732762563 21242585133964075099143845)
                    ·
                      refine ⟨3982984712618264081089471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21242585133964075099143845 3982984712618264081089471)
                      ·
                        rfl

theorem cell23_7756835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_7756835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756835 prefixEnd_7756835 := by exact prefixLift 7756835
  have htrace : WordTrace (prefixWord ++ tailWord_7756835) baseStart_7756835 baseEnd_7756835 := by
    simpa [prefixWord, tailWord_7756835, baseEnd_7756835] using wordTrace_append hprefix tailTrace_7756835
  have hstable : (prefixWord ++ tailWord_7756835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756835).length < 2 ^ (prefixWord ++ tailWord_7756835).sum := by decide
  have hdescent : baseEnd_7756835 < baseStart_7756835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756842 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_7756842 : Nat := 118140960795 + 7756842 * 2 ^ 59
def prefixEnd_7756842 : Nat := 4983230072969 + 3 ^ 40 * 7756842 * 2
def baseEnd_7756842 : Nat := 3982988306982845553701939

theorem tailTrace_7756842 : CollatzResearch.WordTrace tailWord_7756842 prefixEnd_7756842 3982988306982845553701939 := by
  unfold tailWord_7756842
  simp only [CollatzResearch.WordTrace]
  refine ⟨70728817541073417997232195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188610180109529114659285853 70728817541073417997232195)
  ·
    refine ⟨106093226311610126995848293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70728817541073417997232195 106093226311610126995848293)
    ·
      refine ⟨19892479933426898811721555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106093226311610126995848293 19892479933426898811721555)
      ·
        refine ⟨29838719900140348217582333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19892479933426898811721555 29838719900140348217582333)
        ·
          refine ⟨11189519962552630581593375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29838719900140348217582333 11189519962552630581593375)
          ·
            refine ⟨16784279943828945872390063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11189519962552630581593375 16784279943828945872390063)
            ·
              refine ⟨25176419915743418808585095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16784279943828945872390063 25176419915743418808585095)
              ·
                refine ⟨37764629873615128212877643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25176419915743418808585095 37764629873615128212877643)
                ·
                  refine ⟨56646944810422692319316465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37764629873615128212877643 56646944810422692319316465)
                  ·
                    refine ⟨42485208607817019239487349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56646944810422692319316465 42485208607817019239487349)
                    ·
                      refine ⟨3982988306982845553701939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42485208607817019239487349 3982988306982845553701939)
                      ·
                        rfl

theorem cell23_7756842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_7756842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756842 prefixEnd_7756842 := by exact prefixLift 7756842
  have htrace : WordTrace (prefixWord ++ tailWord_7756842) baseStart_7756842 baseEnd_7756842 := by
    simpa [prefixWord, tailWord_7756842, baseEnd_7756842] using wordTrace_append hprefix tailTrace_7756842
  have hstable : (prefixWord ++ tailWord_7756842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756842).length < 2 ^ (prefixWord ++ tailWord_7756842).sum := by decide
  have hdescent : baseEnd_7756842 < baseStart_7756842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756855 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_7756855 : Nat := 118140960795 + 7756855 * 2 ^ 59
def prefixEnd_7756855 : Nat := 4983230072969 + 3 ^ 40 * 7756855 * 2
def baseEnd_7756855 : Nat := 3982994982231354002839379

theorem tailTrace_7756855 : CollatzResearch.WordTrace tailWord_7756855 prefixEnd_7756855 3982994982231354002839379 := by
  unfold tailWord_7756855
  simp only [CollatzResearch.WordTrace]
  refine ⟨282915744313246575209152019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188610496208831050139434679 282915744313246575209152019)
  ·
    refine ⟨424373616469869862813728029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282915744313246575209152019 424373616469869862813728029)
    ·
      refine ⟨159140106176201198555148011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424373616469869862813728029 159140106176201198555148011)
      ·
        refine ⟨238710159264301797832722017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159140106176201198555148011 238710159264301797832722017)
        ·
          refine ⟨179032619448226348374541513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238710159264301797832722017 179032619448226348374541513)
          ·
            refine ⟨134274464586169761280906135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179032619448226348374541513 134274464586169761280906135)
            ·
              refine ⟨201411696879254641921359203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134274464586169761280906135 201411696879254641921359203)
              ·
                refine ⟨302117545318881962882038805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201411696879254641921359203 302117545318881962882038805)
                ·
                  refine ⟨14161759936822592010095569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 302117545318881962882038805 14161759936822592010095569)
                  ·
                    refine ⟨10621319952616944007571677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14161759936822592010095569 10621319952616944007571677)
                    ·
                      refine ⟨3982994982231354002839379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10621319952616944007571677 3982994982231354002839379)
                      ·
                        rfl

theorem cell23_7756855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_7756855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756855 prefixEnd_7756855 := by exact prefixLift 7756855
  have htrace : WordTrace (prefixWord ++ tailWord_7756855) baseStart_7756855 baseEnd_7756855 := by
    simpa [prefixWord, tailWord_7756855, baseEnd_7756855] using wordTrace_append hprefix tailTrace_7756855
  have hstable : (prefixWord ++ tailWord_7756855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756855).length < 2 ^ (prefixWord ++ tailWord_7756855).sum := by decide
  have hdescent : baseEnd_7756855 < baseStart_7756855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756872 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_7756872 : Nat := 118140960795 + 7756872 * 2 ^ 59
def prefixEnd_7756872 : Nat := 4983230072969 + 3 ^ 40 * 7756872 * 2
def baseEnd_7756872 : Nat := 3983003711402480436326801

theorem tailTrace_7756872 : CollatzResearch.WordTrace tailWord_7756872 prefixEnd_7756872 3983003711402480436326801 := by
  unfold tailWord_7756872
  simp only [CollatzResearch.WordTrace]
  refine ⟨141458182177092493556260435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188610909569456658075013913 141458182177092493556260435)
  ·
    refine ⟨212187273265638740334390653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141458182177092493556260435 212187273265638740334390653)
    ·
      refine ⟨79570227474614527625396495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212187273265638740334390653 79570227474614527625396495)
      ·
        refine ⟨119355341211921791438094743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79570227474614527625396495 119355341211921791438094743)
        ·
          refine ⟨179033011817882687157142115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119355341211921791438094743 179033011817882687157142115)
          ·
            refine ⟨268549517726824030735713173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179033011817882687157142115 268549517726824030735713173)
            ·
              refine ⟨12588258643444876440736555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268549517726824030735713173 12588258643444876440736555)
              ·
                refine ⟨18882387965167314661104833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12588258643444876440736555 18882387965167314661104833)
                ·
                  refine ⟨14161790973875485995828625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18882387965167314661104833 14161790973875485995828625)
                  ·
                    refine ⟨10621343230406614496871469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14161790973875485995828625 10621343230406614496871469)
                    ·
                      refine ⟨3983003711402480436326801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10621343230406614496871469 3983003711402480436326801)
                      ·
                        rfl

theorem cell23_7756872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_7756872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756872 prefixEnd_7756872 := by exact prefixLift 7756872
  have htrace : WordTrace (prefixWord ++ tailWord_7756872) baseStart_7756872 baseEnd_7756872 := by
    simpa [prefixWord, tailWord_7756872, baseEnd_7756872] using wordTrace_append hprefix tailTrace_7756872
  have hstable : (prefixWord ++ tailWord_7756872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756872).length < 2 ^ (prefixWord ++ tailWord_7756872).sum := by decide
  have hdescent : baseEnd_7756872 < baseStart_7756872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756892 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 6]
def baseStart_7756892 : Nat := 118140960795 + 7756892 * 2 ^ 59
def prefixEnd_7756892 : Nat := 4983230072969 + 3 ^ 40 * 7756892 * 2
def baseEnd_7756892 : Nat := 442557109001730039786301

theorem tailTrace_7756892 : CollatzResearch.WordTrace tailWord_7756892 prefixEnd_7756892 442557109001730039786301 := by
  unfold tailWord_7756892
  simp only [CollatzResearch.WordTrace]
  refine ⟨141458546907056265264124465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188611395876075020352165953 141458546907056265264124465)
  ·
    refine ⟨106093910180292198948093349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141458546907056265264124465 106093910180292198948093349)
    ·
      refine ⟨19892608158804787302767503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106093910180292198948093349 19892608158804787302767503)
      ·
        refine ⟨29838912238207180954151255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19892608158804787302767503 29838912238207180954151255)
        ·
          refine ⟨44758368357310771431226883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29838912238207180954151255 44758368357310771431226883)
          ·
            refine ⟨67137552535966157146840325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44758368357310771431226883 67137552535966157146840325)
            ·
              refine ⟨12588291100493654465032561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67137552535966157146840325 12588291100493654465032561)
              ·
                refine ⟨9441218325370240848774421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588291100493654465032561 9441218325370240848774421)
                ·
                  refine ⟨442557109001730039786301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9441218325370240848774421 442557109001730039786301)
                  ·
                    rfl

theorem cell23_7756892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_7756892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756892 prefixEnd_7756892 := by exact prefixLift 7756892
  have htrace : WordTrace (prefixWord ++ tailWord_7756892) baseStart_7756892 baseEnd_7756892 := by
    simpa [prefixWord, tailWord_7756892, baseEnd_7756892] using wordTrace_append hprefix tailTrace_7756892
  have hstable : (prefixWord ++ tailWord_7756892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756892).length < 2 ^ (prefixWord ++ tailWord_7756892).sum := by decide
  have hdescent : baseEnd_7756892 < baseStart_7756892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756905 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 3, 5]
def baseStart_7756905 : Nat := 118140960795 + 7756905 * 2 ^ 59
def prefixEnd_7756905 : Nat := 4983230072969 + 3 ^ 40 * 7756905 * 2
def baseEnd_7756905 : Nat := 1327673552088026269071383

theorem tailTrace_7756905 : CollatzResearch.WordTrace tailWord_7756905 prefixEnd_7756905 1327673552088026269071383 := by
  unfold tailWord_7756905
  simp only [CollatzResearch.WordTrace]
  refine ⟨282917567963065433748472169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188611711975376955832314779 282917567963065433748472169)
  ·
    refine ⟨212188175972299075311354127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282917567963065433748472169 212188175972299075311354127)
    ·
      refine ⟨318282263958448612967031191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212188175972299075311354127 318282263958448612967031191)
      ·
        refine ⟨477423395937672919450546787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318282263958448612967031191 477423395937672919450546787)
        ·
          refine ⟨716135093906509379175820181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477423395937672919450546787 716135093906509379175820181)
          ·
            refine ⟨33568832526867627148866571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 716135093906509379175820181 33568832526867627148866571)
            ·
              refine ⟨50353248790301440723299857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33568832526867627148866571 50353248790301440723299857)
              ·
                refine ⟨37764936592726080542474893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50353248790301440723299857 37764936592726080542474893)
                ·
                  refine ⟨14161851222272280203428085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37764936592726080542474893 14161851222272280203428085)
                  ·
                    refine ⟨1327673552088026269071383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14161851222272280203428085 1327673552088026269071383)
                    ·
                      rfl

theorem cell23_7756905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_7756905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756905 prefixEnd_7756905 := by exact prefixLift 7756905
  have htrace : WordTrace (prefixWord ++ tailWord_7756905) baseStart_7756905 baseEnd_7756905 := by
    simpa [prefixWord, tailWord_7756905, baseEnd_7756905] using wordTrace_append hprefix tailTrace_7756905
  have hstable : (prefixWord ++ tailWord_7756905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756905).length < 2 ^ (prefixWord ++ tailWord_7756905).sum := by decide
  have hdescent : baseEnd_7756905 < baseStart_7756905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756912 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 1, 5, 2]
def baseStart_7756912 : Nat := 118140960795 + 7756912 * 2 ^ 59
def prefixEnd_7756912 : Nat := 4983230072969 + 3 ^ 40 * 7756912 * 2
def baseEnd_7756912 : Nat := 3983024250628660279826617

theorem tailTrace_7756912 : CollatzResearch.WordTrace tailWord_7756912 prefixEnd_7756912 3983024250628660279826617 := by
  unfold tailWord_7756912
  simp only [CollatzResearch.WordTrace]
  refine ⟨141458911637020036971988495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188611882182693382629317993 141458911637020036971988495)
  ·
    refine ⟨212188367455530055457982743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141458911637020036971988495 212188367455530055457982743)
    ·
      refine ⟨318282551183295083186974115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212188367455530055457982743 318282551183295083186974115)
      ·
        refine ⟨477423826774942624780461173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318282551183295083186974115 477423826774942624780461173)
        ·
          refine ⟨44758483760150871073168235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 477423826774942624780461173 44758483760150871073168235)
          ·
            refine ⟨67137725640226306609752353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44758483760150871073168235 67137725640226306609752353)
            ·
              refine ⟨50353294230169729957314265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67137725640226306609752353 50353294230169729957314265)
              ·
                refine ⟨37764970672627297467985699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50353294230169729957314265 37764970672627297467985699)
                ·
                  refine ⟨56647456008940946201978549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37764970672627297467985699 56647456008940946201978549)
                  ·
                    refine ⟨5310699000838213706435489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56647456008940946201978549 5310699000838213706435489)
                    ·
                      refine ⟨3983024250628660279826617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310699000838213706435489 3983024250628660279826617)
                      ·
                        rfl

theorem cell23_7756912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 5, 2].length) (baseStart_7756912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756912 prefixEnd_7756912 := by exact prefixLift 7756912
  have htrace : WordTrace (prefixWord ++ tailWord_7756912) baseStart_7756912 baseEnd_7756912 := by
    simpa [prefixWord, tailWord_7756912, baseEnd_7756912] using wordTrace_append hprefix tailTrace_7756912
  have hstable : (prefixWord ++ tailWord_7756912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756912).length < 2 ^ (prefixWord ++ tailWord_7756912).sum := by decide
  have hdescent : baseEnd_7756912 < baseStart_7756912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7756929 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 1, 5, 2]
def baseStart_7756929 : Nat := 118140960795 + 7756929 * 2 ^ 59
def prefixEnd_7756929 : Nat := 4983230072969 + 3 ^ 40 * 7756929 * 2
def baseEnd_7756929 : Nat := 3983032979799786713314039

theorem tailTrace_7756929 : CollatzResearch.WordTrace tailWord_7756929 prefixEnd_7756929 3983032979799786713314039 := by
  unfold tailWord_7756929
  simp only [CollatzResearch.WordTrace]
  refine ⟨282918443314978485847345841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188612295543318990564897227 282918443314978485847345841)
  ·
    refine ⟨212188832486233864385509381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282918443314978485847345841 212188832486233864385509381)
    ·
      refine ⟨39785406091168849572283009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212188832486233864385509381 39785406091168849572283009)
      ·
        refine ⟨29839054568376637179212257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39785406091168849572283009 29839054568376637179212257)
        ·
          refine ⟨22379290926282477884409193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29839054568376637179212257 22379290926282477884409193)
          ·
            refine ⟨16784468194711858413306895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22379290926282477884409193 16784468194711858413306895)
            ·
              refine ⟨25176702292067787619960343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16784468194711858413306895 25176702292067787619960343)
              ·
                refine ⟨37765053438101681429940515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25176702292067787619960343 37765053438101681429940515)
                ·
                  refine ⟨56647580157152522144910773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37765053438101681429940515 56647580157152522144910773)
                  ·
                    refine ⟨5310710639733048951085385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56647580157152522144910773 5310710639733048951085385)
                    ·
                      refine ⟨3983032979799786713314039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310710639733048951085385 3983032979799786713314039)
                      ·
                        rfl

theorem cell23_7756929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_7756929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7756929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7756929 prefixEnd_7756929 := by exact prefixLift 7756929
  have htrace : WordTrace (prefixWord ++ tailWord_7756929) baseStart_7756929 baseEnd_7756929 := by
    simpa [prefixWord, tailWord_7756929, baseEnd_7756929] using wordTrace_append hprefix tailTrace_7756929
  have hstable : (prefixWord ++ tailWord_7756929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7756929).length < 2 ^ (prefixWord ++ tailWord_7756929).sum := by decide
  have hdescent : baseEnd_7756929 < baseStart_7756929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7756929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757009 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_7757009 : Nat := 118140960795 + 7757009 * 2 ^ 59
def prefixEnd_7757009 : Nat := 4983230072969 + 3 ^ 40 * 7757009 * 2
def baseEnd_7757009 : Nat := 3983074058252146400313671

theorem tailTrace_7757009 : CollatzResearch.WordTrace tailWord_7757009 prefixEnd_7757009 3983074058252146400313671 := by
  unfold tailWord_7757009
  simp only [CollatzResearch.WordTrace]
  refine ⟨282921361154688659510258081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188614240769792439673505387 282921361154688659510258081)
  ·
    refine ⟨212191020866016494632693561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282921361154688659510258081 212191020866016494632693561)
    ·
      refine ⟨159143265649512370974520171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212191020866016494632693561 159143265649512370974520171)
      ·
        refine ⟨238714898474268556461780257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159143265649512370974520171 238714898474268556461780257)
        ·
          refine ⟨179036173855701417346335193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238714898474268556461780257 179036173855701417346335193)
          ·
            refine ⟨134277130391776063009751395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179036173855701417346335193 134277130391776063009751395)
            ·
              refine ⟨201415695587664094514627093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134277130391776063009751395 201415695587664094514627093)
              ·
                refine ⟨9441360730671754430373145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201415695587664094514627093 9441360730671754430373145)
                ·
                  refine ⟨7081020548003815822779859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441360730671754430373145 7081020548003815822779859)
                  ·
                    refine ⟨10621530822005723734169789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7081020548003815822779859 10621530822005723734169789)
                    ·
                      refine ⟨3983074058252146400313671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10621530822005723734169789 3983074058252146400313671)
                      ·
                        rfl

theorem cell23_7757009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_7757009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757009 prefixEnd_7757009 := by exact prefixLift 7757009
  have htrace : WordTrace (prefixWord ++ tailWord_7757009) baseStart_7757009 baseEnd_7757009 := by
    simpa [prefixWord, tailWord_7757009, baseEnd_7757009] using wordTrace_append hprefix tailTrace_7757009
  have hstable : (prefixWord ++ tailWord_7757009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757009).length < 2 ^ (prefixWord ++ tailWord_7757009).sum := by decide
  have hdescent : baseEnd_7757009 < baseStart_7757009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757010 : List Nat := [3, 2, 2, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_7757010 : Nat := 118140960795 + 7757010 * 2 ^ 59
def prefixEnd_7757010 : Nat := 4983230072969 + 3 ^ 40 * 7757010 * 2
def baseEnd_7757010 : Nat := 3983074571732800896401167

theorem tailTrace_7757010 : CollatzResearch.WordTrace tailWord_7757010 prefixEnd_7757010 3983074571732800896401167 := by
  unfold tailWord_7757010
  simp only [CollatzResearch.WordTrace]
  refine ⟨70730349406921259170261121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188614265085123357787362989 70730349406921259170261121)
  ·
    refine ⟨53047762055190944377695841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70730349406921259170261121 53047762055190944377695841)
    ·
      refine ⟨39785821541393208283271881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53047762055190944377695841 39785821541393208283271881)
      ·
        refine ⟨29839366156044906212453911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39785821541393208283271881 29839366156044906212453911)
        ·
          refine ⟨44759049234067359318680867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29839366156044906212453911 44759049234067359318680867)
          ·
            refine ⟨67138573851101038978021301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44759049234067359318680867 67138573851101038978021301)
            ·
              refine ⟨6294241298540722404189497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67138573851101038978021301 6294241298540722404189497)
              ·
                refine ⟨4720680973905541803142123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6294241298540722404189497 4720680973905541803142123)
                ·
                  refine ⟨7081021460858312704713185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720680973905541803142123 7081021460858312704713185)
                  ·
                    refine ⟨5310766095643734528534889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7081021460858312704713185 5310766095643734528534889)
                    ·
                      refine ⟨3983074571732800896401167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310766095643734528534889 3983074571732800896401167)
                      ·
                        rfl

theorem cell23_7757010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_7757010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757010 prefixEnd_7757010 := by exact prefixLift 7757010
  have htrace : WordTrace (prefixWord ++ tailWord_7757010) baseStart_7757010 baseEnd_7757010 := by
    simpa [prefixWord, tailWord_7757010, baseEnd_7757010] using wordTrace_append hprefix tailTrace_7757010
  have hstable : (prefixWord ++ tailWord_7757010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757010).length < 2 ^ (prefixWord ++ tailWord_7757010).sum := by decide
  have hdescent : baseEnd_7757010 < baseStart_7757010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757036 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 1, 3, 2]
def baseStart_7757036 : Nat := 118140960795 + 7757036 * 2 ^ 59
def prefixEnd_7757036 : Nat := 4983230072969 + 3 ^ 40 * 7757036 * 2
def baseEnd_7757036 : Nat := 3983087922229817794676047

theorem tailTrace_7757036 : CollatzResearch.WordTrace tailWord_7757036 prefixEnd_7757036 3983087922229817794676047 := by
  unfold tailWord_7757036
  simp only [CollatzResearch.WordTrace]
  refine ⟨141461172962795421560745481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188614897283727228747660641 141461172962795421560745481)
  ·
    refine ⟨106095879722096566170559111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141461172962795421560745481 106095879722096566170559111)
    ·
      refine ⟨159143819583144849255838667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106095879722096566170559111 159143819583144849255838667)
      ·
        refine ⟨238715729374717273883758001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159143819583144849255838667 238715729374717273883758001)
        ·
          refine ⟨179036797031037955412818501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238715729374717273883758001 179036797031037955412818501)
          ·
            refine ⟨33569399443319616639903469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179036797031037955412818501 33569399443319616639903469)
            ·
              refine ⟨12588524791244856239963801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33569399443319616639903469 12588524791244856239963801)
              ·
                refine ⟨9441393593433642179972851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588524791244856239963801 9441393593433642179972851)
                ·
                  refine ⟨14162090390150463269959277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9441393593433642179972851 14162090390150463269959277)
                  ·
                    refine ⟨5310783896306423726234729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14162090390150463269959277 5310783896306423726234729)
                    ·
                      refine ⟨3983087922229817794676047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310783896306423726234729 3983087922229817794676047)
                      ·
                        rfl

theorem cell23_7757036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_7757036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757036 prefixEnd_7757036 := by exact prefixLift 7757036
  have htrace : WordTrace (prefixWord ++ tailWord_7757036) baseStart_7757036 baseEnd_7757036 := by
    simpa [prefixWord, tailWord_7757036, baseEnd_7757036] using wordTrace_append hprefix tailTrace_7757036
  have hstable : (prefixWord ++ tailWord_7757036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757036).length < 2 ^ (prefixWord ++ tailWord_7757036).sum := by decide
  have hdescent : baseEnd_7757036 < baseStart_7757036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757049 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 1, 4, 2]
def baseStart_7757049 : Nat := 118140960795 + 7757049 * 2 ^ 59
def prefixEnd_7757049 : Nat := 4983230072969 + 3 ^ 40 * 7757049 * 2
def baseEnd_7757049 : Nat := 3983094597478326243813487

theorem tailTrace_7757049 : CollatzResearch.WordTrace tailWord_7757049 prefixEnd_7757049 3983094597478326243813487 := by
  unfold tailWord_7757049
  simp only [CollatzResearch.WordTrace]
  refine ⟨282922820074543746341714201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188615213383029164227809467 282922820074543746341714201)
  ·
    refine ⟨212192115055907809756285651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282922820074543746341714201 212192115055907809756285651)
    ·
      refine ⟨318288172583861714634428477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212192115055907809756285651 318288172583861714634428477)
      ·
        refine ⟨119358064718948142987910679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318288172583861714634428477 119358064718948142987910679)
        ·
          refine ⟨179037097078422214481866019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119358064718948142987910679 179037097078422214481866019)
          ·
            refine ⟨268555645617633321722799029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179037097078422214481866019 268555645617633321722799029)
            ·
              refine ⟨25177091776653123911512409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268555645617633321722799029 25177091776653123911512409)
              ·
                refine ⟨18882818832489842933634307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25177091776653123911512409 18882818832489842933634307)
                ·
                  refine ⟨28324228248734764400451461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18882818832489842933634307 28324228248734764400451461)
                  ·
                    refine ⟨5310792796637768325084649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28324228248734764400451461 5310792796637768325084649)
                    ·
                      refine ⟨3983094597478326243813487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310792796637768325084649 3983094597478326243813487)
                      ·
                        rfl

theorem cell23_7757049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_7757049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757049 prefixEnd_7757049 := by exact prefixLift 7757049
  have htrace : WordTrace (prefixWord ++ tailWord_7757049) baseStart_7757049 baseEnd_7757049 := by
    simpa [prefixWord, tailWord_7757049, baseEnd_7757049] using wordTrace_append hprefix tailTrace_7757049
  have hstable : (prefixWord ++ tailWord_7757049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757049).length < 2 ^ (prefixWord ++ tailWord_7757049).sum := by decide
  have hdescent : baseEnd_7757049 < baseStart_7757049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757075 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8]
def baseStart_7757075 : Nat := 118140960795 + 7757075 * 2 ^ 59
def prefixEnd_7757075 : Nat := 4983230072969 + 3 ^ 40 * 7757075 * 2
def baseEnd_7757075 : Nat := 3983107947975343142088367

theorem tailTrace_7757075 : CollatzResearch.WordTrace tailWord_7757075 prefixEnd_7757075 3983107947975343142088367 := by
  unfold tailWord_7757075
  simp only [CollatzResearch.WordTrace]
  refine ⟨282923768372449552782160679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188615845581633035188107119 282923768372449552782160679)
  ·
    refine ⟨424385652558674329173241019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282923768372449552782160679 424385652558674329173241019)
    ·
      refine ⟨636578478838011493759861529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424385652558674329173241019 636578478838011493759861529)
      ·
        refine ⟨477433859128508620319896147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636578478838011493759861529 477433859128508620319896147)
        ·
          refine ⟨716150788692762930479844221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477433859128508620319896147 716150788692762930479844221)
          ·
            refine ⟨268556545759786098929941583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 716150788692762930479844221 268556545759786098929941583)
            ·
              refine ⟨402834818639679148394912375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268556545759786098929941583 402834818639679148394912375)
              ·
                refine ⟨604252227959518722592368563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402834818639679148394912375 604252227959518722592368563)
                ·
                  refine ⟨906378341939278083888552845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604252227959518722592368563 906378341939278083888552845)
                  ·
                    refine ⟨339891878227229281458207317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906378341939278083888552845 339891878227229281458207317)
                    ·
                      refine ⟨3983107947975343142088367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 339891878227229281458207317 3983107947975343142088367)
                      ·
                        rfl

theorem cell23_7757075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_7757075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757075 prefixEnd_7757075 := by exact prefixLift 7757075
  have htrace : WordTrace (prefixWord ++ tailWord_7757075) baseStart_7757075 baseEnd_7757075 := by
    simpa [prefixWord, tailWord_7757075, baseEnd_7757075] using wordTrace_append hprefix tailTrace_7757075
  have hstable : (prefixWord ++ tailWord_7757075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757075).length < 2 ^ (prefixWord ++ tailWord_7757075).sum := by decide
  have hdescent : baseEnd_7757075 < baseStart_7757075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757106 : List Nat := [3, 2, 1, 1, 4, 2, 2, 3, 5]
def baseStart_7757106 : Nat := 118140960795 + 7757106 * 2 ^ 59
def prefixEnd_7757106 : Nat := 4983230072969 + 3 ^ 40 * 7757106 * 2
def baseEnd_7757106 : Nat := 442569318430625835644525

theorem tailTrace_7757106 : CollatzResearch.WordTrace tailWord_7757106 prefixEnd_7757106 442569318430625835644525 := by
  unfold tailWord_7757106
  simp only [CollatzResearch.WordTrace]
  refine ⟨70731224758834311269134793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188616599356891496717692781 70731224758834311269134793)
  ·
    refine ⟨53048418569125733451851095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70731224758834311269134793 53048418569125733451851095)
    ·
      refine ⟨79572627853688600177776643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53048418569125733451851095 79572627853688600177776643)
      ·
        refine ⟨119358941780532900266664965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79572627853688600177776643 119358941780532900266664965)
        ·
          refine ⟨22379801583849918799999681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119358941780532900266664965 22379801583849918799999681)
          ·
            refine ⟨16784851187887439099999761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22379801583849918799999681 16784851187887439099999761)
            ·
              refine ⟨12588638390915579324999821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16784851187887439099999761 12588638390915579324999821)
              ·
                refine ⟨4720739396593342246874933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12588638390915579324999821 4720739396593342246874933)
                ·
                  refine ⟨442569318430625835644525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4720739396593342246874933 442569318430625835644525)
                  ·
                    rfl

theorem cell23_7757106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_7757106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757106 prefixEnd_7757106 := by exact prefixLift 7757106
  have htrace : WordTrace (prefixWord ++ tailWord_7757106) baseStart_7757106 baseEnd_7757106 := by
    simpa [prefixWord, tailWord_7757106, baseEnd_7757106] using wordTrace_append hprefix tailTrace_7757106
  have hstable : (prefixWord ++ tailWord_7757106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757106).length < 2 ^ (prefixWord ++ tailWord_7757106).sum := by decide
  have hdescent : baseEnd_7757106 < baseStart_7757106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757117 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7757117 : Nat := 118140960795 + 7757117 * 2 ^ 59
def prefixEnd_7757117 : Nat := 4983230072969 + 3 ^ 40 * 7757117 * 2
def baseEnd_7757117 : Nat := 3983129514162831977763175

theorem tailTrace_7757117 : CollatzResearch.WordTrace tailWord_7757117 prefixEnd_7757117 3983129514162831977763175 := by
  unfold tailWord_7757117
  simp only [CollatzResearch.WordTrace]
  refine ⟨282925300238297393955189605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188616866825531595970126403 282925300238297393955189605)
  ·
    refine ⟨53048493794680761366598051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282925300238297393955189605 53048493794680761366598051)
    ·
      refine ⟨79572740692021142049897077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53048493794680761366598051 79572740692021142049897077)
      ·
        refine ⟨7459944439876982067177851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79572740692021142049897077 7459944439876982067177851)
        ·
          refine ⟨11189916659815473100766777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459944439876982067177851 11189916659815473100766777)
          ·
            refine ⟨8392437494861604825575083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11189916659815473100766777 8392437494861604825575083)
            ·
              refine ⟨12588656242292407238362625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8392437494861604825575083 12588656242292407238362625)
              ·
                refine ⟨9441492181719305428771969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588656242292407238362625 9441492181719305428771969)
                ·
                  refine ⟨7081119136289479071578977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441492181719305428771969 7081119136289479071578977)
                  ·
                    refine ⟨5310839352217109303684233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7081119136289479071578977 5310839352217109303684233)
                    ·
                      refine ⟨3983129514162831977763175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310839352217109303684233 3983129514162831977763175)
                      ·
                        rfl

theorem cell23_7757117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7757117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757117 prefixEnd_7757117 := by exact prefixLift 7757117
  have htrace : WordTrace (prefixWord ++ tailWord_7757117) baseStart_7757117 baseEnd_7757117 := by
    simpa [prefixWord, tailWord_7757117, baseEnd_7757117] using wordTrace_append hprefix tailTrace_7757117
  have hstable : (prefixWord ++ tailWord_7757117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757117).length < 2 ^ (prefixWord ++ tailWord_7757117).sum := by decide
  have hdescent : baseEnd_7757117 < baseStart_7757117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757139 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 2, 4, 2]
def baseStart_7757139 : Nat := 118140960795 + 7757139 * 2 ^ 59
def prefixEnd_7757139 : Nat := 4983230072969 + 3 ^ 40 * 7757139 * 2
def baseEnd_7757139 : Nat := 3983140810737230891688073

theorem tailTrace_7757139 : CollatzResearch.WordTrace tailWord_7757139 prefixEnd_7757139 3983140810737230891688073 := by
  unfold tailWord_7757139
  simp only [CollatzResearch.WordTrace]
  refine ⟨282926102644217691712490471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188617401762811794474993647 282926102644217691712490471)
  ·
    refine ⟨424389153966326537568735707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282926102644217691712490471 424389153966326537568735707)
    ·
      refine ⟨636583730949489806353103561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424389153966326537568735707 636583730949489806353103561)
      ·
        refine ⟨477437798212117354764827671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636583730949489806353103561 477437798212117354764827671)
        ·
          refine ⟨716156697318176032147241507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477437798212117354764827671 716156697318176032147241507)
          ·
            refine ⟨1074235045977264048220862261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716156697318176032147241507 1074235045977264048220862261)
            ·
              refine ⟨100709535560368504520705837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1074235045977264048220862261 100709535560368504520705837)
              ·
                refine ⟨37766075835138189195264689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100709535560368504520705837 37766075835138189195264689)
                ·
                  refine ⟨28324556876353641896448517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37766075835138189195264689 28324556876353641896448517)
                  ·
                    refine ⟨5310854414316307855584097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28324556876353641896448517 5310854414316307855584097)
                    ·
                      refine ⟨3983140810737230891688073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310854414316307855584097 3983140810737230891688073)
                      ·
                        rfl

theorem cell23_7757139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4, 2].length) (baseStart_7757139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757139 prefixEnd_7757139 := by exact prefixLift 7757139
  have htrace : WordTrace (prefixWord ++ tailWord_7757139) baseStart_7757139 baseEnd_7757139 := by
    simpa [prefixWord, tailWord_7757139, baseEnd_7757139] using wordTrace_append hprefix tailTrace_7757139
  have hstable : (prefixWord ++ tailWord_7757139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757139).length < 2 ^ (prefixWord ++ tailWord_7757139).sum := by decide
  have hdescent : baseEnd_7757139 < baseStart_7757139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757209 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 3, 5]
def baseStart_7757209 : Nat := 118140960795 + 7757209 * 2 ^ 59
def prefixEnd_7757209 : Nat := 4983230072969 + 3 ^ 40 * 7757209 * 2
def baseEnd_7757209 : Nat := 1327725584794348539270917

theorem tailTrace_7757209 : CollatzResearch.WordTrace tailWord_7757209 prefixEnd_7757209 1327725584794348539270917 := by
  unfold tailWord_7757209
  simp only [CollatzResearch.WordTrace]
  refine ⟨282928655753964093667538681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188619103835976062445025787 282928655753964093667538681)
  ·
    refine ⟨212196491815473070250654011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282928655753964093667538681 212196491815473070250654011)
    ·
      refine ⟨318294737723209605375981017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212196491815473070250654011 318294737723209605375981017)
      ·
        refine ⟨238721053292407204031985763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318294737723209605375981017 238721053292407204031985763)
        ·
          refine ⟨358081579938610806047978645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238721053292407204031985763 358081579938610806047978645)
          ·
            refine ⟨16785074059622381533498999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 358081579938610806047978645 16785074059622381533498999)
            ·
              refine ⟨25177611089433572300248499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16785074059622381533498999 25177611089433572300248499)
              ·
                refine ⟨37766416634150358450372749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25177611089433572300248499 37766416634150358450372749)
                ·
                  refine ⟨14162406237806384418889781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37766416634150358450372749 14162406237806384418889781)
                  ·
                    refine ⟨1327725584794348539270917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14162406237806384418889781 1327725584794348539270917)
                    ·
                      rfl

theorem cell23_7757209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_7757209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757209 prefixEnd_7757209 := by exact prefixLift 7757209
  have htrace : WordTrace (prefixWord ++ tailWord_7757209) baseStart_7757209 baseEnd_7757209 := by
    simpa [prefixWord, tailWord_7757209, baseEnd_7757209] using wordTrace_append hprefix tailTrace_7757209
  have hstable : (prefixWord ++ tailWord_7757209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757209).length < 2 ^ (prefixWord ++ tailWord_7757209).sum := by decide
  have hdescent : baseEnd_7757209 < baseStart_7757209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757240 : List Nat := [2, 1, 2, 1, 2, 2, 6, 2, 1, 1, 3]
def baseStart_7757240 : Nat := 118140960795 + 7757240 * 2 ^ 59
def prefixEnd_7757240 : Nat := 4983230072969 + 3 ^ 40 * 7757240 * 2
def baseEnd_7757240 : Nat := 3983192672283334996525109

theorem tailTrace_7757240 : CollatzResearch.WordTrace tailWord_7757240 prefixEnd_7757240 3983192672283334996525109 := by
  unfold tailWord_7757240
  simp only [CollatzResearch.WordTrace]
  refine ⟨141464893208425892980958587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188619857611234523974611449 141464893208425892980958587)
  ·
    refine ⟨212197339812638839471437881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141464893208425892980958587 212197339812638839471437881)
    ·
      refine ⟨159148004859479129603578411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212197339812638839471437881 159148004859479129603578411)
      ·
        refine ⟨238722007289218694405367617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159148004859479129603578411 238722007289218694405367617)
        ·
          refine ⟨179041505466914020804025713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238722007289218694405367617 179041505466914020804025713)
          ·
            refine ⟨134281129100185515603019285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179041505466914020804025713 134281129100185515603019285)
            ·
              refine ⟨6294427926571196043891529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134281129100185515603019285 6294427926571196043891529)
              ·
                refine ⟨4720820944928397032918647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6294427926571196043891529 4720820944928397032918647)
                ·
                  refine ⟨7081231417392595549377971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4720820944928397032918647 7081231417392595549377971)
                  ·
                    refine ⟨10621847126088893324066957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7081231417392595549377971 10621847126088893324066957)
                    ·
                      refine ⟨3983192672283334996525109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10621847126088893324066957 3983192672283334996525109)
                      ·
                        rfl

theorem cell23_7757240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 1, 3].length) (baseStart_7757240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757240 prefixEnd_7757240 := by exact prefixLift 7757240
  have htrace : WordTrace (prefixWord ++ tailWord_7757240) baseStart_7757240 baseEnd_7757240 := by
    simpa [prefixWord, tailWord_7757240, baseEnd_7757240] using wordTrace_append hprefix tailTrace_7757240
  have hstable : (prefixWord ++ tailWord_7757240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757240).length < 2 ^ (prefixWord ++ tailWord_7757240).sum := by decide
  have hdescent : baseEnd_7757240 < baseStart_7757240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757246 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_7757246 : Nat := 118140960795 + 7757246 * 2 ^ 59
def prefixEnd_7757246 : Nat := 4983230072969 + 3 ^ 40 * 7757246 * 2
def baseEnd_7757246 : Nat := 3983195753167261973050081

theorem tailTrace_7757246 : CollatzResearch.WordTrace tailWord_7757246 prefixEnd_7757246 3983195753167261973050081 := by
  unfold tailWord_7757246
  simp only [CollatzResearch.WordTrace]
  refine ⟨35366250656853756123329449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188620003503220032657757061 35366250656853756123329449)
  ·
    refine ⟨26524687992640317092497087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35366250656853756123329449 26524687992640317092497087)
    ·
      refine ⟨39787031988960475638745631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26524687992640317092497087 39787031988960475638745631)
      ·
        refine ⟨59680547983440713458118447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39787031988960475638745631 59680547983440713458118447)
        ·
          refine ⟨89520821975161070187177671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59680547983440713458118447 89520821975161070187177671)
          ·
            refine ⟨134281232962741605280766507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89520821975161070187177671 134281232962741605280766507)
            ·
              refine ⟨201421849444112407921149761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134281232962741605280766507 201421849444112407921149761)
              ·
                refine ⟨151066387083084305940862321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201421849444112407921149761 151066387083084305940862321)
                ·
                  refine ⟨113299790312313229455646741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151066387083084305940862321 113299790312313229455646741)
                  ·
                    refine ⟨5310927670889682630733441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113299790312313229455646741 5310927670889682630733441)
                    ·
                      refine ⟨3983195753167261973050081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5310927670889682630733441 3983195753167261973050081)
                      ·
                        rfl

theorem cell23_7757246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_7757246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757246 prefixEnd_7757246 := by exact prefixLift 7757246
  have htrace : WordTrace (prefixWord ++ tailWord_7757246) baseStart_7757246 baseEnd_7757246 := by
    simpa [prefixWord, tailWord_7757246, baseEnd_7757246] using wordTrace_append hprefix tailTrace_7757246
  have hstable : (prefixWord ++ tailWord_7757246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757246).length < 2 ^ (prefixWord ++ tailWord_7757246).sum := by decide
  have hdescent : baseEnd_7757246 < baseStart_7757246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757256 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 2, 4]
def baseStart_7757256 : Nat := 118140960795 + 7757256 * 2 ^ 59
def prefixEnd_7757256 : Nat := 4983230072969 + 3 ^ 40 * 7757256 * 2
def baseEnd_7757256 : Nat := 1327733629324602311308345

theorem tailTrace_7757256 : CollatzResearch.WordTrace tailWord_7757256 prefixEnd_7757256 1327733629324602311308345 := by
  unfold tailWord_7757256
  simp only [CollatzResearch.WordTrace]
  refine ⟨141465184992396910347249811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188620246656529213796333081 141465184992396910347249811)
  ·
    refine ⟨212197777488595365520874717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141465184992396910347249811 212197777488595365520874717)
    ·
      refine ⟨79574166558223262070328019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212197777488595365520874717 79574166558223262070328019)
      ·
        refine ⟨119361249837334893105492029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79574166558223262070328019 119361249837334893105492029)
        ·
          refine ⟨44760468689000584914559511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119361249837334893105492029 44760468689000584914559511)
          ·
            refine ⟨67140703033500877371839267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44760468689000584914559511 67140703033500877371839267)
            ·
              refine ⟨100711054550251316057758901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67140703033500877371839267 100711054550251316057758901)
              ·
                refine ⟨9441661364086060880414897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100711054550251316057758901 9441661364086060880414897)
                ·
                  refine ⟨7081246023064545660311173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441661364086060880414897 7081246023064545660311173)
                  ·
                    refine ⟨1327733629324602311308345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081246023064545660311173 1327733629324602311308345)
                    ·
                      rfl

theorem cell23_7757256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_7757256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757256 prefixEnd_7757256 := by exact prefixLift 7757256
  have htrace : WordTrace (prefixWord ++ tailWord_7757256) baseStart_7757256 baseEnd_7757256 := by
    simpa [prefixWord, tailWord_7757256, baseEnd_7757256] using wordTrace_append hprefix tailTrace_7757256
  have hstable : (prefixWord ++ tailWord_7757256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757256).length < 2 ^ (prefixWord ++ tailWord_7757256).sum := by decide
  have hdescent : baseEnd_7757256 < baseStart_7757256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757259 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4]
def baseStart_7757259 : Nat := 118140960795 + 7757259 * 2 ^ 59
def prefixEnd_7757259 : Nat := 4983230072969 + 3 ^ 40 * 7757259 * 2
def baseEnd_7757259 : Nat := 3983202428415770422187521

theorem tailTrace_7757259 : CollatzResearch.WordTrace tailWord_7757259 prefixEnd_7757259 3983202428415770422187521 := by
  unfold tailWord_7757259
  simp only [CollatzResearch.WordTrace]
  refine ⟨282930479403782952206858831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188620319602521968137905887 282930479403782952206858831)
  ·
    refine ⟨424395719105674428310288247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282930479403782952206858831 424395719105674428310288247)
    ·
      refine ⟨636593578658511642465432371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424395719105674428310288247 636593578658511642465432371)
      ·
        refine ⟨954890367987767463698148557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636593578658511642465432371 954890367987767463698148557)
        ·
          refine ⟨358083887995412798886805709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 954890367987767463698148557 358083887995412798886805709)
          ·
            refine ⟨134281457998279799582552141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358083887995412798886805709 134281457998279799582552141)
            ·
              refine ⟨50355546749354924843457053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134281457998279799582552141 50355546749354924843457053)
              ·
                refine ⟨18883330031008096816296395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50355546749354924843457053 18883330031008096816296395)
                ·
                  refine ⟨28324995046512145224444593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18883330031008096816296395 28324995046512145224444593)
                  ·
                    refine ⟨21243746284884108918333445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28324995046512145224444593 21243746284884108918333445)
                    ·
                      refine ⟨3983202428415770422187521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21243746284884108918333445 3983202428415770422187521)
                      ·
                        rfl

theorem cell23_7757259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4].length) (baseStart_7757259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757259 prefixEnd_7757259 := by exact prefixLift 7757259
  have htrace : WordTrace (prefixWord ++ tailWord_7757259) baseStart_7757259 baseEnd_7757259 := by
    simpa [prefixWord, tailWord_7757259, baseEnd_7757259] using wordTrace_append hprefix tailTrace_7757259
  have hstable : (prefixWord ++ tailWord_7757259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757259).length < 2 ^ (prefixWord ++ tailWord_7757259).sum := by decide
  have hdescent : baseEnd_7757259 < baseStart_7757259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757283 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7757283 : Nat := 118140960795 + 7757283 * 2 ^ 59
def prefixEnd_7757283 : Nat := 4983230072969 + 3 ^ 40 * 7757283 * 2
def baseEnd_7757283 : Nat := 3983214751951478328287411

theorem tailTrace_7757283 : CollatzResearch.WordTrace tailWord_7757283 prefixEnd_7757283 3983214751951478328287411 := by
  unfold tailWord_7757283
  simp only [CollatzResearch.WordTrace]
  refine ⟨282931354755696004305732503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188620903170464002870488335 282931354755696004305732503)
  ·
    refine ⟨424397032133544006458598755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282931354755696004305732503 424397032133544006458598755)
    ·
      refine ⟨636595548200316009687898133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424397032133544006458598755 636595548200316009687898133)
      ·
        refine ⟨29840416321889812954120225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 636595548200316009687898133 29840416321889812954120225)
        ·
          refine ⟨22380312241417359715590169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29840416321889812954120225 22380312241417359715590169)
          ·
            refine ⟨16785234181063019786692627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22380312241417359715590169 16785234181063019786692627)
            ·
              refine ⟨25177851271594529680038941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16785234181063019786692627 25177851271594529680038941)
              ·
                refine ⟨9441694226847948630014603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25177851271594529680038941 9441694226847948630014603)
                ·
                  refine ⟨14162541340271922945021905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9441694226847948630014603 14162541340271922945021905)
                  ·
                    refine ⟨10621906005203942208766429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14162541340271922945021905 10621906005203942208766429)
                    ·
                      refine ⟨3983214751951478328287411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10621906005203942208766429 3983214751951478328287411)
                      ·
                        rfl

theorem cell23_7757283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7757283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757283 prefixEnd_7757283 := by exact prefixLift 7757283
  have htrace : WordTrace (prefixWord ++ tailWord_7757283) baseStart_7757283 baseEnd_7757283 := by
    simpa [prefixWord, tailWord_7757283, baseEnd_7757283] using wordTrace_append hprefix tailTrace_7757283
  have hstable : (prefixWord ++ tailWord_7757283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757283).length < 2 ^ (prefixWord ++ tailWord_7757283).sum := by decide
  have hdescent : baseEnd_7757283 < baseStart_7757283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757290 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_7757290 : Nat := 118140960795 + 7757290 * 2 ^ 59
def prefixEnd_7757290 : Nat := 4983230072969 + 3 ^ 40 * 7757290 * 2
def baseEnd_7757290 : Nat := 1327739448772019933633293

theorem tailTrace_7757290 : CollatzResearch.WordTrace tailWord_7757290 prefixEnd_7757290 1327739448772019933633293 := by
  unfold tailWord_7757290
  simp only [CollatzResearch.WordTrace]
  refine ⟨70732902516667661125309331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188621073377780429667491549 70732902516667661125309331)
  ·
    refine ⟨106099353775001491687963997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70732902516667661125309331 106099353775001491687963997)
    ·
      refine ⟨39787257665625559382986499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106099353775001491687963997 39787257665625559382986499)
      ·
        refine ⟨59680886498438339074479749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39787257665625559382986499 59680886498438339074479749)
        ·
          refine ⟨11190166218457188576464953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59680886498438339074479749 11190166218457188576464953)
          ·
            refine ⟨8392624663842891432348715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11190166218457188576464953 8392624663842891432348715)
            ·
              refine ⟨12588936995764337148523073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8392624663842891432348715 12588936995764337148523073)
              ·
                refine ⟨9441702746823252861392305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12588936995764337148523073 9441702746823252861392305)
                ·
                  refine ⟨7081277060117439646044229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441702746823252861392305 7081277060117439646044229)
                  ·
                    refine ⟨1327739448772019933633293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081277060117439646044229 1327739448772019933633293)
                    ·
                      rfl

theorem cell23_7757290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_7757290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757290 prefixEnd_7757290 := by exact prefixLift 7757290
  have htrace : WordTrace (prefixWord ++ tailWord_7757290) baseStart_7757290 baseEnd_7757290 := by
    simpa [prefixWord, tailWord_7757290, baseEnd_7757290] using wordTrace_append hprefix tailTrace_7757290
  have hstable : (prefixWord ++ tailWord_7757290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757290).length < 2 ^ (prefixWord ++ tailWord_7757290).sum := by decide
  have hdescent : baseEnd_7757290 < baseStart_7757290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757370 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2]
def baseStart_7757370 : Nat := 118140960795 + 7757370 * 2 ^ 59
def prefixEnd_7757370 : Nat := 4983230072969 + 3 ^ 40 * 7757370 * 2
def baseEnd_7757370 : Nat := 3983259424768419487899511

theorem tailTrace_7757370 : CollatzResearch.WordTrace tailWord_7757370 prefixEnd_7757370 3983259424768419487899511 := by
  unfold tailWord_7757370
  simp only [CollatzResearch.WordTrace]
  refine ⟨70733631976595204541037391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188623018604253878776099709 70733631976595204541037391)
  ·
    refine ⟨106100447964892806811556087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70733631976595204541037391 106100447964892806811556087)
    ·
      refine ⟨159150671947339210217334131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106100447964892806811556087 159150671947339210217334131)
      ·
        refine ⟨238726007921008815326001197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159150671947339210217334131 238726007921008815326001197)
        ·
          refine ⟨89522252970378305747250449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238726007921008815326001197 89522252970378305747250449)
          ·
            refine ⟨67141689727783729310437837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89522252970378305747250449 67141689727783729310437837)
            ·
              refine ⟨25178133647918898491414189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67141689727783729310437837 25178133647918898491414189)
              ·
                refine ⟨9441800117969586934280321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25178133647918898491414189 9441800117969586934280321)
                ·
                  refine ⟨7081350088477190200710241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441800117969586934280321 7081350088477190200710241)
                  ·
                    refine ⟨5311012566357892650532681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7081350088477190200710241 5311012566357892650532681)
                    ·
                      refine ⟨3983259424768419487899511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311012566357892650532681 3983259424768419487899511)
                      ·
                        rfl

theorem cell23_7757370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_7757370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757370 prefixEnd_7757370 := by exact prefixLift 7757370
  have htrace : WordTrace (prefixWord ++ tailWord_7757370) baseStart_7757370 baseEnd_7757370 := by
    simpa [prefixWord, tailWord_7757370, baseEnd_7757370] using wordTrace_append hprefix tailTrace_7757370
  have hstable : (prefixWord ++ tailWord_7757370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757370).length < 2 ^ (prefixWord ++ tailWord_7757370).sum := by decide
  have hdescent : baseEnd_7757370 < baseStart_7757370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757413 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 2, 5, 2]
def baseStart_7757413 : Nat := 118140960795 + 7757413 * 2 ^ 59
def prefixEnd_7757413 : Nat := 4983230072969 + 3 ^ 40 * 7757413 * 2
def baseEnd_7757413 : Nat := 3983281504436562819661813

theorem tailTrace_7757413 : CollatzResearch.WordTrace tailWord_7757413 prefixEnd_7757413 3983281504436562819661813 := by
  unfold tailWord_7757413
  simp only [CollatzResearch.WordTrace]
  refine ⟨282936096245225036507964893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188624064163483357671976595 282936096245225036507964893)
  ·
    refine ⟨106101036091959388690486835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282936096245225036507964893 106101036091959388690486835)
    ·
      refine ⟨159151554137939083035730253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106101036091959388690486835 159151554137939083035730253)
      ·
        refine ⟨59681832801727156138398845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159151554137939083035730253 59681832801727156138398845)
        ·
          refine ⟨22380687300647683551899567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59681832801727156138398845 22380687300647683551899567)
          ·
            refine ⟨33571030950971525327849351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22380687300647683551899567 33571030950971525327849351)
            ·
              refine ⟨50356546426457287991774027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33571030950971525327849351 50356546426457287991774027)
              ·
                refine ⟨75534819639685931987661041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50356546426457287991774027 75534819639685931987661041)
                ·
                  refine ⟨56651114729764448990745781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75534819639685931987661041 56651114729764448990745781)
                  ·
                    refine ⟨5311042005915417092882417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56651114729764448990745781 5311042005915417092882417)
                    ·
                      refine ⟨3983281504436562819661813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311042005915417092882417 3983281504436562819661813)
                      ·
                        rfl

theorem cell23_7757413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_7757413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757413 prefixEnd_7757413 := by exact prefixLift 7757413
  have htrace : WordTrace (prefixWord ++ tailWord_7757413) baseStart_7757413 baseEnd_7757413 := by
    simpa [prefixWord, tailWord_7757413, baseEnd_7757413] using wordTrace_append hprefix tailTrace_7757413
  have hstable : (prefixWord ++ tailWord_7757413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757413).length < 2 ^ (prefixWord ++ tailWord_7757413).sum := by decide
  have hdescent : baseEnd_7757413 < baseStart_7757413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757470 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7757470 : Nat := 118140960795 + 7757470 * 2 ^ 59
def prefixEnd_7757470 : Nat := 4983230072969 + 3 ^ 40 * 7757470 * 2
def baseEnd_7757470 : Nat := 1327770257611289698883017

theorem tailTrace_7757470 : CollatzResearch.WordTrace tailWord_7757470 prefixEnd_7757470 1327770257611289698883017 := by
  unfold tailWord_7757470
  simp only [CollatzResearch.WordTrace]
  refine ⟨35367271900752316905348733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188625450137345690161859909 35367271900752316905348733)
  ·
    refine ⟨13262726962782118839505775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35367271900752316905348733 13262726962782118839505775)
    ·
      refine ⟨19894090444173178259258663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13262726962782118839505775 19894090444173178259258663)
      ·
        refine ⟨29841135666259767388887995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19894090444173178259258663 29841135666259767388887995)
        ·
          refine ⟨44761703499389651083331993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29841135666259767388887995 44761703499389651083331993)
          ·
            refine ⟨33571277624542238312498995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44761703499389651083331993 33571277624542238312498995)
            ·
              refine ⟨50356916436813357468748493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33571277624542238312498995 50356916436813357468748493)
              ·
                refine ⟨18883843663805009050780685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50356916436813357468748493 18883843663805009050780685)
                ·
                  refine ⟨7081441373926878394042757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18883843663805009050780685 7081441373926878394042757)
                  ·
                    refine ⟨1327770257611289698883017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081441373926878394042757 1327770257611289698883017)
                    ·
                      rfl

theorem cell23_7757470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7757470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757470 prefixEnd_7757470 := by exact prefixLift 7757470
  have htrace : WordTrace (prefixWord ++ tailWord_7757470) baseStart_7757470 baseEnd_7757470 := by
    simpa [prefixWord, tailWord_7757470, baseEnd_7757470] using wordTrace_append hprefix tailTrace_7757470
  have hstable : (prefixWord ++ tailWord_7757470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757470).length < 2 ^ (prefixWord ++ tailWord_7757470).sum := by decide
  have hdescent : baseEnd_7757470 < baseStart_7757470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757496 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 3, 5]
def baseStart_7757496 : Nat := 118140960795 + 7757496 * 2 ^ 59
def prefixEnd_7757496 : Nat := 4983230072969 + 3 ^ 40 * 7757496 * 2
def baseEnd_7757496 : Nat := 1327774707776961998307977

theorem tailTrace_7757496 : CollatzResearch.WordTrace tailWord_7757496 prefixEnd_7757496 1327774707776961998307977 := by
  unfold tailWord_7757496
  simp only [CollatzResearch.WordTrace]
  refine ⟨141469561751962170841618171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188626082335949561122157561 141469561751962170841618171)
  ·
    refine ⟨212204342627943256262427257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141469561751962170841618171 212204342627943256262427257)
    ·
      refine ⟨159153256970957442196820443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212204342627943256262427257 159153256970957442196820443)
      ·
        refine ⟨238729885456436163295230665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159153256970957442196820443 238729885456436163295230665)
        ·
          refine ⟨179047414092327122471422999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238729885456436163295230665 179047414092327122471422999)
          ·
            refine ⟨268571121138490683707134499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179047414092327122471422999 268571121138490683707134499)
            ·
              refine ⟨402856681707736025560701749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268571121138490683707134499 402856681707736025560701749)
              ·
                refine ⟨37767813910100252396315789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402856681707736025560701749 37767813910100252396315789)
                ·
                  refine ⟨14162930216287594648618421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37767813910100252396315789 14162930216287594648618421)
                  ·
                    refine ⟨1327774707776961998307977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14162930216287594648618421 1327774707776961998307977)
                    ·
                      rfl

theorem cell23_7757496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_7757496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757496 prefixEnd_7757496 := by exact prefixLift 7757496
  have htrace : WordTrace (prefixWord ++ tailWord_7757496) baseStart_7757496 baseEnd_7757496 := by
    simpa [prefixWord, tailWord_7757496, baseEnd_7757496] using wordTrace_append hprefix tailTrace_7757496
  have hstable : (prefixWord ++ tailWord_7757496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757496).length < 2 ^ (prefixWord ++ tailWord_7757496).sum := by decide
  have hdescent : baseEnd_7757496 < baseStart_7757496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757503 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 1, 5, 2]
def baseStart_7757503 : Nat := 118140960795 + 7757503 * 2 ^ 59
def prefixEnd_7757503 : Nat := 4983230072969 + 3 ^ 40 * 7757503 * 2
def baseEnd_7757503 : Nat := 3983327717695467467536399

theorem tailTrace_7757503 : CollatzResearch.WordTrace tailWord_7757503 prefixEnd_7757503 3983327717695467467536399 := by
  unfold tailWord_7757503
  simp only [CollatzResearch.WordTrace]
  refine ⟨282939378814898981878741163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188626252543265987919160775 282939378814898981878741163)
  ·
    refine ⟨424409068222348472818111745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282939378814898981878741163 424409068222348472818111745)
    ·
      refine ⟨318306801166761354613583809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424409068222348472818111745 318306801166761354613583809)
      ·
        refine ⟨238730100875071015960187857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318306801166761354613583809 238730100875071015960187857)
        ·
          refine ⟨179047575656303261970140893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238730100875071015960187857 179047575656303261970140893)
          ·
            refine ⟨67142840871113723238802835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179047575656303261970140893 67142840871113723238802835)
            ·
              refine ⟨100714261306670584858204253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67142840871113723238802835 100714261306670584858204253)
              ·
                refine ⟨37767847990001469321826595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100714261306670584858204253 37767847990001469321826595)
                ·
                  refine ⟨56651771985002203982739893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37767847990001469321826595 56651771985002203982739893)
                  ·
                    refine ⟨5311103623593956623381865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56651771985002203982739893 5311103623593956623381865)
                    ·
                      refine ⟨3983327717695467467536399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311103623593956623381865 3983327717695467467536399)
                      ·
                        rfl

theorem cell23_7757503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_7757503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757503 prefixEnd_7757503 := by exact prefixLift 7757503
  have htrace : WordTrace (prefixWord ++ tailWord_7757503) baseStart_7757503 baseEnd_7757503 := by
    simpa [prefixWord, tailWord_7757503, baseEnd_7757503] using wordTrace_append hprefix tailTrace_7757503
  have hstable : (prefixWord ++ tailWord_7757503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757503).length < 2 ^ (prefixWord ++ tailWord_7757503).sum := by decide
  have hdescent : baseEnd_7757503 < baseStart_7757503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757600 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3]
def baseStart_7757600 : Nat := 118140960795 + 7757600 * 2 ^ 59
def prefixEnd_7757600 : Nat := 4983230072969 + 3 ^ 40 * 7757600 * 2
def baseEnd_7757600 : Nat := 3983377525318953588023453

theorem tailTrace_7757600 : CollatzResearch.WordTrace tailWord_7757600 prefixEnd_7757600 3983377525318953588023453 := by
  unfold tailWord_7757600
  simp only [CollatzResearch.WordTrace]
  refine ⟨141471458347773783722511127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188628611130365044963348169 141471458347773783722511127)
  ·
    refine ⟨212207187521660675583766691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141471458347773783722511127 212207187521660675583766691)
    ·
      refine ⟨318310781282491013375650037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212207187521660675583766691 318310781282491013375650037)
      ·
        refine ⟨29841635745233532503967191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318310781282491013375650037 29841635745233532503967191)
        ·
          refine ⟨44762453617850298755950787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29841635745233532503967191 44762453617850298755950787)
          ·
            refine ⟨67143680426775448133926181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44762453617850298755950787 67143680426775448133926181)
            ·
              refine ⟨12589440080020396525111159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67143680426775448133926181 12589440080020396525111159)
              ·
                refine ⟨18884160120030594787666739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12589440080020396525111159 18884160120030594787666739)
                ·
                  refine ⟨28326240180045892181500109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18884160120030594787666739 28326240180045892181500109)
                  ·
                    refine ⟨10622340067517209568062541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28326240180045892181500109 10622340067517209568062541)
                    ·
                      refine ⟨3983377525318953588023453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10622340067517209568062541 3983377525318953588023453)
                      ·
                        rfl

theorem cell23_7757600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_7757600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757600 prefixEnd_7757600 := by exact prefixLift 7757600
  have htrace : WordTrace (prefixWord ++ tailWord_7757600) baseStart_7757600 baseEnd_7757600 := by
    simpa [prefixWord, tailWord_7757600, baseEnd_7757600] using wordTrace_append hprefix tailTrace_7757600
  have hstable : (prefixWord ++ tailWord_7757600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757600).length < 2 ^ (prefixWord ++ tailWord_7757600).sum := by decide
  have hdescent : baseEnd_7757600 < baseStart_7757600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757621 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_7757621 : Nat := 118140960795 + 7757621 * 2 ^ 59
def prefixEnd_7757621 : Nat := 4983230072969 + 3 ^ 40 * 7757621 * 2
def baseEnd_7757621 : Nat := 3983388308412698005860857

theorem tailTrace_7757621 : CollatzResearch.WordTrace tailWord_7757621 prefixEnd_7757621 3983388308412698005860857 := by
  unfold tailWord_7757621
  simp only [CollatzResearch.WordTrace]
  refine ⟨282943682628471488031536717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188629121752314325354357811 282943682628471488031536717)
  ·
    refine ⟨106103880985676808011826269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282943682628471488031536717 106103880985676808011826269)
    ·
      refine ⟨39788955369628803004434851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106103880985676808011826269 39788955369628803004434851)
      ·
        refine ⟨59683433054443204506652277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39788955369628803004434851 59683433054443204506652277)
        ·
          refine ⟨5595321848854050422498651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59683433054443204506652277 5595321848854050422498651)
          ·
            refine ⟨8392982773281075633747977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595321848854050422498651 8392982773281075633747977)
            ·
              refine ⟨6294737079960806725310983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8392982773281075633747977 6294737079960806725310983)
              ·
                refine ⟨9442105619941210087966475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294737079960806725310983 9442105619941210087966475)
                ·
                  refine ⟨14163158429911815131949713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9442105619941210087966475 14163158429911815131949713)
                  ·
                    refine ⟨10622368822433861348962285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14163158429911815131949713 10622368822433861348962285)
                    ·
                      refine ⟨3983388308412698005860857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10622368822433861348962285 3983388308412698005860857)
                      ·
                        rfl

theorem cell23_7757621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_7757621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757621 prefixEnd_7757621 := by exact prefixLift 7757621
  have htrace : WordTrace (prefixWord ++ tailWord_7757621) baseStart_7757621 baseEnd_7757621 := by
    simpa [prefixWord, tailWord_7757621, baseEnd_7757621] using wordTrace_append hprefix tailTrace_7757621
  have hstable : (prefixWord ++ tailWord_7757621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757621).length < 2 ^ (prefixWord ++ tailWord_7757621).sum := by decide
  have hdescent : baseEnd_7757621 < baseStart_7757621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757663 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 7]
def baseStart_7757663 : Nat := 118140960795 + 7757663 * 2 ^ 59
def prefixEnd_7757663 : Nat := 4983230072969 + 3 ^ 40 * 7757663 * 2
def baseEnd_7757663 : Nat := 442601097177798537948407

theorem tailTrace_7757663 : CollatzResearch.WordTrace tailWord_7757663 prefixEnd_7757663 442601097177798537948407 := by
  unfold tailWord_7757663
  simp only [CollatzResearch.WordTrace]
  refine ⟨282945214494319329204565643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188630142996212886136377095 282945214494319329204565643)
  ·
    refine ⟨424417821741478993806848465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282945214494319329204565643 424417821741478993806848465)
    ·
      refine ⟨318313366306109245355136349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424417821741478993806848465 318313366306109245355136349)
      ·
        refine ⟨119367512364790967008176131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318313366306109245355136349 119367512364790967008176131)
        ·
          refine ⟨179051268547186450512264197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119367512364790967008176131 179051268547186450512264197)
          ·
            refine ⟨33572112852597459471049537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179051268547186450512264197 33572112852597459471049537)
            ·
              refine ⟨25179084639448094603287153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33572112852597459471049537 25179084639448094603287153)
              ·
                refine ⟨18884313479586070952465365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25179084639448094603287153 18884313479586070952465365)
                ·
                  refine ⟨442601097177798537948407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18884313479586070952465365 442601097177798537948407)
                  ·
                    rfl

theorem cell23_7757663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 7].length) (baseStart_7757663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757663 prefixEnd_7757663 := by exact prefixLift 7757663
  have htrace : WordTrace (prefixWord ++ tailWord_7757663) baseStart_7757663 baseEnd_7757663 := by
    simpa [prefixWord, tailWord_7757663, baseEnd_7757663] using wordTrace_append hprefix tailTrace_7757663
  have hstable : (prefixWord ++ tailWord_7757663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757663).length < 2 ^ (prefixWord ++ tailWord_7757663).sum := by decide
  have hdescent : baseEnd_7757663 < baseStart_7757663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757673 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 3]
def baseStart_7757673 : Nat := 118140960795 + 7757673 * 2 ^ 59
def prefixEnd_7757673 : Nat := 4983230072969 + 3 ^ 40 * 7757673 * 2
def baseEnd_7757673 : Nat := 3983415009406731802410617

theorem tailTrace_7757673 : CollatzResearch.WordTrace tailWord_7757673 prefixEnd_7757673 3983415009406731802410617 := by
  unfold tailWord_7757673
  simp only [CollatzResearch.WordTrace]
  refine ⟨282945579224283100912429673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188630386149522067274953115 282945579224283100912429673)
  ·
    refine ⟨212209184418212325684322255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282945579224283100912429673 212209184418212325684322255)
    ·
      refine ⟨318313776627318488526483383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212209184418212325684322255 318313776627318488526483383)
      ·
        refine ⟨477470664940977732789725075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318313776627318488526483383 477470664940977732789725075)
        ·
          refine ⟨716205997411466599184587613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477470664940977732789725075 716205997411466599184587613)
          ·
            refine ⟨268577249029299974694220355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 716205997411466599184587613 268577249029299974694220355)
            ·
              refine ⟨402865873543949962041330533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268577249029299974694220355 402865873543949962041330533)
              ·
                refine ⟨75537351289490617882749475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402865873543949962041330533 75537351289490617882749475)
                ·
                  refine ⟨113306026934235926824124213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75537351289490617882749475 113306026934235926824124213)
                  ·
                    refine ⟨10622440025084618139761645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113306026934235926824124213 10622440025084618139761645)
                    ·
                      refine ⟨3983415009406731802410617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10622440025084618139761645 3983415009406731802410617)
                      ·
                        rfl

theorem cell23_7757673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_7757673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757673 prefixEnd_7757673 := by exact prefixLift 7757673
  have htrace : WordTrace (prefixWord ++ tailWord_7757673) baseStart_7757673 baseEnd_7757673 := by
    simpa [prefixWord, tailWord_7757673, baseEnd_7757673] using wordTrace_append hprefix tailTrace_7757673
  have hstable : (prefixWord ++ tailWord_7757673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757673).length < 2 ^ (prefixWord ++ tailWord_7757673).sum := by decide
  have hdescent : baseEnd_7757673 < baseStart_7757673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757713 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_7757713 : Nat := 118140960795 + 7757713 * 2 ^ 59
def prefixEnd_7757713 : Nat := 4983230072969 + 3 ^ 40 * 7757713 * 2
def baseEnd_7757713 : Nat := 3983435548632911645910433

theorem tailTrace_7757713 : CollatzResearch.WordTrace tailWord_7757713 prefixEnd_7757713 3983435548632911645910433 := by
  unfold tailWord_7757713
  simp only [CollatzResearch.WordTrace]
  refine ⟨282947038144138187743885793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188631358762758791829257195 282947038144138187743885793)
  ·
    refine ⟨212210278608103640807914345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282947038144138187743885793 212210278608103640807914345)
    ·
      refine ⟨159157708956077730605935759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212210278608103640807914345 159157708956077730605935759)
      ·
        refine ⟨238736563434116595908903639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159157708956077730605935759 238736563434116595908903639)
        ·
          refine ⟨358104845151174893863355459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238736563434116595908903639 358104845151174893863355459)
          ·
            refine ⟨537157267726762340795033189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358104845151174893863355459 537157267726762340795033189)
            ·
              refine ⟨100716987698767938899068723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 537157267726762340795033189 100716987698767938899068723)
              ·
                refine ⟨151075481548151908348603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100716987698767938899068723 151075481548151908348603085)
                ·
                  refine ⟨56653305580556965630726157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151075481548151908348603085 56653305580556965630726157)
                  ·
                    refine ⟨21244989592708862111522309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56653305580556965630726157 21244989592708862111522309)
                    ·
                      refine ⟨3983435548632911645910433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21244989592708862111522309 3983435548632911645910433)
                      ·
                        rfl

theorem cell23_7757713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_7757713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757713 prefixEnd_7757713 := by exact prefixLift 7757713
  have htrace : WordTrace (prefixWord ++ tailWord_7757713) baseStart_7757713 baseEnd_7757713 := by
    simpa [prefixWord, tailWord_7757713, baseEnd_7757713] using wordTrace_append hprefix tailTrace_7757713
  have hstable : (prefixWord ++ tailWord_7757713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757713).length < 2 ^ (prefixWord ++ tailWord_7757713).sum := by decide
  have hdescent : baseEnd_7757713 < baseStart_7757713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757727 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 2, 5]
def baseStart_7757727 : Nat := 118140960795 + 7757727 * 2 ^ 59
def prefixEnd_7757727 : Nat := 4983230072969 + 3 ^ 40 * 7757727 * 2
def baseEnd_7757727 : Nat := 1327814245787358197045123

theorem tailTrace_7757727 : CollatzResearch.WordTrace tailWord_7757727 prefixEnd_7757727 1327814245787358197045123 := by
  unfold tailWord_7757727
  simp only [CollatzResearch.WordTrace]
  refine ⟨282947548766087468134895435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188631699177391645423263623 282947548766087468134895435)
  ·
    refine ⟨424421323149131202202343153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282947548766087468134895435 424421323149131202202343153)
    ·
      refine ⟨318315992361848401651757365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424421323149131202202343153 318315992361848401651757365)
      ·
        refine ⟨29842124283923287654852253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318315992361848401651757365 29842124283923287654852253)
        ·
          refine ⟨11190796606471232870569595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29842124283923287654852253 11190796606471232870569595)
          ·
            refine ⟨16786194909706849305854393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11190796606471232870569595 16786194909706849305854393)
            ·
              refine ⟨12589646182280136979390795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16786194909706849305854393 12589646182280136979390795)
              ·
                refine ⟨18884469273420205469086193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12589646182280136979390795 18884469273420205469086193)
                ·
                  refine ⟨14163351955065154101814645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18884469273420205469086193 14163351955065154101814645)
                  ·
                    refine ⟨1327814245787358197045123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14163351955065154101814645 1327814245787358197045123)
                    ·
                      rfl

theorem cell23_7757727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_7757727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757727 prefixEnd_7757727 := by exact prefixLift 7757727
  have htrace : WordTrace (prefixWord ++ tailWord_7757727) baseStart_7757727 baseEnd_7757727 := by
    simpa [prefixWord, tailWord_7757727, baseEnd_7757727] using wordTrace_append hprefix tailTrace_7757727
  have hstable : (prefixWord ++ tailWord_7757727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757727).length < 2 ^ (prefixWord ++ tailWord_7757727).sum := by decide
  have hdescent : baseEnd_7757727 < baseStart_7757727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757743 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_7757743 : Nat := 118140960795 + 7757743 * 2 ^ 59
def prefixEnd_7757743 : Nat := 4983230072969 + 3 ^ 40 * 7757743 * 2
def baseEnd_7757743 : Nat := 3983450953052546528535295

theorem tailTrace_7757743 : CollatzResearch.WordTrace tailWord_7757743 prefixEnd_7757743 3983450953052546528535295 := by
  unfold tailWord_7757743
  simp only [CollatzResearch.WordTrace]
  refine ⟨282948132334029502867477883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188632088222686335244985255 282948132334029502867477883)
  ·
    refine ⟨424422198501044254301216825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282948132334029502867477883 424422198501044254301216825)
    ·
      refine ⟨318316648875783190725912619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424422198501044254301216825 318316648875783190725912619)
      ·
        refine ⟨477474973313674786088868929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318316648875783190725912619 477474973313674786088868929)
        ·
          refine ⟨358106229985256089566651697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477474973313674786088868929 358106229985256089566651697)
          ·
            refine ⟨268579672488942067174988773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358106229985256089566651697 268579672488942067174988773)
            ·
              refine ⟨50358688591676637595310395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268579672488942067174988773 50358688591676637595310395)
              ·
                refine ⟨75538032887514956392965593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50358688591676637595310395 75538032887514956392965593)
                ·
                  refine ⟨56653524665636217294724195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75538032887514956392965593 56653524665636217294724195)
                  ·
                    refine ⟨84980286998454325942086293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56653524665636217294724195 84980286998454325942086293)
                    ·
                      refine ⟨3983450953052546528535295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84980286998454325942086293 3983450953052546528535295)
                      ·
                        rfl

theorem cell23_7757743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_7757743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757743 prefixEnd_7757743 := by exact prefixLift 7757743
  have htrace : WordTrace (prefixWord ++ tailWord_7757743) baseStart_7757743 baseEnd_7757743 := by
    simpa [prefixWord, tailWord_7757743, baseEnd_7757743] using wordTrace_append hprefix tailTrace_7757743
  have hstable : (prefixWord ++ tailWord_7757743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757743).length < 2 ^ (prefixWord ++ tailWord_7757743).sum := by decide
  have hdescent : baseEnd_7757743 < baseStart_7757743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757748 : List Nat := [2, 5, 2, 1, 2, 2, 2, 2, 5]
def baseStart_7757748 : Nat := 118140960795 + 7757748 * 2 ^ 59
def prefixEnd_7757748 : Nat := 4983230072969 + 3 ^ 40 * 7757748 * 2
def baseEnd_7757748 : Nat := 442605946717313223219197

theorem tailTrace_7757748 : CollatzResearch.WordTrace tailWord_7757748 prefixEnd_7757748 442605946717313223219197 := by
  unfold tailWord_7757748
  simp only [CollatzResearch.WordTrace]
  refine ⟨141474157349505694360704949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188632209799340925814273265 141474157349505694360704949)
  ·
    refine ⟨13263202251516158846316089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141474157349505694360704949 13263202251516158846316089)
    ·
      refine ⟨9947401688637119134737067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13263202251516158846316089 9947401688637119134737067)
      ·
        refine ⟨14921102532955678702105601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9947401688637119134737067 14921102532955678702105601)
        ·
          refine ⟨11190826899716759026579201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14921102532955678702105601 11190826899716759026579201)
          ·
            refine ⟨8393120174787569269934401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11190826899716759026579201 8393120174787569269934401)
            ·
              refine ⟨6294840131090676952450801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393120174787569269934401 6294840131090676952450801)
              ·
                refine ⟨4721130098318007714338101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6294840131090676952450801 4721130098318007714338101)
                ·
                  refine ⟨442605946717313223219197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4721130098318007714338101 442605946717313223219197)
                  ·
                    rfl

theorem cell23_7757748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_7757748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757748 prefixEnd_7757748 := by exact prefixLift 7757748
  have htrace : WordTrace (prefixWord ++ tailWord_7757748) baseStart_7757748 baseEnd_7757748 := by
    simpa [prefixWord, tailWord_7757748, baseEnd_7757748] using wordTrace_append hprefix tailTrace_7757748
  have hstable : (prefixWord ++ tailWord_7757748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757748).length < 2 ^ (prefixWord ++ tailWord_7757748).sum := by decide
  have hdescent : baseEnd_7757748 < baseStart_7757748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757770 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 6]
def baseStart_7757770 : Nat := 118140960795 + 7757770 * 2 ^ 59
def prefixEnd_7757770 : Nat := 4983230072969 + 3 ^ 40 * 7757770 * 2
def baseEnd_7757770 : Nat := 442607201892246435877519

theorem tailTrace_7757770 : CollatzResearch.WordTrace tailWord_7757770 prefixEnd_7757770 442607201892246435877519 := by
  unfold tailWord_7757770
  simp only [CollatzResearch.WordTrace]
  refine ⟨70737279276232921619677691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188632744736621124319140509 70737279276232921619677691)
  ·
    refine ⟨106105918914349382429516537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70737279276232921619677691 106105918914349382429516537)
    ·
      refine ⟨79579439185762036822137403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106105918914349382429516537 79579439185762036822137403)
      ·
        refine ⟨119369158778643055233206105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79579439185762036822137403 119369158778643055233206105)
        ·
          refine ⟨89526869083982291424904579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119369158778643055233206105 89526869083982291424904579)
          ·
            refine ⟨134290303625973437137356869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89526869083982291424904579 134290303625973437137356869)
            ·
              refine ⟨25179431929870019463254413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134290303625973437137356869 25179431929870019463254413)
              ·
                refine ⟨9442286973701257298720405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25179431929870019463254413 9442286973701257298720405)
                ·
                  refine ⟨442607201892246435877519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9442286973701257298720405 442607201892246435877519)
                  ·
                    rfl

theorem cell23_7757770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_7757770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757770 prefixEnd_7757770 := by exact prefixLift 7757770
  have htrace : WordTrace (prefixWord ++ tailWord_7757770) baseStart_7757770 baseEnd_7757770 := by
    simpa [prefixWord, tailWord_7757770, baseEnd_7757770] using wordTrace_append hprefix tailTrace_7757770
  have hstable : (prefixWord ++ tailWord_7757770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757770).length < 2 ^ (prefixWord ++ tailWord_7757770).sum := by decide
  have hdescent : baseEnd_7757770 < baseStart_7757770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757807 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 4, 3, 2]
def baseStart_7757807 : Nat := 118140960795 + 7757807 * 2 ^ 59
def prefixEnd_7757807 : Nat := 4983230072969 + 3 ^ 40 * 7757807 * 2
def baseEnd_7757807 : Nat := 3983483815814434278135001

theorem tailTrace_7757807 : CollatzResearch.WordTrace tailWord_7757807 prefixEnd_7757807 3983483815814434278135001 := by
  unfold tailWord_7757807
  simp only [CollatzResearch.WordTrace]
  refine ⟨282950466605797641797807675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188633644403865094531871783 282950466605797641797807675)
  ·
    refine ⟨424425699908696462696711513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282950466605797641797807675 424425699908696462696711513)
    ·
      refine ⟨318319274931522347022533635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424425699908696462696711513 318319274931522347022533635)
      ·
        refine ⟨477478912397283520533800453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318319274931522347022533635 477478912397283520533800453)
        ·
          refine ⟨89527296074490660100087585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477478912397283520533800453 89527296074490660100087585)
          ·
            refine ⟨67145472055867995075065689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89527296074490660100087585 67145472055867995075065689)
            ·
              refine ⟨50359104041900996306299267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67145472055867995075065689 50359104041900996306299267)
              ·
                refine ⟨75538656062851494459448901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50359104041900996306299267 75538656062851494459448901)
                ·
                  refine ⟨14163498011784655211146669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75538656062851494459448901 14163498011784655211146669)
                  ·
                    refine ⟨5311311754419245704180001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14163498011784655211146669 5311311754419245704180001)
                    ·
                      refine ⟨3983483815814434278135001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311311754419245704180001 3983483815814434278135001)
                      ·
                        rfl

theorem cell23_7757807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3, 2].length) (baseStart_7757807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757807 prefixEnd_7757807 := by exact prefixLift 7757807
  have htrace : WordTrace (prefixWord ++ tailWord_7757807) baseStart_7757807 baseEnd_7757807 := by
    simpa [prefixWord, tailWord_7757807, baseEnd_7757807] using wordTrace_append hprefix tailTrace_7757807
  have hstable : (prefixWord ++ tailWord_7757807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757807).length < 2 ^ (prefixWord ++ tailWord_7757807).sum := by decide
  have hdescent : baseEnd_7757807 < baseStart_7757807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757834 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_7757834 : Nat := 118140960795 + 7757834 * 2 ^ 59
def prefixEnd_7757834 : Nat := 4983230072969 + 3 ^ 40 * 7757834 * 2
def baseEnd_7757834 : Nat := 1327832559930701890832459

theorem tailTrace_7757834 : CollatzResearch.WordTrace tailWord_7757834 prefixEnd_7757834 1327832559930701890832459 := by
  unfold tailWord_7757834
  simp only [CollatzResearch.WordTrace]
  refine ⟨70737862844174956352260139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188634300917799883606027037 70737862844174956352260139)
  ·
    refine ⟨106106794266262434528390209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70737862844174956352260139 106106794266262434528390209)
    ·
      refine ⟨79580095699696825896292657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106106794266262434528390209 79580095699696825896292657)
      ·
        refine ⟨59685071774772619422219493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79580095699696825896292657 59685071774772619422219493)
        ·
          refine ⟨11190950957769866141666155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59685071774772619422219493 11190950957769866141666155)
          ·
            refine ⟨16786426436654799212499233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11190950957769866141666155 16786426436654799212499233)
            ·
              refine ⟨12589819827491099409374425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16786426436654799212499233 12589819827491099409374425)
              ·
                refine ⟨9442364870618324557030819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12589819827491099409374425 9442364870618324557030819)
                ·
                  refine ⟨14163547305927486835546229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9442364870618324557030819 14163547305927486835546229)
                  ·
                    refine ⟨1327832559930701890832459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14163547305927486835546229 1327832559930701890832459)
                    ·
                      rfl

theorem cell23_7757834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_7757834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757834 prefixEnd_7757834 := by exact prefixLift 7757834
  have htrace : WordTrace (prefixWord ++ tailWord_7757834) baseStart_7757834 baseEnd_7757834 := by
    simpa [prefixWord, tailWord_7757834, baseEnd_7757834] using wordTrace_append hprefix tailTrace_7757834
  have hstable : (prefixWord ++ tailWord_7757834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757834).length < 2 ^ (prefixWord ++ tailWord_7757834).sum := by decide
  have hdescent : baseEnd_7757834 < baseStart_7757834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757900 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_7757900 : Nat := 118140960795 + 7757900 * 2 ^ 59
def prefixEnd_7757900 : Nat := 4983230072969 + 3 ^ 40 * 7757900 * 2
def baseEnd_7757900 : Nat := 3983531569515302414272073

theorem tailTrace_7757900 : CollatzResearch.WordTrace tailWord_7757900 prefixEnd_7757900 3983531569515302414272073 := by
  unfold tailWord_7757900
  simp only [CollatzResearch.WordTrace]
  refine ⟨141476929297230359340471577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188635905729640479120628769 141476929297230359340471577)
  ·
    refine ⟨106107696972922769505353683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141476929297230359340471577 106107696972922769505353683)
    ·
      refine ⟨159161545459384154258030525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106107696972922769505353683 159161545459384154258030525)
      ·
        refine ⟨59685579547269057846761447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159161545459384154258030525 59685579547269057846761447)
        ·
          refine ⟨89528369320903586770142171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59685579547269057846761447 89528369320903586770142171)
          ·
            refine ⟨134292553981355380155213257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89528369320903586770142171 134292553981355380155213257)
            ·
              refine ⟨100719415486016535116409943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134292553981355380155213257 100719415486016535116409943)
              ·
                refine ⟨151079123229024802674614915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100719415486016535116409943 151079123229024802674614915)
                ·
                  refine ⟨226618684843537204011922373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151079123229024802674614915 226618684843537204011922373)
                  ·
                    refine ⟨42491003408163225752235445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226618684843537204011922373 42491003408163225752235445)
                    ·
                      refine ⟨3983531569515302414272073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42491003408163225752235445 3983531569515302414272073)
                      ·
                        rfl

theorem cell23_7757900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_7757900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757900 prefixEnd_7757900 := by exact prefixLift 7757900
  have htrace : WordTrace (prefixWord ++ tailWord_7757900) baseStart_7757900 baseEnd_7757900 := by
    simpa [prefixWord, tailWord_7757900, baseEnd_7757900] using wordTrace_append hprefix tailTrace_7757900
  have hstable : (prefixWord ++ tailWord_7757900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757900).length < 2 ^ (prefixWord ++ tailWord_7757900).sum := by decide
  have hdescent : baseEnd_7757900 < baseStart_7757900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757944 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 6, 2, 2]
def baseStart_7757944 : Nat := 118140960795 + 7757944 * 2 ^ 59
def prefixEnd_7757944 : Nat := 4983230072969 + 3 ^ 40 * 7757944 * 2
def baseEnd_7757944 : Nat := 3983554162664100242121871

theorem tailTrace_7757944 : CollatzResearch.WordTrace tailWord_7757944 prefixEnd_7757944 3983554162664100242121871 := by
  unfold tailWord_7757944
  simp only [CollatzResearch.WordTrace]
  refine ⟨141477731703150657097772443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188636975604200876130363257 141477731703150657097772443)
  ·
    refine ⟨212216597554725985646658665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141477731703150657097772443 212216597554725985646658665)
    ·
      refine ⟨159162448166044489234993999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212216597554725985646658665 159162448166044489234993999)
      ·
        refine ⟨238743672249066733852490999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159162448166044489234993999 238743672249066733852490999)
        ·
          refine ⟨358115508373600100778736499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238743672249066733852490999 358115508373600100778736499)
          ·
            refine ⟨537173262560400151168104749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358115508373600100778736499 537173262560400151168104749)
            ·
              refine ⟨201439973460150056688039281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537173262560400151168104749 201439973460150056688039281)
              ·
                refine ⟨151079980095112542516029461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201439973460150056688039281 151079980095112542516029461)
                ·
                  refine ⟨7081874066958400430438881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151079980095112542516029461 7081874066958400430438881)
                  ·
                    refine ⟨5311405550218800322829161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7081874066958400430438881 5311405550218800322829161)
                    ·
                      refine ⟨3983554162664100242121871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311405550218800322829161 3983554162664100242121871)
                      ·
                        rfl

theorem cell23_7757944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 2, 2].length) (baseStart_7757944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757944 prefixEnd_7757944 := by exact prefixLift 7757944
  have htrace : WordTrace (prefixWord ++ tailWord_7757944) baseStart_7757944 baseEnd_7757944 := by
    simpa [prefixWord, tailWord_7757944, baseEnd_7757944] using wordTrace_append hprefix tailTrace_7757944
  have hstable : (prefixWord ++ tailWord_7757944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757944).length < 2 ^ (prefixWord ++ tailWord_7757944).sum := by decide
  have hdescent : baseEnd_7757944 < baseStart_7757944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757972 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7757972 : Nat := 118140960795 + 7757972 * 2 ^ 59
def prefixEnd_7757972 : Nat := 4983230072969 + 3 ^ 40 * 7757972 * 2
def baseEnd_7757972 : Nat := 3983568540122426132571743

theorem tailTrace_7757972 : CollatzResearch.WordTrace tailWord_7757972 prefixEnd_7757972 3983568540122426132571743 := by
  unfold tailWord_7757972
  simp only [CollatzResearch.WordTrace]
  refine ⟨141478242325099937488782085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188637656433466583318376113 141478242325099937488782085)
  ·
    refine ⟨26527170435956238279146641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141478242325099937488782085 26527170435956238279146641)
    ·
      refine ⟨19895377826967178709359981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26527170435956238279146641 19895377826967178709359981)
      ·
        refine ⟨7460766685112692016009993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19895377826967178709359981 7460766685112692016009993)
        ·
          refine ⟨5595575013834519012007495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7460766685112692016009993 5595575013834519012007495)
          ·
            refine ⟨8393362520751778518011243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595575013834519012007495 8393362520751778518011243)
            ·
              refine ⟨12590043781127667777016865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393362520751778518011243 12590043781127667777016865)
              ·
                refine ⟨9442532835845750832762649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12590043781127667777016865 9442532835845750832762649)
                ·
                  refine ⟨7081899626884313124571987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9442532835845750832762649 7081899626884313124571987)
                  ·
                    refine ⟨10622849440326469686857981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7081899626884313124571987 10622849440326469686857981)
                    ·
                      refine ⟨3983568540122426132571743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10622849440326469686857981 3983568540122426132571743)
                      ·
                        rfl

theorem cell23_7757972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7757972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757972 prefixEnd_7757972 := by exact prefixLift 7757972
  have htrace : WordTrace (prefixWord ++ tailWord_7757972) baseStart_7757972 baseEnd_7757972 := by
    simpa [prefixWord, tailWord_7757972, baseEnd_7757972] using wordTrace_append hprefix tailTrace_7757972
  have hstable : (prefixWord ++ tailWord_7757972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757972).length < 2 ^ (prefixWord ++ tailWord_7757972).sum := by decide
  have hdescent : baseEnd_7757972 < baseStart_7757972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757978 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7757978 : Nat := 118140960795 + 7757978 * 2 ^ 59
def prefixEnd_7757978 : Nat := 4983230072969 + 3 ^ 40 * 7757978 * 2
def baseEnd_7757978 : Nat := 3983571621006353109096715

theorem tailTrace_7757978 : CollatzResearch.WordTrace tailWord_7757978 prefixEnd_7757978 3983571621006353109096715 := by
  unfold tailWord_7757978
  simp only [CollatzResearch.WordTrace]
  refine ⟨70739175872044534500570647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188637802325452092001521725 70739175872044534500570647)
  ·
    refine ⟨106108763808066801750855971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70739175872044534500570647 106108763808066801750855971)
    ·
      refine ⟨159163145712100202626283957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106108763808066801750855971 159163145712100202626283957)
      ·
        refine ⟨14921544910509393996214121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159163145712100202626283957 14921544910509393996214121)
        ·
          refine ⟨11191158682882045497160591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14921544910509393996214121 11191158682882045497160591)
          ·
            refine ⟨16786738024323068245740887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191158682882045497160591 16786738024323068245740887)
            ·
              refine ⟨25180107036484602368611331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16786738024323068245740887 25180107036484602368611331)
              ·
                refine ⟨37770160554726903552916997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25180107036484602368611331 37770160554726903552916997)
                ·
                  refine ⟨7081905104011294416171937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37770160554726903552916997 7081905104011294416171937)
                  ·
                    refine ⟨5311428828008470812128953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7081905104011294416171937 5311428828008470812128953)
                    ·
                      refine ⟨3983571621006353109096715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311428828008470812128953 3983571621006353109096715)
                      ·
                        rfl

theorem cell23_7757978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7757978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757978 prefixEnd_7757978 := by exact prefixLift 7757978
  have htrace : WordTrace (prefixWord ++ tailWord_7757978) baseStart_7757978 baseEnd_7757978 := by
    simpa [prefixWord, tailWord_7757978, baseEnd_7757978] using wordTrace_append hprefix tailTrace_7757978
  have hstable : (prefixWord ++ tailWord_7757978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757978).length < 2 ^ (prefixWord ++ tailWord_7757978).sum := by decide
  have hdescent : baseEnd_7757978 < baseStart_7757978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7757984 : List Nat := [2, 1, 1, 4, 2, 2, 2, 4, 5]
def baseStart_7757984 : Nat := 118140960795 + 7757984 * 2 ^ 59
def prefixEnd_7757984 : Nat := 4983230072969 + 3 ^ 40 * 7757984 * 2
def baseEnd_7757984 : Nat := 442619411321142231735743

theorem tailTrace_7757984 : CollatzResearch.WordTrace tailWord_7757984 prefixEnd_7757984 442619411321142231735743 := by
  unfold tailWord_7757984
  simp only [CollatzResearch.WordTrace]
  refine ⟨141478461163078200513500503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188637948217437600684667337 141478461163078200513500503)
  ·
    refine ⟨212217691744617300770250755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141478461163078200513500503 212217691744617300770250755)
    ·
      refine ⟨318326537616925951155376133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212217691744617300770250755 318326537616925951155376133)
      ·
        refine ⟨59686225803173615841633025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318326537616925951155376133 59686225803173615841633025)
        ·
          refine ⟨44764669352380211881224769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59686225803173615841633025 44764669352380211881224769)
          ·
            refine ⟨33573502014285158910918577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44764669352380211881224769 33573502014285158910918577)
            ·
              refine ⟨25180126510713869183188933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33573502014285158910918577 25180126510713869183188933)
              ·
                refine ⟨4721273720758850471847925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25180126510713869183188933 4721273720758850471847925)
                ·
                  refine ⟨442619411321142231735743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4721273720758850471847925 442619411321142231735743)
                  ·
                    rfl

theorem cell23_7757984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 5].length) (baseStart_7757984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7757984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7757984 prefixEnd_7757984 := by exact prefixLift 7757984
  have htrace : WordTrace (prefixWord ++ tailWord_7757984) baseStart_7757984 baseEnd_7757984 := by
    simpa [prefixWord, tailWord_7757984, baseEnd_7757984] using wordTrace_append hprefix tailTrace_7757984
  have hstable : (prefixWord ++ tailWord_7757984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7757984).length < 2 ^ (prefixWord ++ tailWord_7757984).sum := by decide
  have hdescent : baseEnd_7757984 < baseStart_7757984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7757984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758034 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7758034 : Nat := 118140960795 + 7758034 * 2 ^ 59
def prefixEnd_7758034 : Nat := 4983230072969 + 3 ^ 40 * 7758034 * 2
def baseEnd_7758034 : Nat := 3983600375923004889996457

theorem tailTrace_7758034 : CollatzResearch.WordTrace tailWord_7758034 prefixEnd_7758034 3983600375923004889996457 := by
  unfold tailWord_7758034
  simp only [CollatzResearch.WordTrace]
  refine ⟨70739686493993814891580289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188639163983983506377547437 70739686493993814891580289)
  ·
    refine ⟨53054764870495361168685217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70739686493993814891580289 53054764870495361168685217)
    ·
      refine ⟨39791073652871520876513913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53054764870495361168685217 39791073652871520876513913)
      ·
        refine ⟨29843305239653640657385435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39791073652871520876513913 29843305239653640657385435)
        ·
          refine ⟨44764957859480460986078153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29843305239653640657385435 44764957859480460986078153)
          ·
            refine ⟨33573718394610345739558615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44764957859480460986078153 33573718394610345739558615)
            ·
              refine ⟨50360577591915518609337923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33573718394610345739558615 50360577591915518609337923)
              ·
                refine ⟨75540866387873277914006885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50360577591915518609337923 75540866387873277914006885)
                ·
                  refine ⟨14163912447726239608876291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75540866387873277914006885 14163912447726239608876291)
                  ·
                    refine ⟨21245868671589359413314437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14163912447726239608876291 21245868671589359413314437)
                    ·
                      refine ⟨3983600375923004889996457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21245868671589359413314437 3983600375923004889996457)
                      ·
                        rfl

theorem cell23_7758034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7758034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758034 prefixEnd_7758034 := by exact prefixLift 7758034
  have htrace : WordTrace (prefixWord ++ tailWord_7758034) baseStart_7758034 baseEnd_7758034 := by
    simpa [prefixWord, tailWord_7758034, baseEnd_7758034] using wordTrace_append hprefix tailTrace_7758034
  have hstable : (prefixWord ++ tailWord_7758034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758034).length < 2 ^ (prefixWord ++ tailWord_7758034).sum := by decide
  have hdescent : baseEnd_7758034 < baseStart_7758034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758057 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 6]
def baseStart_7758057 : Nat := 118140960795 + 7758057 * 2 ^ 59
def prefixEnd_7758057 : Nat := 4983230072969 + 3 ^ 40 * 7758057 * 2
def baseEnd_7758057 : Nat := 442623576219784255556539

theorem tailTrace_7758057 : CollatzResearch.WordTrace tailWord_7758057 prefixEnd_7758057 442623576219784255556539 := by
  unfold tailWord_7758057
  simp only [CollatzResearch.WordTrace]
  refine ⟨282959584854891934494408425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188639723236594622996272283 282959584854891934494408425)
  ·
    refine ⟨212219688641168950870806319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282959584854891934494408425 212219688641168950870806319)
    ·
      refine ⟨318329532961753426306209479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212219688641168950870806319 318329532961753426306209479)
      ·
        refine ⟨477494299442630139459314219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318329532961753426306209479 477494299442630139459314219)
        ·
          refine ⟨716241449163945209188971329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477494299442630139459314219 716241449163945209188971329)
          ·
            refine ⟨537181086872958906891728497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716241449163945209188971329 537181086872958906891728497)
            ·
              refine ⟨402885815154719180168796373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537181086872958906891728497 402885815154719180168796373)
              ·
                refine ⟨9442636292688730785206165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 402885815154719180168796373 9442636292688730785206165)
                ·
                  refine ⟨442623576219784255556539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9442636292688730785206165 442623576219784255556539)
                  ·
                    rfl

theorem cell23_7758057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 6].length) (baseStart_7758057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758057 prefixEnd_7758057 := by exact prefixLift 7758057
  have htrace : WordTrace (prefixWord ++ tailWord_7758057) baseStart_7758057 baseEnd_7758057 := by
    simpa [prefixWord, tailWord_7758057, baseEnd_7758057] using wordTrace_append hprefix tailTrace_7758057
  have hstable : (prefixWord ++ tailWord_7758057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758057).length < 2 ^ (prefixWord ++ tailWord_7758057).sum := by decide
  have hdescent : baseEnd_7758057 < baseStart_7758057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758078 : List Nat := [4, 2, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7758078 : Nat := 118140960795 + 7758078 * 2 ^ 59
def prefixEnd_7758078 : Nat := 4983230072969 + 3 ^ 40 * 7758078 * 2
def baseEnd_7758078 : Nat := 1327874323023934239282085

theorem tailTrace_7758078 : CollatzResearch.WordTrace tailWord_7758078 prefixEnd_7758078 1327874323023934239282085 := by
  unfold tailWord_7758078
  simp only [CollatzResearch.WordTrace]
  refine ⟨35370043848476981885115361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188640233858543903387281925 35370043848476981885115361)
  ·
    refine ⟨26527532886357736413836521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35370043848476981885115361 26527532886357736413836521)
    ·
      refine ⟨19895649664768302310377391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26527532886357736413836521 19895649664768302310377391)
      ·
        refine ⟨29843474497152453465566087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19895649664768302310377391 29843474497152453465566087)
        ·
          refine ⟨44765211745728680198349131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29843474497152453465566087 44765211745728680198349131)
          ·
            refine ⟨67147817618593020297523697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44765211745728680198349131 67147817618593020297523697)
            ·
              refine ⟨50360863213944765223142773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67147817618593020297523697 50360863213944765223142773)
              ·
                refine ⟨4721330926307321739669635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50360863213944765223142773 4721330926307321739669635)
                ·
                  refine ⟨7081996389460982609504453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721330926307321739669635 7081996389460982609504453)
                  ·
                    refine ⟨1327874323023934239282085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7081996389460982609504453 1327874323023934239282085)
                    ·
                      rfl

theorem cell23_7758078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7758078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758078 prefixEnd_7758078 := by exact prefixLift 7758078
  have htrace : WordTrace (prefixWord ++ tailWord_7758078) baseStart_7758078 baseEnd_7758078 := by
    simpa [prefixWord, tailWord_7758078, baseEnd_7758078] using wordTrace_append hprefix tailTrace_7758078
  have hstable : (prefixWord ++ tailWord_7758078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758078).length < 2 ^ (prefixWord ++ tailWord_7758078).sum := by decide
  have hdescent : baseEnd_7758078 < baseStart_7758078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758124 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_7758124 : Nat := 118140960795 + 7758124 * 2 ^ 59
def prefixEnd_7758124 : Nat := 4983230072969 + 3 ^ 40 * 7758124 * 2
def baseEnd_7758124 : Nat := 3983646589181909537871043

theorem tailTrace_7758124 : CollatzResearch.WordTrace tailWord_7758124 prefixEnd_7758124 3983646589181909537871043 := by
  unfold tailWord_7758124
  simp only [CollatzResearch.WordTrace]
  refine ⟨141481014272824602468548713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188641352363766136624731617 141481014272824602468548713)
  ·
    refine ⟨106110760704618451851411535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141481014272824602468548713 106110760704618451851411535)
    ·
      refine ⟨159166141056927677777117303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106110760704618451851411535 159166141056927677777117303)
      ·
        refine ⟨238749211585391516665675955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159166141056927677777117303 238749211585391516665675955)
        ·
          refine ⟨358123817378087274998513933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238749211585391516665675955 358123817378087274998513933)
          ·
            refine ⟨134296431516782728124442725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358123817378087274998513933 134296431516782728124442725)
            ·
              refine ⟨25180580909396761523333011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134296431516782728124442725 25180580909396761523333011)
              ·
                refine ⟨37770871364095142284999517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25180580909396761523333011 37770871364095142284999517)
                ·
                  refine ⟨14164076761535678356874819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37770871364095142284999517 14164076761535678356874819)
                  ·
                    refine ⟨21246115142303517535312229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14164076761535678356874819 21246115142303517535312229)
                    ·
                      refine ⟨3983646589181909537871043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21246115142303517535312229 3983646589181909537871043)
                      ·
                        rfl

theorem cell23_7758124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_7758124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758124 prefixEnd_7758124 := by exact prefixLift 7758124
  have htrace : WordTrace (prefixWord ++ tailWord_7758124) baseStart_7758124 baseEnd_7758124 := by
    simpa [prefixWord, tailWord_7758124, baseEnd_7758124] using wordTrace_append hprefix tailTrace_7758124
  have hstable : (prefixWord ++ tailWord_7758124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758124).length < 2 ^ (prefixWord ++ tailWord_7758124).sum := by decide
  have hdescent : baseEnd_7758124 < baseStart_7758124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758138 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_7758138 : Nat := 118140960795 + 7758138 * 2 ^ 59
def prefixEnd_7758138 : Nat := 4983230072969 + 3 ^ 40 * 7758138 * 2
def baseEnd_7758138 : Nat := 1327884592637024161031993

theorem tailTrace_7758138 : CollatzResearch.WordTrace tailWord_7758138 prefixEnd_7758138 1327884592637024161031993 := by
  unfold tailWord_7758138
  simp only [CollatzResearch.WordTrace]
  refine ⟨70740634791899621332026767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188641692778398990218738045 70740634791899621332026767)
  ·
    refine ⟨106110952187849431998040151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70740634791899621332026767 106110952187849431998040151)
    ·
      refine ⟨159166428281774147997060227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106110952187849431998040151 159166428281774147997060227)
      ·
        refine ⟨238749642422661221995590341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159166428281774147997060227 238749642422661221995590341)
        ·
          refine ⟨44765557954248979124173189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238749642422661221995590341 44765557954248979124173189)
          ·
            refine ⟨8393542116421683585782473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44765557954248979124173189 8393542116421683585782473)
            ·
              refine ⟨6295156587316262689336855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393542116421683585782473 6295156587316262689336855)
              ·
                refine ⟨9442734880974394034005283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295156587316262689336855 9442734880974394034005283)
                ·
                  refine ⟨14164102321461591051007925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9442734880974394034005283 14164102321461591051007925)
                  ·
                    refine ⟨1327884592637024161031993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14164102321461591051007925 1327884592637024161031993)
                    ·
                      rfl

theorem cell23_7758138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_7758138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758138 prefixEnd_7758138 := by exact prefixLift 7758138
  have htrace : WordTrace (prefixWord ++ tailWord_7758138) baseStart_7758138 baseEnd_7758138 := by
    simpa [prefixWord, tailWord_7758138, baseEnd_7758138] using wordTrace_append hprefix tailTrace_7758138
  have hstable : (prefixWord ++ tailWord_7758138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758138).length < 2 ^ (prefixWord ++ tailWord_7758138).sum := by decide
  have hdescent : baseEnd_7758138 < baseStart_7758138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758144 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3]
def baseStart_7758144 : Nat := 118140960795 + 7758144 * 2 ^ 59
def prefixEnd_7758144 : Nat := 4983230072969 + 3 ^ 40 * 7758144 * 2
def baseEnd_7758144 : Nat := 3983656858794999459620951

theorem tailTrace_7758144 : CollatzResearch.WordTrace tailWord_7758144 prefixEnd_7758144 3983656858794999459620951 := by
  unfold tailWord_7758144
  simp only [CollatzResearch.WordTrace]
  refine ⟨141481379002788374176412743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188641838670384498901883657 141481379002788374176412743)
  ·
    refine ⟨212222068504182561264619115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141481379002788374176412743 212222068504182561264619115)
    ·
      refine ⟨318333102756273841896928673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212222068504182561264619115 318333102756273841896928673)
      ·
        refine ⟨238749827067205381422696505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318333102756273841896928673 238749827067205381422696505)
        ·
          refine ⟨179062370300404036067022379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238749827067205381422696505 179062370300404036067022379)
          ·
            refine ⟨268593555450606054100533569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179062370300404036067022379 268593555450606054100533569)
            ·
              refine ⟨201445166587954540575400177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268593555450606054100533569 201445166587954540575400177)
              ·
                refine ⟨151083874940965905431550133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201445166587954540575400177 151083874940965905431550133)
                ·
                  refine ⟨14164113275715553634207825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151083874940965905431550133 14164113275715553634207825)
                  ·
                    refine ⟨10623084956786665225655869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14164113275715553634207825 10623084956786665225655869)
                    ·
                      refine ⟨3983656858794999459620951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10623084956786665225655869 3983656858794999459620951)
                      ·
                        rfl

theorem cell23_7758144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_7758144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758144 prefixEnd_7758144 := by exact prefixLift 7758144
  have htrace : WordTrace (prefixWord ++ tailWord_7758144) baseStart_7758144 baseEnd_7758144 := by
    simpa [prefixWord, tailWord_7758144, baseEnd_7758144] using wordTrace_append hprefix tailTrace_7758144
  have hstable : (prefixWord ++ tailWord_7758144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758144).length < 2 ^ (prefixWord ++ tailWord_7758144).sum := by decide
  have hdescent : baseEnd_7758144 < baseStart_7758144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758178 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_7758178 : Nat := 118140960795 + 7758178 * 2 ^ 59
def prefixEnd_7758178 : Nat := 4983230072969 + 3 ^ 40 * 7758178 * 2
def baseEnd_7758178 : Nat := 3983674317137252326595795

theorem tailTrace_7758178 : CollatzResearch.WordTrace tailWord_7758178 prefixEnd_7758178 3983674317137252326595795 := by
  unfold tailWord_7758178
  simp only [CollatzResearch.WordTrace]
  refine ⟨70740999521863393039890797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188642665391635714773042125 70740999521863393039890797)
  ·
    refine ⟨26527874820698772389959049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70740999521863393039890797 26527874820698772389959049)
    ·
      refine ⟨19895906115524079292469287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26527874820698772389959049 19895906115524079292469287)
      ·
        refine ⟨29843859173286118938703931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19895906115524079292469287 29843859173286118938703931)
        ·
          refine ⟨44765788759929178408055897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29843859173286118938703931 44765788759929178408055897)
          ·
            refine ⟨33574341569946883806041923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44765788759929178408055897 33574341569946883806041923)
            ·
              refine ⟨50361512354920325709062885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33574341569946883806041923 50361512354920325709062885)
              ·
                refine ⟨9442783566547561070449291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50361512354920325709062885 9442783566547561070449291)
                ·
                  refine ⟨14164175349821341605673937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9442783566547561070449291 14164175349821341605673937)
                  ·
                    refine ⟨10623131512366006204255453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14164175349821341605673937 10623131512366006204255453)
                    ·
                      refine ⟨3983674317137252326595795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10623131512366006204255453 3983674317137252326595795)
                      ·
                        rfl

theorem cell23_7758178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_7758178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758178 prefixEnd_7758178 := by exact prefixLift 7758178
  have htrace : WordTrace (prefixWord ++ tailWord_7758178) baseStart_7758178 baseEnd_7758178 := by
    simpa [prefixWord, tailWord_7758178, baseEnd_7758178] using wordTrace_append hprefix tailTrace_7758178
  have hstable : (prefixWord ++ tailWord_7758178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758178).length < 2 ^ (prefixWord ++ tailWord_7758178).sum := by decide
  have hdescent : baseEnd_7758178 < baseStart_7758178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758181 : List Nat := [1, 3, 1, 3, 1, 5, 2, 7]
def baseStart_7758181 : Nat := 118140960795 + 7758181 * 2 ^ 59
def prefixEnd_7758181 : Nat := 4983230072969 + 3 ^ 40 * 7758181 * 2
def baseEnd_7758181 : Nat := 147543550280711696846603

theorem tailTrace_7758181 : CollatzResearch.WordTrace tailWord_7758181 prefixEnd_7758181 147543550280711696846603 := by
  unfold tailWord_7758181
  simp only [CollatzResearch.WordTrace]
  refine ⟨282964107506442703671922397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188642738337628469114614931 282964107506442703671922397)
  ·
    refine ⟨106111540314916013876970899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282964107506442703671922397 106111540314916013876970899)
    ·
      refine ⟨159167310472374020815456349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106111540314916013876970899 159167310472374020815456349)
      ·
        refine ⟨59687741427140257805796131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159167310472374020815456349 59687741427140257805796131)
        ·
          refine ⟨89531612140710386708694197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59687741427140257805796131 89531612140710386708694197)
          ·
            refine ⟨8393588638191598753940081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89531612140710386708694197 8393588638191598753940081)
            ·
              refine ⟨6295191478643699065455061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393588638191598753940081 6295191478643699065455061)
              ·
                refine ⟨147543550280711696846603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6295191478643699065455061 147543550280711696846603)
                ·
                  rfl

theorem cell23_7758181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 7].length) (baseStart_7758181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758181 prefixEnd_7758181 := by exact prefixLift 7758181
  have htrace : WordTrace (prefixWord ++ tailWord_7758181) baseStart_7758181 baseEnd_7758181 := by
    simpa [prefixWord, tailWord_7758181, baseEnd_7758181] using wordTrace_append hprefix tailTrace_7758181
  have hstable : (prefixWord ++ tailWord_7758181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758181).length < 2 ^ (prefixWord ++ tailWord_7758181).sum := by decide
  have hdescent : baseEnd_7758181 < baseStart_7758181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758192 : List Nat := [2, 1, 1, 1, 4, 5, 1, 3, 1, 2, 2]
def baseStart_7758192 : Nat := 118140960795 + 7758192 * 2 ^ 59
def prefixEnd_7758192 : Nat := 4983230072969 + 3 ^ 40 * 7758192 * 2
def baseEnd_7758192 : Nat := 3983681505866415271820731

theorem tailTrace_7758192 : CollatzResearch.WordTrace tailWord_7758192 prefixEnd_7758192 3983681505866415271820731 := by
  unfold tailWord_7758192
  simp only [CollatzResearch.WordTrace]
  refine ⟨141482254354701426275286415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188643005806268568367048553 141482254354701426275286415)
  ·
    refine ⟨212223381532052139412929623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141482254354701426275286415 212223381532052139412929623)
    ·
      refine ⟨318335072298078209119394435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212223381532052139412929623 318335072298078209119394435)
      ·
        refine ⟨477502608447117313679091653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318335072298078209119394435 477502608447117313679091653)
        ·
          refine ⟨89531739083834496314829685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477502608447117313679091653 89531739083834496314829685)
          ·
            refine ⟨8393600539109484029515283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89531739083834496314829685 8393600539109484029515283)
            ·
              refine ⟨12590400808664226044272925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393600539109484029515283 12590400808664226044272925)
              ·
                refine ⟨4721400303249084766602347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12590400808664226044272925 4721400303249084766602347)
                ·
                  refine ⟨7082100454873627149903521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721400303249084766602347 7082100454873627149903521)
                  ·
                    refine ⟨5311575341155220362427641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082100454873627149903521 5311575341155220362427641)
                    ·
                      refine ⟨3983681505866415271820731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311575341155220362427641 3983681505866415271820731)
                      ·
                        rfl

theorem cell23_7758192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 2, 2].length) (baseStart_7758192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758192 prefixEnd_7758192 := by exact prefixLift 7758192
  have htrace : WordTrace (prefixWord ++ tailWord_7758192) baseStart_7758192 baseEnd_7758192 := by
    simpa [prefixWord, tailWord_7758192, baseEnd_7758192] using wordTrace_append hprefix tailTrace_7758192
  have hstable : (prefixWord ++ tailWord_7758192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758192).length < 2 ^ (prefixWord ++ tailWord_7758192).sum := by decide
  have hdescent : baseEnd_7758192 < baseStart_7758192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758198 : List Nat := [5, 1, 1, 4, 1, 2, 9]
def baseStart_7758198 : Nat := 118140960795 + 7758198 * 2 ^ 59
def prefixEnd_7758198 : Nat := 4983230072969 + 3 ^ 40 * 7758198 * 2
def baseEnd_7758198 : Nat := 49181291194448669732663

theorem tailTrace_7758198 : CollatzResearch.WordTrace tailWord_7758198 prefixEnd_7758198 49181291194448669732663 := by
  unfold tailWord_7758198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17685295471711319723455703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188643151698254077050194165 17685295471711319723455703)
  ·
    refine ⟨26527943207566979585183555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17685295471711319723455703 26527943207566979585183555)
    ·
      refine ⟨39791914811350469377775333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26527943207566979585183555 39791914811350469377775333)
      ·
        refine ⟨7460984027128213008332875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39791914811350469377775333 7460984027128213008332875)
        ·
          refine ⟨11191476040692319512499313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460984027128213008332875 11191476040692319512499313)
          ·
            refine ⟨8393607030519239634374485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11191476040692319512499313 8393607030519239634374485)
            ·
              refine ⟨49181291194448669732663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8393607030519239634374485 49181291194448669732663)
              ·
                rfl

theorem cell23_7758198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 9].length) (baseStart_7758198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758198 prefixEnd_7758198 := by exact prefixLift 7758198
  have htrace : WordTrace (prefixWord ++ tailWord_7758198) baseStart_7758198 baseEnd_7758198 := by
    simpa [prefixWord, tailWord_7758198, baseEnd_7758198] using wordTrace_append hprefix tailTrace_7758198
  have hstable : (prefixWord ++ tailWord_7758198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758198).length < 2 ^ (prefixWord ++ tailWord_7758198).sum := by decide
  have hdescent : baseEnd_7758198 < baseStart_7758198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758201 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 5, 3, 2]
def baseStart_7758201 : Nat := 118140960795 + 7758201 * 2 ^ 59
def prefixEnd_7758201 : Nat := 4983230072969 + 3 ^ 40 * 7758201 * 2
def baseEnd_7758201 : Nat := 3983686127192305736608189

theorem tailTrace_7758201 : CollatzResearch.WordTrace tailWord_7758201 prefixEnd_7758201 3983686127192305736608189 := by
  unfold tailWord_7758201
  simp only [CollatzResearch.WordTrace]
  refine ⟨282964836966370247087650457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188643224644246831391766971 282964836966370247087650457)
  ·
    refine ⟨212223627724777685315737843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282964836966370247087650457 212223627724777685315737843)
    ·
      refine ⟨318335441587166527973606765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212223627724777685315737843 318335441587166527973606765)
      ·
        refine ⟨119375790595187447990102537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318335441587166527973606765 119375790595187447990102537)
        ·
          refine ⟨89531842946390585992576903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119375790595187447990102537 89531842946390585992576903)
          ·
            refine ⟨134297764419585878988865355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89531842946390585992576903 134297764419585878988865355)
            ·
              refine ⟨201446646629378818483298033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134297764419585878988865355 201446646629378818483298033)
              ·
                refine ⟨151084984972034113862473525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201446646629378818483298033 151084984972034113862473525)
                ·
                  refine ⟨14164217341128198174606893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151084984972034113862473525 14164217341128198174606893)
                  ·
                    refine ⟨5311581502923074315477585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14164217341128198174606893 5311581502923074315477585)
                    ·
                      refine ⟨3983686127192305736608189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311581502923074315477585 3983686127192305736608189)
                      ·
                        rfl

theorem cell23_7758201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_7758201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758201 prefixEnd_7758201 := by exact prefixLift 7758201
  have htrace : WordTrace (prefixWord ++ tailWord_7758201) baseStart_7758201 baseEnd_7758201 := by
    simpa [prefixWord, tailWord_7758201, baseEnd_7758201] using wordTrace_append hprefix tailTrace_7758201
  have hstable : (prefixWord ++ tailWord_7758201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758201).length < 2 ^ (prefixWord ++ tailWord_7758201).sum := by decide
  have hdescent : baseEnd_7758201 < baseStart_7758201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758209 : List Nat := [1, 2, 4, 3, 1, 2, 3, 2, 1, 2, 2]
def baseStart_7758209 : Nat := 118140960795 + 7758209 * 2 ^ 59
def prefixEnd_7758209 : Nat := 4983230072969 + 3 ^ 40 * 7758209 * 2
def baseEnd_7758209 : Nat := 3983690235037541705308153

theorem tailTrace_7758209 : CollatzResearch.WordTrace tailWord_7758209 prefixEnd_7758209 3983690235037541705308153 := by
  unfold tailWord_7758209
  simp only [CollatzResearch.WordTrace]
  refine ⟨282965128750341264453941681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188643419166894176302627787 282965128750341264453941681)
  ·
    refine ⟨212223846562755948340456261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282965128750341264453941681 212223846562755948340456261)
    ·
      refine ⟨39791971230516740313835549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212223846562755948340456261 39791971230516740313835549)
      ·
        refine ⟨14921989211443777617688331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39791971230516740313835549 14921989211443777617688331)
        ·
          refine ⟨22382983817165666426532497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14921989211443777617688331 22382983817165666426532497)
          ·
            refine ⟨16787237862874249819899373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22382983817165666426532497 16787237862874249819899373)
            ·
              refine ⟨6295214198577843682462265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16787237862874249819899373 6295214198577843682462265)
              ·
                refine ⟨4721410648933382761846699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295214198577843682462265 4721410648933382761846699)
                ·
                  refine ⟨7082115973400074142770049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721410648933382761846699 7082115973400074142770049)
                  ·
                    refine ⟨5311586980050055607077537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082115973400074142770049 5311586980050055607077537)
                    ·
                      refine ⟨3983690235037541705308153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311586980050055607077537 3983690235037541705308153)
                      ·
                        rfl

theorem cell23_7758209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_7758209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758209 prefixEnd_7758209 := by exact prefixLift 7758209
  have htrace : WordTrace (prefixWord ++ tailWord_7758209) baseStart_7758209 baseEnd_7758209 := by
    simpa [prefixWord, tailWord_7758209, baseEnd_7758209] using wordTrace_append hprefix tailTrace_7758209
  have hstable : (prefixWord ++ tailWord_7758209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758209).length < 2 ^ (prefixWord ++ tailWord_7758209).sum := by decide
  have hdescent : baseEnd_7758209 < baseStart_7758209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758260 : List Nat := [2, 5, 2, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_7758260 : Nat := 118140960795 + 7758260 * 2 ^ 59
def prefixEnd_7758260 : Nat := 4983230072969 + 3 ^ 40 * 7758260 * 2
def baseEnd_7758260 : Nat := 3983716422550921005770419

theorem tailTrace_7758260 : CollatzResearch.WordTrace tailWord_7758260 prefixEnd_7758260 3983716422550921005770419 := by
  unfold tailWord_7758260
  simp only [CollatzResearch.WordTrace]
  refine ⟨141483494436578250082024117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188644659248771000109365489 141483494436578250082024117)
  ·
    refine ⟨13264077603429210945189761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141483494436578250082024117 13264077603429210945189761)
    ·
      refine ⟨9948058202571908208892321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13264077603429210945189761 9948058202571908208892321)
      ·
        refine ⟨7461043651928931156669241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9948058202571908208892321 7461043651928931156669241)
        ·
          refine ⟨5595782738946698367501931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7461043651928931156669241 5595782738946698367501931)
          ·
            refine ⟨8393674108420047551252897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5595782738946698367501931 8393674108420047551252897)
            ·
              refine ⟨6295255581315035663439673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8393674108420047551252897 6295255581315035663439673)
              ·
                refine ⟨4721441685986276747579755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6295255581315035663439673 4721441685986276747579755)
                ·
                  refine ⟨7082162528979415121369633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4721441685986276747579755 7082162528979415121369633)
                  ·
                    refine ⟨5311621896734561341027225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082162528979415121369633 5311621896734561341027225)
                    ·
                      refine ⟨3983716422550921005770419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311621896734561341027225 3983716422550921005770419)
                      ·
                        rfl

theorem cell23_7758260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_7758260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758260 prefixEnd_7758260 := by exact prefixLift 7758260
  have htrace : WordTrace (prefixWord ++ tailWord_7758260) baseStart_7758260 baseEnd_7758260 := by
    simpa [prefixWord, tailWord_7758260, baseEnd_7758260] using wordTrace_append hprefix tailTrace_7758260
  have hstable : (prefixWord ++ tailWord_7758260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758260).length < 2 ^ (prefixWord ++ tailWord_7758260).sum := by decide
  have hdescent : baseEnd_7758260 < baseStart_7758260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758265 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 2, 2, 2]
def baseStart_7758265 : Nat := 118140960795 + 7758265 * 2 ^ 59
def prefixEnd_7758265 : Nat := 4983230072969 + 3 ^ 40 * 7758265 * 2
def baseEnd_7758265 : Nat := 3983718989954193486207895

theorem tailTrace_7758265 : CollatzResearch.WordTrace tailWord_7758265 prefixEnd_7758265 3983718989954193486207895 := by
  unfold tailWord_7758265
  simp only [CollatzResearch.WordTrace]
  refine ⟨282967171238138386017980249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188644780825425590678653499 282967171238138386017980249)
  ·
    refine ⟨212225378428603789513485187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282967171238138386017980249 212225378428603789513485187)
    ·
      refine ⟨318338067642905684270227781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212225378428603789513485187 318338067642905684270227781)
      ·
        refine ⟨59688387683044815800667709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318338067642905684270227781 59688387683044815800667709)
        ·
          refine ⟨22383145381141805925250391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59688387683044815800667709 22383145381141805925250391)
          ·
            refine ⟨33574718071712708887875587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22383145381141805925250391 33574718071712708887875587)
            ·
              refine ⟨50362077107569063331813381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33574718071712708887875587 50362077107569063331813381)
              ·
                refine ⟨9442889457669199374715009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50362077107569063331813381 9442889457669199374715009)
                ·
                  refine ⟨7082167093251899531036257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9442889457669199374715009 7082167093251899531036257)
                  ·
                    refine ⟨5311625319938924648277193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082167093251899531036257 5311625319938924648277193)
                    ·
                      refine ⟨3983718989954193486207895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311625319938924648277193 3983718989954193486207895)
                      ·
                        rfl

theorem cell23_7758265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_7758265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758265 prefixEnd_7758265 := by exact prefixLift 7758265
  have htrace : WordTrace (prefixWord ++ tailWord_7758265) baseStart_7758265 baseEnd_7758265 := by
    simpa [prefixWord, tailWord_7758265, baseEnd_7758265] using wordTrace_append hprefix tailTrace_7758265
  have hstable : (prefixWord ++ tailWord_7758265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758265).length < 2 ^ (prefixWord ++ tailWord_7758265).sum := by decide
  have hdescent : baseEnd_7758265 < baseStart_7758265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758301 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7758301 : Nat := 118140960795 + 7758301 * 2 ^ 59
def prefixEnd_7758301 : Nat := 4983230072969 + 3 ^ 40 * 7758301 * 2
def baseEnd_7758301 : Nat := 1327912491752585115119243

theorem tailTrace_7758301 : CollatzResearch.WordTrace tailWord_7758301 prefixEnd_7758301 1327912491752585115119243 := by
  unfold tailWord_7758301
  simp only [CollatzResearch.WordTrace]
  refine ⟨282968484266007964166290757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188645656177338642777527171 282968484266007964166290757)
  ·
    refine ⟨53056590799876493281179517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282968484266007964166290757 53056590799876493281179517)
    ·
      refine ⟨19896221549953684980442319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53056590799876493281179517 19896221549953684980442319)
      ·
        refine ⟨29844332324930527470663479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896221549953684980442319 29844332324930527470663479)
        ·
          refine ⟨44766498487395791205995219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29844332324930527470663479 44766498487395791205995219)
          ·
            refine ⟨67149747731093686808992829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44766498487395791205995219 67149747731093686808992829)
            ·
              refine ⟨25181155399160132553372311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67149747731093686808992829 25181155399160132553372311)
              ·
                refine ⟨37771733098740198830058467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25181155399160132553372311 37771733098740198830058467)
                ·
                  refine ⟨56657599648110298245087701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37771733098740198830058467 56657599648110298245087701)
                  ·
                    refine ⟨1327912491752585115119243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56657599648110298245087701 1327912491752585115119243)
                    ·
                      rfl

theorem cell23_7758301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7758301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758301 prefixEnd_7758301 := by exact prefixLift 7758301
  have htrace : WordTrace (prefixWord ++ tailWord_7758301) baseStart_7758301 baseEnd_7758301 := by
    simpa [prefixWord, tailWord_7758301, baseEnd_7758301] using wordTrace_append hprefix tailTrace_7758301
  have hstable : (prefixWord ++ tailWord_7758301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758301).length < 2 ^ (prefixWord ++ tailWord_7758301).sum := by decide
  have hdescent : baseEnd_7758301 < baseStart_7758301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758321 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_7758321 : Nat := 118140960795 + 7758321 * 2 ^ 59
def prefixEnd_7758321 : Nat := 4983230072969 + 3 ^ 40 * 7758321 * 2
def baseEnd_7758321 : Nat := 3983747744870845267107637

theorem tailTrace_7758321 : CollatzResearch.WordTrace tailWord_7758321 prefixEnd_7758321 3983747744870845267107637 := by
  unfold tailWord_7758321
  simp only [CollatzResearch.WordTrace]
  refine ⟨282969213725935507582018817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188646142483957005054679211 282969213725935507582018817)
  ·
    refine ⟨212226910294451630686514113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282969213725935507582018817 212226910294451630686514113)
    ·
      refine ⟨159170182720838723014885585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212226910294451630686514113 159170182720838723014885585)
      ·
        refine ⟨119377637040629042261164189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159170182720838723014885585 119377637040629042261164189)
        ·
          refine ⟨44766613890235890847936571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119377637040629042261164189 44766613890235890847936571)
          ·
            refine ⟨67149920835353836271904857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44766613890235890847936571 67149920835353836271904857)
            ·
              refine ⟨50362440626515377203928643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67149920835353836271904857 50362440626515377203928643)
              ·
                refine ⟨75543660939773065805892965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50362440626515377203928643 75543660939773065805892965)
                ·
                  refine ⟨14164436426207449838604931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75543660939773065805892965 14164436426207449838604931)
                  ·
                    refine ⟨21246654639311174757907397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14164436426207449838604931 21246654639311174757907397)
                    ·
                      refine ⟨3983747744870845267107637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21246654639311174757907397 3983747744870845267107637)
                      ·
                        rfl

theorem cell23_7758321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_7758321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758321 prefixEnd_7758321 := by exact prefixLift 7758321
  have htrace : WordTrace (prefixWord ++ tailWord_7758321) baseStart_7758321 baseEnd_7758321 := by
    simpa [prefixWord, tailWord_7758321, baseEnd_7758321] using wordTrace_append hprefix tailTrace_7758321
  have hstable : (prefixWord ++ tailWord_7758321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758321).length < 2 ^ (prefixWord ++ tailWord_7758321).sum := by decide
  have hdescent : baseEnd_7758321 < baseStart_7758321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758341 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_7758341 : Nat := 118140960795 + 7758341 * 2 ^ 59
def prefixEnd_7758341 : Nat := 4983230072969 + 3 ^ 40 * 7758341 * 2
def baseEnd_7758341 : Nat := 3983758014483935188857545

theorem tailTrace_7758341 : CollatzResearch.WordTrace tailWord_7758341 prefixEnd_7758341 3983758014483935188857545 := by
  unfold tailWord_7758341
  simp only [CollatzResearch.WordTrace]
  refine ⟨282969943185863050997746877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188646628790575367331831251 282969943185863050997746877)
  ·
    refine ⟨106113728694698644124155079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282969943185863050997746877 106113728694698644124155079)
    ·
      refine ⟨159170593042047966186232619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106113728694698644124155079 159170593042047966186232619)
      ·
        refine ⟨238755889563071949279348929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159170593042047966186232619 238755889563071949279348929)
        ·
          refine ⟨179066917172303961959511697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238755889563071949279348929 179066917172303961959511697)
          ·
            refine ⟨134300187879227971469633773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179066917172303961959511697 134300187879227971469633773)
            ·
              refine ⟨50362570454710489301112665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134300187879227971469633773 50362570454710489301112665)
              ·
                refine ⟨37771927841032866975834499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50362570454710489301112665 37771927841032866975834499)
                ·
                  refine ⟨56657891761549300463751749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37771927841032866975834499 56657891761549300463751749)
                  ·
                    refine ⟨10623354705290493836953453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56657891761549300463751749 10623354705290493836953453)
                    ·
                      refine ⟨3983758014483935188857545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10623354705290493836953453 3983758014483935188857545)
                      ·
                        rfl

theorem cell23_7758341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_7758341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758341 prefixEnd_7758341 := by exact prefixLift 7758341
  have htrace : WordTrace (prefixWord ++ tailWord_7758341) baseStart_7758341 baseEnd_7758341 := by
    simpa [prefixWord, tailWord_7758341, baseEnd_7758341] using wordTrace_append hprefix tailTrace_7758341
  have hstable : (prefixWord ++ tailWord_7758341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758341).length < 2 ^ (prefixWord ++ tailWord_7758341).sum := by decide
  have hdescent : baseEnd_7758341 < baseStart_7758341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758348 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_7758348 : Nat := 118140960795 + 7758348 * 2 ^ 59
def prefixEnd_7758348 : Nat := 4983230072969 + 3 ^ 40 * 7758348 * 2
def baseEnd_7758348 : Nat := 1327920536282838887156671

theorem tailTrace_7758348 : CollatzResearch.WordTrace tailWord_7758348 prefixEnd_7758348 1327920536282838887156671 := by
  unfold tailWord_7758348
  simp only [CollatzResearch.WordTrace]
  refine ⟨141485099248418845596625849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188646798997891794128834465 141485099248418845596625849)
  ·
    refine ⟨106113824436314134197469387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141485099248418845596625849 106113824436314134197469387)
    ·
      refine ⟨159170736654471201296204081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106113824436314134197469387 159170736654471201296204081)
      ·
        refine ⟨119378052490853400972153061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159170736654471201296204081 119378052490853400972153061)
        ·
          refine ⟨22383384842035012682278699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119378052490853400972153061 22383384842035012682278699)
          ·
            refine ⟨33575077263052519023418049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22383384842035012682278699 33575077263052519023418049)
            ·
              refine ⟨25181307947289389267563537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33575077263052519023418049 25181307947289389267563537)
              ·
                refine ⟨18885980960467041950672653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25181307947289389267563537 18885980960467041950672653)
                ·
                  refine ⟨7082242860175140731502245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18885980960467041950672653 7082242860175140731502245)
                  ·
                    refine ⟨1327920536282838887156671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082242860175140731502245 1327920536282838887156671)
                    ·
                      rfl

theorem cell23_7758348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_7758348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758348 prefixEnd_7758348 := by exact prefixLift 7758348
  have htrace : WordTrace (prefixWord ++ tailWord_7758348) baseStart_7758348 baseEnd_7758348 := by
    simpa [prefixWord, tailWord_7758348, baseEnd_7758348] using wordTrace_append hprefix tailTrace_7758348
  have hstable : (prefixWord ++ tailWord_7758348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758348).length < 2 ^ (prefixWord ++ tailWord_7758348).sum := by decide
  have hdescent : baseEnd_7758348 < baseStart_7758348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758382 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7758382 : Nat := 118140960795 + 7758382 * 2 ^ 59
def prefixEnd_7758382 : Nat := 4983230072969 + 3 ^ 40 * 7758382 * 2
def baseEnd_7758382 : Nat := 1327926355730256509481619

theorem tailTrace_7758382 : CollatzResearch.WordTrace tailWord_7758382 prefixEnd_7758382 1327926355730256509481619 := by
  unfold tailWord_7758382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35371429822339314374998675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188647625719143009999992933 35371429822339314374998675)
  ·
    refine ⟨53057144733508971562498013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35371429822339314374998675 53057144733508971562498013)
    ·
      refine ⟨19896429275065864335936755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53057144733508971562498013 19896429275065864335936755)
      ·
        refine ⟨29844643912598796503905133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896429275065864335936755 29844643912598796503905133)
        ·
          refine ⟨11191741467224548688964425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29844643912598796503905133 11191741467224548688964425)
          ·
            refine ⟨8393806100418411516723319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11191741467224548688964425 8393806100418411516723319)
            ·
              refine ⟨12590709150627617275084979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8393806100418411516723319 12590709150627617275084979)
              ·
                refine ⟨18886063725941425912627469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12590709150627617275084979 18886063725941425912627469)
                ·
                  refine ⟨7082273897228034717235301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18886063725941425912627469 7082273897228034717235301)
                  ·
                    refine ⟨1327926355730256509481619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082273897228034717235301 1327926355730256509481619)
                    ·
                      rfl

theorem cell23_7758382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7758382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758382 prefixEnd_7758382 := by exact prefixLift 7758382
  have htrace : WordTrace (prefixWord ++ tailWord_7758382) baseStart_7758382 baseEnd_7758382 := by
    simpa [prefixWord, tailWord_7758382, baseEnd_7758382] using wordTrace_append hprefix tailTrace_7758382
  have hstable : (prefixWord ++ tailWord_7758382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758382).length < 2 ^ (prefixWord ++ tailWord_7758382).sum := by decide
  have hdescent : baseEnd_7758382 < baseStart_7758382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758391 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 3, 5]
def baseStart_7758391 : Nat := 118140960795 + 7758391 * 2 ^ 59
def prefixEnd_7758391 : Nat := 4983230072969 + 3 ^ 40 * 7758391 * 2
def baseEnd_7758391 : Nat := 1327927896172219997744105

theorem tailTrace_7758391 : CollatzResearch.WordTrace tailWord_7758391 prefixEnd_7758391 1327927896172219997744105 := by
  unfold tailWord_7758391
  simp only [CollatzResearch.WordTrace]
  refine ⟨282971766835681909537067027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188647844557121273024711351 282971766835681909537067027)
  ·
    refine ⟨424457650253522864305600541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282971766835681909537067027 424457650253522864305600541)
    ·
      refine ⟨159171618845071074114600203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424457650253522864305600541 159171618845071074114600203)
      ·
        refine ⟨238757428267606611171900305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159171618845071074114600203 238757428267606611171900305)
        ·
          refine ⟨179068071200704958378925229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238757428267606611171900305 179068071200704958378925229)
          ·
            refine ⟨67150526700264359392096961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179068071200704958378925229 67150526700264359392096961)
            ·
              refine ⟨50362895025198269544072721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67150526700264359392096961 50362895025198269544072721)
              ·
                refine ⟨37772171268898702158054541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50362895025198269544072721 37772171268898702158054541)
                ·
                  refine ⟨14164564225837013309270453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37772171268898702158054541 14164564225837013309270453)
                  ·
                    refine ⟨1327927896172219997744105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14164564225837013309270453 1327927896172219997744105)
                    ·
                      rfl

theorem cell23_7758391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_7758391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758391 prefixEnd_7758391 := by exact prefixLift 7758391
  have htrace : WordTrace (prefixWord ++ tailWord_7758391) baseStart_7758391 baseEnd_7758391 := by
    simpa [prefixWord, tailWord_7758391, baseEnd_7758391] using wordTrace_append hprefix tailTrace_7758391
  have hstable : (prefixWord ++ tailWord_7758391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758391).length < 2 ^ (prefixWord ++ tailWord_7758391).sum := by decide
  have hdescent : baseEnd_7758391 < baseStart_7758391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758421 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_7758421 : Nat := 118140960795 + 7758421 * 2 ^ 59
def prefixEnd_7758421 : Nat := 4983230072969 + 3 ^ 40 * 7758421 * 2
def baseEnd_7758421 : Nat := 1327933030978764958619059

theorem tailTrace_7758421 : CollatzResearch.WordTrace tailWord_7758421 prefixEnd_7758421 1327933030978764958619059 := by
  unfold tailWord_7758421
  simp only [CollatzResearch.WordTrace]
  refine ⟨282972861025573224660659117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188648574017048816440439411 282972861025573224660659117)
  ·
    refine ⟨106114822884589959247747169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282972861025573224660659117 106114822884589959247747169)
    ·
      refine ⟨79586117163442469435810377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106114822884589959247747169 79586117163442469435810377)
      ·
        refine ⟨59689587872581852076857783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79586117163442469435810377 59689587872581852076857783)
        ·
          refine ⟨89534381808872778115286675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59689587872581852076857783 89534381808872778115286675)
          ·
            refine ⟨134301572713309167172930013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89534381808872778115286675 134301572713309167172930013)
            ·
              refine ⟨50363089767490937689848755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134301572713309167172930013 50363089767490937689848755)
              ·
                refine ⟨75544634651236406534773133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50363089767490937689848755 75544634651236406534773133)
                ·
                  refine ⟨28329237994213652450539925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75544634651236406534773133 28329237994213652450539925)
                  ·
                    refine ⟨1327933030978764958619059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28329237994213652450539925 1327933030978764958619059)
                    ·
                      rfl

theorem cell23_7758421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_7758421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758421 prefixEnd_7758421 := by exact prefixLift 7758421
  have htrace : WordTrace (prefixWord ++ tailWord_7758421) baseStart_7758421 baseEnd_7758421 := by
    simpa [prefixWord, tailWord_7758421, baseEnd_7758421] using wordTrace_append hprefix tailTrace_7758421
  have hstable : (prefixWord ++ tailWord_7758421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758421).length < 2 ^ (prefixWord ++ tailWord_7758421).sum := by decide
  have hdescent : baseEnd_7758421 < baseStart_7758421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758441 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_7758441 : Nat := 118140960795 + 7758441 * 2 ^ 59
def prefixEnd_7758441 : Nat := 4983230072969 + 3 ^ 40 * 7758441 * 2
def baseEnd_7758441 : Nat := 3983809362549384797607085

theorem tailTrace_7758441 : CollatzResearch.WordTrace tailWord_7758441 prefixEnd_7758441 3983809362549384797607085 := by
  unfold tailWord_7758441
  simp only [CollatzResearch.WordTrace]
  refine ⟨282973590485500768076387177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188649060323667178717591451 282973590485500768076387177)
  ·
    refine ⟨212230192864125576057290383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282973590485500768076387177 212230192864125576057290383)
    ·
      refine ⟨318345289296188364085935575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212230192864125576057290383 318345289296188364085935575)
      ·
        refine ⟨477517933944282546128903363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318345289296188364085935575 477517933944282546128903363)
        ·
          refine ⟨716276900916423819193355045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477517933944282546128903363 716276900916423819193355045)
          ·
            refine ⟨134301918921829466098754071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 716276900916423819193355045 134301918921829466098754071)
            ·
              refine ⟨201452878382744199148131107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134301918921829466098754071 201452878382744199148131107)
              ·
                refine ⟨302179317574116298722196661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201452878382744199148131107 302179317574116298722196661)
                ·
                  refine ⟨28329311022573403005205937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302179317574116298722196661 28329311022573403005205937)
                  ·
                    refine ⟨21246983266930052253904453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28329311022573403005205937 21246983266930052253904453)
                    ·
                      refine ⟨3983809362549384797607085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21246983266930052253904453 3983809362549384797607085)
                      ·
                        rfl

theorem cell23_7758441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_7758441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758441 prefixEnd_7758441 := by exact prefixLift 7758441
  have htrace : WordTrace (prefixWord ++ tailWord_7758441) baseStart_7758441 baseEnd_7758441 := by
    simpa [prefixWord, tailWord_7758441, baseEnd_7758441] using wordTrace_append hprefix tailTrace_7758441
  have hstable : (prefixWord ++ tailWord_7758441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758441).length < 2 ^ (prefixWord ++ tailWord_7758441).sum := by decide
  have hdescent : baseEnd_7758441 < baseStart_7758441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758465 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_7758465 : Nat := 118140960795 + 7758465 * 2 ^ 59
def prefixEnd_7758465 : Nat := 4983230072969 + 3 ^ 40 * 7758465 * 2
def baseEnd_7758465 : Nat := 3983821686085092703706975

theorem tailTrace_7758465 : CollatzResearch.WordTrace tailWord_7758465 prefixEnd_7758465 3983821686085092703706975 := by
  unfold tailWord_7758465
  simp only [CollatzResearch.WordTrace]
  refine ⟨282974465837413820175260849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188649643891609213450173899 282974465837413820175260849)
  ·
    refine ⟨212230849378060365131445637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282974465837413820175260849 212230849378060365131445637)
    ·
      refine ⟨39793284258386318462146057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212230849378060365131445637 39793284258386318462146057)
      ·
        refine ⟨29844963193789738846609543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39793284258386318462146057 29844963193789738846609543)
        ·
          refine ⟨44767444790684608269914315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29844963193789738846609543 44767444790684608269914315)
          ·
            refine ⟨67151167186026912404871473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44767444790684608269914315 67151167186026912404871473)
            ·
              refine ⟨50363375389520184303653605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67151167186026912404871473 50363375389520184303653605)
              ·
                refine ⟨9443132885535034556935051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50363375389520184303653605 9443132885535034556935051)
                ·
                  refine ⟨14164699328302551835402577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9443132885535034556935051 14164699328302551835402577)
                  ·
                    refine ⟨10623524496226913876551933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14164699328302551835402577 10623524496226913876551933)
                    ·
                      refine ⟨3983821686085092703706975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10623524496226913876551933 3983821686085092703706975)
                      ·
                        rfl

theorem cell23_7758465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_7758465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758465 prefixEnd_7758465 := by exact prefixLift 7758465
  have htrace : WordTrace (prefixWord ++ tailWord_7758465) baseStart_7758465 baseEnd_7758465 := by
    simpa [prefixWord, tailWord_7758465, baseEnd_7758465] using wordTrace_append hprefix tailTrace_7758465
  have hstable : (prefixWord ++ tailWord_7758465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758465).length < 2 ^ (prefixWord ++ tailWord_7758465).sum := by decide
  have hdescent : baseEnd_7758465 < baseStart_7758465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758466 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_7758466 : Nat := 118140960795 + 7758466 * 2 ^ 59
def prefixEnd_7758466 : Nat := 4983230072969 + 3 ^ 40 * 7758466 * 2
def baseEnd_7758466 : Nat := 3983822199565747199794471

theorem tailTrace_7758466 : CollatzResearch.WordTrace tailWord_7758466 prefixEnd_7758466 3983822199565747199794471 := by
  unfold tailWord_7758466
  simp only [CollatzResearch.WordTrace]
  refine ⟨70743625577602549336511813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188649668206940131564031501 70743625577602549336511813)
  ·
    refine ⟨13264429795800478000595965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70743625577602549336511813 13264429795800478000595965)
    ·
      refine ⟨4974161173425179250223487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13264429795800478000595965 4974161173425179250223487)
      ·
        refine ⟨7461241760137768875335231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974161173425179250223487 7461241760137768875335231)
        ·
          refine ⟨11191862640206653313002847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461241760137768875335231 11191862640206653313002847)
          ·
            refine ⟨16787793960309979969504271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191862640206653313002847 16787793960309979969504271)
            ·
              refine ⟨25181690940464969954256407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16787793960309979969504271 25181690940464969954256407)
              ·
                refine ⟨37772536410697454931384611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25181690940464969954256407 37772536410697454931384611)
                ·
                  refine ⟨56658804616046182397076917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37772536410697454931384611 56658804616046182397076917)
                  ·
                    refine ⟨5311762932754329599725961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56658804616046182397076917 5311762932754329599725961)
                    ·
                      refine ⟨3983822199565747199794471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311762932754329599725961 3983822199565747199794471)
                      ·
                        rfl

theorem cell23_7758466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_7758466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758466 prefixEnd_7758466 := by exact prefixLift 7758466
  have htrace : WordTrace (prefixWord ++ tailWord_7758466) baseStart_7758466 baseEnd_7758466 := by
    simpa [prefixWord, tailWord_7758466, baseEnd_7758466] using wordTrace_append hprefix tailTrace_7758466
  have hstable : (prefixWord ++ tailWord_7758466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758466).length < 2 ^ (prefixWord ++ tailWord_7758466).sum := by decide
  have hdescent : baseEnd_7758466 < baseStart_7758466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758482 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7758482 : Nat := 118140960795 + 7758482 * 2 ^ 59
def prefixEnd_7758482 : Nat := 4983230072969 + 3 ^ 40 * 7758482 * 2
def baseEnd_7758482 : Nat := 3983830415256219137194397

theorem tailTrace_7758482 : CollatzResearch.WordTrace tailWord_7758482 prefixEnd_7758482 3983830415256219137194397 := by
  unfold tailWord_7758482
  simp only [CollatzResearch.WordTrace]
  refine ⟨70743771469588058019657425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188650057252234821385753133 70743771469588058019657425)
  ·
    refine ⟨53057828602191043514743069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70743771469588058019657425 53057828602191043514743069)
    ·
      refine ⟨19896685725821641318028651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53057828602191043514743069 19896685725821641318028651)
      ·
        refine ⟨29845028588732461977042977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19896685725821641318028651 29845028588732461977042977)
        ·
          refine ⟨22383771441549346482782233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29845028588732461977042977 22383771441549346482782233)
          ·
            refine ⟨16787828581162009862086675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22383771441549346482782233 16787828581162009862086675)
            ·
              refine ⟨25181742871743014793130013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16787828581162009862086675 25181742871743014793130013)
              ·
                refine ⟨9443153576903630547423755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25181742871743014793130013 9443153576903630547423755)
                ·
                  refine ⟨14164730365355445821135633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9443153576903630547423755 14164730365355445821135633)
                  ·
                    refine ⟨10623547774016584365851725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14164730365355445821135633 10623547774016584365851725)
                    ·
                      refine ⟨3983830415256219137194397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10623547774016584365851725 3983830415256219137194397)
                      ·
                        rfl

theorem cell23_7758482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7758482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758482 prefixEnd_7758482 := by exact prefixLift 7758482
  have htrace : WordTrace (prefixWord ++ tailWord_7758482) baseStart_7758482 baseEnd_7758482 := by
    simpa [prefixWord, tailWord_7758482, baseEnd_7758482] using wordTrace_append hprefix tailTrace_7758482
  have hstable : (prefixWord ++ tailWord_7758482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758482).length < 2 ^ (prefixWord ++ tailWord_7758482).sum := by decide
  have hdescent : baseEnd_7758482 < baseStart_7758482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758506 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7758506 : Nat := 118140960795 + 7758506 * 2 ^ 59
def prefixEnd_7758506 : Nat := 4983230072969 + 3 ^ 40 * 7758506 * 2
def baseEnd_7758506 : Nat := 1327947579597309014431429

theorem tailTrace_7758506 : CollatzResearch.WordTrace tailWord_7758506 prefixEnd_7758506 1327947579597309014431429 := by
  unfold tailWord_7758506
  simp only [CollatzResearch.WordTrace]
  refine ⟨70743990307566321044375843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188650640820176856118335581 70743990307566321044375843)
  ·
    refine ⟨106115985461349481566563765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70743990307566321044375843 106115985461349481566563765)
    ·
      refine ⟨9948373637001513896865353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106115985461349481566563765 9948373637001513896865353)
      ·
        refine ⟨7461280227751135422649015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9948373637001513896865353 7461280227751135422649015)
        ·
          refine ⟨11191920341626703133973523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461280227751135422649015 11191920341626703133973523)
          ·
            refine ⟨16787880512440054700960285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11191920341626703133973523 16787880512440054700960285)
            ·
              refine ⟨6295455192165020512860107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16787880512440054700960285 6295455192165020512860107)
              ·
                refine ⟨9443182788247530769290161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295455192165020512860107 9443182788247530769290161)
                ·
                  refine ⟨7082387091185648076967621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9443182788247530769290161 7082387091185648076967621)
                  ·
                    refine ⟨1327947579597309014431429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7082387091185648076967621 1327947579597309014431429)
                    ·
                      rfl

theorem cell23_7758506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7758506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758506 prefixEnd_7758506 := by exact prefixLift 7758506
  have htrace : WordTrace (prefixWord ++ tailWord_7758506) baseStart_7758506 baseEnd_7758506 := by
    simpa [prefixWord, tailWord_7758506, baseEnd_7758506] using wordTrace_append hprefix tailTrace_7758506
  have hstable : (prefixWord ++ tailWord_7758506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758506).length < 2 ^ (prefixWord ++ tailWord_7758506).sum := by decide
  have hdescent : baseEnd_7758506 < baseStart_7758506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758522 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2]
def baseStart_7758522 : Nat := 118140960795 + 7758522 * 2 ^ 59
def prefixEnd_7758522 : Nat := 4983230072969 + 3 ^ 40 * 7758522 * 2
def baseEnd_7758522 : Nat := 3983850954482398980694213

theorem tailTrace_7758522 : CollatzResearch.WordTrace tailWord_7758522 prefixEnd_7758522 3983850954482398980694213 := by
  unfold tailWord_7758522
  simp only [CollatzResearch.WordTrace]
  refine ⟨70744136199551829727521455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188651029865471545940057213 70744136199551829727521455)
  ·
    refine ⟨106116204299327744591282183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70744136199551829727521455 106116204299327744591282183)
    ·
      refine ⟨159174306448991616886923275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106116204299327744591282183 159174306448991616886923275)
      ·
        refine ⟨238761459673487425330384913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159174306448991616886923275 238761459673487425330384913)
        ·
          refine ⟨179071094755115568997788685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238761459673487425330384913 179071094755115568997788685)
          ·
            refine ⟨67151660533168338374170757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179071094755115568997788685 67151660533168338374170757)
            ·
              refine ⟨12590936349969063445157017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67151660533168338374170757 12590936349969063445157017)
              ·
                refine ⟨9443202262476797583867763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12590936349969063445157017 9443202262476797583867763)
                ·
                  refine ⟨14164803393715196375801645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9443202262476797583867763 14164803393715196375801645)
                  ·
                    refine ⟨5311801272643198640925617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14164803393715196375801645 5311801272643198640925617)
                    ·
                      refine ⟨3983850954482398980694213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311801272643198640925617 3983850954482398980694213)
                      ·
                        rfl

theorem cell23_7758522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_7758522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758522 prefixEnd_7758522 := by exact prefixLift 7758522
  have htrace : WordTrace (prefixWord ++ tailWord_7758522) baseStart_7758522 baseEnd_7758522 := by
    simpa [prefixWord, tailWord_7758522, baseEnd_7758522] using wordTrace_append hprefix tailTrace_7758522
  have hstable : (prefixWord ++ tailWord_7758522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758522).length < 2 ^ (prefixWord ++ tailWord_7758522).sum := by decide
  have hdescent : baseEnd_7758522 < baseStart_7758522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758538 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_7758538 : Nat := 118140960795 + 7758538 * 2 ^ 59
def prefixEnd_7758538 : Nat := 4983230072969 + 3 ^ 40 * 7758538 * 2
def baseEnd_7758538 : Nat := 3983859170172870918094139

theorem tailTrace_7758538 : CollatzResearch.WordTrace tailWord_7758538 prefixEnd_7758538 3983859170172870918094139 := by
  unfold tailWord_7758538
  simp only [CollatzResearch.WordTrace]
  refine ⟨70744282091537338410667067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188651418910766235761778845 70744282091537338410667067)
  ·
    refine ⟨106116423137306007616000601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70744282091537338410667067 106116423137306007616000601)
    ·
      refine ⟨79587317352979505712000451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106116423137306007616000601 79587317352979505712000451)
      ·
        refine ⟨119380976029469258568000677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79587317352979505712000451 119380976029469258568000677)
        ·
          refine ⟨22383933005525485981500127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119380976029469258568000677 22383933005525485981500127)
          ·
            refine ⟨33575899508288228972250191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22383933005525485981500127 33575899508288228972250191)
            ·
              refine ⟨50363849262432343458375287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33575899508288228972250191 50363849262432343458375287)
              ·
                refine ⟨75545773893648515187562931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50363849262432343458375287 75545773893648515187562931)
                ·
                  refine ⟨113318660840472772781344397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75545773893648515187562931 113318660840472772781344397)
                  ·
                    refine ⟨42494497815177289793004149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113318660840472772781344397 42494497815177289793004149)
                    ·
                      refine ⟨3983859170172870918094139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42494497815177289793004149 3983859170172870918094139)
                      ·
                        rfl

theorem cell23_7758538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_7758538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758538 prefixEnd_7758538 := by exact prefixLift 7758538
  have htrace : WordTrace (prefixWord ++ tailWord_7758538) baseStart_7758538 baseEnd_7758538 := by
    simpa [prefixWord, tailWord_7758538, baseEnd_7758538] using wordTrace_append hprefix tailTrace_7758538
  have hstable : (prefixWord ++ tailWord_7758538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758538).length < 2 ^ (prefixWord ++ tailWord_7758538).sum := by decide
  have hdescent : baseEnd_7758538 < baseStart_7758538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758552 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 4, 2, 2]
def baseStart_7758552 : Nat := 118140960795 + 7758552 * 2 ^ 59
def prefixEnd_7758552 : Nat := 4983230072969 + 3 ^ 40 * 7758552 * 2
def baseEnd_7758552 : Nat := 3983866358902033863319075

theorem tailTrace_7758552 : CollatzResearch.WordTrace tailWord_7758552 prefixEnd_7758552 3983866358902033863319075 := by
  unfold tailWord_7758552
  simp only [CollatzResearch.WordTrace]
  refine ⟨141488819494049317016838955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188651759325399089355785273 141488819494049317016838955)
  ·
    refine ⟨212233229241073975525258433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141488819494049317016838955 212233229241073975525258433)
    ·
      refine ⟨159174921930805481643943825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212233229241073975525258433 159174921930805481643943825)
      ·
        refine ⟨119381191448104111232957869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159174921930805481643943825 119381191448104111232957869)
        ·
          refine ⟨44767946793039041712359201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119381191448104111232957869 44767946793039041712359201)
          ·
            refine ⟨33575960094779281284269401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44767946793039041712359201 33575960094779281284269401)
            ·
              refine ⟨25181970071084460963202051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33575960094779281284269401 25181970071084460963202051)
              ·
                refine ⟨37772955106626691444803077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25181970071084460963202051 37772955106626691444803077)
                ·
                  refine ⟨7082429082492504645900577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37772955106626691444803077 7082429082492504645900577)
                  ·
                    refine ⟨5311821811869378484425433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082429082492504645900577 5311821811869378484425433)
                    ·
                      refine ⟨3983866358902033863319075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311821811869378484425433 3983866358902033863319075)
                      ·
                        rfl

theorem cell23_7758552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 2, 2].length) (baseStart_7758552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758552 prefixEnd_7758552 := by exact prefixLift 7758552
  have htrace : WordTrace (prefixWord ++ tailWord_7758552) baseStart_7758552 baseEnd_7758552 := by
    simpa [prefixWord, tailWord_7758552, baseEnd_7758552] using wordTrace_append hprefix tailTrace_7758552
  have hstable : (prefixWord ++ tailWord_7758552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758552).length < 2 ^ (prefixWord ++ tailWord_7758552).sum := by decide
  have hdescent : baseEnd_7758552 < baseStart_7758552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758569 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 2, 2, 2]
def baseStart_7758569 : Nat := 118140960795 + 7758569 * 2 ^ 59
def prefixEnd_7758569 : Nat := 4983230072969 + 3 ^ 40 * 7758569 * 2
def baseEnd_7758569 : Nat := 3983875088073160296806497

theorem tailTrace_7758569 : CollatzResearch.WordTrace tailWord_7758569 prefixEnd_7758569 3983875088073160296806497 := by
  unfold tailWord_7758569
  simp only [CollatzResearch.WordTrace]
  refine ⟨282978259029037045937046761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188652172686024697291364507 282978259029037045937046761)
  ·
    refine ⟨212233694271777784452785071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282978259029037045937046761 212233694271777784452785071)
    ·
      refine ⟨318350541407666676679177607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212233694271777784452785071 318350541407666676679177607)
      ·
        refine ⟨477525812111500015018766411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318350541407666676679177607 477525812111500015018766411)
        ·
          refine ⟨716288718167250022528149617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477525812111500015018766411 716288718167250022528149617)
          ·
            refine ⟨537216538625437516896112213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716288718167250022528149617 537216538625437516896112213)
            ·
              refine ⟨6295506312016845901126315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 537216538625437516896112213 6295506312016845901126315)
              ·
                refine ⟨9443259468025268851689473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295506312016845901126315 9443259468025268851689473)
                ·
                  refine ⟨7082444601018951638767105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9443259468025268851689473 7082444601018951638767105)
                  ·
                    refine ⟨5311833450764213729075329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082444601018951638767105 5311833450764213729075329)
                    ·
                      refine ⟨3983875088073160296806497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311833450764213729075329 3983875088073160296806497)
                      ·
                        rfl

theorem cell23_7758569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 2, 2].length) (baseStart_7758569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758569 prefixEnd_7758569 := by exact prefixLift 7758569
  have htrace : WordTrace (prefixWord ++ tailWord_7758569) baseStart_7758569 baseEnd_7758569 := by
    simpa [prefixWord, tailWord_7758569, baseEnd_7758569] using wordTrace_append hprefix tailTrace_7758569
  have hstable : (prefixWord ++ tailWord_7758569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758569).length < 2 ^ (prefixWord ++ tailWord_7758569).sum := by decide
  have hdescent : baseEnd_7758569 < baseStart_7758569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758648 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 8]
def baseStart_7758648 : Nat := 118140960795 + 7758648 * 2 ^ 59
def prefixEnd_7758648 : Nat := 4983230072969 + 3 ^ 40 * 7758648 * 2
def baseEnd_7758648 : Nat := 442657294782762831968737

theorem tailTrace_7758648 : CollatzResearch.WordTrace tailWord_7758648 prefixEnd_7758648 442657294782762831968737 := by
  unfold tailWord_7758648
  simp only [CollatzResearch.WordTrace]
  refine ⟨141490570197875421214586299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188654093597167228286115065 141490570197875421214586299)
  ·
    refine ⟨212235855296813131821879449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141490570197875421214586299 212235855296813131821879449)
    ·
      refine ⟨159176891472609848866409587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212235855296813131821879449 159176891472609848866409587)
      ·
        refine ⟨238765337208914773299614381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159176891472609848866409587 238765337208914773299614381)
        ·
          refine ⟨89537001453343039987355393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238765337208914773299614381 89537001453343039987355393)
          ·
            refine ⟨67152751090007279990516545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89537001453343039987355393 67152751090007279990516545)
            ·
              refine ⟨50364563317505459992887409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67152751090007279990516545 50364563317505459992887409)
              ·
                refine ⟨37773422488129094994665557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50364563317505459992887409 37773422488129094994665557)
                ·
                  refine ⟨442657294782762831968737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37773422488129094994665557 442657294782762831968737)
                  ·
                    rfl

theorem cell23_7758648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 8].length) (baseStart_7758648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758648 prefixEnd_7758648 := by exact prefixLift 7758648
  have htrace : WordTrace (prefixWord ++ tailWord_7758648) baseStart_7758648 baseEnd_7758648 := by
    simpa [prefixWord, tailWord_7758648, baseEnd_7758648] using wordTrace_append hprefix tailTrace_7758648
  have hstable : (prefixWord ++ tailWord_7758648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758648).length < 2 ^ (prefixWord ++ tailWord_7758648).sum := by decide
  have hdescent : baseEnd_7758648 < baseStart_7758648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758665 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 6]
def baseStart_7758665 : Nat := 118140960795 + 7758665 * 2 ^ 59
def prefixEnd_7758665 : Nat := 4983230072969 + 3 ^ 40 * 7758665 * 2
def baseEnd_7758665 : Nat := 442658264690665769022895

theorem tailTrace_7758665 : CollatzResearch.WordTrace tailWord_7758665 prefixEnd_7758665 442658264690665769022895 := by
  unfold tailWord_7758665
  simp only [CollatzResearch.WordTrace]
  refine ⟨282981760436689254332541449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188654506957792836221694299 282981760436689254332541449)
  ·
    refine ⟨212236320327516940749406087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282981760436689254332541449 212236320327516940749406087)
    ·
      refine ⟨318354480491275411124109131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212236320327516940749406087 318354480491275411124109131)
      ·
        refine ⟨477531720736913116686163697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318354480491275411124109131 477531720736913116686163697)
        ·
          refine ⟨358148790552684837514622773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477531720736913116686163697 358148790552684837514622773)
          ·
            refine ⟨33576449114314203516995885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 358148790552684837514622773 33576449114314203516995885)
            ·
              refine ⟨12591168417867826318873457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33576449114314203516995885 12591168417867826318873457)
              ·
                refine ⟨9443376313400869739155093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12591168417867826318873457 9443376313400869739155093)
                ·
                  refine ⟨442658264690665769022895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9443376313400869739155093 442658264690665769022895)
                  ·
                    rfl

theorem cell23_7758665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 6].length) (baseStart_7758665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758665 prefixEnd_7758665 := by exact prefixLift 7758665
  have htrace : WordTrace (prefixWord ++ tailWord_7758665) baseStart_7758665 baseEnd_7758665 := by
    simpa [prefixWord, tailWord_7758665, baseEnd_7758665] using wordTrace_append hprefix tailTrace_7758665
  have hstable : (prefixWord ++ tailWord_7758665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758665).length < 2 ^ (prefixWord ++ tailWord_7758665).sum := by decide
  have hdescent : baseEnd_7758665 < baseStart_7758665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758682 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 6]
def baseStart_7758682 : Nat := 118140960795 + 7758682 * 2 ^ 59
def prefixEnd_7758682 : Nat := 4983230072969 + 3 ^ 40 * 7758682 * 2
def baseEnd_7758682 : Nat := 442659234598568706077053

theorem tailTrace_7758682 : CollatzResearch.WordTrace tailWord_7758682 prefixEnd_7758682 442659234598568706077053 := by
  unfold tailWord_7758682
  simp only [CollatzResearch.WordTrace]
  refine ⟨70745595119406916558977575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188654920318418444157273533 70745595119406916558977575)
  ·
    refine ⟨106118392679110374838466363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70745595119406916558977575 106118392679110374838466363)
    ·
      refine ⟨159177589018665562257699545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106118392679110374838466363 159177589018665562257699545)
      ·
        refine ⟨119383191763999171693274659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159177589018665562257699545 119383191763999171693274659)
        ·
          refine ⟨179074787645998757539911989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119383191763999171693274659 179074787645998757539911989)
          ·
            refine ⟨16788261341812383519366749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179074787645998757539911989 16788261341812383519366749)
            ·
              refine ⟨6295598003179643819762531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16788261341812383519366749 6295598003179643819762531)
              ·
                refine ⟨9443397004769465729643797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6295598003179643819762531 9443397004769465729643797)
                ·
                  refine ⟨442659234598568706077053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9443397004769465729643797 442659234598568706077053)
                  ·
                    rfl

theorem cell23_7758682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_7758682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758682 prefixEnd_7758682 := by exact prefixLift 7758682
  have htrace : WordTrace (prefixWord ++ tailWord_7758682) baseStart_7758682 baseEnd_7758682 := by
    simpa [prefixWord, tailWord_7758682, baseEnd_7758682] using wordTrace_append hprefix tailTrace_7758682
  have hstable : (prefixWord ++ tailWord_7758682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758682).length < 2 ^ (prefixWord ++ tailWord_7758682).sum := by decide
  have hdescent : baseEnd_7758682 < baseStart_7758682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758745 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_7758745 : Nat := 118140960795 + 7758745 * 2 ^ 59
def prefixEnd_7758745 : Nat := 4983230072969 + 3 ^ 40 * 7758745 * 2
def baseEnd_7758745 : Nat := 3983965460668351608205687

theorem tailTrace_7758745 : CollatzResearch.WordTrace tailWord_7758745 prefixEnd_7758745 3983965460668351608205687 := by
  unfold tailWord_7758745
  simp only [CollatzResearch.WordTrace]
  refine ⟨282984678276399427995453689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188656452184266285330302459 282984678276399427995453689)
  ·
    refine ⟨212238508707299570996590267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282984678276399427995453689 212238508707299570996590267)
    ·
      refine ⟨318357763060949356494885401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212238508707299570996590267 318357763060949356494885401)
      ·
        refine ⟨238768322295712017371164051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318357763060949356494885401 238768322295712017371164051)
        ·
          refine ⟨358152483443568026056746077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238768322295712017371164051 358152483443568026056746077)
          ·
            refine ⟨134307181291338009771279779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358152483443568026056746077 134307181291338009771279779)
            ·
              refine ⟨201460771937007014656919669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134307181291338009771279779 201460771937007014656919669)
              ·
                refine ⟨18886947369094407624086219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201460771937007014656919669 18886947369094407624086219)
                ·
                  refine ⟨28330421053641611436129329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18886947369094407624086219 28330421053641611436129329)
                  ·
                    refine ⟨21247815790231208577096997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28330421053641611436129329 21247815790231208577096997)
                    ·
                      refine ⟨3983965460668351608205687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21247815790231208577096997 3983965460668351608205687)
                      ·
                        rfl

theorem cell23_7758745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_7758745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758745 prefixEnd_7758745 := by exact prefixLift 7758745
  have htrace : WordTrace (prefixWord ++ tailWord_7758745) baseStart_7758745 baseEnd_7758745 := by
    simpa [prefixWord, tailWord_7758745, baseEnd_7758745] using wordTrace_append hprefix tailTrace_7758745
  have hstable : (prefixWord ++ tailWord_7758745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758745).length < 2 ^ (prefixWord ++ tailWord_7758745).sum := by decide
  have hdescent : baseEnd_7758745 < baseStart_7758745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758746 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_7758746 : Nat := 118140960795 + 7758746 * 2 ^ 59
def prefixEnd_7758746 : Nat := 4983230072969 + 3 ^ 40 * 7758746 * 2
def baseEnd_7758746 : Nat := 1327988658049668701431061

theorem tailTrace_7758746 : CollatzResearch.WordTrace tailWord_7758746 prefixEnd_7758746 1327988658049668701431061 := by
  unfold tailWord_7758746
  simp only [CollatzResearch.WordTrace]
  refine ⟨70746178687348951291560023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188656476499597203444160061 70746178687348951291560023)
  ·
    refine ⟨106119268031023426937340035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70746178687348951291560023 106119268031023426937340035)
    ·
      refine ⟨159178902046535140406010053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106119268031023426937340035 159178902046535140406010053)
      ·
        refine ⟨29846044133725338826126885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159178902046535140406010053 29846044133725338826126885)
        ·
          refine ⟨5596133275073501029898791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29846044133725338826126885 5596133275073501029898791)
          ·
            refine ⟨8394199912610251544848187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5596133275073501029898791 8394199912610251544848187)
            ·
              refine ⟨12591299868915377317272281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394199912610251544848187 12591299868915377317272281)
              ·
                refine ⟨9443474901686532987954211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12591299868915377317272281 9443474901686532987954211)
                ·
                  refine ⟨14165212352529799481931317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9443474901686532987954211 14165212352529799481931317)
                  ·
                    refine ⟨1327988658049668701431061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14165212352529799481931317 1327988658049668701431061)
                    ·
                      rfl

theorem cell23_7758746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_7758746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758746 prefixEnd_7758746 := by exact prefixLift 7758746
  have htrace : WordTrace (prefixWord ++ tailWord_7758746) baseStart_7758746 baseEnd_7758746 := by
    simpa [prefixWord, tailWord_7758746, baseEnd_7758746] using wordTrace_append hprefix tailTrace_7758746
  have hstable : (prefixWord ++ tailWord_7758746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758746).length < 2 ^ (prefixWord ++ tailWord_7758746).sum := by decide
  have hdescent : baseEnd_7758746 < baseStart_7758746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758749 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_7758749 : Nat := 118140960795 + 7758749 * 2 ^ 59
def prefixEnd_7758749 : Nat := 4983230072969 + 3 ^ 40 * 7758749 * 2
def baseEnd_7758749 : Nat := 3983967514590969592555669

theorem tailTrace_7758749 : CollatzResearch.WordTrace tailWord_7758749 prefixEnd_7758749 3983967514590969592555669 := by
  unfold tailWord_7758749
  simp only [CollatzResearch.WordTrace]
  refine ⟨282984824168384936678599301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188656549445589957785732867 282984824168384936678599301)
  ·
    refine ⟨53059654531572175627237369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282984824168384936678599301 53059654531572175627237369)
    ·
      refine ⟨39794740898679131720428027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53059654531572175627237369 39794740898679131720428027)
      ·
        refine ⟨59692111348018697580642041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39794740898679131720428027 59692111348018697580642041)
        ·
          refine ⟨44769083511014023185481531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59692111348018697580642041 44769083511014023185481531)
          ·
            refine ⟨67153625266521034778222297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44769083511014023185481531 67153625266521034778222297)
            ·
              refine ⟨50365218949890776083666723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67153625266521034778222297 50365218949890776083666723)
              ·
                refine ⟨75547828424836164125500085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50365218949890776083666723 75547828424836164125500085)
                ·
                  refine ⟨7082608914828390386765633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75547828424836164125500085 7082608914828390386765633)
                  ·
                    refine ⟨5311956686121292790074225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7082608914828390386765633 5311956686121292790074225)
                    ·
                      refine ⟨3983967514590969592555669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5311956686121292790074225 3983967514590969592555669)
                      ·
                        rfl

theorem cell23_7758749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_7758749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758749 prefixEnd_7758749 := by exact prefixLift 7758749
  have htrace : WordTrace (prefixWord ++ tailWord_7758749) baseStart_7758749 baseEnd_7758749 := by
    simpa [prefixWord, tailWord_7758749, baseEnd_7758749] using wordTrace_append hprefix tailTrace_7758749
  have hstable : (prefixWord ++ tailWord_7758749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758749).length < 2 ^ (prefixWord ++ tailWord_7758749).sum := by decide
  have hdescent : baseEnd_7758749 < baseStart_7758749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7758769 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_7758769 : Nat := 118140960795 + 7758769 * 2 ^ 59
def prefixEnd_7758769 : Nat := 4983230072969 + 3 ^ 40 * 7758769 * 2
def baseEnd_7758769 : Nat := 3983977784204059514305577

theorem tailTrace_7758769 : CollatzResearch.WordTrace tailWord_7758769 prefixEnd_7758769 3983977784204059514305577 := by
  unfold tailWord_7758769
  simp only [CollatzResearch.WordTrace]
  refine ⟨282985553628312480094327361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188657035752208320062884907 282985553628312480094327361)
  ·
    refine ⟨212239165221234360070745521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282985553628312480094327361 212239165221234360070745521)
    ·
      refine ⟨159179373915925770053059141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212239165221234360070745521 159179373915925770053059141)
      ·
        refine ⟨29846132609236081884948589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159179373915925770053059141 29846132609236081884948589)
        ·
          refine ⟨11192299728463530706855721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29846132609236081884948589 11192299728463530706855721)
          ·
            refine ⟨8394224796347648030141791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11192299728463530706855721 8394224796347648030141791)
            ·
              refine ⟨12591337194521472045212687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8394224796347648030141791 12591337194521472045212687)
              ·
                refine ⟨18887005791782208067819031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12591337194521472045212687 18887005791782208067819031)
                ·
                  refine ⟨28330508687673312101728547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18887005791782208067819031 28330508687673312101728547)
                  ·
                    refine ⟨42495763031509968152592821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28330508687673312101728547 42495763031509968152592821)
                    ·
                      refine ⟨3983977784204059514305577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42495763031509968152592821 3983977784204059514305577)
                      ·
                        rfl

theorem cell23_7758769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_7758769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7758769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7758769 prefixEnd_7758769 := by exact prefixLift 7758769
  have htrace : WordTrace (prefixWord ++ tailWord_7758769) baseStart_7758769 baseEnd_7758769 := by
    simpa [prefixWord, tailWord_7758769, baseEnd_7758769] using wordTrace_append hprefix tailTrace_7758769
  have hstable : (prefixWord ++ tailWord_7758769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7758769).length < 2 ^ (prefixWord ++ tailWord_7758769).sum := by decide
  have hdescent : baseEnd_7758769 < baseStart_7758769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7758769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
