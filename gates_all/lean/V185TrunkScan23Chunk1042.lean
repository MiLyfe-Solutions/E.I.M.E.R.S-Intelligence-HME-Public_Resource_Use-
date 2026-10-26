import V185TrunkScan23Chunk1041

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6168360 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_6168360 : Nat := 118140960795 + 6168360 * 2 ^ 59
def prefixEnd_6168360 : Nat := 4983230072969 + 3 ^ 40 * 6168360 * 2
def baseEnd_6168360 : Nat := 3167333529967591496832235

theorem tailTrace_6168360 : CollatzResearch.WordTrace tailWord_6168360 prefixEnd_6168360 3167333529967591496832235 := by
  unfold tailWord_6168360
  simp only [CollatzResearch.WordTrace]
  refine ⟨112489285966546333430959267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149985714622061777907945689 112489285966546333430959267)
  ·
    refine ⟨168733928949819500146438901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112489285966546333430959267 168733928949819500146438901)
    ·
      refine ⟨15818805839045578138728647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168733928949819500146438901 15818805839045578138728647)
      ·
        refine ⟨23728208758568367208092971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15818805839045578138728647 23728208758568367208092971)
        ·
          refine ⟨35592313137852550812139457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23728208758568367208092971 35592313137852550812139457)
          ·
            refine ⟨26694234853389413109104593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35592313137852550812139457 26694234853389413109104593)
            ·
              refine ⟨20020676140042059831828445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26694234853389413109104593 20020676140042059831828445)
              ·
                refine ⟨7507753552515772436935667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20020676140042059831828445 7507753552515772436935667)
                ·
                  refine ⟨11261630328773658655403501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507753552515772436935667 11261630328773658655403501)
                  ·
                    refine ⟨4223111373290121995776313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11261630328773658655403501 4223111373290121995776313)
                    ·
                      refine ⟨3167333529967591496832235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223111373290121995776313 3167333529967591496832235)
                      ·
                        rfl

theorem cell23_6168360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_6168360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168360 prefixEnd_6168360 := by exact prefixLift 6168360
  have htrace : WordTrace (prefixWord ++ tailWord_6168360) baseStart_6168360 baseEnd_6168360 := by
    simpa [prefixWord, tailWord_6168360, baseEnd_6168360] using wordTrace_append hprefix tailTrace_6168360
  have hstable : (prefixWord ++ tailWord_6168360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168360).length < 2 ^ (prefixWord ++ tailWord_6168360).sum := by decide
  have hdescent : baseEnd_6168360 < baseStart_6168360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168430 : List Nat := [4, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_6168430 : Nat := 118140960795 + 6168430 * 2 ^ 59
def prefixEnd_6168430 : Nat := 4983230072969 + 3 ^ 40 * 6168430 * 2
def baseEnd_6168430 : Nat := 351929941512600691439657

theorem tailTrace_6168430 : CollatzResearch.WordTrace tailWord_6168430 prefixEnd_6168430 351929941512600691439657 := by
  unfold tailWord_6168430
  simp only [CollatzResearch.WordTrace]
  refine ⟨28122640630354883602120843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149987416695226045877977829 28122640630354883602120843)
  ·
    refine ⟨42183960945532325403181265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28122640630354883602120843 42183960945532325403181265)
    ·
      refine ⟨31637970709149244052385949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42183960945532325403181265 31637970709149244052385949)
      ·
        refine ⟨11864239015930966519644731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31637970709149244052385949 11864239015930966519644731)
        ·
          refine ⟨17796358523896449779467097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11864239015930966519644731 17796358523896449779467097)
          ·
            refine ⟨13347268892922337334600323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17796358523896449779467097 13347268892922337334600323)
            ·
              refine ⟨20020903339383506001900485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13347268892922337334600323 20020903339383506001900485)
              ·
                refine ⟨3753919376134407375356341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20020903339383506001900485 3753919376134407375356341)
                ·
                  refine ⟨351929941512600691439657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3753919376134407375356341 351929941512600691439657)
                  ·
                    rfl

theorem cell23_6168430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_6168430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168430 prefixEnd_6168430 := by exact prefixLift 6168430
  have htrace : WordTrace (prefixWord ++ tailWord_6168430) baseStart_6168430 baseEnd_6168430 := by
    simpa [prefixWord, tailWord_6168430, baseEnd_6168430] using wordTrace_append hprefix tailTrace_6168430
  have hstable : (prefixWord ++ tailWord_6168430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168430).length < 2 ^ (prefixWord ++ tailWord_6168430).sum := by decide
  have hdescent : baseEnd_6168430 < baseStart_6168430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168439 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 4, 8]
def baseStart_6168439 : Nat := 118140960795 + 6168439 * 2 ^ 59
def prefixEnd_6168439 : Nat := 4983230072969 + 3 ^ 40 * 6168439 * 2
def baseEnd_6168439 : Nat := 1055791364979765562581457

theorem tailTrace_6168439 : CollatzResearch.WordTrace tailWord_6168439 prefixEnd_6168439 1055791364979765562581457 := by
  unfold tailWord_6168439
  simp only [CollatzResearch.WordTrace]
  refine ⟨224981453299806463354044371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149987635533204308902696247 224981453299806463354044371)
  ·
    refine ⟨337472179949709695031066557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224981453299806463354044371 337472179949709695031066557)
    ·
      refine ⟨126552067481141135636649959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337472179949709695031066557 126552067481141135636649959)
      ·
        refine ⟨189828101221711703454974939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126552067481141135636649959 189828101221711703454974939)
        ·
          refine ⟨284742151832567555182462409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189828101221711703454974939 284742151832567555182462409)
          ·
            refine ⟨213556613874425666386846807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284742151832567555182462409 213556613874425666386846807)
            ·
              refine ⟨320334920811638499580270211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213556613874425666386846807 320334920811638499580270211)
              ·
                refine ⟨480502381217457749370405317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320334920811638499580270211 480502381217457749370405317)
                ·
                  refine ⟨90094196478273328006950997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480502381217457749370405317 90094196478273328006950997)
                  ·
                    refine ⟨1055791364979765562581457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90094196478273328006950997 1055791364979765562581457)
                    ·
                      rfl

theorem cell23_6168439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_6168439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168439 prefixEnd_6168439 := by exact prefixLift 6168439
  have htrace : WordTrace (prefixWord ++ tailWord_6168439) baseStart_6168439 baseEnd_6168439 := by
    simpa [prefixWord, tailWord_6168439, baseEnd_6168439] using wordTrace_append hprefix tailTrace_6168439
  have hstable : (prefixWord ++ tailWord_6168439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168439).length < 2 ^ (prefixWord ++ tailWord_6168439).sum := by decide
  have hdescent : baseEnd_6168439 < baseStart_6168439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168523 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 1, 5, 2]
def baseStart_6168523 : Nat := 118140960795 + 6168523 * 2 ^ 59
def prefixEnd_6168523 : Nat := 4983230072969 + 3 ^ 40 * 6168523 * 2
def baseEnd_6168523 : Nat := 3167417227314274359093985

theorem tailTrace_6168523 : CollatzResearch.WordTrace tailWord_6168523 prefixEnd_6168523 3167417227314274359093985 := by
  unfold tailWord_6168523
  simp only [CollatzResearch.WordTrace]
  refine ⟨224984517031502145700102223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149989678021001430466734815 224984517031502145700102223)
  ·
    refine ⟨337476775547253218550153335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224984517031502145700102223 337476775547253218550153335)
    ·
      refine ⟨506215163320879827825230003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337476775547253218550153335 506215163320879827825230003)
      ·
        refine ⟨759322744981319741737845005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506215163320879827825230003 759322744981319741737845005)
        ·
          refine ⟨284746029367994903151691877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 759322744981319741737845005 284746029367994903151691877)
          ·
            refine ⟨53389880506499044340942227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284746029367994903151691877 53389880506499044340942227)
            ·
              refine ⟨80084820759748566511413341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53389880506499044340942227 80084820759748566511413341)
              ·
                refine ⟨30031807784905712441780003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80084820759748566511413341 30031807784905712441780003)
                ·
                  refine ⟨45047711677358568662670005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30031807784905712441780003 45047711677358568662670005)
                  ·
                    refine ⟨4223222969752365812125313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45047711677358568662670005 4223222969752365812125313)
                    ·
                      refine ⟨3167417227314274359093985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223222969752365812125313 3167417227314274359093985)
                      ·
                        rfl

theorem cell23_6168523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5, 2].length) (baseStart_6168523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168523 prefixEnd_6168523 := by exact prefixLift 6168523
  have htrace : WordTrace (prefixWord ++ tailWord_6168523) baseStart_6168523 baseEnd_6168523 := by
    simpa [prefixWord, tailWord_6168523, baseEnd_6168523] using wordTrace_append hprefix tailTrace_6168523
  have hstable : (prefixWord ++ tailWord_6168523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168523).length < 2 ^ (prefixWord ++ tailWord_6168523).sum := by decide
  have hdescent : baseEnd_6168523 < baseStart_6168523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168547 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 3]
def baseStart_6168547 : Nat := 118140960795 + 6168547 * 2 ^ 59
def prefixEnd_6168547 : Nat := 4983230072969 + 3 ^ 40 * 6168547 * 2
def baseEnd_6168547 : Nat := 3167429550849982265193875

theorem tailTrace_6168547 : CollatzResearch.WordTrace tailWord_6168547 prefixEnd_6168547 3167429550849982265193875 := by
  unfold tailWord_6168547
  simp only [CollatzResearch.WordTrace]
  refine ⟨224985392383415197798975895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149990261588943465199317263 224985392383415197798975895)
  ·
    refine ⟨337478088575122796698463843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224985392383415197798975895 337478088575122796698463843)
    ·
      refine ⟨506217132862684195047695765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337478088575122796698463843 506217132862684195047695765)
      ·
        refine ⟨23728928102938321642860739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 506217132862684195047695765 23728928102938321642860739)
        ·
          refine ⟨35593392154407482464291109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23728928102938321642860739 35593392154407482464291109)
          ·
            refine ⟨6673761028951402962054583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35593392154407482464291109 6673761028951402962054583)
            ·
              refine ⟨10010641543427104443081875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6673761028951402962054583 10010641543427104443081875)
              ·
                refine ⟨15015962315140656664622813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10010641543427104443081875 15015962315140656664622813)
                ·
                  refine ⟨5630985868177746249233555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15015962315140656664622813 5630985868177746249233555)
                  ·
                    refine ⟨8446478802266619373850333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5630985868177746249233555 8446478802266619373850333)
                    ·
                      refine ⟨3167429550849982265193875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8446478802266619373850333 3167429550849982265193875)
                      ·
                        rfl

theorem cell23_6168547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_6168547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168547 prefixEnd_6168547 := by exact prefixLift 6168547
  have htrace : WordTrace (prefixWord ++ tailWord_6168547) baseStart_6168547 baseEnd_6168547 := by
    simpa [prefixWord, tailWord_6168547, baseEnd_6168547] using wordTrace_append hprefix tailTrace_6168547
  have hstable : (prefixWord ++ tailWord_6168547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168547).length < 2 ^ (prefixWord ++ tailWord_6168547).sum := by decide
  have hdescent : baseEnd_6168547 < baseStart_6168547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168574 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6168574 : Nat := 118140960795 + 6168574 * 2 ^ 59
def prefixEnd_6168574 : Nat := 4983230072969 + 3 ^ 40 * 6168574 * 2
def baseEnd_6168574 : Nat := 3167443414827653659556251

theorem tailTrace_6168574 : CollatzResearch.WordTrace tailWord_6168574 prefixEnd_6168574 3167443414827653659556251 := by
  unfold tailWord_6168574
  simp only [CollatzResearch.WordTrace]
  refine ⟨28123297144289672676276097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149990918102878254273472517 28123297144289672676276097)
  ·
    refine ⟨21092472858217254507207073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28123297144289672676276097 21092472858217254507207073)
    ·
      refine ⟨15819354643662940880405305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21092472858217254507207073 15819354643662940880405305)
      ·
        refine ⟨11864515982747205660303979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15819354643662940880405305 11864515982747205660303979)
        ·
          refine ⟨17796773974120808490455969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11864515982747205660303979 17796773974120808490455969)
          ·
            refine ⟨13347580480590606367841977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17796773974120808490455969 13347580480590606367841977)
            ·
              refine ⟨10010685360442954775881483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13347580480590606367841977 10010685360442954775881483)
              ·
                refine ⟨15016028040664432163822225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10010685360442954775881483 15016028040664432163822225)
                ·
                  refine ⟨11262021030498324122866669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15016028040664432163822225 11262021030498324122866669)
                  ·
                    refine ⟨4223257886436871546075001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11262021030498324122866669 4223257886436871546075001)
                    ·
                      refine ⟨3167443414827653659556251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223257886436871546075001 3167443414827653659556251)
                      ·
                        rfl

theorem cell23_6168574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6168574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168574 prefixEnd_6168574 := by exact prefixLift 6168574
  have htrace : WordTrace (prefixWord ++ tailWord_6168574) baseStart_6168574 baseEnd_6168574 := by
    simpa [prefixWord, tailWord_6168574, baseEnd_6168574] using wordTrace_append hprefix tailTrace_6168574
  have hstable : (prefixWord ++ tailWord_6168574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168574).length < 2 ^ (prefixWord ++ tailWord_6168574).sum := by decide
  have hdescent : baseEnd_6168574 < baseStart_6168574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168583 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_6168583 : Nat := 118140960795 + 6168583 * 2 ^ 59
def prefixEnd_6168583 : Nat := 4983230072969 + 3 ^ 40 * 6168583 * 2
def baseEnd_6168583 : Nat := 3167448036153544124343709

theorem tailTrace_6168583 : CollatzResearch.WordTrace tailWord_6168583 prefixEnd_6168583 3167448036153544124343709 := by
  unfold tailWord_6168583
  simp only [CollatzResearch.WordTrace]
  refine ⟨224986705411284775947286403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149991136940856517298190935 224986705411284775947286403)
  ·
    refine ⟨337480058116927163920929605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224986705411284775947286403 337480058116927163920929605)
    ·
      refine ⟨63277510896923843235174301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337480058116927163920929605 63277510896923843235174301)
      ·
        refine ⟨23729066586346441213190363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63277510896923843235174301 23729066586346441213190363)
        ·
          refine ⟨35593599879519661819785545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23729066586346441213190363 35593599879519661819785545)
          ·
            refine ⟨26695199909639746364839159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35593599879519661819785545 26695199909639746364839159)
            ·
              refine ⟨40042799864459619547258739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26695199909639746364839159 40042799864459619547258739)
              ·
                refine ⟨60064199796689429320888109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40042799864459619547258739 60064199796689429320888109)
                ·
                  refine ⟨22524074923758535995333041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60064199796689429320888109 22524074923758535995333041)
                  ·
                    refine ⟨16893056192818901996499781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22524074923758535995333041 16893056192818901996499781)
                    ·
                      refine ⟨3167448036153544124343709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16893056192818901996499781 3167448036153544124343709)
                      ·
                        rfl

theorem cell23_6168583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_6168583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168583 prefixEnd_6168583 := by exact prefixLift 6168583
  have htrace : WordTrace (prefixWord ++ tailWord_6168583) baseStart_6168583 baseEnd_6168583 := by
    simpa [prefixWord, tailWord_6168583, baseEnd_6168583] using wordTrace_append hprefix tailTrace_6168583
  have hstable : (prefixWord ++ tailWord_6168583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168583).length < 2 ^ (prefixWord ++ tailWord_6168583).sum := by decide
  have hdescent : baseEnd_6168583 < baseStart_6168583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168597 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_6168597 : Nat := 118140960795 + 6168597 * 2 ^ 59
def prefixEnd_6168597 : Nat := 4983230072969 + 3 ^ 40 * 6168597 * 2
def baseEnd_6168597 : Nat := 1055818408294235689856215

theorem tailTrace_6168597 : CollatzResearch.WordTrace tailWord_6168597 prefixEnd_6168597 1055818408294235689856215 := by
  unfold tailWord_6168597
  simp only [CollatzResearch.WordTrace]
  refine ⟨224987216033234056338296045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149991477355489370892197363 224987216033234056338296045)
  ·
    refine ⟨84370206012462771126861017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224987216033234056338296045 84370206012462771126861017)
    ·
      refine ⟨63277654509347078345145763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84370206012462771126861017 63277654509347078345145763)
      ·
        refine ⟨94916481764020617517718645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63277654509347078345145763 94916481764020617517718645)
        ·
          refine ⟨8898420165376932892286123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94916481764020617517718645 8898420165376932892286123)
          ·
            refine ⟨13347630248065399338429185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8898420165376932892286123 13347630248065399338429185)
            ·
              refine ⟨10010722686049049503821889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13347630248065399338429185 10010722686049049503821889)
              ·
                refine ⟨7508042014536787127866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10010722686049049503821889 7508042014536787127866417)
                ·
                  refine ⟨5631031510902590345899813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7508042014536787127866417 5631031510902590345899813)
                  ·
                    refine ⟨1055818408294235689856215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631031510902590345899813 1055818408294235689856215)
                    ·
                      rfl

theorem cell23_6168597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_6168597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168597 prefixEnd_6168597 := by exact prefixLift 6168597
  have htrace : WordTrace (prefixWord ++ tailWord_6168597) baseStart_6168597 baseEnd_6168597 := by
    simpa [prefixWord, tailWord_6168597, baseEnd_6168597] using wordTrace_append hprefix tailTrace_6168597
  have hstable : (prefixWord ++ tailWord_6168597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168597).length < 2 ^ (prefixWord ++ tailWord_6168597).sum := by decide
  have hdescent : baseEnd_6168597 < baseStart_6168597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168638 : List Nat := [4, 2, 1, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_6168638 : Nat := 118140960795 + 6168638 * 2 ^ 59
def prefixEnd_6168638 : Nat := 4983230072969 + 3 ^ 40 * 6168638 * 2
def baseEnd_6168638 : Nat := 3167476277589541409155957

theorem tailTrace_6168638 : CollatzResearch.WordTrace tailWord_6168638 prefixEnd_6168638 3167476277589541409155957 := by
  unfold tailWord_6168638
  simp only [CollatzResearch.WordTrace]
  refine ⟨28123588928260690042567321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149992474284057013560359045 28123588928260690042567321)
  ·
    refine ⟨21092691696195517531925491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28123588928260690042567321 21092691696195517531925491)
    ·
      refine ⟨31639037544293276297888237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21092691696195517531925491 31639037544293276297888237)
      ·
        refine ⟨11864639079109978611708089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31639037544293276297888237 11864639079109978611708089)
        ·
          refine ⟨8898479309332483958781067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11864639079109978611708089 8898479309332483958781067)
          ·
            refine ⟨13347718963998725938171601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8898479309332483958781067 13347718963998725938171601)
            ·
              refine ⟨10010789222999044453628701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13347718963998725938171601 10010789222999044453628701)
              ·
                refine ⟨3754045958624641670110763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10010789222999044453628701 3754045958624641670110763)
                ·
                  refine ⟨5631068937936962505166145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754045958624641670110763 5631068937936962505166145)
                  ·
                    refine ⟨4223301703452721878874609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5631068937936962505166145 4223301703452721878874609)
                    ·
                      refine ⟨3167476277589541409155957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223301703452721878874609 3167476277589541409155957)
                      ·
                        rfl

theorem cell23_6168638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_6168638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168638 prefixEnd_6168638 := by exact prefixLift 6168638
  have htrace : WordTrace (prefixWord ++ tailWord_6168638) baseStart_6168638 baseEnd_6168638 := by
    simpa [prefixWord, tailWord_6168638, baseEnd_6168638] using wordTrace_append hprefix tailTrace_6168638
  have hstable : (prefixWord ++ tailWord_6168638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168638).length < 2 ^ (prefixWord ++ tailWord_6168638).sum := by decide
  have hdescent : baseEnd_6168638 < baseStart_6168638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168647 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_6168647 : Nat := 118140960795 + 6168647 * 2 ^ 59
def prefixEnd_6168647 : Nat := 4983230072969 + 3 ^ 40 * 6168647 * 2
def baseEnd_6168647 : Nat := 3167480898915431873943415

theorem tailTrace_6168647 : CollatzResearch.WordTrace tailWord_6168647 prefixEnd_6168647 3167480898915431873943415 := by
  unfold tailWord_6168647
  simp only [CollatzResearch.WordTrace]
  refine ⟨224989039683052914877616195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149992693122035276585077463 224989039683052914877616195)
  ·
    refine ⟨337483559524579372316424293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224989039683052914877616195 337483559524579372316424293)
    ·
      refine ⟨63278167410858632309329555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337483559524579372316424293 63278167410858632309329555)
      ·
        refine ⟨94917251116287948463994333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63278167410858632309329555 94917251116287948463994333)
        ·
          refine ⟨35593969168607980673997875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94917251116287948463994333 35593969168607980673997875)
          ·
            refine ⟨53390953752911971010996813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35593969168607980673997875 53390953752911971010996813)
            ·
              refine ⟨20021607657341989129123805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53390953752911971010996813 20021607657341989129123805)
              ·
                refine ⟨7508102871503245923421427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20021607657341989129123805 7508102871503245923421427)
                ·
                  refine ⟨11262154307254868885132141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7508102871503245923421427 11262154307254868885132141)
                  ·
                    refine ⟨4223307865220575831924553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11262154307254868885132141 4223307865220575831924553)
                    ·
                      refine ⟨3167480898915431873943415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223307865220575831924553 3167480898915431873943415)
                      ·
                        rfl

theorem cell23_6168647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_6168647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168647 prefixEnd_6168647 := by exact prefixLift 6168647
  have htrace : WordTrace (prefixWord ++ tailWord_6168647) baseStart_6168647 baseEnd_6168647 := by
    simpa [prefixWord, tailWord_6168647, baseEnd_6168647] using wordTrace_append hprefix tailTrace_6168647
  have hstable : (prefixWord ++ tailWord_6168647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168647).length < 2 ^ (prefixWord ++ tailWord_6168647).sum := by decide
  have hdescent : baseEnd_6168647 < baseStart_6168647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168654 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_6168654 : Nat := 118140960795 + 6168654 * 2 ^ 59
def prefixEnd_6168654 : Nat := 4983230072969 + 3 ^ 40 * 6168654 * 2
def baseEnd_6168654 : Nat := 3167484493280013346555883

theorem tailTrace_6168654 : CollatzResearch.WordTrace tailWord_6168654 prefixEnd_6168654 3167484493280013346555883 := by
  unfold tailWord_6168654
  simp only [CollatzResearch.WordTrace]
  refine ⟨28123661874253444384140127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149992863329351703382080677 28123661874253444384140127)
  ·
    refine ⟨42185492811380166576210191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28123661874253444384140127 42185492811380166576210191)
    ·
      refine ⟨63278239217070249864315287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42185492811380166576210191 63278239217070249864315287)
      ·
        refine ⟨94917358825605374796472931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63278239217070249864315287 94917358825605374796472931)
        ·
          refine ⟨142376038238408062194709397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94917358825605374796472931 142376038238408062194709397)
          ·
            refine ⟨6673876792425377915377003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142376038238408062194709397 6673876792425377915377003)
            ·
              refine ⟨10010815188638066873065505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6673876792425377915377003 10010815188638066873065505)
              ·
                refine ⟨7508111391478550154799129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10010815188638066873065505 7508111391478550154799129)
                ·
                  refine ⟨5631083543608912616099347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7508111391478550154799129 5631083543608912616099347)
                  ·
                    refine ⟨8446625315413368924149021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5631083543608912616099347 8446625315413368924149021)
                    ·
                      refine ⟨3167484493280013346555883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8446625315413368924149021 3167484493280013346555883)
                      ·
                        rfl

theorem cell23_6168654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_6168654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168654 prefixEnd_6168654 := by exact prefixLift 6168654
  have htrace : WordTrace (prefixWord ++ tailWord_6168654) baseStart_6168654 baseEnd_6168654 := by
    simpa [prefixWord, tailWord_6168654, baseEnd_6168654] using wordTrace_append hprefix tailTrace_6168654
  have hstable : (prefixWord ++ tailWord_6168654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168654).length < 2 ^ (prefixWord ++ tailWord_6168654).sum := by decide
  have hdescent : baseEnd_6168654 < baseStart_6168654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168663 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_6168663 : Nat := 118140960795 + 6168663 * 2 ^ 59
def prefixEnd_6168663 : Nat := 4983230072969 + 3 ^ 40 * 6168663 * 2
def baseEnd_6168663 : Nat := 3167489114605903811343341

theorem tailTrace_6168663 : CollatzResearch.WordTrace tailWord_6168663 prefixEnd_6168663 3167489114605903811343341 := by
  unfold tailWord_6168663
  simp only [CollatzResearch.WordTrace]
  refine ⟨224989623250994949610198643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149993082167329966406799095 224989623250994949610198643)
  ·
    refine ⟨337484434876492424415297965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224989623250994949610198643 337484434876492424415297965)
    ·
      refine ⟨126556663078684659155736737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337484434876492424415297965 126556663078684659155736737)
      ·
        refine ⟨94917497309013494366802553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126556663078684659155736737 94917497309013494366802553)
        ·
          refine ⟨71188122981760120775101915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94917497309013494366802553 71188122981760120775101915)
          ·
            refine ⟨106782184472640181162652873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71188122981760120775101915 106782184472640181162652873)
            ·
              refine ⟨80086638354480135871989655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106782184472640181162652873 80086638354480135871989655)
              ·
                refine ⟨120129957531720203807984483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80086638354480135871989655 120129957531720203807984483)
                ·
                  refine ⟨180194936297580305711976725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120129957531720203807984483 180194936297580305711976725)
                  ·
                    refine ⟨8446637638949076830248909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 180194936297580305711976725 8446637638949076830248909)
                    ·
                      refine ⟨3167489114605903811343341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8446637638949076830248909 3167489114605903811343341)
                      ·
                        rfl

theorem cell23_6168663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_6168663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168663 prefixEnd_6168663 := by exact prefixLift 6168663
  have htrace : WordTrace (prefixWord ++ tailWord_6168663) baseStart_6168663 baseEnd_6168663 := by
    simpa [prefixWord, tailWord_6168663, baseEnd_6168663] using wordTrace_append hprefix tailTrace_6168663
  have hstable : (prefixWord ++ tailWord_6168663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168663).length < 2 ^ (prefixWord ++ tailWord_6168663).sum := by decide
  have hdescent : baseEnd_6168663 < baseStart_6168663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168677 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 1, 4, 2]
def baseStart_6168677 : Nat := 118140960795 + 6168677 * 2 ^ 59
def prefixEnd_6168677 : Nat := 4983230072969 + 3 ^ 40 * 6168677 * 2
def baseEnd_6168677 : Nat := 3167496303335066756568277

theorem tailTrace_6168677 : CollatzResearch.WordTrace tailWord_6168677 prefixEnd_6168677 3167496303335066756568277 := by
  unfold tailWord_6168677
  simp only [CollatzResearch.WordTrace]
  refine ⟨224990133872944230001208285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149993422581962820000805523 224990133872944230001208285)
  ·
    refine ⟨84371300202354086250453107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224990133872944230001208285 84371300202354086250453107)
    ·
      refine ⟨126556950303531129375679661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84371300202354086250453107 126556950303531129375679661)
      ·
        refine ⟨47458856363824173515879873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126556950303531129375679661 47458856363824173515879873)
        ·
          refine ⟨35594142272868130136909905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47458856363824173515879873 35594142272868130136909905)
          ·
            refine ⟨26695606704651097602682429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35594142272868130136909905 26695606704651097602682429)
            ·
              refine ⟨10010852514244161601005911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26695606704651097602682429 10010852514244161601005911)
              ·
                refine ⟨15016278771366242401508867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10010852514244161601005911 15016278771366242401508867)
                ·
                  refine ⟨22524418157049363602263301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15016278771366242401508867 22524418157049363602263301)
                  ·
                    refine ⟨4223328404446755675424369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22524418157049363602263301 4223328404446755675424369)
                    ·
                      refine ⟨3167496303335066756568277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223328404446755675424369 3167496303335066756568277)
                      ·
                        rfl

theorem cell23_6168677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_6168677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168677 prefixEnd_6168677 := by exact prefixLift 6168677
  have htrace : WordTrace (prefixWord ++ tailWord_6168677) baseStart_6168677 baseEnd_6168677 := by
    simpa [prefixWord, tailWord_6168677, baseEnd_6168677] using wordTrace_append hprefix tailTrace_6168677
  have hstable : (prefixWord ++ tailWord_6168677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168677).length < 2 ^ (prefixWord ++ tailWord_6168677).sum := by decide
  have hdescent : baseEnd_6168677 < baseStart_6168677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168694 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6168694 : Nat := 118140960795 + 6168694 * 2 ^ 59
def prefixEnd_6168694 : Nat := 4983230072969 + 3 ^ 40 * 6168694 * 2
def baseEnd_6168694 : Nat := 3167505032506193190055699

theorem tailTrace_6168694 : CollatzResearch.WordTrace tailWord_6168694 prefixEnd_6168694 3167505032506193190055699 := by
  unfold tailWord_6168694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14061922119617665119036071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149993835942588427936384757 14061922119617665119036071)
  ·
    refine ⟨21092883179426497678554107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14061922119617665119036071 21092883179426497678554107)
    ·
      refine ⟨31639324769139746517831161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21092883179426497678554107 31639324769139746517831161)
      ·
        refine ⟨23729493576854809888373371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31639324769139746517831161 23729493576854809888373371)
        ·
          refine ⟨35594240365282214832560057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23729493576854809888373371 35594240365282214832560057)
          ·
            refine ⟨26695680273961661124420043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35594240365282214832560057 26695680273961661124420043)
            ·
              refine ⟨40043520410942491686630065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26695680273961661124420043 40043520410942491686630065)
              ·
                refine ⟨30032640308206868764972549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40043520410942491686630065 30032640308206868764972549)
                ·
                  refine ⟨5631120057788787893432353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30032640308206868764972549 5631120057788787893432353)
                  ·
                    refine ⟨4223340043341590920074265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5631120057788787893432353 4223340043341590920074265)
                    ·
                      refine ⟨3167505032506193190055699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223340043341590920074265 3167505032506193190055699)
                      ·
                        rfl

theorem cell23_6168694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6168694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168694 prefixEnd_6168694 := by exact prefixLift 6168694
  have htrace : WordTrace (prefixWord ++ tailWord_6168694) baseStart_6168694 baseEnd_6168694 := by
    simpa [prefixWord, tailWord_6168694, baseEnd_6168694] using wordTrace_append hprefix tailTrace_6168694
  have hstable : (prefixWord ++ tailWord_6168694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168694).length < 2 ^ (prefixWord ++ tailWord_6168694).sum := by decide
  have hdescent : baseEnd_6168694 < baseStart_6168694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168720 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 2, 5, 2]
def baseStart_6168720 : Nat := 118140960795 + 6168720 * 2 ^ 59
def prefixEnd_6168720 : Nat := 4983230072969 + 3 ^ 40 * 6168720 * 2
def baseEnd_6168720 : Nat := 3167518383003210088330579

theorem tailTrace_6168720 : CollatzResearch.WordTrace tailWord_6168720 prefixEnd_6168720 3167518383003210088330579 := by
  unfold tailWord_6168720
  simp only [CollatzResearch.WordTrace]
  refine ⟨112495851105894224172511807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149994468141192298896682409 112495851105894224172511807)
  ·
    refine ⟨168743776658841336258767711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112495851105894224172511807 168743776658841336258767711)
    ·
      refine ⟨253115664988262004388151567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168743776658841336258767711 253115664988262004388151567)
      ·
        refine ⟨379673497482393006582227351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253115664988262004388151567 379673497482393006582227351)
        ·
          refine ⟨569510246223589509873341027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379673497482393006582227351 569510246223589509873341027)
          ·
            refine ⟨854265369335384264810011541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569510246223589509873341027 854265369335384264810011541)
            ·
              refine ⟨40043689187596137412969291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 854265369335384264810011541 40043689187596137412969291)
              ·
                refine ⟨60065533781394206119453937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40043689187596137412969291 60065533781394206119453937)
                ·
                  refine ⟨45049150336045654589590453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60065533781394206119453937 45049150336045654589590453)
                  ·
                    refine ⟨4223357844004280117774105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45049150336045654589590453 4223357844004280117774105)
                    ·
                      refine ⟨3167518383003210088330579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223357844004280117774105 3167518383003210088330579)
                      ·
                        rfl

theorem cell23_6168720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 5, 2].length) (baseStart_6168720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168720 prefixEnd_6168720 := by exact prefixLift 6168720
  have htrace : WordTrace (prefixWord ++ tailWord_6168720) baseStart_6168720 baseEnd_6168720 := by
    simpa [prefixWord, tailWord_6168720, baseEnd_6168720] using wordTrace_append hprefix tailTrace_6168720
  have hstable : (prefixWord ++ tailWord_6168720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168720).length < 2 ^ (prefixWord ++ tailWord_6168720).sum := by decide
  have hdescent : baseEnd_6168720 < baseStart_6168720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168728 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6168728 : Nat := 118140960795 + 6168728 * 2 ^ 59
def prefixEnd_6168728 : Nat := 4983230072969 + 3 ^ 40 * 6168728 * 2
def baseEnd_6168728 : Nat := 3167522490848446057030543

theorem tailTrace_6168728 : CollatzResearch.WordTrace tailWord_6168728 prefixEnd_6168728 3167522490848446057030543 := by
  unfold tailWord_6168728
  simp only [CollatzResearch.WordTrace]
  refine ⟨112495996997879732855657419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149994662663839643807543225 112495996997879732855657419)
  ·
    refine ⟨168743995496819599283486129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112495996997879732855657419 168743995496819599283486129)
    ·
      refine ⟨126557996622614699462614597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168743995496819599283486129 126557996622614699462614597)
      ·
        refine ⟨23729624366740256149240237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126557996622614699462614597 23729624366740256149240237)
        ·
          refine ⟨8898609137527596055965089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23729624366740256149240237 8898609137527596055965089)
          ·
            refine ⟨6673956853145697041973817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8898609137527596055965089 6673956853145697041973817)
            ·
              refine ⟨5005467639859272781480363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6673956853145697041973817 5005467639859272781480363)
              ·
                refine ⟨7508201459788909172220545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005467639859272781480363 7508201459788909172220545)
                ·
                  refine ⟨5631151094841681879165409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7508201459788909172220545 5631151094841681879165409)
                  ·
                    refine ⟨4223363321131261409374057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5631151094841681879165409 4223363321131261409374057)
                    ·
                      refine ⟨3167522490848446057030543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223363321131261409374057 3167522490848446057030543)
                      ·
                        rfl

theorem cell23_6168728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6168728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168728 prefixEnd_6168728 := by exact prefixLift 6168728
  have htrace : WordTrace (prefixWord ++ tailWord_6168728) baseStart_6168728 baseEnd_6168728 := by
    simpa [prefixWord, tailWord_6168728, baseEnd_6168728] using wordTrace_append hprefix tailTrace_6168728
  have hstable : (prefixWord ++ tailWord_6168728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168728).length < 2 ^ (prefixWord ++ tailWord_6168728).sum := by decide
  have hdescent : baseEnd_6168728 < baseStart_6168728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168763 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6]
def baseStart_6168763 : Nat := 118140960795 + 6168763 * 2 ^ 59
def prefixEnd_6168763 : Nat := 4983230072969 + 3 ^ 40 * 6168763 * 2
def baseEnd_6168763 : Nat := 3167540462671353420092881

theorem tailTrace_6168763 : CollatzResearch.WordTrace tailWord_6168763 prefixEnd_6168763 3167540462671353420092881 := by
  unfold tailWord_6168763
  simp only [CollatzResearch.WordTrace]
  refine ⟨224993270550632666688838943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149995513700421777792559295 224993270550632666688838943)
  ·
    refine ⟨337489905825949000033258415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224993270550632666688838943 337489905825949000033258415)
    ·
      refine ⟨506234858738923500049887623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337489905825949000033258415 506234858738923500049887623)
      ·
        refine ⟨759352288108385250074831435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506234858738923500049887623 759352288108385250074831435)
        ·
          refine ⟨1139028432162577875112247153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759352288108385250074831435 1139028432162577875112247153)
          ·
            refine ⟨854271324121933406334185365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139028432162577875112247153 854271324121933406334185365)
            ·
              refine ⟨40043968318215628421914939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 854271324121933406334185365 40043968318215628421914939)
              ·
                refine ⟨60065952477323442632872409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40043968318215628421914939 60065952477323442632872409)
                ·
                  refine ⟨45049464357992581974654307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60065952477323442632872409 45049464357992581974654307)
                  ·
                    refine ⟨67574196536988872961981461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45049464357992581974654307 67574196536988872961981461)
                    ·
                      refine ⟨3167540462671353420092881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67574196536988872961981461 3167540462671353420092881)
                      ·
                        rfl

theorem cell23_6168763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_6168763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168763 prefixEnd_6168763 := by exact prefixLift 6168763
  have htrace : WordTrace (prefixWord ++ tailWord_6168763) baseStart_6168763 baseEnd_6168763 := by
    simpa [prefixWord, tailWord_6168763, baseEnd_6168763] using wordTrace_append hprefix tailTrace_6168763
  have hstable : (prefixWord ++ tailWord_6168763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168763).length < 2 ^ (prefixWord ++ tailWord_6168763).sum := by decide
  have hdescent : baseEnd_6168763 < baseStart_6168763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168773 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 8]
def baseStart_6168773 : Nat := 118140960795 + 6168773 * 2 ^ 59
def prefixEnd_6168773 : Nat := 4983230072969 + 3 ^ 40 * 6168773 * 2
def baseEnd_6168773 : Nat := 351949510830877597885315

theorem tailTrace_6168773 : CollatzResearch.WordTrace tailWord_6168773 prefixEnd_6168773 351949510830877597885315 := by
  unfold tailWord_6168773
  simp only [CollatzResearch.WordTrace]
  refine ⟨224993635280596438396702973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149995756853730958931135315 224993635280596438396702973)
  ·
    refine ⟨84372613230223664398763615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224993635280596438396702973 84372613230223664398763615)
    ·
      refine ⟨126558919845335496598145423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84372613230223664398763615 126558919845335496598145423)
      ·
        refine ⟨189838379768003244897218135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126558919845335496598145423 189838379768003244897218135)
        ·
          refine ⟨284757569652004867345827203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189838379768003244897218135 284757569652004867345827203)
          ·
            refine ⟨427136354478007301018740805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284757569652004867345827203 427136354478007301018740805)
            ·
              refine ⟨80088066464626368941013901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 427136354478007301018740805 80088066464626368941013901)
              ·
                refine ⟨30033024924234888352880213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80088066464626368941013901 30033024924234888352880213)
                ·
                  refine ⟨351949510830877597885315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30033024924234888352880213 351949510830877597885315)
                  ·
                    rfl

theorem cell23_6168773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_6168773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168773 prefixEnd_6168773 := by exact prefixLift 6168773
  have htrace : WordTrace (prefixWord ++ tailWord_6168773) baseStart_6168773 baseEnd_6168773 := by
    simpa [prefixWord, tailWord_6168773, baseEnd_6168773] using wordTrace_append hprefix tailTrace_6168773
  have hstable : (prefixWord ++ tailWord_6168773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168773).length < 2 ^ (prefixWord ++ tailWord_6168773).sum := by decide
  have hdescent : baseEnd_6168773 < baseStart_6168773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168860 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_6168860 : Nat := 118140960795 + 6168860 * 2 ^ 59
def prefixEnd_6168860 : Nat := 4983230072969 + 3 ^ 40 * 6168860 * 2
def baseEnd_6168860 : Nat := 3167590270294839540579935

theorem tailTrace_6168860 : CollatzResearch.WordTrace tailWord_6168860 prefixEnd_6168860 3167590270294839540579935 := by
  unfold tailWord_6168860
  simp only [CollatzResearch.WordTrace]
  refine ⟨112498404215640626127560017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149997872287520834836746689 112498404215640626127560017)
  ·
    refine ⟨84373803161730469595670013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112498404215640626127560017 84373803161730469595670013)
    ·
      refine ⟨31640176185648926098376255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84373803161730469595670013 31640176185648926098376255)
      ·
        refine ⟨47460264278473389147564383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31640176185648926098376255 47460264278473389147564383)
        ·
          refine ⟨71190396417710083721346575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47460264278473389147564383 71190396417710083721346575)
          ·
            refine ⟨106785594626565125582019863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71190396417710083721346575 106785594626565125582019863)
            ·
              refine ⟨160178391939847688373029795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106785594626565125582019863 160178391939847688373029795)
              ·
                refine ⟨240267587909771532559544693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160178391939847688373029795 240267587909771532559544693)
                ·
                  refine ⟨22525086366541081177457315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240267587909771532559544693 22525086366541081177457315)
                  ·
                    refine ⟨33787629549811621766185973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22525086366541081177457315 33787629549811621766185973)
                    ·
                      refine ⟨3167590270294839540579935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33787629549811621766185973 3167590270294839540579935)
                      ·
                        rfl

theorem cell23_6168860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_6168860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168860 prefixEnd_6168860 := by exact prefixLift 6168860
  have htrace : WordTrace (prefixWord ++ tailWord_6168860) baseStart_6168860 baseEnd_6168860 := by
    simpa [prefixWord, tailWord_6168860, baseEnd_6168860] using wordTrace_append hprefix tailTrace_6168860
  have hstable : (prefixWord ++ tailWord_6168860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168860).length < 2 ^ (prefixWord ++ tailWord_6168860).sum := by decide
  have hdescent : baseEnd_6168860 < baseStart_6168860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168868 : List Nat := [2, 3, 1, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_6168868 : Nat := 118140960795 + 6168868 * 2 ^ 59
def prefixEnd_6168868 : Nat := 4983230072969 + 3 ^ 40 * 6168868 * 2
def baseEnd_6168868 : Nat := 3167594378140075509279899

theorem tailTrace_6168868 : CollatzResearch.WordTrace tailWord_6168868 prefixEnd_6168868 3167594378140075509279899 := by
  unfold tailWord_6168868
  simp only [CollatzResearch.WordTrace]
  refine ⟨112498550107626134810705629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149998066810168179747607505 112498550107626134810705629)
  ·
    refine ⟨42186956290359800554014611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112498550107626134810705629 42186956290359800554014611)
    ·
      refine ⟨63280434435539700831021917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42186956290359800554014611 63280434435539700831021917)
      ·
        refine ⟨23730162913327387811633219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63280434435539700831021917 23730162913327387811633219)
        ·
          refine ⟨35595244369991081717449829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23730162913327387811633219 35595244369991081717449829)
          ·
            refine ⟨6674108319373327822021843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35595244369991081717449829 6674108319373327822021843)
            ·
              refine ⟨10011162479059991733032765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674108319373327822021843 10011162479059991733032765)
              ·
                refine ⟨3754185929647496899887287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10011162479059991733032765 3754185929647496899887287)
                ·
                  refine ⟨5631278894471245349830931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754185929647496899887287 5631278894471245349830931)
                  ·
                    refine ⟨8446918341706868024746397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5631278894471245349830931 8446918341706868024746397)
                    ·
                      refine ⟨3167594378140075509279899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8446918341706868024746397 3167594378140075509279899)
                      ·
                        rfl

theorem cell23_6168868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_6168868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168868 prefixEnd_6168868 := by exact prefixLift 6168868
  have htrace : WordTrace (prefixWord ++ tailWord_6168868) baseStart_6168868 baseEnd_6168868 := by
    simpa [prefixWord, tailWord_6168868, baseEnd_6168868] using wordTrace_append hprefix tailTrace_6168868
  have hstable : (prefixWord ++ tailWord_6168868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168868).length < 2 ^ (prefixWord ++ tailWord_6168868).sum := by decide
  have hdescent : baseEnd_6168868 < baseStart_6168868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168878 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6168878 : Nat := 118140960795 + 6168878 * 2 ^ 59
def prefixEnd_6168878 : Nat := 4983230072969 + 3 ^ 40 * 6168878 * 2
def baseEnd_6168878 : Nat := 3167599512946620470154853

theorem tailTrace_6168878 : CollatzResearch.WordTrace tailWord_6168878 prefixEnd_6168878 3167599512946620470154853 := by
  unfold tailWord_6168878
  simp only [CollatzResearch.WordTrace]
  refine ⟨28124683118152005166159411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149998309963477360886183525 28124683118152005166159411)
  ·
    refine ⟨42187024677228007749239117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28124683118152005166159411 42187024677228007749239117)
    ·
      refine ⟨15820134253960502905964669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42187024677228007749239117 15820134253960502905964669)
      ·
        refine ⟨5932550345235188589736751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15820134253960502905964669 5932550345235188589736751)
        ·
          refine ⟨8898825517852782884605127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5932550345235188589736751 8898825517852782884605127)
          ·
            refine ⟨13348238276779174326907691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8898825517852782884605127 13348238276779174326907691)
            ·
              refine ⟨20022357415168761490361537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13348238276779174326907691 20022357415168761490361537)
              ·
                refine ⟨15016768061376571117771153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20022357415168761490361537 15016768061376571117771153)
                ·
                  refine ⟨11262576046032428338328365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15016768061376571117771153 11262576046032428338328365)
                  ·
                    refine ⟨4223466017262160626873137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11262576046032428338328365 4223466017262160626873137)
                    ·
                      refine ⟨3167599512946620470154853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223466017262160626873137 3167599512946620470154853)
                      ·
                        rfl

theorem cell23_6168878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6168878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168878 prefixEnd_6168878 := by exact prefixLift 6168878
  have htrace : WordTrace (prefixWord ++ tailWord_6168878) baseStart_6168878 baseEnd_6168878 := by
    simpa [prefixWord, tailWord_6168878, baseEnd_6168878] using wordTrace_append hprefix tailTrace_6168878
  have hstable : (prefixWord ++ tailWord_6168878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168878).length < 2 ^ (prefixWord ++ tailWord_6168878).sum := by decide
  have hdescent : baseEnd_6168878 < baseStart_6168878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168884 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_6168884 : Nat := 118140960795 + 6168884 * 2 ^ 59
def prefixEnd_6168884 : Nat := 4983230072969 + 3 ^ 40 * 6168884 * 2
def baseEnd_6168884 : Nat := 1055867531276849148893275

theorem tailTrace_6168884 : CollatzResearch.WordTrace tailWord_6168884 prefixEnd_6168884 1055867531276849148893275 := by
  unfold tailWord_6168884
  simp only [CollatzResearch.WordTrace]
  refine ⟨112498841891597152176996853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149998455855462869569329137 112498841891597152176996853)
  ·
    refine ⟨10546766427337233016593455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112498841891597152176996853 10546766427337233016593455)
    ·
      refine ⟨15820149641005849524890183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10546766427337233016593455 15820149641005849524890183)
      ·
        refine ⟨23730224461508774287335275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15820149641005849524890183 23730224461508774287335275)
        ·
          refine ⟨35595336692263161431002913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23730224461508774287335275 35595336692263161431002913)
          ·
            refine ⟨26696502519197371073252185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35595336692263161431002913 26696502519197371073252185)
            ·
              refine ⟨20022376889398028304939139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26696502519197371073252185 20022376889398028304939139)
              ·
                refine ⟨30033565334097042457408709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20022376889398028304939139 30033565334097042457408709)
                ·
                  refine ⟨5631293500143195460764133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30033565334097042457408709 5631293500143195460764133)
                  ·
                    refine ⟨1055867531276849148893275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631293500143195460764133 1055867531276849148893275)
                    ·
                      rfl

theorem cell23_6168884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_6168884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168884 prefixEnd_6168884 := by exact prefixLift 6168884
  have htrace : WordTrace (prefixWord ++ tailWord_6168884) baseStart_6168884 baseEnd_6168884 := by
    simpa [prefixWord, tailWord_6168884, baseEnd_6168884] using wordTrace_append hprefix tailTrace_6168884
  have hstable : (prefixWord ++ tailWord_6168884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168884).length < 2 ^ (prefixWord ++ tailWord_6168884).sum := by decide
  have hdescent : baseEnd_6168884 < baseStart_6168884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168907 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 3]
def baseStart_6168907 : Nat := 118140960795 + 6168907 * 2 ^ 59
def prefixEnd_6168907 : Nat := 4983230072969 + 3 ^ 40 * 6168907 * 2
def baseEnd_6168907 : Nat := 3167614403885600856692219

theorem tailTrace_6168907 : CollatzResearch.WordTrace tailWord_6168907 prefixEnd_6168907 3167614403885600856692219 := by
  unfold tailWord_6168907
  simp only [CollatzResearch.WordTrace]
  refine ⟨224998522662110979282080975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149999015108073986188053983 224998522662110979282080975)
  ·
    refine ⟨337497783993166468923121463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224998522662110979282080975 337497783993166468923121463)
    ·
      refine ⟨506246675989749703384682195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337497783993166468923121463 506246675989749703384682195)
      ·
        refine ⟨759370013984624555077023293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506246675989749703384682195 759370013984624555077023293)
        ·
          refine ⟨284763755244234208153883735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 759370013984624555077023293 284763755244234208153883735)
          ·
            refine ⟨427145632866351312230825603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284763755244234208153883735 427145632866351312230825603)
            ·
              refine ⟨640718449299526968346238405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427145632866351312230825603 640718449299526968346238405)
              ·
                refine ⟨120134709243661306564919701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 640718449299526968346238405 120134709243661306564919701)
                ·
                  refine ⟨5631314495796623745230611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120134709243661306564919701 5631314495796623745230611)
                  ·
                    refine ⟨8446971743694935617845917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5631314495796623745230611 8446971743694935617845917)
                    ·
                      refine ⟨3167614403885600856692219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8446971743694935617845917 3167614403885600856692219)
                      ·
                        rfl

theorem cell23_6168907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 3].length) (baseStart_6168907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168907 prefixEnd_6168907 := by exact prefixLift 6168907
  have htrace : WordTrace (prefixWord ++ tailWord_6168907) baseStart_6168907 baseEnd_6168907 := by
    simpa [prefixWord, tailWord_6168907, baseEnd_6168907] using wordTrace_append hprefix tailTrace_6168907
  have hstable : (prefixWord ++ tailWord_6168907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168907).length < 2 ^ (prefixWord ++ tailWord_6168907).sum := by decide
  have hdescent : baseEnd_6168907 < baseStart_6168907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168910 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_6168910 : Nat := 118140960795 + 6168910 * 2 ^ 59
def prefixEnd_6168910 : Nat := 4983230072969 + 3 ^ 40 * 6168910 * 2
def baseEnd_6168910 : Nat := 1055871981442521448318235

theorem tailTrace_6168910 : CollatzResearch.WordTrace tailWord_6168910 prefixEnd_6168910 1055871981442521448318235 := by
  unfold tailWord_6168910
  simp only [CollatzResearch.WordTrace]
  refine ⟨28124829010137513849305023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149999088054066740529626789 28124829010137513849305023)
  ·
    refine ⟨42187243515206270773957535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28124829010137513849305023 42187243515206270773957535)
    ·
      refine ⟨63280865272809406160936303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42187243515206270773957535 63280865272809406160936303)
      ·
        refine ⟨94921297909214109241404455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63280865272809406160936303 94921297909214109241404455)
        ·
          refine ⟨142381946863821163862106683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94921297909214109241404455 142381946863821163862106683)
          ·
            refine ⟨213572920295731745793160025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142381946863821163862106683 213572920295731745793160025)
            ·
              refine ⟨160179690221798809344870019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213572920295731745793160025 160179690221798809344870019)
              ·
                refine ⟨240269535332698214017305029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160179690221798809344870019 240269535332698214017305029)
                ·
                  refine ⟨45050537874880915128244693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240269535332698214017305029 45050537874880915128244693)
                  ·
                    refine ⟨1055871981442521448318235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45050537874880915128244693 1055871981442521448318235)
                    ·
                      rfl

theorem cell23_6168910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_6168910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168910 prefixEnd_6168910 := by exact prefixLift 6168910
  have htrace : WordTrace (prefixWord ++ tailWord_6168910) baseStart_6168910 baseEnd_6168910 := by
    simpa [prefixWord, tailWord_6168910, baseEnd_6168910] using wordTrace_append hprefix tailTrace_6168910
  have hstable : (prefixWord ++ tailWord_6168910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168910).length < 2 ^ (prefixWord ++ tailWord_6168910).sum := by decide
  have hdescent : baseEnd_6168910 < baseStart_6168910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168920 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_6168920 : Nat := 118140960795 + 6168920 * 2 ^ 59
def prefixEnd_6168920 : Nat := 4983230072969 + 3 ^ 40 * 6168920 * 2
def baseEnd_6168920 : Nat := 3167621079134109305829659

theorem tailTrace_6168920 : CollatzResearch.WordTrace tailWord_6168920 prefixEnd_6168920 3167621079134109305829659 := by
  unfold tailWord_6168920
  simp only [CollatzResearch.WordTrace]
  refine ⟨112499498405531941251152107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149999331207375921668202809 112499498405531941251152107)
  ·
    refine ⟨168749247608297911876728161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112499498405531941251152107 168749247608297911876728161)
    ·
      refine ⟨126561935706223433907546121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168749247608297911876728161 126561935706223433907546121)
      ·
        refine ⟨94921451779667575430659591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126561935706223433907546121 94921451779667575430659591)
        ·
          refine ⟨142382177669501363145989387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94921451779667575430659591 142382177669501363145989387)
          ·
            refine ⟨213573266504252044718984081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142382177669501363145989387 213573266504252044718984081)
            ·
              refine ⟨160179949878189033539238061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213573266504252044718984081 160179949878189033539238061)
              ·
                refine ⟨60067481204320887577214273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160179949878189033539238061 60067481204320887577214273)
                ·
                  refine ⟨45050610903240665682910705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60067481204320887577214273 45050610903240665682910705)
                  ·
                    refine ⟨33787958177430499262183029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45050610903240665682910705 33787958177430499262183029)
                    ·
                      refine ⟨3167621079134109305829659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33787958177430499262183029 3167621079134109305829659)
                      ·
                        rfl

theorem cell23_6168920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_6168920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168920 prefixEnd_6168920 := by exact prefixLift 6168920
  have htrace : WordTrace (prefixWord ++ tailWord_6168920) baseStart_6168920 baseEnd_6168920 := by
    simpa [prefixWord, tailWord_6168920, baseEnd_6168920] using wordTrace_append hprefix tailTrace_6168920
  have hstable : (prefixWord ++ tailWord_6168920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168920).length < 2 ^ (prefixWord ++ tailWord_6168920).sum := by decide
  have hdescent : baseEnd_6168920 < baseStart_6168920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168941 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_6168941 : Nat := 118140960795 + 6168941 * 2 ^ 59
def prefixEnd_6168941 : Nat := 4983230072969 + 3 ^ 40 * 6168941 * 2
def baseEnd_6168941 : Nat := 3167631862227853723667063

theorem tailTrace_6168941 : CollatzResearch.WordTrace tailWord_6168941 prefixEnd_6168941 3167631862227853723667063 := by
  unfold tailWord_6168941
  simp only [CollatzResearch.WordTrace]
  refine ⟨224999762743987803088818677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149999841829325202059212451 224999762743987803088818677)
  ·
    refine ⟨21093727757248856539576751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224999762743987803088818677 21093727757248856539576751)
    ·
      refine ⟨31640591635873284809365127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21093727757248856539576751 31640591635873284809365127)
      ·
        refine ⟨47460887453809927214047691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31640591635873284809365127 47460887453809927214047691)
        ·
          refine ⟨71191331180714890821071537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47460887453809927214047691 71191331180714890821071537)
          ·
            refine ⟨53393498385536168115803653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71191331180714890821071537 53393498385536168115803653)
            ·
              refine ⟨10011280947288031521713185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53393498385536168115803653 10011280947288031521713185)
              ·
                refine ⟨7508460710466023641284889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10011280947288031521713185 7508460710466023641284889)
                ·
                  refine ⟨5631345532849517730963667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7508460710466023641284889 5631345532849517730963667)
                  ·
                    refine ⟨8447018299274276596445501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5631345532849517730963667 8447018299274276596445501)
                    ·
                      refine ⟨3167631862227853723667063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447018299274276596445501 3167631862227853723667063)
                      ·
                        rfl

theorem cell23_6168941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_6168941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168941 prefixEnd_6168941 := by exact prefixLift 6168941
  have htrace : WordTrace (prefixWord ++ tailWord_6168941) baseStart_6168941 baseEnd_6168941 := by
    simpa [prefixWord, tailWord_6168941, baseEnd_6168941] using wordTrace_append hprefix tailTrace_6168941
  have hstable : (prefixWord ++ tailWord_6168941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168941).length < 2 ^ (prefixWord ++ tailWord_6168941).sum := by decide
  have hdescent : baseEnd_6168941 < baseStart_6168941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168957 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 2, 6]
def baseStart_6168957 : Nat := 118140960795 + 6168957 * 2 ^ 59
def prefixEnd_6168957 : Nat := 4983230072969 + 3 ^ 40 * 6168957 * 2
def baseEnd_6168957 : Nat := 1055880025972775220355663

theorem tailTrace_6168957 : CollatzResearch.WordTrace tailWord_6168957 prefixEnd_6168957 1055880025972775220355663 := by
  unfold tailWord_6168957
  simp only [CollatzResearch.WordTrace]
  refine ⟨225000346311929837821401125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150000230874619891880934083 225000346311929837821401125)
  ·
    refine ⟨42187564933486844591512711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225000346311929837821401125 42187564933486844591512711)
    ·
      refine ⟨63281347400230266887269067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42187564933486844591512711 63281347400230266887269067)
      ·
        refine ⟨94922021100345400330903601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63281347400230266887269067 94922021100345400330903601)
        ·
          refine ⟨71191515825259050248177701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94922021100345400330903601 71191515825259050248177701)
          ·
            refine ⟨13348409217236071921533319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71191515825259050248177701 13348409217236071921533319)
            ·
              refine ⟨20022613825854107882299979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13348409217236071921533319 20022613825854107882299979)
              ·
                refine ⟨30033920738781161823449969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20022613825854107882299979 30033920738781161823449969)
                ·
                  refine ⟨22525440554085871367587477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30033920738781161823449969 22525440554085871367587477)
                  ·
                    refine ⟨1055880025972775220355663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22525440554085871367587477 1055880025972775220355663)
                    ·
                      rfl

theorem cell23_6168957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_6168957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168957 prefixEnd_6168957 := by exact prefixLift 6168957
  have htrace : WordTrace (prefixWord ++ tailWord_6168957) baseStart_6168957 baseEnd_6168957 := by
    simpa [prefixWord, tailWord_6168957, baseEnd_6168957] using wordTrace_append hprefix tailTrace_6168957
  have hstable : (prefixWord ++ tailWord_6168957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168957).length < 2 ^ (prefixWord ++ tailWord_6168957).sum := by decide
  have hdescent : baseEnd_6168957 < baseStart_6168957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168967 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_6168967 : Nat := 118140960795 + 6168967 * 2 ^ 59
def prefixEnd_6168967 : Nat := 4983230072969 + 3 ^ 40 * 6168967 * 2
def baseEnd_6168967 : Nat := 3167645212724870621941943

theorem tailTrace_6168967 : CollatzResearch.WordTrace tailWord_6168967 prefixEnd_6168967 3167645212724870621941943 := by
  unfold tailWord_6168967
  simp only [CollatzResearch.WordTrace]
  refine ⟨225000711041893609529265155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150000474027929073019510103 225000711041893609529265155)
  ·
    refine ⟨337501066562840414293897733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225000711041893609529265155 337501066562840414293897733)
    ·
      refine ⟨63281449980532577680105825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337501066562840414293897733 63281449980532577680105825)
      ·
        refine ⟨47461087485399433260079369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63281449980532577680105825 47461087485399433260079369)
        ·
          refine ⟨35595815614049574945059527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47461087485399433260079369 35595815614049574945059527)
          ·
            refine ⟨53393723421074362417589291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35595815614049574945059527 53393723421074362417589291)
            ·
              refine ⟨80090585131611543626383937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53393723421074362417589291 80090585131611543626383937)
              ·
                refine ⟨60067938848708657719787953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80090585131611543626383937 60067938848708657719787953)
                ·
                  refine ⟨45050954136531493289840965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60067938848708657719787953 45050954136531493289840965)
                  ·
                    refine ⟨8447053900599654991845181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45050954136531493289840965 8447053900599654991845181)
                    ·
                      refine ⟨3167645212724870621941943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447053900599654991845181 3167645212724870621941943)
                      ·
                        rfl

theorem cell23_6168967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_6168967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168967 prefixEnd_6168967 := by exact prefixLift 6168967
  have htrace : WordTrace (prefixWord ++ tailWord_6168967) baseStart_6168967 baseEnd_6168967 := by
    simpa [prefixWord, tailWord_6168967, baseEnd_6168967] using wordTrace_append hprefix tailTrace_6168967
  have hstable : (prefixWord ++ tailWord_6168967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168967).length < 2 ^ (prefixWord ++ tailWord_6168967).sum := by decide
  have hdescent : baseEnd_6168967 < baseStart_6168967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6168997 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_6168997 : Nat := 118140960795 + 6168997 * 2 ^ 59
def prefixEnd_6168997 : Nat := 4983230072969 + 3 ^ 40 * 6168997 * 2
def baseEnd_6168997 : Nat := 3167660617144505504566805

theorem tailTrace_6168997 : CollatzResearch.WordTrace tailWord_6168997 prefixEnd_6168997 3167660617144505504566805 := by
  unfold tailWord_6168997
  simp only [CollatzResearch.WordTrace]
  refine ⟨225001805231784924652857245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150001203487856616435238163 225001805231784924652857245)
  ·
    refine ⟨84375676961919346744821467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225001805231784924652857245 84375676961919346744821467)
    ·
      refine ⟨126563515442879020117232201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84375676961919346744821467 126563515442879020117232201)
      ·
        refine ⟨94922636582159265087924151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126563515442879020117232201 94922636582159265087924151)
        ·
          refine ⟨142383954873238897631886227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94922636582159265087924151 142383954873238897631886227)
          ·
            refine ⟨213575932309858346447829341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142383954873238897631886227 213575932309858346447829341)
            ·
              refine ⟨80090974616196879917936003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213575932309858346447829341 80090974616196879917936003)
              ·
                refine ⟨120136461924295319876904005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80090974616196879917936003 120136461924295319876904005)
                ·
                  refine ⟨22525586610805372476919501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120136461924295319876904005 22525586610805372476919501)
                  ·
                    refine ⟨8447094979052014678844813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22525586610805372476919501 8447094979052014678844813)
                    ·
                      refine ⟨3167660617144505504566805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447094979052014678844813 3167660617144505504566805)
                      ·
                        rfl

theorem cell23_6168997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_6168997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6168997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6168997 prefixEnd_6168997 := by exact prefixLift 6168997
  have htrace : WordTrace (prefixWord ++ tailWord_6168997) baseStart_6168997 baseEnd_6168997 := by
    simpa [prefixWord, tailWord_6168997, baseEnd_6168997] using wordTrace_append hprefix tailTrace_6168997
  have hstable : (prefixWord ++ tailWord_6168997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6168997).length < 2 ^ (prefixWord ++ tailWord_6168997).sum := by decide
  have hdescent : baseEnd_6168997 < baseStart_6168997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6168997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169017 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 1, 7]
def baseStart_6169017 : Nat := 118140960795 + 6169017 * 2 ^ 59
def prefixEnd_6169017 : Nat := 4983230072969 + 3 ^ 40 * 6169017 * 2
def baseEnd_6169017 : Nat := 1055890295585865142105571

theorem tailTrace_6169017 : CollatzResearch.WordTrace tailWord_6169017 prefixEnd_6169017 1055890295585865142105571 := by
  unfold tailWord_6169017
  simp only [CollatzResearch.WordTrace]
  refine ⟨225002534691712468068585305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150001689794474978712390203 225002534691712468068585305)
  ·
    refine ⟨168751901018784351051438979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225002534691712468068585305 168751901018784351051438979)
    ·
      refine ⟨253127851528176526577158469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168751901018784351051438979 253127851528176526577158469)
      ·
        refine ⟨47461472161533098733217213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253127851528176526577158469 47461472161533098733217213)
        ·
          refine ⟨17798052060574912024956455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47461472161533098733217213 17798052060574912024956455)
          ·
            refine ⟨26697078090862368037434683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17798052060574912024956455 26697078090862368037434683)
            ·
              refine ⟨40045617136293552056152025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26697078090862368037434683 40045617136293552056152025)
              ·
                refine ⟨30034212852220164042114019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40045617136293552056152025 30034212852220164042114019)
                ·
                  refine ⟨45051319278330246063171029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30034212852220164042114019 45051319278330246063171029)
                  ·
                    refine ⟨1055890295585865142105571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45051319278330246063171029 1055890295585865142105571)
                    ·
                      rfl

theorem cell23_6169017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_6169017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169017 prefixEnd_6169017 := by exact prefixLift 6169017
  have htrace : WordTrace (prefixWord ++ tailWord_6169017) baseStart_6169017 baseEnd_6169017 := by
    simpa [prefixWord, tailWord_6169017, baseEnd_6169017] using wordTrace_append hprefix tailTrace_6169017
  have hstable : (prefixWord ++ tailWord_6169017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169017).length < 2 ^ (prefixWord ++ tailWord_6169017).sum := by decide
  have hdescent : baseEnd_6169017 < baseStart_6169017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169108 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6169108 : Nat := 118140960795 + 6169108 * 2 ^ 59
def prefixEnd_6169108 : Nat := 4983230072969 + 3 ^ 40 * 6169108 * 2
def baseEnd_6169108 : Nat := 3167717613497154570278795

theorem tailTrace_6169108 : CollatzResearch.WordTrace tailWord_6169108 prefixEnd_6169108 3167717613497154570278795 := by
  unfold tailWord_6169108
  simp only [CollatzResearch.WordTrace]
  refine ⟨112502926867191395305073989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150003902489588527073431985 112502926867191395305073989)
  ·
    refine ⟨21094298787598386619701373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112502926867191395305073989 21094298787598386619701373)
    ·
      refine ⟨7910362045349394982388015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21094298787598386619701373 7910362045349394982388015)
      ·
        refine ⟨11865543068024092473582023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7910362045349394982388015 11865543068024092473582023)
        ·
          refine ⟨17798314602036138710373035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11865543068024092473582023 17798314602036138710373035)
          ·
            refine ⟨26697471903054208065559553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17798314602036138710373035 26697471903054208065559553)
            ·
              refine ⟨20023103927290656049169665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26697471903054208065559553 20023103927290656049169665)
              ·
                refine ⟨15017327945467992036877249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20023103927290656049169665 15017327945467992036877249)
                ·
                  refine ⟨11262995959100994027657937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15017327945467992036877249 11262995959100994027657937)
                  ·
                    refine ⟨8447246969325745520743453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11262995959100994027657937 8447246969325745520743453)
                    ·
                      refine ⟨3167717613497154570278795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447246969325745520743453 3167717613497154570278795)
                      ·
                        rfl

theorem cell23_6169108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6169108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169108 prefixEnd_6169108 := by exact prefixLift 6169108
  have htrace : WordTrace (prefixWord ++ tailWord_6169108) baseStart_6169108 baseEnd_6169108 := by
    simpa [prefixWord, tailWord_6169108, baseEnd_6169108] using wordTrace_append hprefix tailTrace_6169108
  have hstable : (prefixWord ++ tailWord_6169108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169108).length < 2 ^ (prefixWord ++ tailWord_6169108).sum := by decide
  have hdescent : baseEnd_6169108 < baseStart_6169108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169121 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_6169121 : Nat := 118140960795 + 6169121 * 2 ^ 59
def prefixEnd_6169121 : Nat := 4983230072969 + 3 ^ 40 * 6169121 * 2
def baseEnd_6169121 : Nat := 3167724288745663019416235

theorem tailTrace_6169121 : CollatzResearch.WordTrace tailWord_6169121 prefixEnd_6169121 3167724288745663019416235 := by
  unfold tailWord_6169121
  simp only [CollatzResearch.WordTrace]
  refine ⟨225006327883335693830371217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150004218588890462553580811 225006327883335693830371217)
  ·
    refine ⟨168754745912501770372778413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225006327883335693830371217 168754745912501770372778413)
    ·
      refine ⟨63283029717188163889791905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168754745912501770372778413 63283029717188163889791905)
      ·
        refine ⟨47462272287891122917343929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63283029717188163889791905 47462272287891122917343929)
        ·
          refine ⟨35596704215918342188007947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47462272287891122917343929 35596704215918342188007947)
          ·
            refine ⟨53395056323877513282011921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35596704215918342188007947 53395056323877513282011921)
            ·
              refine ⟨40046292242908134961508941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53395056323877513282011921 40046292242908134961508941)
              ·
                refine ⟨15017359591090550610565853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40046292242908134961508941 15017359591090550610565853)
                ·
                  refine ⟨5631509846658956478962195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15017359591090550610565853 5631509846658956478962195)
                  ·
                    refine ⟨8447264769988434718443293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5631509846658956478962195 8447264769988434718443293)
                    ·
                      refine ⟨3167724288745663019416235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447264769988434718443293 3167724288745663019416235)
                      ·
                        rfl

theorem cell23_6169121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_6169121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169121 prefixEnd_6169121 := by exact prefixLift 6169121
  have htrace : WordTrace (prefixWord ++ tailWord_6169121) baseStart_6169121 baseEnd_6169121 := by
    simpa [prefixWord, tailWord_6169121, baseEnd_6169121] using wordTrace_append hprefix tailTrace_6169121
  have hstable : (prefixWord ++ tailWord_6169121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169121).length < 2 ^ (prefixWord ++ tailWord_6169121).sum := by decide
  have hdescent : baseEnd_6169121 < baseStart_6169121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169144 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_6169144 : Nat := 118140960795 + 6169144 * 2 ^ 59
def prefixEnd_6169144 : Nat := 4983230072969 + 3 ^ 40 * 6169144 * 2
def baseEnd_6169144 : Nat := 3167736098800716429428629

theorem tailTrace_6169144 : CollatzResearch.WordTrace tailWord_6169144 prefixEnd_6169144 3167736098800716429428629 := by
  unfold tailWord_6169144
  simp only [CollatzResearch.WordTrace]
  refine ⟨112503583381126184379229243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150004777841501579172305657 112503583381126184379229243)
  ·
    refine ⟨168755375071689276568843865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112503583381126184379229243 168755375071689276568843865)
    ·
      refine ⟨126566531303766957426632899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168755375071689276568843865 126566531303766957426632899)
      ·
        refine ⟨189849796955650436139949349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126566531303766957426632899 189849796955650436139949349)
        ·
          refine ⟨35596836929184456776240503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189849796955650436139949349 35596836929184456776240503)
          ·
            refine ⟨53395255393776685164360755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35596836929184456776240503 53395255393776685164360755)
            ·
              refine ⟨80092883090665027746541133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53395255393776685164360755 80092883090665027746541133)
              ·
                refine ⟨30034831158999385404952925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80092883090665027746541133 30034831158999385404952925)
                ·
                  refine ⟨11263061684624769526857347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30034831158999385404952925 11263061684624769526857347)
                  ·
                    refine ⟨16894592526937154290286021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11263061684624769526857347 16894592526937154290286021)
                    ·
                      refine ⟨3167736098800716429428629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16894592526937154290286021 3167736098800716429428629)
                      ·
                        rfl

theorem cell23_6169144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_6169144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169144 prefixEnd_6169144 := by exact prefixLift 6169144
  have htrace : WordTrace (prefixWord ++ tailWord_6169144) baseStart_6169144 baseEnd_6169144 := by
    simpa [prefixWord, tailWord_6169144, baseEnd_6169144] using wordTrace_append hprefix tailTrace_6169144
  have hstable : (prefixWord ++ tailWord_6169144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169144).length < 2 ^ (prefixWord ++ tailWord_6169144).sum := by decide
  have hdescent : baseEnd_6169144 < baseStart_6169144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169148 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_6169148 : Nat := 118140960795 + 6169148 * 2 ^ 59
def prefixEnd_6169148 : Nat := 4983230072969 + 3 ^ 40 * 6169148 * 2
def baseEnd_6169148 : Nat := 3167738152723334413778611

theorem tailTrace_6169148 : CollatzResearch.WordTrace tailWord_6169148 prefixEnd_6169148 3167738152723334413778611 := by
  unfold tailWord_6169148
  simp only [CollatzResearch.WordTrace]
  refine ⟨112503656327118938720802049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150004875102825251627736065 112503656327118938720802049)
  ·
    refine ⟨84377742245339204040601537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112503656327118938720802049 84377742245339204040601537)
    ·
      refine ⟨63283306684004403030451153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84377742245339204040601537 63283306684004403030451153)
      ·
        refine ⟨47462480013003302272838365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63283306684004403030451153 47462480013003302272838365)
        ·
          refine ⟨17798430004876238352314387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47462480013003302272838365 17798430004876238352314387)
          ·
            refine ⟨26697645007314357528471581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17798430004876238352314387 26697645007314357528471581)
            ·
              refine ⟨10011616877742884073176843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26697645007314357528471581 10011616877742884073176843)
              ·
                refine ⟨15017425316614326109765265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10011616877742884073176843 15017425316614326109765265)
                ·
                  refine ⟨11263068987460744582323949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15017425316614326109765265 11263068987460744582323949)
                  ·
                    refine ⟨4223650870297779218371481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11263068987460744582323949 4223650870297779218371481)
                    ·
                      refine ⟨3167738152723334413778611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223650870297779218371481 3167738152723334413778611)
                      ·
                        rfl

theorem cell23_6169148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_6169148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169148 prefixEnd_6169148 := by exact prefixLift 6169148
  have htrace : WordTrace (prefixWord ++ tailWord_6169148) baseStart_6169148 baseEnd_6169148 := by
    simpa [prefixWord, tailWord_6169148, baseEnd_6169148] using wordTrace_append hprefix tailTrace_6169148
  have hstable : (prefixWord ++ tailWord_6169148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169148).length < 2 ^ (prefixWord ++ tailWord_6169148).sum := by decide
  have hdescent : baseEnd_6169148 < baseStart_6169148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169164 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6169164 : Nat := 118140960795 + 6169164 * 2 ^ 59
def prefixEnd_6169164 : Nat := 4983230072969 + 3 ^ 40 * 6169164 * 2
def baseEnd_6169164 : Nat := 3167746368413806351178537

theorem tailTrace_6169164 : CollatzResearch.WordTrace tailWord_6169164 prefixEnd_6169164 3167746368413806351178537 := by
  unfold tailWord_6169164
  simp only [CollatzResearch.WordTrace]
  refine ⟨112503948111089956087093273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150005264148119941449457697 112503948111089956087093273)
  ·
    refine ⟨84377961083317467065319955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112503948111089956087093273 84377961083317467065319955)
    ·
      refine ⟨126566941624976200597979933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84377961083317467065319955 126566941624976200597979933)
      ·
        refine ⟨47462603109366075224242475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126566941624976200597979933 47462603109366075224242475)
        ·
          refine ⟨71193904664049112836363713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47462603109366075224242475 71193904664049112836363713)
          ·
            refine ⟨53395428498036834627272785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71193904664049112836363713 53395428498036834627272785)
            ·
              refine ⟨40046571373527625970454589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53395428498036834627272785 40046571373527625970454589)
              ·
                refine ⟨15017464265072859738920471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40046571373527625970454589 15017464265072859738920471)
                ·
                  refine ⟨22526196397609289608380707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15017464265072859738920471 22526196397609289608380707)
                  ·
                    refine ⟨33789294596413934412571061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22526196397609289608380707 33789294596413934412571061)
                    ·
                      refine ⟨3167746368413806351178537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33789294596413934412571061 3167746368413806351178537)
                      ·
                        rfl

theorem cell23_6169164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6169164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169164 prefixEnd_6169164 := by exact prefixLift 6169164
  have htrace : WordTrace (prefixWord ++ tailWord_6169164) baseStart_6169164 baseEnd_6169164 := by
    simpa [prefixWord, tailWord_6169164, baseEnd_6169164] using wordTrace_append hprefix tailTrace_6169164
  have hstable : (prefixWord ++ tailWord_6169164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169164).length < 2 ^ (prefixWord ++ tailWord_6169164).sum := by decide
  have hdescent : baseEnd_6169164 < baseStart_6169164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169177 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_6169177 : Nat := 118140960795 + 6169177 * 2 ^ 59
def prefixEnd_6169177 : Nat := 4983230072969 + 3 ^ 40 * 6169177 * 2
def baseEnd_6169177 : Nat := 3167753043662314800315977

theorem tailTrace_6169177 : CollatzResearch.WordTrace tailWord_6169177 prefixEnd_6169177 3167753043662314800315977 := by
  unfold tailWord_6169177
  simp only [CollatzResearch.WordTrace]
  refine ⟨225008370371132815394409785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150005580247421876929606523 225008370371132815394409785)
  ·
    refine ⟨168756277778349611545807339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225008370371132815394409785 168756277778349611545807339)
    ·
      refine ⟨253134416667524417318711009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168756277778349611545807339 253134416667524417318711009)
      ·
        refine ⟨189850812500643312989033257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253134416667524417318711009 189850812500643312989033257)
        ·
          refine ⟨142388109375482484741774943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189850812500643312989033257 142388109375482484741774943)
          ·
            refine ⟨213582164063223727112662415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142388109375482484741774943 213582164063223727112662415)
            ·
              refine ⟨320373246094835590668993623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213582164063223727112662415 320373246094835590668993623)
              ·
                refine ⟨480559869142253386003490435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320373246094835590668993623 480559869142253386003490435)
                ·
                  refine ⟨720839803713380079005235653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480559869142253386003490435 720839803713380079005235653)
                  ·
                    refine ⟨135157463196258764813481685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720839803713380079005235653 135157463196258764813481685)
                    ·
                      refine ⟨3167753043662314800315977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135157463196258764813481685 3167753043662314800315977)
                      ·
                        rfl

theorem cell23_6169177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_6169177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169177 prefixEnd_6169177 := by exact prefixLift 6169177
  have htrace : WordTrace (prefixWord ++ tailWord_6169177) baseStart_6169177 baseEnd_6169177 := by
    simpa [prefixWord, tailWord_6169177, baseEnd_6169177] using wordTrace_append hprefix tailTrace_6169177
  have hstable : (prefixWord ++ tailWord_6169177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169177).length < 2 ^ (prefixWord ++ tailWord_6169177).sum := by decide
  have hdescent : baseEnd_6169177 < baseStart_6169177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169188 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_6169188 : Nat := 118140960795 + 6169188 * 2 ^ 59
def prefixEnd_6169188 : Nat := 4983230072969 + 3 ^ 40 * 6169188 * 2
def baseEnd_6169188 : Nat := 1055919563983171419092809

theorem tailTrace_6169188 : CollatzResearch.WordTrace tailWord_6169188 prefixEnd_6169188 1055919563983171419092809 := by
  unfold tailWord_6169188
  simp only [CollatzResearch.WordTrace]
  refine ⟨112504385787046482136530109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150005847716061976182040145 112504385787046482136530109)
  ·
    refine ⟨42189144670142430801198791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112504385787046482136530109 42189144670142430801198791)
    ·
      refine ⟨63283717005213646201798187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42189144670142430801198791 63283717005213646201798187)
      ·
        refine ⟨94925575507820469302697281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63283717005213646201798187 94925575507820469302697281)
        ·
          refine ⟨71194181630865351977022961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94925575507820469302697281 71194181630865351977022961)
          ·
            refine ⟨53395636223149013982767221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71194181630865351977022961 53395636223149013982767221)
            ·
              refine ⟨5005840895920220060884427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53395636223149013982767221 5005840895920220060884427)
              ·
                refine ⟨7508761343880330091326641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005840895920220060884427 7508761343880330091326641)
                ·
                  refine ⟨5631571007910247568494981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7508761343880330091326641 5631571007910247568494981)
                  ·
                    refine ⟨1055919563983171419092809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631571007910247568494981 1055919563983171419092809)
                    ·
                      rfl

theorem cell23_6169188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_6169188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169188 prefixEnd_6169188 := by exact prefixLift 6169188
  have htrace : WordTrace (prefixWord ++ tailWord_6169188) baseStart_6169188 baseEnd_6169188 := by
    simpa [prefixWord, tailWord_6169188, baseEnd_6169188] using wordTrace_append hprefix tailTrace_6169188
  have hstable : (prefixWord ++ tailWord_6169188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169188).length < 2 ^ (prefixWord ++ tailWord_6169188).sum := by decide
  have hdescent : baseEnd_6169188 < baseStart_6169188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169198 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_6169198 : Nat := 118140960795 + 6169198 * 2 ^ 59
def prefixEnd_6169198 : Nat := 4983230072969 + 3 ^ 40 * 6169198 * 2
def baseEnd_6169198 : Nat := 3167763826756059218153381

theorem tailTrace_6169198 : CollatzResearch.WordTrace tailWord_6169198 prefixEnd_6169198 3167763826756059218153381 := by
  unfold tailWord_6169198
  simp only [CollatzResearch.WordTrace]
  refine ⟨28126142038007091997615531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150006090869371157320616165 28126142038007091997615531)
  ·
    refine ⟨42189213057010637996423297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28126142038007091997615531 42189213057010637996423297)
    ·
      refine ⟨31641909792757978497317473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42189213057010637996423297 31641909792757978497317473)
      ·
        refine ⟨23731432344568483872988105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31641909792757978497317473 23731432344568483872988105)
        ·
          refine ⟨17798574258426362904741079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23731432344568483872988105 17798574258426362904741079)
          ·
            refine ⟨26697861387639544357111619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17798574258426362904741079 26697861387639544357111619)
            ·
              refine ⟨40046792081459316535667429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26697861387639544357111619 40046792081459316535667429)
              ·
                refine ⟨7508773515273621850437643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40046792081459316535667429 7508773515273621850437643)
                ·
                  refine ⟨11263160272910432775656465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7508773515273621850437643 11263160272910432775656465)
                  ·
                    refine ⟨8447370204682824581742349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11263160272910432775656465 8447370204682824581742349)
                    ·
                      refine ⟨3167763826756059218153381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447370204682824581742349 3167763826756059218153381)
                      ·
                        rfl

theorem cell23_6169198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_6169198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169198 prefixEnd_6169198 := by exact prefixLift 6169198
  have htrace : WordTrace (prefixWord ++ tailWord_6169198) baseStart_6169198 baseEnd_6169198 := by
    simpa [prefixWord, tailWord_6169198, baseEnd_6169198] using wordTrace_append hprefix tailTrace_6169198
  have hstable : (prefixWord ++ tailWord_6169198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169198).length < 2 ^ (prefixWord ++ tailWord_6169198).sum := by decide
  have hdescent : baseEnd_6169198 < baseStart_6169198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169245 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_6169245 : Nat := 118140960795 + 6169245 * 2 ^ 59
def prefixEnd_6169245 : Nat := 4983230072969 + 3 ^ 40 * 6169245 * 2
def baseEnd_6169245 : Nat := 3167787960346820534265665

theorem tailTrace_6169245 : CollatzResearch.WordTrace tailWord_6169245 prefixEnd_6169245 3167787960346820534265665 := by
  unfold tailWord_6169245
  simp only [CollatzResearch.WordTrace]
  refine ⟨225010850534886463007885189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150007233689924308671923459 225010850534886463007885189)
  ·
    refine ⟨42189534475291211813978473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225010850534886463007885189 42189534475291211813978473)
    ·
      refine ⟨31642150856468408860483855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42189534475291211813978473 31642150856468408860483855)
      ·
        refine ⟨47463226284702613290725783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31642150856468408860483855 47463226284702613290725783)
        ·
          refine ⟨71194839427053919936088675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47463226284702613290725783 71194839427053919936088675)
          ·
            refine ⟨106792259140580879904133013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71194839427053919936088675 106792259140580879904133013)
            ·
              refine ⟨5005887147214728745506235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106792259140580879904133013 5005887147214728745506235)
              ·
                refine ⟨7508830720822093118259353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005887147214728745506235 7508830720822093118259353)
                ·
                  refine ⟨5631623040616569838694515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7508830720822093118259353 5631623040616569838694515)
                  ·
                    refine ⟨8447434560924854758041773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5631623040616569838694515 8447434560924854758041773)
                    ·
                      refine ⟨3167787960346820534265665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447434560924854758041773 3167787960346820534265665)
                      ·
                        rfl

theorem cell23_6169245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_6169245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169245 prefixEnd_6169245 := by exact prefixLift 6169245
  have htrace : WordTrace (prefixWord ++ tailWord_6169245) baseStart_6169245 baseEnd_6169245 := by
    simpa [prefixWord, tailWord_6169245, baseEnd_6169245] using wordTrace_append hprefix tailTrace_6169245
  have hstable : (prefixWord ++ tailWord_6169245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169245).length < 2 ^ (prefixWord ++ tailWord_6169245).sum := by decide
  have hdescent : baseEnd_6169245 < baseStart_6169245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169264 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_6169264 : Nat := 118140960795 + 6169264 * 2 ^ 59
def prefixEnd_6169264 : Nat := 4983230072969 + 3 ^ 40 * 6169264 * 2
def baseEnd_6169264 : Nat := 3167797716479255959928077

theorem tailTrace_6169264 : CollatzResearch.WordTrace tailWord_6169264 prefixEnd_6169264 3167797716479255959928077 := by
  unfold tailWord_6169264
  simp only [CollatzResearch.WordTrace]
  refine ⟨112505771760908814626413423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150007695681211752835217897 112505771760908814626413423)
  ·
    refine ⟨168758657641363221939620135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112505771760908814626413423 168758657641363221939620135)
    ·
      refine ⟨253137986462044832909430203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168758657641363221939620135 253137986462044832909430203)
      ·
        refine ⟨379706979693067249364145305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253137986462044832909430203 379706979693067249364145305)
        ·
          refine ⟨284780234769800437023108979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379706979693067249364145305 284780234769800437023108979)
          ·
            refine ⟨427170352154700655534663469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284780234769800437023108979 427170352154700655534663469)
            ·
              refine ⟨160188882058012745825498801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427170352154700655534663469 160188882058012745825498801)
              ·
                refine ⟨120141661543509559369124101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160188882058012745825498801 120141661543509559369124101)
                ·
                  refine ⟨22526561539408042381710769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120141661543509559369124101 22526561539408042381710769)
                  ·
                    refine ⟨16894921154556031786283077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22526561539408042381710769 16894921154556031786283077)
                    ·
                      refine ⟨3167797716479255959928077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16894921154556031786283077 3167797716479255959928077)
                      ·
                        rfl

theorem cell23_6169264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_6169264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169264 prefixEnd_6169264 := by exact prefixLift 6169264
  have htrace : WordTrace (prefixWord ++ tailWord_6169264) baseStart_6169264 baseEnd_6169264 := by
    simpa [prefixWord, tailWord_6169264, baseEnd_6169264] using wordTrace_append hprefix tailTrace_6169264
  have hstable : (prefixWord ++ tailWord_6169264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169264).length < 2 ^ (prefixWord ++ tailWord_6169264).sum := by decide
  have hdescent : baseEnd_6169264 < baseStart_6169264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169298 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_6169298 : Nat := 118140960795 + 6169298 * 2 ^ 59
def prefixEnd_6169298 : Nat := 4983230072969 + 3 ^ 40 * 6169298 * 2
def baseEnd_6169298 : Nat := 3167815174821508826902921

theorem tailTrace_6169298 : CollatzResearch.WordTrace tailWord_6169298 prefixEnd_6169298 3167815174821508826902921 := by
  unfold tailWord_6169298
  simp only [CollatzResearch.WordTrace]
  refine ⟨56253195900923613264891137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150008522402462968706376365 56253195900923613264891137)
  ·
    refine ⟨42189896925692709948668353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56253195900923613264891137 42189896925692709948668353)
    ·
      refine ⟨31642422694269532461501265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42189896925692709948668353 31642422694269532461501265)
      ·
        refine ⟨23731817020702149346125949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31642422694269532461501265 23731817020702149346125949)
        ·
          refine ⟨8899431382763306004797231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23731817020702149346125949 8899431382763306004797231)
          ·
            refine ⟨13349147074144959007195847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8899431382763306004797231 13349147074144959007195847)
            ·
              refine ⟨20023720611217438510793771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13349147074144959007195847 20023720611217438510793771)
              ·
                refine ⟨30035580916826157766190657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20023720611217438510793771 30035580916826157766190657)
                ·
                  refine ⟨22526685687619618324642993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30035580916826157766190657 22526685687619618324642993)
                  ·
                    refine ⟨16895014265714713743482245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22526685687619618324642993 16895014265714713743482245)
                    ·
                      refine ⟨3167815174821508826902921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16895014265714713743482245 3167815174821508826902921)
                      ·
                        rfl

theorem cell23_6169298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_6169298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169298 prefixEnd_6169298 := by exact prefixLift 6169298
  have htrace : WordTrace (prefixWord ++ tailWord_6169298) baseStart_6169298 baseEnd_6169298 := by
    simpa [prefixWord, tailWord_6169298, baseEnd_6169298] using wordTrace_append hprefix tailTrace_6169298
  have hstable : (prefixWord ++ tailWord_6169298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169298).length < 2 ^ (prefixWord ++ tailWord_6169298).sum := by decide
  have hdescent : baseEnd_6169298 < baseStart_6169298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169308 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 7]
def baseStart_6169308 : Nat := 118140960795 + 6169308 * 2 ^ 59
def prefixEnd_6169308 : Nat := 4983230072969 + 3 ^ 40 * 6169308 * 2
def baseEnd_6169308 : Nat := 351980034403117087530875

theorem tailTrace_6169308 : CollatzResearch.WordTrace tailWord_6169308 prefixEnd_6169308 351980034403117087530875 := by
  unfold tailWord_6169308
  simp only [CollatzResearch.WordTrace]
  refine ⟨112506574166829112383714289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150008765555772149844952385 112506574166829112383714289)
  ·
    refine ⟨84379930625121834287785717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112506574166829112383714289 84379930625121834287785717)
    ·
      refine ⟨7910618496105171964479911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84379930625121834287785717 7910618496105171964479911)
      ·
        refine ⟨11865927744157757946719867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7910618496105171964479911 11865927744157757946719867)
        ·
          refine ⟨17798891616236636920079801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11865927744157757946719867 17798891616236636920079801)
          ·
            refine ⟨13349168712177477690059851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17798891616236636920079801 13349168712177477690059851)
            ·
              refine ⟨20023753068266216535089777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13349168712177477690059851 20023753068266216535089777)
              ·
                refine ⟨15017814801199662401317333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20023753068266216535089777 15017814801199662401317333)
                ·
                  refine ⟨351980034403117087530875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15017814801199662401317333 351980034403117087530875)
                  ·
                    rfl

theorem cell23_6169308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_6169308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169308 prefixEnd_6169308 := by exact prefixLift 6169308
  have htrace : WordTrace (prefixWord ++ tailWord_6169308) baseStart_6169308 baseEnd_6169308 := by
    simpa [prefixWord, tailWord_6169308, baseEnd_6169308] using wordTrace_append hprefix tailTrace_6169308
  have hstable : (prefixWord ++ tailWord_6169308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169308).length < 2 ^ (prefixWord ++ tailWord_6169308).sum := by decide
  have hdescent : baseEnd_6169308 < baseStart_6169308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169321 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 2, 5]
def baseStart_6169321 : Nat := 118140960795 + 6169321 * 2 ^ 59
def prefixEnd_6169321 : Nat := 4983230072969 + 3 ^ 40 * 6169321 * 2
def baseEnd_6169321 : Nat := 1055942328292187412305105

theorem tailTrace_6169321 : CollatzResearch.WordTrace tailWord_6169321 prefixEnd_6169321 1055942328292187412305105 := by
  unfold tailWord_6169321
  simp only [CollatzResearch.WordTrace]
  refine ⟨225013622482611127987651817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150009081655074085325101211 225013622482611127987651817)
  ·
    refine ⟨168760216861958345990738863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225013622482611127987651817 168760216861958345990738863)
    ·
      refine ⟨253140325292937518986108295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168760216861958345990738863 253140325292937518986108295)
      ·
        refine ⟨379710487939406278479162443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253140325292937518986108295 379710487939406278479162443)
        ·
          refine ⟨569565731909109417718743665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379710487939406278479162443 569565731909109417718743665)
          ·
            refine ⟨427174298931832063289057749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569565731909109417718743665 427174298931832063289057749)
            ·
              refine ⟨10011897631214813983337291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 427174298931832063289057749 10011897631214813983337291)
              ·
                refine ⟨15017846446822220975005937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10011897631214813983337291 15017846446822220975005937)
                ·
                  refine ⟨11263384835116665731254453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15017846446822220975005937 11263384835116665731254453)
                  ·
                    refine ⟨1055942328292187412305105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11263384835116665731254453 1055942328292187412305105)
                    ·
                      rfl

theorem cell23_6169321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_6169321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169321 prefixEnd_6169321 := by exact prefixLift 6169321
  have htrace : WordTrace (prefixWord ++ tailWord_6169321) baseStart_6169321 baseEnd_6169321 := by
    simpa [prefixWord, tailWord_6169321, baseEnd_6169321] using wordTrace_append hprefix tailTrace_6169321
  have hstable : (prefixWord ++ tailWord_6169321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169321).length < 2 ^ (prefixWord ++ tailWord_6169321).sum := by decide
  have hdescent : baseEnd_6169321 < baseStart_6169321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169341 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_6169341 : Nat := 118140960795 + 6169341 * 2 ^ 59
def prefixEnd_6169341 : Nat := 4983230072969 + 3 ^ 40 * 6169341 * 2
def baseEnd_6169341 : Nat := 3167837254489652158665223

theorem tailTrace_6169341 : CollatzResearch.WordTrace tailWord_6169341 prefixEnd_6169341 3167837254489652158665223 := by
  unfold tailWord_6169341
  simp only [CollatzResearch.WordTrace]
  refine ⟨225014351942538671403379877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150009567961692447602253251 225014351942538671403379877)
  ·
    refine ⟨42190190989226000888133727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225014351942538671403379877 42190190989226000888133727)
    ·
      refine ⟨63285286483839001332200591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42190190989226000888133727 63285286483839001332200591)
      ·
        refine ⟨94927929725758501998300887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63285286483839001332200591 94927929725758501998300887)
        ·
          refine ⟨142391894588637752997451331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94927929725758501998300887 142391894588637752997451331)
          ·
            refine ⟨213587841882956629496176997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142391894588637752997451331 213587841882956629496176997)
            ·
              refine ⟨40047720353054368030533187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213587841882956629496176997 40047720353054368030533187)
              ·
                refine ⟨60071580529581552045799781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40047720353054368030533187 60071580529581552045799781)
                ·
                  refine ⟨11263421349296541008587459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60071580529581552045799781 11263421349296541008587459)
                  ·
                    refine ⟨16895132023944811512881189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11263421349296541008587459 16895132023944811512881189)
                    ·
                      refine ⟨3167837254489652158665223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16895132023944811512881189 3167837254489652158665223)
                      ·
                        rfl

theorem cell23_6169341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_6169341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169341 prefixEnd_6169341 := by exact prefixLift 6169341
  have htrace : WordTrace (prefixWord ++ tailWord_6169341) baseStart_6169341 baseEnd_6169341 := by
    simpa [prefixWord, tailWord_6169341, baseEnd_6169341] using wordTrace_append hprefix tailTrace_6169341
  have hstable : (prefixWord ++ tailWord_6169341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169341).length < 2 ^ (prefixWord ++ tailWord_6169341).sum := by decide
  have hdescent : baseEnd_6169341 < baseStart_6169341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169361 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_6169361 : Nat := 118140960795 + 6169361 * 2 ^ 59
def prefixEnd_6169361 : Nat := 4983230072969 + 3 ^ 40 * 6169361 * 2
def baseEnd_6169361 : Nat := 3167847524102742080415131

theorem tailTrace_6169361 : CollatzResearch.WordTrace tailWord_6169361 prefixEnd_6169361 3167847524102742080415131 := by
  unfold tailWord_6169361
  simp only [CollatzResearch.WordTrace]
  refine ⟨225015081402466214819107937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150010054268310809879405291 225015081402466214819107937)
  ·
    refine ⟨168761311051849661114330953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225015081402466214819107937 168761311051849661114330953)
    ·
      refine ⟨126570983288887245835748215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168761311051849661114330953 126570983288887245835748215)
      ·
        refine ⟨189856474933330868753622323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126570983288887245835748215 189856474933330868753622323)
        ·
          refine ⟨284784712399996303130433485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189856474933330868753622323 284784712399996303130433485)
          ·
            refine ⟨106794267149998613673912557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284784712399996303130433485 106794267149998613673912557)
            ·
              refine ⟨40047850181249480127717209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106794267149998613673912557 40047850181249480127717209)
              ·
                refine ⟨30035887635937110095787907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40047850181249480127717209 30035887635937110095787907)
                ·
                  refine ⟨45053831453905665143681861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30035887635937110095787907 45053831453905665143681861)
                  ·
                    refine ⟨8447593397607312214440349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45053831453905665143681861 8447593397607312214440349)
                    ·
                      refine ⟨3167847524102742080415131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447593397607312214440349 3167847524102742080415131)
                      ·
                        rfl

theorem cell23_6169361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_6169361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169361 prefixEnd_6169361 := by exact prefixLift 6169361
  have htrace : WordTrace (prefixWord ++ tailWord_6169361) baseStart_6169361 baseEnd_6169361 := by
    simpa [prefixWord, tailWord_6169361, baseEnd_6169361] using wordTrace_append hprefix tailTrace_6169361
  have hstable : (prefixWord ++ tailWord_6169361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169361).length < 2 ^ (prefixWord ++ tailWord_6169361).sum := by decide
  have hdescent : baseEnd_6169361 < baseStart_6169361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169378 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_6169378 : Nat := 118140960795 + 6169378 * 2 ^ 59
def prefixEnd_6169378 : Nat := 4983230072969 + 3 ^ 40 * 6169378 * 2
def baseEnd_6169378 : Nat := 3167856253273868513902553

theorem tailTrace_6169378 : CollatzResearch.WordTrace tailWord_6169378 prefixEnd_6169378 3167856253273868513902553 := by
  unfold tailWord_6169378
  simp only [CollatzResearch.WordTrace]
  refine ⟨56253925360851156680619197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150010467628936417814984525 56253925360851156680619197)
  ·
    refine ⟨21095222010319183755232199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56253925360851156680619197 21095222010319183755232199)
    ·
      refine ⟨31642833015478775632848299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21095222010319183755232199 31642833015478775632848299)
      ·
        refine ⟨47464249523218163449272449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31642833015478775632848299 47464249523218163449272449)
        ·
          refine ⟨35598187142413622586954337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47464249523218163449272449 35598187142413622586954337)
          ·
            refine ⟨26698640356810216940215753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35598187142413622586954337 26698640356810216940215753)
            ·
              refine ⟨20023980267607662705161815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26698640356810216940215753 20023980267607662705161815)
              ·
                refine ⟨30035970401411494057742723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20023980267607662705161815 30035970401411494057742723)
                ·
                  refine ⟨45053955602117241086614085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30035970401411494057742723 45053955602117241086614085)
                  ·
                    refine ⟨8447616675396982703740141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45053955602117241086614085 8447616675396982703740141)
                    ·
                      refine ⟨3167856253273868513902553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8447616675396982703740141 3167856253273868513902553)
                      ·
                        rfl

theorem cell23_6169378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_6169378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169378 prefixEnd_6169378 := by exact prefixLift 6169378
  have htrace : WordTrace (prefixWord ++ tailWord_6169378) baseStart_6169378 baseEnd_6169378 := by
    simpa [prefixWord, tailWord_6169378, baseEnd_6169378] using wordTrace_append hprefix tailTrace_6169378
  have hstable : (prefixWord ++ tailWord_6169378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169378).length < 2 ^ (prefixWord ++ tailWord_6169378).sum := by decide
  have hdescent : baseEnd_6169378 < baseStart_6169378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169402 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_6169402 : Nat := 118140960795 + 6169402 * 2 ^ 59
def prefixEnd_6169402 : Nat := 4983230072969 + 3 ^ 40 * 6169402 * 2
def baseEnd_6169402 : Nat := 1055956192269858806667481

theorem tailTrace_6169402 : CollatzResearch.WordTrace tailWord_6169402 prefixEnd_6169402 1055956192269858806667481 := by
  unfold tailWord_6169402
  simp only [CollatzResearch.WordTrace]
  refine ⟨56254144198829419705337615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150011051196878452547566973 56254144198829419705337615)
  ·
    refine ⟨84381216298244129558006423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56254144198829419705337615 84381216298244129558006423)
    ·
      refine ⟨126571824447366194337009635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84381216298244129558006423 126571824447366194337009635)
      ·
        refine ⟨189857736671049291505514453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126571824447366194337009635 189857736671049291505514453)
        ·
          refine ⟨4449790703227717769660495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189857736671049291505514453 4449790703227717769660495)
          ·
            refine ⟨6674686054841576654490743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449790703227717769660495 6674686054841576654490743)
            ·
              refine ⟨10012029082262364981736115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674686054841576654490743 10012029082262364981736115)
              ·
                refine ⟨15018043623393547472604173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10012029082262364981736115 15018043623393547472604173)
                ·
                  refine ⟨5631766358772580302226565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15018043623393547472604173 5631766358772580302226565)
                  ·
                    refine ⟨1055956192269858806667481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631766358772580302226565 1055956192269858806667481)
                    ·
                      rfl

theorem cell23_6169402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_6169402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169402 prefixEnd_6169402 := by exact prefixLift 6169402
  have htrace : WordTrace (prefixWord ++ tailWord_6169402) baseStart_6169402 baseEnd_6169402 := by
    simpa [prefixWord, tailWord_6169402, baseEnd_6169402] using wordTrace_append hprefix tailTrace_6169402
  have hstable : (prefixWord ++ tailWord_6169402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169402).length < 2 ^ (prefixWord ++ tailWord_6169402).sum := by decide
  have hdescent : baseEnd_6169402 < baseStart_6169402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169411 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 3, 5]
def baseStart_6169411 : Nat := 118140960795 + 6169411 * 2 ^ 59
def prefixEnd_6169411 : Nat := 4983230072969 + 3 ^ 40 * 6169411 * 2
def baseEnd_6169411 : Nat := 1055957732711822294929967

theorem tailTrace_6169411 : CollatzResearch.WordTrace tailWord_6169411 prefixEnd_6169411 1055957732711822294929967 := by
  unfold tailWord_6169411
  simp only [CollatzResearch.WordTrace]
  refine ⟨225016905052285073358428087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150011270034856715572285391 225016905052285073358428087)
  ·
    refine ⟨337525357578427610037642131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225016905052285073358428087 337525357578427610037642131)
    ·
      refine ⟨506288036367641415056463197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337525357578427610037642131 506288036367641415056463197)
      ·
        refine ⟨189858013637865530646173699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506288036367641415056463197 189858013637865530646173699)
        ·
          refine ⟨284787020456798295969260549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189858013637865530646173699 284787020456798295969260549)
          ·
            refine ⟨53397566335649680494236353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284787020456798295969260549 53397566335649680494236353)
            ·
              refine ⟨40048174751737260370677265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53397566335649680494236353 40048174751737260370677265)
              ·
                refine ⟨30036131063802945278007949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40048174751737260370677265 30036131063802945278007949)
                ·
                  refine ⟨11263549148926104479252981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30036131063802945278007949 11263549148926104479252981)
                  ·
                    refine ⟨1055957732711822294929967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11263549148926104479252981 1055957732711822294929967)
                    ·
                      rfl

theorem cell23_6169411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 5].length) (baseStart_6169411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169411 prefixEnd_6169411 := by exact prefixLift 6169411
  have htrace : WordTrace (prefixWord ++ tailWord_6169411) baseStart_6169411 baseEnd_6169411 := by
    simpa [prefixWord, tailWord_6169411, baseEnd_6169411] using wordTrace_append hprefix tailTrace_6169411
  have hstable : (prefixWord ++ tailWord_6169411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169411).length < 2 ^ (prefixWord ++ tailWord_6169411).sum := by decide
  have hdescent : baseEnd_6169411 < baseStart_6169411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169418 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_6169418 : Nat := 118140960795 + 6169418 * 2 ^ 59
def prefixEnd_6169418 : Nat := 4983230072969 + 3 ^ 40 * 6169418 * 2
def baseEnd_6169418 : Nat := 3167876792500048357402369

theorem tailTrace_6169418 : CollatzResearch.WordTrace tailWord_6169418 prefixEnd_6169418 3167876792500048357402369 := by
  unfold tailWord_6169418
  simp only [CollatzResearch.WordTrace]
  refine ⟨56254290090814928388483227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150011440242173142369288605 56254290090814928388483227)
  ·
    refine ⟨84381435136222392582724841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56254290090814928388483227 84381435136222392582724841)
    ·
      refine ⟨63286076352166794437043631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84381435136222392582724841 63286076352166794437043631)
      ·
        refine ⟨94929114528250191655565447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63286076352166794437043631 94929114528250191655565447)
        ·
          refine ⟨142393671792375287483348171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94929114528250191655565447 142393671792375287483348171)
          ·
            refine ⟨213590507688562931225022257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142393671792375287483348171 213590507688562931225022257)
            ·
              refine ⟨160192880766422198418766693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213590507688562931225022257 160192880766422198418766693)
              ·
                refine ⟨30036165143704162203518755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160192880766422198418766693 30036165143704162203518755)
                ·
                  refine ⟨45054247715556243305278133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30036165143704162203518755 45054247715556243305278133)
                  ·
                    refine ⟨4223835723333397809869825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45054247715556243305278133 4223835723333397809869825)
                    ·
                      refine ⟨3167876792500048357402369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223835723333397809869825 3167876792500048357402369)
                      ·
                        rfl

theorem cell23_6169418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_6169418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169418 prefixEnd_6169418 := by exact prefixLift 6169418
  have htrace : WordTrace (prefixWord ++ tailWord_6169418) baseStart_6169418 baseEnd_6169418 := by
    simpa [prefixWord, tailWord_6169418, baseEnd_6169418] using wordTrace_append hprefix tailTrace_6169418
  have hstable : (prefixWord ++ tailWord_6169418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169418).length < 2 ^ (prefixWord ++ tailWord_6169418).sum := by decide
  have hdescent : baseEnd_6169418 < baseStart_6169418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169458 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_6169458 : Nat := 118140960795 + 6169458 * 2 ^ 59
def prefixEnd_6169458 : Nat := 4983230072969 + 3 ^ 40 * 6169458 * 2
def baseEnd_6169458 : Nat := 1055965777242076066967395

theorem tailTrace_6169458 : CollatzResearch.WordTrace tailWord_6169458 prefixEnd_6169458 1055965777242076066967395 := by
  unfold tailWord_6169458
  simp only [CollatzResearch.WordTrace]
  refine ⟨56254654820778700096347257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150012412855409866923592685 56254654820778700096347257)
  ·
    refine ⟨42190991115584025072260443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56254654820778700096347257 42190991115584025072260443)
    ·
      refine ⟨63286486673376037608390665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42190991115584025072260443 63286486673376037608390665)
      ·
        refine ⟨47464865005032028206292999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63286486673376037608390665 47464865005032028206292999)
        ·
          refine ⟨71197297507548042309439499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47464865005032028206292999 71197297507548042309439499)
          ·
            refine ⟨106795946261322063464159249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71197297507548042309439499 106795946261322063464159249)
            ·
              refine ⟨80096959695991547598119437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106795946261322063464159249 80096959695991547598119437)
              ·
                refine ⟨30036359885996830349294789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80096959695991547598119437 30036359885996830349294789)
                ·
                  refine ⟨5631817478624405690492773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30036359885996830349294789 5631817478624405690492773)
                  ·
                    refine ⟨1055965777242076066967395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5631817478624405690492773 1055965777242076066967395)
                    ·
                      rfl

theorem cell23_6169458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_6169458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169458 prefixEnd_6169458 := by exact prefixLift 6169458
  have htrace : WordTrace (prefixWord ++ tailWord_6169458) baseStart_6169458 baseEnd_6169458 := by
    simpa [prefixWord, tailWord_6169458, baseEnd_6169458] using wordTrace_append hprefix tailTrace_6169458
  have hstable : (prefixWord ++ tailWord_6169458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169458).length < 2 ^ (prefixWord ++ tailWord_6169458).sum := by decide
  have hdescent : baseEnd_6169458 < baseStart_6169458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169471 : List Nat := [1, 1, 2, 2, 1, 1, 7, 8]
def baseStart_6169471 : Nat := 118140960795 + 6169471 * 2 ^ 59
def prefixEnd_6169471 : Nat := 4983230072969 + 3 ^ 40 * 6169471 * 2
def baseEnd_6169471 : Nat := 117329778036101357408875

theorem tailTrace_6169471 : CollatzResearch.WordTrace tailWord_6169471 prefixEnd_6169471 117329778036101357408875 := by
  unfold tailWord_6169471
  simp only [CollatzResearch.WordTrace]
  refine ⟨225019093432067703605612267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150012728954711802403741511 225019093432067703605612267)
  ·
    refine ⟨337528640148101555408418401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225019093432067703605612267 337528640148101555408418401)
    ·
      refine ⟨253146480111076166556313801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337528640148101555408418401 253146480111076166556313801)
      ·
        refine ⟨189859860083307124917235351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253146480111076166556313801 189859860083307124917235351)
        ·
          refine ⟨284789790124960687375853027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189859860083307124917235351 284789790124960687375853027)
          ·
            refine ⟨427184685187441031063779541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284789790124960687375853027 427184685187441031063779541)
            ·
              refine ⟨10012141059080649165557333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 427184685187441031063779541 10012141059080649165557333)
              ·
                refine ⟨117329778036101357408875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10012141059080649165557333 117329778036101357408875)
                ·
                  rfl

theorem cell23_6169471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 8].length) (baseStart_6169471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169471 prefixEnd_6169471 := by exact prefixLift 6169471
  have htrace : WordTrace (prefixWord ++ tailWord_6169471) baseStart_6169471 baseEnd_6169471 := by
    simpa [prefixWord, tailWord_6169471, baseEnd_6169471] using wordTrace_append hprefix tailTrace_6169471
  have hstable : (prefixWord ++ tailWord_6169471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169471).length < 2 ^ (prefixWord ++ tailWord_6169471).sum := by decide
  have hdescent : baseEnd_6169471 < baseStart_6169471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169482 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_6169482 : Nat := 118140960795 + 6169482 * 2 ^ 59
def prefixEnd_6169482 : Nat := 4983230072969 + 3 ^ 40 * 6169482 * 2
def baseEnd_6169482 : Nat := 3167909655261936107002075

theorem tailTrace_6169482 : CollatzResearch.WordTrace tailWord_6169482 prefixEnd_6169482 3167909655261936107002075 := by
  unfold tailWord_6169482
  simp only [CollatzResearch.WordTrace]
  refine ⟨56254873658756963121065675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150012996423351901656175133 56254873658756963121065675)
  ·
    refine ⟨84382310488135444681598513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56254873658756963121065675 84382310488135444681598513)
    ·
      refine ⟨63286732866101583511198885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84382310488135444681598513 63286732866101583511198885)
      ·
        refine ⟨11866262412394046908349791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63286732866101583511198885 11866262412394046908349791)
        ·
          refine ⟨17799393618591070362524687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11866262412394046908349791 17799393618591070362524687)
          ·
            refine ⟨26699090427886605543787031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17799393618591070362524687 26699090427886605543787031)
            ·
              refine ⟨40048635641829908315680547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26699090427886605543787031 40048635641829908315680547)
              ·
                refine ⟨60072953462744862473520821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40048635641829908315680547 60072953462744862473520821)
                ·
                  refine ⟨5631839387132330856892577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60072953462744862473520821 5631839387132330856892577)
                  ·
                    refine ⟨4223879540349248142669433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5631839387132330856892577 4223879540349248142669433)
                    ·
                      refine ⟨3167909655261936107002075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4223879540349248142669433 3167909655261936107002075)
                      ·
                        rfl

theorem cell23_6169482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_6169482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169482 prefixEnd_6169482 := by exact prefixLift 6169482
  have htrace : WordTrace (prefixWord ++ tailWord_6169482) baseStart_6169482 baseEnd_6169482 := by
    simpa [prefixWord, tailWord_6169482, baseEnd_6169482] using wordTrace_append hprefix tailTrace_6169482
  have hstable : (prefixWord ++ tailWord_6169482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169482).length < 2 ^ (prefixWord ++ tailWord_6169482).sum := by decide
  have hdescent : baseEnd_6169482 < baseStart_6169482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169526 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6169526 : Nat := 118140960795 + 6169526 * 2 ^ 59
def prefixEnd_6169526 : Nat := 4983230072969 + 3 ^ 40 * 6169526 * 2
def baseEnd_6169526 : Nat := 1055977416136911311617291

theorem tailTrace_6169526 : CollatzResearch.WordTrace tailWord_6169526 prefixEnd_6169526 1055977416136911311617291 := by
  unfold tailWord_6169526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14063818715429277999929027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150014066297912298665909621 14063818715429277999929027)
  ·
    refine ⟨21095728073143916999893541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14063818715429277999929027 21095728073143916999893541)
    ·
      refine ⟨3955449013714484437480039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21095728073143916999893541 3955449013714484437480039)
      ·
        refine ⟨5933173520571726656220059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3955449013714484437480039 5933173520571726656220059)
        ·
          refine ⟨8899760280857589984330089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5933173520571726656220059 8899760280857589984330089)
          ·
            refine ⟨6674820210643192488247567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8899760280857589984330089 6674820210643192488247567)
            ·
              refine ⟨10012230315964788732371351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674820210643192488247567 10012230315964788732371351)
              ·
                refine ⟨15018345473947183098557027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10012230315964788732371351 15018345473947183098557027)
                ·
                  refine ⟨22527518210920774647835541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15018345473947183098557027 22527518210920774647835541)
                  ·
                    refine ⟨1055977416136911311617291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22527518210920774647835541 1055977416136911311617291)
                    ·
                      rfl

theorem cell23_6169526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6169526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169526 prefixEnd_6169526 := by exact prefixLift 6169526
  have htrace : WordTrace (prefixWord ++ tailWord_6169526) baseStart_6169526 baseEnd_6169526 := by
    simpa [prefixWord, tailWord_6169526, baseEnd_6169526] using wordTrace_append hprefix tailTrace_6169526
  have hstable : (prefixWord ++ tailWord_6169526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169526).length < 2 ^ (prefixWord ++ tailWord_6169526).sum := by decide
  have hdescent : baseEnd_6169526 < baseStart_6169526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169531 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 6, 6]
def baseStart_6169531 : Nat := 118140960795 + 6169531 * 2 ^ 59
def prefixEnd_6169531 : Nat := 4983230072969 + 3 ^ 40 * 6169531 * 2
def baseEnd_6169531 : Nat := 1055978271938002138429783

theorem tailTrace_6169531 : CollatzResearch.WordTrace tailWord_6169531 prefixEnd_6169531 1055978271938002138429783 := by
  unfold tailWord_6169531
  simp only [CollatzResearch.WordTrace]
  refine ⟨225021281811850333852796447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150014187874566889235197631 225021281811850333852796447)
  ·
    refine ⟨337531922717775500779194671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225021281811850333852796447 337531922717775500779194671)
    ·
      refine ⟨506297884076663251168792007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337531922717775500779194671 506297884076663251168792007)
      ·
        refine ⟨759446826114994876753188011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506297884076663251168792007 759446826114994876753188011)
        ·
          refine ⟨1139170239172492315129782017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759446826114994876753188011 1139170239172492315129782017)
          ·
            refine ⟨854377679379369236347336513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139170239172492315129782017 854377679379369236347336513)
            ·
              refine ⟨640783259534526927260502385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854377679379369236347336513 640783259534526927260502385)
              ·
                refine ⟨480587444650895195445376789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640783259534526927260502385 480587444650895195445376789)
                ·
                  refine ⟨22527536468010712286502037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 480587444650895195445376789 22527536468010712286502037)
                  ·
                    refine ⟨1055978271938002138429783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22527536468010712286502037 1055978271938002138429783)
                    ·
                      rfl

theorem cell23_6169531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 6].length) (baseStart_6169531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169531 prefixEnd_6169531 := by exact prefixLift 6169531
  have htrace : WordTrace (prefixWord ++ tailWord_6169531) baseStart_6169531 baseEnd_6169531 := by
    simpa [prefixWord, tailWord_6169531, baseEnd_6169531] using wordTrace_append hprefix tailTrace_6169531
  have hstable : (prefixWord ++ tailWord_6169531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169531).length < 2 ^ (prefixWord ++ tailWord_6169531).sum := by decide
  have hdescent : baseEnd_6169531 < baseStart_6169531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169662 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_6169662 : Nat := 118140960795 + 6169662 * 2 ^ 59
def prefixEnd_6169662 : Nat := 4983230072969 + 3 ^ 40 * 6169662 * 2
def baseEnd_6169662 : Nat := 3168002081779745402751247

theorem tailTrace_6169662 : CollatzResearch.WordTrace tailWord_6169662 prefixEnd_6169662 3168002081779745402751247 := by
  unfold tailWord_6169662
  simp only [CollatzResearch.WordTrace]
  refine ⟨28128257471796967903226905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150017373182917162150543493 28128257471796967903226905)
  ·
    refine ⟨21096193103847725927420179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28128257471796967903226905 21096193103847725927420179)
    ·
      refine ⟨31644289655771588891130269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21096193103847725927420179 31644289655771588891130269)
      ·
        refine ⟨11866608620914345834173851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31644289655771588891130269 11866608620914345834173851)
        ·
          refine ⟨17799912931371518751260777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11866608620914345834173851 17799912931371518751260777)
          ·
            refine ⟨13349934698528639063445583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17799912931371518751260777 13349934698528639063445583)
            ·
              refine ⟨20024902047792958595168375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13349934698528639063445583 20024902047792958595168375)
              ·
                refine ⟨30037353071689437892752563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20024902047792958595168375 30037353071689437892752563)
                ·
                  refine ⟨45056029607534156839128845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30037353071689437892752563 45056029607534156839128845)
                  ·
                    refine ⟨16896011102825308814673317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45056029607534156839128845 16896011102825308814673317)
                    ·
                      refine ⟨3168002081779745402751247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16896011102825308814673317 3168002081779745402751247)
                      ·
                        rfl

theorem cell23_6169662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_6169662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169662 prefixEnd_6169662 := by exact prefixLift 6169662
  have htrace : WordTrace (prefixWord ++ tailWord_6169662) baseStart_6169662 baseEnd_6169662 := by
    simpa [prefixWord, tailWord_6169662, baseEnd_6169662] using wordTrace_append hprefix tailTrace_6169662
  have hstable : (prefixWord ++ tailWord_6169662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169662).length < 2 ^ (prefixWord ++ tailWord_6169662).sum := by decide
  have hdescent : baseEnd_6169662 < baseStart_6169662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169688 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_6169688 : Nat := 118140960795 + 6169688 * 2 ^ 59
def prefixEnd_6169688 : Nat := 4983230072969 + 3 ^ 40 * 6169688 * 2
def baseEnd_6169688 : Nat := 3168015432276762301026127

theorem tailTrace_6169688 : CollatzResearch.WordTrace tailWord_6169688 prefixEnd_6169688 3168015432276762301026127 := by
  unfold tailWord_6169688
  simp only [CollatzResearch.WordTrace]
  refine ⟨112513504036140774833130859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150018005381521033110841145 112513504036140774833130859)
  ·
    refine ⟨168770256054211162249696289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112513504036140774833130859 168770256054211162249696289)
    ·
      refine ⟨126577692040658371687272217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168770256054211162249696289 126577692040658371687272217)
      ·
        refine ⟨94933269030493778765454163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126577692040658371687272217 94933269030493778765454163)
        ·
          refine ⟨142399903545740668148181245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94933269030493778765454163 142399903545740668148181245)
          ·
            refine ⟨53399963829652750555567967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142399903545740668148181245 53399963829652750555567967)
            ·
              refine ⟨80099945744479125833351951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53399963829652750555567967 80099945744479125833351951)
              ·
                refine ⟨120149918616718688750027927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80099945744479125833351951 120149918616718688750027927)
                ·
                  refine ⟨180224877925078033125041891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120149918616718688750027927 180224877925078033125041891)
                  ·
                    refine ⟨270337316887617049687562837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 180224877925078033125041891 270337316887617049687562837)
                    ·
                      refine ⟨3168015432276762301026127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 270337316887617049687562837 3168015432276762301026127)
                      ·
                        rfl

theorem cell23_6169688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_6169688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169688 prefixEnd_6169688 := by exact prefixLift 6169688
  have htrace : WordTrace (prefixWord ++ tailWord_6169688) baseStart_6169688 baseEnd_6169688 := by
    simpa [prefixWord, tailWord_6169688, baseEnd_6169688] using wordTrace_append hprefix tailTrace_6169688
  have hstable : (prefixWord ++ tailWord_6169688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169688).length < 2 ^ (prefixWord ++ tailWord_6169688).sum := by decide
  have hdescent : baseEnd_6169688 < baseStart_6169688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169712 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 3, 1, 3]
def baseStart_6169712 : Nat := 118140960795 + 6169712 * 2 ^ 59
def prefixEnd_6169712 : Nat := 4983230072969 + 3 ^ 40 * 6169712 * 2
def baseEnd_6169712 : Nat := 3168027755812470207126017

theorem tailTrace_6169712 : CollatzResearch.WordTrace tailWord_6169712 prefixEnd_6169712 3168027755812470207126017 := by
  unfold tailWord_6169712
  simp only [CollatzResearch.WordTrace]
  refine ⟨112513941712097300882567695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150018588949463067843423593 112513941712097300882567695)
  ·
    refine ⟨168770912568145951323851543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112513941712097300882567695 168770912568145951323851543)
    ·
      refine ⟨253156368852218926985777315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168770912568145951323851543 253156368852218926985777315)
      ·
        refine ⟨379734553278328390478665973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253156368852218926985777315 379734553278328390478665973)
        ·
          refine ⟨35600114369843286607374935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 379734553278328390478665973 35600114369843286607374935)
          ·
            refine ⟨53400171554764929911062403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35600114369843286607374935 53400171554764929911062403)
            ·
              refine ⟨80100257332147394866593605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53400171554764929911062403 80100257332147394866593605)
              ·
                refine ⟨15018798249777636537486301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80100257332147394866593605 15018798249777636537486301)
                ·
                  refine ⟨5632049343666613701557363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15018798249777636537486301 5632049343666613701557363)
                  ·
                    refine ⟨8448074015499920552336045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5632049343666613701557363 8448074015499920552336045)
                    ·
                      refine ⟨3168027755812470207126017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8448074015499920552336045 3168027755812470207126017)
                      ·
                        rfl

theorem cell23_6169712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 3, 1, 3].length) (baseStart_6169712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169712 prefixEnd_6169712 := by exact prefixLift 6169712
  have htrace : WordTrace (prefixWord ++ tailWord_6169712) baseStart_6169712 baseEnd_6169712 := by
    simpa [prefixWord, tailWord_6169712, baseEnd_6169712] using wordTrace_append hprefix tailTrace_6169712
  have hstable : (prefixWord ++ tailWord_6169712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169712).length < 2 ^ (prefixWord ++ tailWord_6169712).sum := by decide
  have hdescent : baseEnd_6169712 < baseStart_6169712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169732 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_6169732 : Nat := 118140960795 + 6169732 * 2 ^ 59
def prefixEnd_6169732 : Nat := 4983230072969 + 3 ^ 40 * 6169732 * 2
def baseEnd_6169732 : Nat := 1056012675141853376291975

theorem tailTrace_6169732 : CollatzResearch.WordTrace tailWord_6169732 prefixEnd_6169732 1056012675141853376291975 := by
  unfold tailWord_6169732
  simp only [CollatzResearch.WordTrace]
  refine ⟨112514306442061072590431725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150019075256081430120575633 112514306442061072590431725)
  ·
    refine ⟨42192864915772902221411897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112514306442061072590431725 42192864915772902221411897)
    ·
      refine ⟨31644648686829676666058923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42192864915772902221411897 31644648686829676666058923)
      ·
        refine ⟨47466973030244514999088385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31644648686829676666058923 47466973030244514999088385)
        ·
          refine ⟨35600229772683386249316289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47466973030244514999088385 35600229772683386249316289)
          ·
            refine ⟨26700172329512539686987217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35600229772683386249316289 26700172329512539686987217)
            ·
              refine ⟨20025129247134404765240413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26700172329512539686987217 20025129247134404765240413)
              ·
                refine ⟨7509423467675401786965155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20025129247134404765240413 7509423467675401786965155)
                ·
                  refine ⟨11264135201513102680447733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7509423467675401786965155 11264135201513102680447733)
                  ·
                    refine ⟨1056012675141853376291975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11264135201513102680447733 1056012675141853376291975)
                    ·
                      rfl

theorem cell23_6169732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_6169732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169732 prefixEnd_6169732 := by exact prefixLift 6169732
  have htrace : WordTrace (prefixWord ++ tailWord_6169732) baseStart_6169732 baseEnd_6169732 := by
    simpa [prefixWord, tailWord_6169732, baseEnd_6169732] using wordTrace_append hprefix tailTrace_6169732
  have hstable : (prefixWord ++ tailWord_6169732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169732).length < 2 ^ (prefixWord ++ tailWord_6169732).sum := by decide
  have hdescent : baseEnd_6169732 < baseStart_6169732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169735 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_6169735 : Nat := 118140960795 + 6169735 * 2 ^ 59
def prefixEnd_6169735 : Nat := 4983230072969 + 3 ^ 40 * 6169735 * 2
def baseEnd_6169735 : Nat := 3168039565867523617138411

theorem tailTrace_6169735 : CollatzResearch.WordTrace tailWord_6169735 prefixEnd_6169735 3168039565867523617138411 := by
  unfold tailWord_6169735
  simp only [CollatzResearch.WordTrace]
  refine ⟨225028722303111276693222659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150019148202074184462148439 225028722303111276693222659)
  ·
    refine ⟨337543083454666915039833989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225028722303111276693222659 337543083454666915039833989)
    ·
      refine ⟨63289328147750046569968873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337543083454666915039833989 63289328147750046569968873)
      ·
        refine ⟨47466996110812534927476655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63289328147750046569968873 47466996110812534927476655)
        ·
          refine ⟨71200494166218802391214983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47466996110812534927476655 71200494166218802391214983)
          ·
            refine ⟨106800741249328203586822475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71200494166218802391214983 106800741249328203586822475)
            ·
              refine ⟨160201111873992305380233713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106800741249328203586822475 160201111873992305380233713)
              ·
                refine ⟨120150833905494229035175285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160201111873992305380233713 120150833905494229035175285)
                ·
                  refine ⟨11264140678640083972047683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120150833905494229035175285 11264140678640083972047683)
                  ·
                    refine ⟨16896211017960125958071525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11264140678640083972047683 16896211017960125958071525)
                    ·
                      refine ⟨3168039565867523617138411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16896211017960125958071525 3168039565867523617138411)
                      ·
                        rfl

theorem cell23_6169735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_6169735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169735 prefixEnd_6169735 := by exact prefixLift 6169735
  have htrace : WordTrace (prefixWord ++ tailWord_6169735) baseStart_6169735 baseEnd_6169735 := by
    simpa [prefixWord, tailWord_6169735, baseEnd_6169735] using wordTrace_append hprefix tailTrace_6169735
  have hstable : (prefixWord ++ tailWord_6169735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169735).length < 2 ^ (prefixWord ++ tailWord_6169735).sum := by decide
  have hdescent : baseEnd_6169735 < baseStart_6169735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169746 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_6169746 : Nat := 118140960795 + 6169746 * 2 ^ 59
def prefixEnd_6169746 : Nat := 4983230072969 + 3 ^ 40 * 6169746 * 2
def baseEnd_6169746 : Nat := 3168045214154723074100861

theorem tailTrace_6169746 : CollatzResearch.WordTrace tailWord_6169746 prefixEnd_6169746 3168045214154723074100861 := by
  unfold tailWord_6169746
  simp only [CollatzResearch.WordTrace]
  refine ⟨56257280876517856392968273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150019415670714283714582061 56257280876517856392968273)
  ·
    refine ⟨42192960657388392294726205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56257280876517856392968273 42192960657388392294726205)
    ·
      refine ⟨15822360246520647110522327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42192960657388392294726205 15822360246520647110522327)
      ·
        refine ⟨23733540369780970665783491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15822360246520647110522327 23733540369780970665783491)
        ·
          refine ⟨35600310554671455998675237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23733540369780970665783491 35600310554671455998675237)
          ·
            refine ⟨6675058229000897999751607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35600310554671455998675237 6675058229000897999751607)
            ·
              refine ⟨10012587343501346999627411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6675058229000897999751607 10012587343501346999627411)
              ·
                refine ⟨15018881015252020499441117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10012587343501346999627411 15018881015252020499441117)
                ·
                  refine ⟨5632080380719507687290419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15018881015252020499441117 5632080380719507687290419)
                  ·
                    refine ⟨8448120571079261530935629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5632080380719507687290419 8448120571079261530935629)
                    ·
                      refine ⟨3168045214154723074100861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8448120571079261530935629 3168045214154723074100861)
                      ·
                        rfl

theorem cell23_6169746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_6169746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169746 prefixEnd_6169746 := by exact prefixLift 6169746
  have htrace : WordTrace (prefixWord ++ tailWord_6169746) baseStart_6169746 baseEnd_6169746 := by
    simpa [prefixWord, tailWord_6169746, baseEnd_6169746] using wordTrace_append hprefix tailTrace_6169746
  have hstable : (prefixWord ++ tailWord_6169746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169746).length < 2 ^ (prefixWord ++ tailWord_6169746).sum := by decide
  have hdescent : baseEnd_6169746 < baseStart_6169746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169765 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_6169765 : Nat := 118140960795 + 6169765 * 2 ^ 59
def prefixEnd_6169765 : Nat := 4983230072969 + 3 ^ 40 * 6169765 * 2
def baseEnd_6169765 : Nat := 3168054970287158499763273

theorem tailTrace_6169765 : CollatzResearch.WordTrace tailWord_6169765 prefixEnd_6169765 3168054970287158499763273 := by
  unfold tailWord_6169765
  simp only [CollatzResearch.WordTrace]
  refine ⟨225029816493002591816814749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150019877662001727877876499 225029816493002591816814749)
  ·
    refine ⟨84386181184875971931305531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225029816493002591816814749 84386181184875971931305531)
    ·
      refine ⟨126579271777313957896958297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84386181184875971931305531 126579271777313957896958297)
      ·
        refine ⟨94934453832985468422718723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126579271777313957896958297 94934453832985468422718723)
        ·
          refine ⟨142401680749478202634078085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94934453832985468422718723 142401680749478202634078085)
          ·
            refine ⟨26700315140527162993889641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142401680749478202634078085 26700315140527162993889641)
            ·
              refine ⟨20025236355395372245417231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26700315140527162993889641 20025236355395372245417231)
              ·
                refine ⟨30037854533093058368125847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20025236355395372245417231 30037854533093058368125847)
                ·
                  refine ⟨45056781799639587552188771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30037854533093058368125847 45056781799639587552188771)
                  ·
                    refine ⟨67585172699459381328283157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45056781799639587552188771 67585172699459381328283157)
                    ·
                      refine ⟨3168054970287158499763273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67585172699459381328283157 3168054970287158499763273)
                      ·
                        rfl

theorem cell23_6169765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_6169765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169765 prefixEnd_6169765 := by exact prefixLift 6169765
  have htrace : WordTrace (prefixWord ++ tailWord_6169765) baseStart_6169765 baseEnd_6169765 := by
    simpa [prefixWord, tailWord_6169765, baseEnd_6169765] using wordTrace_append hprefix tailTrace_6169765
  have hstable : (prefixWord ++ tailWord_6169765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169765).length < 2 ^ (prefixWord ++ tailWord_6169765).sum := by decide
  have hdescent : baseEnd_6169765 < baseStart_6169765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169772 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_6169772 : Nat := 118140960795 + 6169772 * 2 ^ 59
def prefixEnd_6169772 : Nat := 4983230072969 + 3 ^ 40 * 6169772 * 2
def baseEnd_6169772 : Nat := 3168058564651739972375741

theorem tailTrace_6169772 : CollatzResearch.WordTrace tailWord_6169772 prefixEnd_6169772 3168058564651739972375741 := by
  unfold tailWord_6169772
  simp only [CollatzResearch.WordTrace]
  refine ⟨112515035901988616006159785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150020047869318154674879713 112515035901988616006159785)
  ·
    refine ⟨84386276926491462004619839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112515035901988616006159785 84386276926491462004619839)
    ·
      refine ⟨126579415389737193006929759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84386276926491462004619839 126579415389737193006929759)
      ·
        refine ⟨189869123084605789510394639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126579415389737193006929759 189869123084605789510394639)
        ·
          refine ⟨284803684626908684265591959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189869123084605789510394639 284803684626908684265591959)
          ·
            refine ⟨427205526940363026398387939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284803684626908684265591959 427205526940363026398387939)
            ·
              refine ⟨640808290410544539597581909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427205526940363026398387939 640808290410544539597581909)
              ·
                refine ⟨7509472153248568823409163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 640808290410544539597581909 7509472153248568823409163)
                ·
                  refine ⟨11264208229872853235113745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7509472153248568823409163 11264208229872853235113745)
                  ·
                    refine ⟨8448156172404639926335309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11264208229872853235113745 8448156172404639926335309)
                    ·
                      refine ⟨3168058564651739972375741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8448156172404639926335309 3168058564651739972375741)
                      ·
                        rfl

theorem cell23_6169772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_6169772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169772 prefixEnd_6169772 := by exact prefixLift 6169772
  have htrace : WordTrace (prefixWord ++ tailWord_6169772) baseStart_6169772 baseEnd_6169772 := by
    simpa [prefixWord, tailWord_6169772, baseEnd_6169772] using wordTrace_append hprefix tailTrace_6169772
  have hstable : (prefixWord ++ tailWord_6169772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169772).length < 2 ^ (prefixWord ++ tailWord_6169772).sum := by decide
  have hdescent : baseEnd_6169772 < baseStart_6169772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169786 : List Nat := [3, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2]
def baseStart_6169786 : Nat := 118140960795 + 6169786 * 2 ^ 59
def prefixEnd_6169786 : Nat := 4983230072969 + 3 ^ 40 * 6169786 * 2
def baseEnd_6169786 : Nat := 3168065753380902917600677

theorem tailTrace_6169786 : CollatzResearch.WordTrace tailWord_6169786 prefixEnd_6169786 3168065753380902917600677 := by
  unfold tailWord_6169786
  simp only [CollatzResearch.WordTrace]
  refine ⟨56257645606481628100832303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150020388283951008268886141 56257645606481628100832303)
  ·
    refine ⟨84386468409722442151248455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56257645606481628100832303 84386468409722442151248455)
    ·
      refine ⟨126579702614583663226872683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84386468409722442151248455 126579702614583663226872683)
      ·
        refine ⟨189869553921875494840309025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126579702614583663226872683 189869553921875494840309025)
        ·
          refine ⟨142402165441406621130231769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189869553921875494840309025 142402165441406621130231769)
          ·
            refine ⟨106801624081054965847673827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142402165441406621130231769 106801624081054965847673827)
            ·
              refine ⟨160202436121582448771510741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106801624081054965847673827 160202436121582448771510741)
              ·
                refine ⟨3754744596599588643082283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160202436121582448771510741 3754744596599588643082283)
                ·
                  refine ⟨5632116894899382964623425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754744596599588643082283 5632116894899382964623425)
                  ·
                    refine ⟨4224087671174537223467569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5632116894899382964623425 4224087671174537223467569)
                    ·
                      refine ⟨3168065753380902917600677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4224087671174537223467569 3168065753380902917600677)
                      ·
                        rfl

theorem cell23_6169786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_6169786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169786 prefixEnd_6169786 := by exact prefixLift 6169786
  have htrace : WordTrace (prefixWord ++ tailWord_6169786) baseStart_6169786 baseEnd_6169786 := by
    simpa [prefixWord, tailWord_6169786, baseEnd_6169786] using wordTrace_append hprefix tailTrace_6169786
  have hstable : (prefixWord ++ tailWord_6169786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169786).length < 2 ^ (prefixWord ++ tailWord_6169786).sum := by decide
  have hdescent : baseEnd_6169786 < baseStart_6169786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169796 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6169796 : Nat := 118140960795 + 6169796 * 2 ^ 59
def prefixEnd_6169796 : Nat := 4983230072969 + 3 ^ 40 * 6169796 * 2
def baseEnd_6169796 : Nat := 1056023629395815959491877

theorem tailTrace_6169796 : CollatzResearch.WordTrace tailWord_6169796 prefixEnd_6169796 1056023629395815959491877 := by
  unfold tailWord_6169796
  simp only [CollatzResearch.WordTrace]
  refine ⟨112515473577945142055596621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150020631437260189407462161 112515473577945142055596621)
  ·
    refine ⟨42193302591729428270848733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112515473577945142055596621 42193302591729428270848733)
    ·
      refine ⟨15822488471898535601568275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42193302591729428270848733 15822488471898535601568275)
      ·
        refine ⟨23733732707847803402352413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15822488471898535601568275 23733732707847803402352413)
        ·
          refine ⟨8900149765442926275882155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23733732707847803402352413 8900149765442926275882155)
          ·
            refine ⟨13350224648164389413823233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900149765442926275882155 13350224648164389413823233)
            ·
              refine ⟨10012668486123292060367425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13350224648164389413823233 10012668486123292060367425)
              ·
                refine ⟨7509501364592469045275569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10012668486123292060367425 7509501364592469045275569)
                ·
                  refine ⟨5632126023444351783956677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7509501364592469045275569 5632126023444351783956677)
                  ·
                    refine ⟨1056023629395815959491877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5632126023444351783956677 1056023629395815959491877)
                    ·
                      rfl

theorem cell23_6169796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6169796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169796 prefixEnd_6169796 := by exact prefixLift 6169796
  have htrace : WordTrace (prefixWord ++ tailWord_6169796) baseStart_6169796 baseEnd_6169796 := by
    simpa [prefixWord, tailWord_6169796, baseEnd_6169796] using wordTrace_append hprefix tailTrace_6169796
  have hstable : (prefixWord ++ tailWord_6169796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169796).length < 2 ^ (prefixWord ++ tailWord_6169796).sum := by decide
  have hdescent : baseEnd_6169796 < baseStart_6169796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169882 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 7]
def baseStart_6169882 : Nat := 118140960795 + 6169882 * 2 ^ 59
def prefixEnd_6169882 : Nat := 4983230072969 + 3 ^ 40 * 6169882 * 2
def baseEnd_6169882 : Nat := 352012783058192726888915

theorem tailTrace_6169882 : CollatzResearch.WordTrace tailWord_6169882 prefixEnd_6169882 352012783058192726888915 := by
  unfold tailWord_6169882
  simp only [CollatzResearch.WordTrace]
  refine ⟨56258520958394680199705975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150022722555719147199215933 56258520958394680199705975)
  ·
    refine ⟨84387781437592020299558963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56258520958394680199705975 84387781437592020299558963)
    ·
      refine ⟨126581672156388030449338445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84387781437592020299558963 126581672156388030449338445)
      ·
        refine ⟨47468127058645511418501917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126581672156388030449338445 47468127058645511418501917)
        ·
          refine ⟨17800547646992066781938219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47468127058645511418501917 17800547646992066781938219)
          ·
            refine ⟨26700821470488100172907329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17800547646992066781938219 26700821470488100172907329)
            ·
              refine ⟨20025616102866075129680497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26700821470488100172907329 20025616102866075129680497)
              ·
                refine ⟨15019212077149556347260373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20025616102866075129680497 15019212077149556347260373)
                ·
                  refine ⟨352012783058192726888915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15019212077149556347260373 352012783058192726888915)
                  ·
                    rfl

theorem cell23_6169882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_6169882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169882 prefixEnd_6169882 := by exact prefixLift 6169882
  have htrace : WordTrace (prefixWord ++ tailWord_6169882) baseStart_6169882 baseEnd_6169882 := by
    simpa [prefixWord, tailWord_6169882, baseEnd_6169882] using wordTrace_append hprefix tailTrace_6169882
  have hstable : (prefixWord ++ tailWord_6169882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169882).length < 2 ^ (prefixWord ++ tailWord_6169882).sum := by decide
  have hdescent : baseEnd_6169882 < baseStart_6169882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169916 : List Nat := [2, 2, 2, 2, 1, 4, 3, 2, 5]
def baseStart_6169916 : Nat := 118140960795 + 6169916 * 2 ^ 59
def prefixEnd_6169916 : Nat := 4983230072969 + 3 ^ 40 * 6169916 * 2
def baseEnd_6169916 : Nat := 352014722873998600997231

theorem tailTrace_6169916 : CollatzResearch.WordTrace tailWord_6169916 prefixEnd_6169916 352014722873998600997231 := by
  unfold tailWord_6169916
  simp only [CollatzResearch.WordTrace]
  refine ⟨112517661957727772302780801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150023549276970363070374401 112517661957727772302780801)
  ·
    refine ⟨84388246468295829227085601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112517661957727772302780801 84388246468295829227085601)
    ·
      refine ⟨63291184851221871920314201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84388246468295829227085601 63291184851221871920314201)
      ·
        refine ⟨47468388638416403940235651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63291184851221871920314201 47468388638416403940235651)
        ·
          refine ⟨71202582957624605910353477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47468388638416403940235651 71202582957624605910353477)
          ·
            refine ⟨13350484304554613608191277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71202582957624605910353477 13350484304554613608191277)
            ·
              refine ⟨5006431614207980103071729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13350484304554613608191277 5006431614207980103071729)
              ·
                refine ⟨3754823710655985077303797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5006431614207980103071729 3754823710655985077303797)
                ·
                  refine ⟨352014722873998600997231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3754823710655985077303797 352014722873998600997231)
                  ·
                    rfl

theorem cell23_6169916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_6169916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169916 prefixEnd_6169916 := by exact prefixLift 6169916
  have htrace : WordTrace (prefixWord ++ tailWord_6169916) baseStart_6169916 baseEnd_6169916 := by
    simpa [prefixWord, tailWord_6169916, baseEnd_6169916] using wordTrace_append hprefix tailTrace_6169916
  have hstable : (prefixWord ++ tailWord_6169916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169916).length < 2 ^ (prefixWord ++ tailWord_6169916).sum := by decide
  have hdescent : baseEnd_6169916 < baseStart_6169916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169935 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_6169935 : Nat := 118140960795 + 6169935 * 2 ^ 59
def prefixEnd_6169935 : Nat := 4983230072969 + 3 ^ 40 * 6169935 * 2
def baseEnd_6169935 : Nat := 3168142261998422834637491

theorem tailTrace_6169935 : CollatzResearch.WordTrace tailWord_6169935 prefixEnd_6169935 3168142261998422834637491 := by
  unfold tailWord_6169935
  simp only [CollatzResearch.WordTrace]
  refine ⟨225036016902386710850503259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150024011268257807233668839 225036016902386710850503259)
  ·
    refine ⟨337554025353580066275754889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225036016902386710850503259 337554025353580066275754889)
    ·
      refine ⟨253165519015185049706816167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337554025353580066275754889 253165519015185049706816167)
      ·
        refine ⟨379748278522777574560224251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253165519015185049706816167 379748278522777574560224251)
        ·
          refine ⟨569622417784166361840336377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379748278522777574560224251 569622417784166361840336377)
          ·
            refine ⟨427216813338124771380252283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569622417784166361840336377 427216813338124771380252283)
            ·
              refine ⟨640825220007187157070378425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427216813338124771380252283 640825220007187157070378425)
              ·
                refine ⟨480618915005390367802783819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640825220007187157070378425 480618915005390367802783819)
                ·
                  refine ⟨720928372508085551704175729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480618915005390367802783819 720928372508085551704175729)
                  ·
                    refine ⟨540696279381064163778131797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 720928372508085551704175729 540696279381064163778131797)
                    ·
                      refine ⟨3168142261998422834637491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 540696279381064163778131797 3168142261998422834637491)
                      ·
                        rfl

theorem cell23_6169935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_6169935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169935 prefixEnd_6169935 := by exact prefixLift 6169935
  have htrace : WordTrace (prefixWord ++ tailWord_6169935) baseStart_6169935 baseEnd_6169935 := by
    simpa [prefixWord, tailWord_6169935, baseEnd_6169935] using wordTrace_append hprefix tailTrace_6169935
  have hstable : (prefixWord ++ tailWord_6169935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169935).length < 2 ^ (prefixWord ++ tailWord_6169935).sum := by decide
  have hdescent : baseEnd_6169935 < baseStart_6169935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6169969 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 3]
def baseStart_6169969 : Nat := 118140960795 + 6169969 * 2 ^ 59
def prefixEnd_6169969 : Nat := 4983230072969 + 3 ^ 40 * 6169969 * 2
def baseEnd_6169969 : Nat := 3168159720340675701612335

theorem tailTrace_6169969 : CollatzResearch.WordTrace tailWord_6169969 prefixEnd_6169969 3168159720340675701612335 := by
  unfold tailWord_6169969
  simp only [CollatzResearch.WordTrace]
  refine ⟨225037256984263534657240961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150024837989509023104827307 225037256984263534657240961)
  ·
    refine ⟨168777942738197650992930721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225037256984263534657240961 168777942738197650992930721)
    ·
      refine ⟨126583457053648238244698041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168777942738197650992930721 126583457053648238244698041)
      ·
        refine ⟨94937592790236178683523531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126583457053648238244698041 94937592790236178683523531)
        ·
          refine ⟨142406389185354268025285297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94937592790236178683523531 142406389185354268025285297)
          ·
            refine ⟨106804791889015701018963973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142406389185354268025285297 106804791889015701018963973)
            ·
              refine ⟨20025898479190443941055745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106804791889015701018963973 20025898479190443941055745)
              ·
                refine ⟨15019423859392832955791809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20025898479190443941055745 15019423859392832955791809)
                ·
                  refine ⟨11264567894544624716843857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15019423859392832955791809 11264567894544624716843857)
                  ·
                    refine ⟨8448425920908468537632893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11264567894544624716843857 8448425920908468537632893)
                    ·
                      refine ⟨3168159720340675701612335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8448425920908468537632893 3168159720340675701612335)
                      ·
                        rfl

theorem cell23_6169969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_6169969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6169969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6169969 prefixEnd_6169969 := by exact prefixLift 6169969
  have htrace : WordTrace (prefixWord ++ tailWord_6169969) baseStart_6169969 baseEnd_6169969 := by
    simpa [prefixWord, tailWord_6169969, baseEnd_6169969] using wordTrace_append hprefix tailTrace_6169969
  have hstable : (prefixWord ++ tailWord_6169969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6169969).length < 2 ^ (prefixWord ++ tailWord_6169969).sum := by decide
  have hdescent : baseEnd_6169969 < baseStart_6169969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6169969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170019 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 1, 5]
def baseStart_6170019 : Nat := 118140960795 + 6170019 * 2 ^ 59
def prefixEnd_6170019 : Nat := 4983230072969 + 3 ^ 40 * 6170019 * 2
def baseEnd_6170019 : Nat := 1056061798124466835329035

theorem tailTrace_6170019 : CollatzResearch.WordTrace tailWord_6170019 prefixEnd_6170019 1056061798124466835329035 := by
  unfold tailWord_6170019
  simp only [CollatzResearch.WordTrace]
  refine ⟨225039080634082393196561111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150026053756054928797707407 225039080634082393196561111)
  ·
    refine ⟨337558620951123589794841667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225039080634082393196561111 337558620951123589794841667)
    ·
      refine ⟨506337931426685384692262501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337558620951123589794841667 506337931426685384692262501)
      ·
        refine ⟨94938362142503509629799219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506337931426685384692262501 94938362142503509629799219)
        ·
          refine ⟨142407543213755264444698829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94938362142503509629799219 142407543213755264444698829)
          ·
            refine ⟨53402828705158224166762061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142407543213755264444698829 53402828705158224166762061)
            ·
              refine ⟨20026060764434334062535773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53402828705158224166762061 20026060764434334062535773)
              ·
                refine ⟨7509772786662875273450915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20026060764434334062535773 7509772786662875273450915)
                ·
                  refine ⟨11264659179994312910176373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7509772786662875273450915 11264659179994312910176373)
                  ·
                    refine ⟨1056061798124466835329035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11264659179994312910176373 1056061798124466835329035)
                    ·
                      rfl

theorem cell23_6170019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 5].length) (baseStart_6170019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170019 prefixEnd_6170019 := by exact prefixLift 6170019
  have htrace : WordTrace (prefixWord ++ tailWord_6170019) baseStart_6170019 baseEnd_6170019 := by
    simpa [prefixWord, tailWord_6170019, baseEnd_6170019] using wordTrace_append hprefix tailTrace_6170019
  have hstable : (prefixWord ++ tailWord_6170019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170019).length < 2 ^ (prefixWord ++ tailWord_6170019).sum := by decide
  have hdescent : baseEnd_6170019 < baseStart_6170019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170033 : List Nat := [1, 2, 2, 4, 1, 1, 1, 6, 1, 1, 3]
def baseStart_6170033 : Nat := 118140960795 + 6170033 * 2 ^ 59
def prefixEnd_6170033 : Nat := 4983230072969 + 3 ^ 40 * 6170033 * 2
def baseEnd_6170033 : Nat := 3168192583102563451212041

theorem tailTrace_6170033 : CollatzResearch.WordTrace tailWord_6170033 prefixEnd_6170033 3168192583102563451212041 := by
  unfold tailWord_6170033
  simp only [CollatzResearch.WordTrace]
  refine ⟨225039591256031673587570753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150026394170687782391713835 225039591256031673587570753)
  ·
    refine ⟨168779693442023755190678065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225039591256031673587570753 168779693442023755190678065)
    ·
      refine ⟨126584770081517816393008549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168779693442023755190678065 126584770081517816393008549)
      ·
        refine ⟨23734644390284590573689103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126584770081517816393008549 23734644390284590573689103)
        ·
          refine ⟨35601966585426885860533655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23734644390284590573689103 35601966585426885860533655)
          ·
            refine ⟨53402949878140328790800483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35601966585426885860533655 53402949878140328790800483)
            ·
              refine ⟨80104424817210493186200725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53402949878140328790800483 80104424817210493186200725)
              ·
                refine ⟨3754894913306741868103159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80104424817210493186200725 3754894913306741868103159)
                ·
                  refine ⟨5632342369960112802154739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3754894913306741868103159 5632342369960112802154739)
                  ·
                    refine ⟨8448513554940169203232109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5632342369960112802154739 8448513554940169203232109)
                    ·
                      refine ⟨3168192583102563451212041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8448513554940169203232109 3168192583102563451212041)
                      ·
                        rfl

theorem cell23_6170033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_6170033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170033 prefixEnd_6170033 := by exact prefixLift 6170033
  have htrace : WordTrace (prefixWord ++ tailWord_6170033) baseStart_6170033 baseEnd_6170033 := by
    simpa [prefixWord, tailWord_6170033, baseEnd_6170033] using wordTrace_append hprefix tailTrace_6170033
  have hstable : (prefixWord ++ tailWord_6170033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170033).length < 2 ^ (prefixWord ++ tailWord_6170033).sum := by decide
  have hdescent : baseEnd_6170033 < baseStart_6170033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170056 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_6170056 : Nat := 118140960795 + 6170056 * 2 ^ 59
def prefixEnd_6170056 : Nat := 4983230072969 + 3 ^ 40 * 6170056 * 2
def baseEnd_6170056 : Nat := 3168204393157616861224435

theorem tailTrace_6170056 : CollatzResearch.WordTrace tailWord_6170056 prefixEnd_6170056 3168204393157616861224435 := by
  unfold tailWord_6170056
  simp only [CollatzResearch.WordTrace]
  refine ⟨112520215067474174257829011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150026953423298899010438681 112520215067474174257829011)
  ·
    refine ⟨168780322601211261386743517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112520215067474174257829011 168780322601211261386743517)
    ·
      refine ⟨63292620975454223020028819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168780322601211261386743517 63292620975454223020028819)
      ·
        refine ⟨94938931463181334530043229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63292620975454223020028819 94938931463181334530043229)
        ·
          refine ⟨35602099298693000448766211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94938931463181334530043229 35602099298693000448766211)
          ·
            refine ⟨53403148948039500673149317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35602099298693000448766211 53403148948039500673149317)
            ·
              refine ⟨10013090427757406376215497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53403148948039500673149317 10013090427757406376215497)
              ·
                refine ⟨7509817820818054782161623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10013090427757406376215497 7509817820818054782161623)
                ·
                  refine ⟨11264726731227082173242435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7509817820818054782161623 11264726731227082173242435)
                  ·
                    refine ⟨16897090096840623259863653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11264726731227082173242435 16897090096840623259863653)
                    ·
                      refine ⟨3168204393157616861224435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16897090096840623259863653 3168204393157616861224435)
                      ·
                        rfl

theorem cell23_6170056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_6170056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170056 prefixEnd_6170056 := by exact prefixLift 6170056
  have htrace : WordTrace (prefixWord ++ tailWord_6170056) baseStart_6170056 baseEnd_6170056 := by
    simpa [prefixWord, tailWord_6170056, baseEnd_6170056] using wordTrace_append hprefix tailTrace_6170056
  have hstable : (prefixWord ++ tailWord_6170056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170056).length < 2 ^ (prefixWord ++ tailWord_6170056).sum := by decide
  have hdescent : baseEnd_6170056 < baseStart_6170056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170059 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 3]
def baseStart_6170059 : Nat := 118140960795 + 6170059 * 2 ^ 59
def prefixEnd_6170059 : Nat := 4983230072969 + 3 ^ 40 * 6170059 * 2
def baseEnd_6170059 : Nat := 3168205933599580349486921

theorem tailTrace_6170059 : CollatzResearch.WordTrace tailWord_6170059 prefixEnd_6170059 3168205933599580349486921 := by
  unfold tailWord_6170059
  simp only [CollatzResearch.WordTrace]
  refine ⟨225040539553937480028017231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150027026369291653352011487 225040539553937480028017231)
  ·
    refine ⟨337560809330906220042025847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225040539553937480028017231 337560809330906220042025847)
    ·
      refine ⟨506341213996359330063038771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337560809330906220042025847 506341213996359330063038771)
      ·
        refine ⟨759511820994538995094558157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506341213996359330063038771 759511820994538995094558157)
        ·
          refine ⟨284816932872952123160459309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 759511820994538995094558157 284816932872952123160459309)
          ·
            refine ⟨106806349827357046185172241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284816932872952123160459309 106806349827357046185172241)
            ·
              refine ⟨80104762370517784638879181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106806349827357046185172241 80104762370517784638879181)
              ·
                refine ⟨30039285888944169239579693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80104762370517784638879181 30039285888944169239579693)
                ·
                  refine ⟨11264732208354063464842385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30039285888944169239579693 11264732208354063464842385)
                  ·
                    refine ⟨8448549156265547598631789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11264732208354063464842385 8448549156265547598631789)
                    ·
                      refine ⟨3168205933599580349486921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8448549156265547598631789 3168205933599580349486921)
                      ·
                        rfl

theorem cell23_6170059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 3].length) (baseStart_6170059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170059 prefixEnd_6170059 := by exact prefixLift 6170059
  have htrace : WordTrace (prefixWord ++ tailWord_6170059) baseStart_6170059 baseEnd_6170059 := by
    simpa [prefixWord, tailWord_6170059, baseEnd_6170059] using wordTrace_append hprefix tailTrace_6170059
  have hstable : (prefixWord ++ tailWord_6170059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170059).length < 2 ^ (prefixWord ++ tailWord_6170059).sum := by decide
  have hdescent : baseEnd_6170059 < baseStart_6170059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170069 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6170069 : Nat := 118140960795 + 6170069 * 2 ^ 59
def prefixEnd_6170069 : Nat := 4983230072969 + 3 ^ 40 * 6170069 * 2
def baseEnd_6170069 : Nat := 3168211068406125310361875

theorem tailTrace_6170069 : CollatzResearch.WordTrace tailWord_6170069 prefixEnd_6170069 3168211068406125310361875 := by
  unfold tailWord_6170069
  simp only [CollatzResearch.WordTrace]
  refine ⟨225040904283901251735881261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150027269522600834490587507 225040904283901251735881261)
  ·
    refine ⟨84390339106462969400955473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225040904283901251735881261 84390339106462969400955473)
    ·
      refine ⟨63292754329847227050716605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84390339106462969400955473 63292754329847227050716605)
      ·
        refine ⟨23734782873692710144018727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63292754329847227050716605 23734782873692710144018727)
        ·
          refine ⟨35602174310539065216028091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23734782873692710144018727 35602174310539065216028091)
          ·
            refine ⟨53403261465808597824042137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35602174310539065216028091 53403261465808597824042137)
            ·
              refine ⟨40052446099356448368031603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53403261465808597824042137 40052446099356448368031603)
              ·
                refine ⟨60078669149034672552047405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40052446099356448368031603 60078669149034672552047405)
                ·
                  refine ⟨22529500930888002207017777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60078669149034672552047405 22529500930888002207017777)
                  ·
                    refine ⟨16897125698166001655263333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22529500930888002207017777 16897125698166001655263333)
                    ·
                      refine ⟨3168211068406125310361875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16897125698166001655263333 3168211068406125310361875)
                      ·
                        rfl

theorem cell23_6170069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6170069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170069 prefixEnd_6170069 := by exact prefixLift 6170069
  have htrace : WordTrace (prefixWord ++ tailWord_6170069) baseStart_6170069 baseEnd_6170069 := by
    simpa [prefixWord, tailWord_6170069, baseEnd_6170069] using wordTrace_append hprefix tailTrace_6170069
  have hstable : (prefixWord ++ tailWord_6170069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170069).length < 2 ^ (prefixWord ++ tailWord_6170069).sum := by decide
  have hdescent : baseEnd_6170069 < baseStart_6170069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170110 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6170110 : Nat := 118140960795 + 6170110 * 2 ^ 59
def prefixEnd_6170110 : Nat := 4983230072969 + 3 ^ 40 * 6170110 * 2
def baseEnd_6170110 : Nat := 3168232121112959649949187

theorem tailTrace_6170110 : CollatzResearch.WordTrace tailWord_6170110 prefixEnd_6170110 3168232121112959649949187 := by
  unfold tailWord_6170110
  simp only [CollatzResearch.WordTrace]
  refine ⟨28130299959594089467265473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150028266451168477158749189 28130299959594089467265473)
  ·
    refine ⟨21097724969695567100449105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28130299959594089467265473 21097724969695567100449105)
    ·
      refine ⟨15823293727271675325336829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21097724969695567100449105 15823293727271675325336829)
      ·
        refine ⟨5933735147726878247001311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15823293727271675325336829 5933735147726878247001311)
        ·
          refine ⟨8900602721590317370501967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5933735147726878247001311 8900602721590317370501967)
          ·
            refine ⟨13350904082385476055752951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900602721590317370501967 13350904082385476055752951)
            ·
              refine ⟨20026356123578214083629427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13350904082385476055752951 20026356123578214083629427)
              ·
                refine ⟨30039534185367321125444141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20026356123578214083629427 30039534185367321125444141)
                ·
                  refine ⟨11264825319512745422041553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30039534185367321125444141 11264825319512745422041553)
                  ·
                    refine ⟨8448618989634559066531165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11264825319512745422041553 8448618989634559066531165)
                    ·
                      refine ⟨3168232121112959649949187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8448618989634559066531165 3168232121112959649949187)
                      ·
                        rfl

theorem cell23_6170110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6170110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170110 prefixEnd_6170110 := by exact prefixLift 6170110
  have htrace : WordTrace (prefixWord ++ tailWord_6170110) baseStart_6170110 baseEnd_6170110 := by
    simpa [prefixWord, tailWord_6170110, baseEnd_6170110] using wordTrace_append hprefix tailTrace_6170110
  have hstable : (prefixWord ++ tailWord_6170110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170110).length < 2 ^ (prefixWord ++ tailWord_6170110).sum := by decide
  have hdescent : baseEnd_6170110 < baseStart_6170110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170163 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 1, 4, 2]
def baseStart_6170163 : Nat := 118140960795 + 6170163 * 2 ^ 59
def prefixEnd_6170163 : Nat := 4983230072969 + 3 ^ 40 * 6170163 * 2
def baseEnd_6170163 : Nat := 3168259335587647942586443

theorem tailTrace_6170163 : CollatzResearch.WordTrace tailWord_6170163 prefixEnd_6170163 3168259335587647942586443 := by
  unfold tailWord_6170163
  simp only [CollatzResearch.WordTrace]
  refine ⟨225044332745560705789803143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150029555163707137193202095 225044332745560705789803143)
  ·
    refine ⟨337566499118341058684704715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225044332745560705789803143 337566499118341058684704715)
    ·
      refine ⟨506349748677511588027057073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337566499118341058684704715 506349748677511588027057073)
      ·
        refine ⟨379762311508133691020292805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506349748677511588027057073 379762311508133691020292805)
        ·
          refine ⟨71205433407775067066304901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379762311508133691020292805 71205433407775067066304901)
          ·
            refine ⟨13351018763957825074932169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71205433407775067066304901 13351018763957825074932169)
            ·
              refine ⟨10013264072968368806199127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13351018763957825074932169 10013264072968368806199127)
              ·
                refine ⟨15019896109452553209298691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10013264072968368806199127 15019896109452553209298691)
                ·
                  refine ⟨22529844164178829813948037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15019896109452553209298691 22529844164178829813948037)
                  ·
                    refine ⟨4224345780783530590115257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22529844164178829813948037 4224345780783530590115257)
                    ·
                      refine ⟨3168259335587647942586443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4224345780783530590115257 3168259335587647942586443)
                      ·
                        rfl

theorem cell23_6170163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4, 2].length) (baseStart_6170163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170163 prefixEnd_6170163 := by exact prefixLift 6170163
  have htrace : WordTrace (prefixWord ++ tailWord_6170163) baseStart_6170163 baseEnd_6170163 := by
    simpa [prefixWord, tailWord_6170163, baseEnd_6170163] using wordTrace_append hprefix tailTrace_6170163
  have hstable : (prefixWord ++ tailWord_6170163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170163).length < 2 ^ (prefixWord ++ tailWord_6170163).sum := by decide
  have hdescent : baseEnd_6170163 < baseStart_6170163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170169 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 9]
def baseStart_6170169 : Nat := 118140960795 + 6170169 * 2 ^ 59
def prefixEnd_6170169 : Nat := 4983230072969 + 3 ^ 40 * 6170169 * 2
def baseEnd_6170169 : Nat := 352029157385730546567935

theorem tailTrace_6170169 : CollatzResearch.WordTrace tailWord_6170169 prefixEnd_6170169 352029157385730546567935 := by
  unfold tailWord_6170169
  simp only [CollatzResearch.WordTrace]
  refine ⟨225044551583538968814521561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150029701055692645876347707 225044551583538968814521561)
  ·
    refine ⟨168783413687654226610891171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225044551583538968814521561 168783413687654226610891171)
    ·
      refine ⟨253175120531481339916336757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168783413687654226610891171 253175120531481339916336757)
      ·
        refine ⟨23735167549826375617156571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253175120531481339916336757 23735167549826375617156571)
        ·
          refine ⟨35602751324739563425734857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23735167549826375617156571 35602751324739563425734857)
          ·
            refine ⟨26702063493554672569301143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35602751324739563425734857 26702063493554672569301143)
            ·
              refine ⟨40053095240332008853951715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26702063493554672569301143 40053095240332008853951715)
              ·
                refine ⟨60079642860498013280927573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40053095240332008853951715 60079642860498013280927573)
                ·
                  refine ⟨352029157385730546567935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60079642860498013280927573 352029157385730546567935)
                  ·
                    rfl

theorem cell23_6170169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 9].length) (baseStart_6170169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170169 prefixEnd_6170169 := by exact prefixLift 6170169
  have htrace : WordTrace (prefixWord ++ tailWord_6170169) baseStart_6170169 baseEnd_6170169 := by
    simpa [prefixWord, tailWord_6170169, baseEnd_6170169] using wordTrace_append hprefix tailTrace_6170169
  have hstable : (prefixWord ++ tailWord_6170169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170169).length < 2 ^ (prefixWord ++ tailWord_6170169).sum := by decide
  have hdescent : baseEnd_6170169 < baseStart_6170169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170196 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_6170196 : Nat := 118140960795 + 6170196 * 2 ^ 59
def prefixEnd_6170196 : Nat := 4983230072969 + 3 ^ 40 * 6170196 * 2
def baseEnd_6170196 : Nat := 3168276280449246313473791

theorem tailTrace_6170196 : CollatzResearch.WordTrace tailWord_6170196 prefixEnd_6170196 3168276280449246313473791 := by
  unfold tailWord_6170196
  simp only [CollatzResearch.WordTrace]
  refine ⟨112522768177220576212877221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150030357569627434950502961 112522768177220576212877221)
  ·
    refine ⟨21098019033228858039914479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112522768177220576212877221 21098019033228858039914479)
    ·
      refine ⟨31647028549843287059871719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21098019033228858039914479 31647028549843287059871719)
      ·
        refine ⟨47470542824764930589807579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31647028549843287059871719 47470542824764930589807579)
        ·
          refine ⟨71205814237147395884711369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47470542824764930589807579 71205814237147395884711369)
          ·
            refine ⟨53404360677860546913533527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71205814237147395884711369 53404360677860546913533527)
            ·
              refine ⟨80106541016790820370300291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53404360677860546913533527 80106541016790820370300291)
              ·
                refine ⟨120159811525186230555450437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80106541016790820370300291 120159811525186230555450437)
                ·
                  refine ⟨22529964660972418229146957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120159811525186230555450437 22529964660972418229146957)
                  ·
                    refine ⟨8448736747864656835930109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22529964660972418229146957 8448736747864656835930109)
                    ·
                      refine ⟨3168276280449246313473791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8448736747864656835930109 3168276280449246313473791)
                      ·
                        rfl

theorem cell23_6170196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_6170196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170196 prefixEnd_6170196 := by exact prefixLift 6170196
  have htrace : WordTrace (prefixWord ++ tailWord_6170196) baseStart_6170196 baseEnd_6170196 := by
    simpa [prefixWord, tailWord_6170196, baseEnd_6170196] using wordTrace_append hprefix tailTrace_6170196
  have hstable : (prefixWord ++ tailWord_6170196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170196).length < 2 ^ (prefixWord ++ tailWord_6170196).sum := by decide
  have hdescent : baseEnd_6170196 < baseStart_6170196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170209 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_6170209 : Nat := 118140960795 + 6170209 * 2 ^ 59
def prefixEnd_6170209 : Nat := 4983230072969 + 3 ^ 40 * 6170209 * 2
def baseEnd_6170209 : Nat := 3168282955697754762611231

theorem tailTrace_6170209 : CollatzResearch.WordTrace tailWord_6170209 prefixEnd_6170209 3168282955697754762611231 := by
  unfold tailWord_6170209
  simp only [CollatzResearch.WordTrace]
  refine ⟨225046010503394055645977681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150030673668929370430651787 225046010503394055645977681)
  ·
    refine ⟨168784507877545541734483261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225046010503394055645977681 168784507877545541734483261)
    ·
      refine ⟨63294190454079578150431223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168784507877545541734483261 63294190454079578150431223)
      ·
        refine ⟨94941285681119367225646835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63294190454079578150431223 94941285681119367225646835)
        ·
          refine ⟨142411928521679050838470253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94941285681119367225646835 142411928521679050838470253)
          ·
            refine ⟨53404473195629644064426345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142411928521679050838470253 53404473195629644064426345)
            ·
              refine ⟨40053354896722233048319759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53404473195629644064426345 40053354896722233048319759)
              ·
                refine ⟨60080032345083349572479639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40053354896722233048319759 60080032345083349572479639)
                ·
                  refine ⟨90120048517625024358719459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60080032345083349572479639 90120048517625024358719459)
                  ·
                    refine ⟨135180072776437536538079189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90120048517625024358719459 135180072776437536538079189)
                    ·
                      refine ⟨3168282955697754762611231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135180072776437536538079189 3168282955697754762611231)
                      ·
                        rfl

theorem cell23_6170209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_6170209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170209 prefixEnd_6170209 := by exact prefixLift 6170209
  have htrace : WordTrace (prefixWord ++ tailWord_6170209) baseStart_6170209 baseEnd_6170209 := by
    simpa [prefixWord, tailWord_6170209, baseEnd_6170209] using wordTrace_append hprefix tailTrace_6170209
  have hstable : (prefixWord ++ tailWord_6170209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170209).length < 2 ^ (prefixWord ++ tailWord_6170209).sum := by decide
  have hdescent : baseEnd_6170209 < baseStart_6170209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170216 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 1, 7]
def baseStart_6170216 : Nat := 118140960795 + 6170216 * 2 ^ 59
def prefixEnd_6170216 : Nat := 4983230072969 + 3 ^ 40 * 6170216 * 2
def baseEnd_6170216 : Nat := 1056095516687445411741233

theorem tailTrace_6170216 : CollatzResearch.WordTrace tailWord_6170216 prefixEnd_6170216 1056095516687445411741233 := by
  unfold tailWord_6170216
  simp only [CollatzResearch.WordTrace]
  refine ⟨112523132907184347920741251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150030843876245797227655001 112523132907184347920741251)
  ·
    refine ⟨168784699360776521881111877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112523132907184347920741251 168784699360776521881111877)
    ·
      refine ⟨31647131130145597852708477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168784699360776521881111877 31647131130145597852708477)
      ·
        refine ⟨11867674173804599194765679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31647131130145597852708477 11867674173804599194765679)
        ·
          refine ⟨17801511260706898792148519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11867674173804599194765679 17801511260706898792148519)
          ·
            refine ⟨26702266891060348188222779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17801511260706898792148519 26702266891060348188222779)
            ·
              refine ⟨40053400336590522282334169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26702266891060348188222779 40053400336590522282334169)
              ·
                refine ⟨30040050252442891711750627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40053400336590522282334169 30040050252442891711750627)
                ·
                  refine ⟨45060075378664337567625941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30040050252442891711750627 45060075378664337567625941)
                  ·
                    refine ⟨1056095516687445411741233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45060075378664337567625941 1056095516687445411741233)
                    ·
                      rfl

theorem cell23_6170216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_6170216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170216 prefixEnd_6170216 := by exact prefixLift 6170216
  have htrace : WordTrace (prefixWord ++ tailWord_6170216) baseStart_6170216 baseEnd_6170216 := by
    simpa [prefixWord, tailWord_6170216, baseEnd_6170216] using wordTrace_append hprefix tailTrace_6170216
  have hstable : (prefixWord ++ tailWord_6170216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170216).length < 2 ^ (prefixWord ++ tailWord_6170216).sum := by decide
  have hdescent : baseEnd_6170216 < baseStart_6170216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170236 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_6170236 : Nat := 118140960795 + 6170236 * 2 ^ 59
def prefixEnd_6170236 : Nat := 4983230072969 + 3 ^ 40 * 6170236 * 2
def baseEnd_6170236 : Nat := 3168296819675426156973607

theorem tailTrace_6170236 : CollatzResearch.WordTrace tailWord_6170236 prefixEnd_6170236 3168296819675426156973607 := by
  unfold tailWord_6170236
  simp only [CollatzResearch.WordTrace]
  refine ⟨112523497637148119628605281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150031330182864159504807041 112523497637148119628605281)
  ·
    refine ⟨84392623227861089721453961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112523497637148119628605281 84392623227861089721453961)
    ·
      refine ⟨63294467420895817291090471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84392623227861089721453961 63294467420895817291090471)
      ·
        refine ⟨94941701131343725936635707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63294467420895817291090471 94941701131343725936635707)
        ·
          refine ⟨142412551697015588904953561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94941701131343725936635707 142412551697015588904953561)
          ·
            refine ⟨106809413772761691678715171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142412551697015588904953561 106809413772761691678715171)
            ·
              refine ⟨160214120659142537518072757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106809413772761691678715171 160214120659142537518072757)
              ·
                refine ⟨15020073811794612892319321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160214120659142537518072757 15020073811794612892319321)
                ·
                  refine ⟨11265055358845959669239491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15020073811794612892319321 11265055358845959669239491)
                  ·
                    refine ⟨16897583038268939503859237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11265055358845959669239491 16897583038268939503859237)
                    ·
                      refine ⟨3168296819675426156973607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16897583038268939503859237 3168296819675426156973607)
                      ·
                        rfl

theorem cell23_6170236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_6170236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170236 prefixEnd_6170236 := by exact prefixLift 6170236
  have htrace : WordTrace (prefixWord ++ tailWord_6170236) baseStart_6170236 baseEnd_6170236 := by
    simpa [prefixWord, tailWord_6170236, baseEnd_6170236] using wordTrace_append hprefix tailTrace_6170236
  have hstable : (prefixWord ++ tailWord_6170236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170236).length < 2 ^ (prefixWord ++ tailWord_6170236).sum := by decide
  have hdescent : baseEnd_6170236 < baseStart_6170236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170249 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_6170249 : Nat := 118140960795 + 6170249 * 2 ^ 59
def prefixEnd_6170249 : Nat := 4983230072969 + 3 ^ 40 * 6170249 * 2
def baseEnd_6170249 : Nat := 3168303494923934606111047

theorem tailTrace_6170249 : CollatzResearch.WordTrace tailWord_6170249 prefixEnd_6170249 3168303494923934606111047 := by
  unfold tailWord_6170249
  simp only [CollatzResearch.WordTrace]
  refine ⟨225047469423249142477433801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150031646282166094984955867 225047469423249142477433801)
  ·
    refine ⟨168785602067436856858075351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225047469423249142477433801 168785602067436856858075351)
    ·
      refine ⟨253178403101155285287113027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168785602067436856858075351 253178403101155285287113027)
      ·
        refine ⟨379767604651732927930669541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253178403101155285287113027 379767604651732927930669541)
        ·
          refine ⟨71206425872199923987000539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 379767604651732927930669541 71206425872199923987000539)
          ·
            refine ⟨106809638808299885980500809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71206425872199923987000539 106809638808299885980500809)
            ·
              refine ⟨80107229106224914485375607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106809638808299885980500809 80107229106224914485375607)
              ·
                refine ⟨120160843659337371728063411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80107229106224914485375607 120160843659337371728063411)
                ·
                  refine ⟨180241265489006057592095117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120160843659337371728063411 180241265489006057592095117)
                  ·
                    refine ⟨67590474558377271597035669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180241265489006057592095117 67590474558377271597035669)
                    ·
                      refine ⟨3168303494923934606111047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67590474558377271597035669 3168303494923934606111047)
                      ·
                        rfl

theorem cell23_6170249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_6170249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170249 prefixEnd_6170249 := by exact prefixLift 6170249
  have htrace : WordTrace (prefixWord ++ tailWord_6170249) baseStart_6170249 baseEnd_6170249 := by
    simpa [prefixWord, tailWord_6170249, baseEnd_6170249] using wordTrace_append hprefix tailTrace_6170249
  have hstable : (prefixWord ++ tailWord_6170249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170249).length < 2 ^ (prefixWord ++ tailWord_6170249).sum := by decide
  have hdescent : baseEnd_6170249 < baseStart_6170249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170263 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 3, 4]
def baseStart_6170263 : Nat := 118140960795 + 6170263 * 2 ^ 59
def prefixEnd_6170263 : Nat := 4983230072969 + 3 ^ 40 * 6170263 * 2
def baseEnd_6170263 : Nat := 1056103561217699183778661

theorem tailTrace_6170263 : CollatzResearch.WordTrace tailWord_6170263 prefixEnd_6170263 1056103561217699183778661 := by
  unfold tailWord_6170263
  simp only [CollatzResearch.WordTrace]
  refine ⟨225047980045198422868443443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150031986696798948578962295 225047980045198422868443443)
  ·
    refine ⟨337571970067797634302665165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225047980045198422868443443 337571970067797634302665165)
    ·
      refine ⟨126589488775424112863499437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337571970067797634302665165 126589488775424112863499437)
      ·
        refine ⟨47471058290784042323812289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126589488775424112863499437 47471058290784042323812289)
        ·
          refine ⟨35603293718088031742859217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47471058290784042323812289 35603293718088031742859217)
          ·
            refine ⟨26702470288566023807144413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35603293718088031742859217 26702470288566023807144413)
            ·
              refine ⟨10013426358212258927679155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26702470288566023807144413 10013426358212258927679155)
              ·
                refine ⟨15020139537318388391518733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10013426358212258927679155 15020139537318388391518733)
                ·
                  refine ⟨5632552326494395646819525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15020139537318388391518733 5632552326494395646819525)
                  ·
                    refine ⟨1056103561217699183778661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5632552326494395646819525 1056103561217699183778661)
                    ·
                      rfl

theorem cell23_6170263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_6170263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170263 prefixEnd_6170263 := by exact prefixLift 6170263
  have htrace : WordTrace (prefixWord ++ tailWord_6170263) baseStart_6170263 baseEnd_6170263 := by
    simpa [prefixWord, tailWord_6170263, baseEnd_6170263] using wordTrace_append hprefix tailTrace_6170263
  have hstable : (prefixWord ++ tailWord_6170263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170263).length < 2 ^ (prefixWord ++ tailWord_6170263).sum := by decide
  have hdescent : baseEnd_6170263 < baseStart_6170263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170299 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7]
def baseStart_6170299 : Nat := 118140960795 + 6170299 * 2 ^ 59
def prefixEnd_6170299 : Nat := 4983230072969 + 3 ^ 40 * 6170299 * 2
def baseEnd_6170299 : Nat := 3168329168956659410485817

theorem tailTrace_6170299 : CollatzResearch.WordTrace tailWord_6170299 prefixEnd_6170299 3168329168956659410485817 := by
  unfold tailWord_6170299
  simp only [CollatzResearch.WordTrace]
  refine ⟨225049293073068001016753951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150032862048712000677835967 225049293073068001016753951)
  ·
    refine ⟨337573939609602001525130927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225049293073068001016753951 337573939609602001525130927)
    ·
      refine ⟨506360909414403002287696391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337573939609602001525130927 506360909414403002287696391)
      ·
        refine ⟨759541364121604503431544587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506360909414403002287696391 759541364121604503431544587)
        ·
          refine ⟨1139312046182406755147316881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759541364121604503431544587 1139312046182406755147316881)
          ·
            refine ⟨854484034636805066360487661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139312046182406755147316881 854484034636805066360487661)
            ·
              refine ⟨320431512988801899885182873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 854484034636805066360487661 320431512988801899885182873)
              ·
                refine ⟨240323634741601424913887155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320431512988801899885182873 240323634741601424913887155)
                ·
                  refine ⟨360485452112402137370830733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240323634741601424913887155 360485452112402137370830733)
                  ·
                    refine ⟨135182044542150801514061525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 360485452112402137370830733 135182044542150801514061525)
                    ·
                      refine ⟨3168329168956659410485817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135182044542150801514061525 3168329168956659410485817)
                      ·
                        rfl

theorem cell23_6170299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_6170299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170299 prefixEnd_6170299 := by exact prefixLift 6170299
  have htrace : WordTrace (prefixWord ++ tailWord_6170299) baseStart_6170299 baseEnd_6170299 := by
    simpa [prefixWord, tailWord_6170299, baseEnd_6170299] using wordTrace_append hprefix tailTrace_6170299
  have hstable : (prefixWord ++ tailWord_6170299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170299).length < 2 ^ (prefixWord ++ tailWord_6170299).sum := by decide
  have hdescent : baseEnd_6170299 < baseStart_6170299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170314 : List Nat := [3, 1, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_6170314 : Nat := 118140960795 + 6170314 * 2 ^ 59
def prefixEnd_6170314 : Nat := 4983230072969 + 3 ^ 40 * 6170314 * 2
def baseEnd_6170314 : Nat := 1056112290388825617266083

theorem tailTrace_6170314 : CollatzResearch.WordTrace tailWord_6170314 prefixEnd_6170314 1056112290388825617266083 := by
  unfold tailWord_6170314
  simp only [CollatzResearch.WordTrace]
  refine ⟨56262460042003414644637499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150033226778675772385699997 56262460042003414644637499)
  ·
    refine ⟨84393690063005121966956249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56262460042003414644637499 84393690063005121966956249)
    ·
      refine ⟨63295267547253841475217187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84393690063005121966956249 63295267547253841475217187)
      ·
        refine ⟨94942901320880762212825781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63295267547253841475217187 94942901320880762212825781)
        ·
          refine ⟨8900896998832571457452417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94942901320880762212825781 8900896998832571457452417)
          ·
            refine ⟨6675672749124428593089313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8900896998832571457452417 6675672749124428593089313)
            ·
              refine ⟨5006754561843321444816985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6675672749124428593089313 5006754561843321444816985)
              ·
                refine ⟨3755065921382491083612739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5006754561843321444816985 3755065921382491083612739)
                ·
                  refine ⟨5632598882073736625419109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755065921382491083612739 5632598882073736625419109)
                  ·
                    refine ⟨1056112290388825617266083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5632598882073736625419109 1056112290388825617266083)
                    ·
                      rfl

theorem cell23_6170314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_6170314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170314 prefixEnd_6170314 := by exact prefixLift 6170314
  have htrace : WordTrace (prefixWord ++ tailWord_6170314) baseStart_6170314 baseEnd_6170314 := by
    simpa [prefixWord, tailWord_6170314, baseEnd_6170314] using wordTrace_append hprefix tailTrace_6170314
  have hstable : (prefixWord ++ tailWord_6170314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170314).length < 2 ^ (prefixWord ++ tailWord_6170314).sum := by decide
  have hdescent : baseEnd_6170314 < baseStart_6170314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170336 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 1, 6]
def baseStart_6170336 : Nat := 118140960795 + 6170336 * 2 ^ 59
def prefixEnd_6170336 : Nat := 4983230072969 + 3 ^ 40 * 6170336 * 2
def baseEnd_6170336 : Nat := 1056116055913625255241049

theorem tailTrace_6170336 : CollatzResearch.WordTrace tailWord_6170336 prefixEnd_6170336 1056116055913625255241049 := by
  unfold tailWord_6170336
  simp only [CollatzResearch.WordTrace]
  refine ⟨112525321286966978167925431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150033761715955970890567241 112525321286966978167925431)
  ·
    refine ⟨168787981930450467251888147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112525321286966978167925431 168787981930450467251888147)
    ·
      refine ⟨253181972895675700877832221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168787981930450467251888147 253181972895675700877832221)
      ·
        refine ⟨94943239835878387829187083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253181972895675700877832221 94943239835878387829187083)
        ·
          refine ⟨142414859753817581743780625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94943239835878387829187083 142414859753817581743780625)
          ·
            refine ⟨106811144815363186307835469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142414859753817581743780625 106811144815363186307835469)
            ·
              refine ⟨40054179305761194865438301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106811144815363186307835469 40054179305761194865438301)
              ·
                refine ⟨15020317239660448074539363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40054179305761194865438301 15020317239660448074539363)
                ·
                  refine ⟨22530475859490672111809045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15020317239660448074539363 22530475859490672111809045)
                  ·
                    refine ⟨1056116055913625255241049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22530475859490672111809045 1056116055913625255241049)
                    ·
                      rfl

theorem cell23_6170336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_6170336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170336 prefixEnd_6170336 := by exact prefixLift 6170336
  have htrace : WordTrace (prefixWord ++ tailWord_6170336) baseStart_6170336 baseEnd_6170336 := by
    simpa [prefixWord, tailWord_6170336, baseEnd_6170336] using wordTrace_append hprefix tailTrace_6170336
  have hstable : (prefixWord ++ tailWord_6170336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170336).length < 2 ^ (prefixWord ++ tailWord_6170336).sum := by decide
  have hdescent : baseEnd_6170336 < baseStart_6170336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170370 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6170370 : Nat := 118140960795 + 6170370 * 2 ^ 59
def prefixEnd_6170370 : Nat := 4983230072969 + 3 ^ 40 * 6170370 * 2
def baseEnd_6170370 : Nat := 1056121875361042877565997

theorem tailTrace_6170370 : CollatzResearch.WordTrace tailWord_6170370 prefixEnd_6170370 1056121875361042877565997 := by
  unfold tailWord_6170370
  simp only [CollatzResearch.WordTrace]
  refine ⟨56262970663952695035647141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150034588437207186761725709 56262970663952695035647141)
  ·
    refine ⟨10549306999491130319183839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56262970663952695035647141 10549306999491130319183839)
    ·
      refine ⟨15823960499236695478775759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10549306999491130319183839 15823960499236695478775759)
      ·
        refine ⟨23735940748855043218163639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15823960499236695478775759 23735940748855043218163639)
        ·
          refine ⟨35603911123282564827245459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23735940748855043218163639 35603911123282564827245459)
          ·
            refine ⟨53405866684923847240868189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35603911123282564827245459 53405866684923847240868189)
            ·
              refine ⟨20027200006846442715325571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53405866684923847240868189 20027200006846442715325571)
              ·
                refine ⟨30040800010269664072988357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20027200006846442715325571 30040800010269664072988357)
                ·
                  refine ⟨5632650001925562013685317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30040800010269664072988357 5632650001925562013685317)
                  ·
                    refine ⟨1056121875361042877565997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5632650001925562013685317 1056121875361042877565997)
                    ·
                      rfl

theorem cell23_6170370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6170370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170370 prefixEnd_6170370 := by exact prefixLift 6170370
  have htrace : WordTrace (prefixWord ++ tailWord_6170370) baseStart_6170370 baseEnd_6170370 := by
    simpa [prefixWord, tailWord_6170370, baseEnd_6170370] using wordTrace_append hprefix tailTrace_6170370
  have hstable : (prefixWord ++ tailWord_6170370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170370).length < 2 ^ (prefixWord ++ tailWord_6170370).sum := by decide
  have hdescent : baseEnd_6170370 < baseStart_6170370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170416 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_6170416 : Nat := 118140960795 + 6170416 * 2 ^ 59
def prefixEnd_6170416 : Nat := 4983230072969 + 3 ^ 40 * 6170416 * 2
def baseEnd_6170416 : Nat := 3168389246193235452722779

theorem tailTrace_6170416 : CollatzResearch.WordTrace tailWord_6170416 prefixEnd_6170416 3168389246193235452722779 := by
  unfold tailWord_6170416
  simp only [CollatzResearch.WordTrace]
  refine ⟨112526780206822064999381551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150035706942429419999175401 112526780206822064999381551)
  ·
    refine ⟨168790170310233097499072327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112526780206822064999381551 168790170310233097499072327)
    ·
      refine ⟨253185255465349646248608491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168790170310233097499072327 253185255465349646248608491)
      ·
        refine ⟨379777883198024469372912737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253185255465349646248608491 379777883198024469372912737)
        ·
          refine ⟨284833412398518352029684553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379777883198024469372912737 284833412398518352029684553)
          ·
            refine ⟨213625059298888764022263415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284833412398518352029684553 213625059298888764022263415)
            ·
              refine ⟨320437588948333146033395123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213625059298888764022263415 320437588948333146033395123)
              ·
                refine ⟨480656383422499719050092685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320437588948333146033395123 480656383422499719050092685)
                ·
                  refine ⟨180246143783437394643784757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480656383422499719050092685 180246143783437394643784757)
                  ·
                    refine ⟨16898075979697255747854821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 180246143783437394643784757 16898075979697255747854821)
                    ·
                      refine ⟨3168389246193235452722779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16898075979697255747854821 3168389246193235452722779)
                      ·
                        rfl

theorem cell23_6170416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_6170416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170416 prefixEnd_6170416 := by exact prefixLift 6170416
  have htrace : WordTrace (prefixWord ++ tailWord_6170416) baseStart_6170416 baseEnd_6170416 := by
    simpa [prefixWord, tailWord_6170416, baseEnd_6170416] using wordTrace_append hprefix tailTrace_6170416
  have hstable : (prefixWord ++ tailWord_6170416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170416).length < 2 ^ (prefixWord ++ tailWord_6170416).sum := by decide
  have hdescent : baseEnd_6170416 < baseStart_6170416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170453 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_6170453 : Nat := 118140960795 + 6170453 * 2 ^ 59
def prefixEnd_6170453 : Nat := 4983230072969 + 3 ^ 40 * 6170453 * 2
def baseEnd_6170453 : Nat := 3168408244977451807960109

theorem tailTrace_6170453 : CollatzResearch.WordTrace tailWord_6170453 prefixEnd_6170453 3168408244977451807960109 := by
  unfold tailWord_6170453
  simp only [CollatzResearch.WordTrace]
  refine ⟨225054909914510085317860013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150036606609673390211906675 225054909914510085317860013)
  ·
    refine ⟨84395591217941281994197505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225054909914510085317860013 84395591217941281994197505)
    ·
      refine ⟨63296693413455961495648129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84395591217941281994197505 63296693413455961495648129)
      ·
        refine ⟨47472520060091971121736097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63296693413455961495648129 47472520060091971121736097)
        ·
          refine ⟨35604390045068978341302073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47472520060091971121736097 35604390045068978341302073)
          ·
            refine ⟨26703292533801733755976555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35604390045068978341302073 26703292533801733755976555)
            ·
              refine ⟨40054938800702600633964833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26703292533801733755976555 40054938800702600633964833)
              ·
                refine ⟨30041204100526950475473625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40054938800702600633964833 30041204100526950475473625)
                ·
                  refine ⟨22530903075395212856605219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30041204100526950475473625 22530903075395212856605219)
                  ·
                    refine ⟨33796354613092819284907829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22530903075395212856605219 33796354613092819284907829)
                    ·
                      refine ⟨3168408244977451807960109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33796354613092819284907829 3168408244977451807960109)
                      ·
                        rfl

theorem cell23_6170453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_6170453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170453 prefixEnd_6170453 := by exact prefixLift 6170453
  have htrace : WordTrace (prefixWord ++ tailWord_6170453) baseStart_6170453 baseEnd_6170453 := by
    simpa [prefixWord, tailWord_6170453, baseEnd_6170453] using wordTrace_append hprefix tailTrace_6170453
  have hstable : (prefixWord ++ tailWord_6170453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170453).length < 2 ^ (prefixWord ++ tailWord_6170453).sum := by decide
  have hdescent : baseEnd_6170453 < baseStart_6170453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170467 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 1, 4, 2]
def baseStart_6170467 : Nat := 118140960795 + 6170467 * 2 ^ 59
def prefixEnd_6170467 : Nat := 4983230072969 + 3 ^ 40 * 6170467 * 2
def baseEnd_6170467 : Nat := 3168415433706614753185045

theorem tailTrace_6170467 : CollatzResearch.WordTrace tailWord_6170467 prefixEnd_6170467 3168415433706614753185045 := by
  unfold tailWord_6170467
  simp only [CollatzResearch.WordTrace]
  refine ⟨225055420536459365708869655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150036947024306243805913103 225055420536459365708869655)
  ·
    refine ⟨337583130804689048563304483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225055420536459365708869655 337583130804689048563304483)
    ·
      refine ⟨506374696207033572844956725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337583130804689048563304483 506374696207033572844956725)
      ·
        refine ⟨47472627769409397454214693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 506374696207033572844956725 47472627769409397454214693)
        ·
          refine ⟨8901117706764262022665255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47472627769409397454214693 8901117706764262022665255)
          ·
            refine ⟨13351676560146393033997883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901117706764262022665255 13351676560146393033997883)
            ·
              refine ⟨20027514840219589550996825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13351676560146393033997883 20027514840219589550996825)
              ·
                refine ⟨15020636130164692163247619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20027514840219589550996825 15020636130164692163247619)
                ·
                  refine ⟨22530954195247038244871429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15020636130164692163247619 22530954195247038244871429)
                  ·
                    refine ⟨4224553911608819670913393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22530954195247038244871429 4224553911608819670913393)
                    ·
                      refine ⟨3168415433706614753185045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4224553911608819670913393 3168415433706614753185045)
                      ·
                        rfl

theorem cell23_6170467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_6170467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170467 prefixEnd_6170467 := by exact prefixLift 6170467
  have htrace : WordTrace (prefixWord ++ tailWord_6170467) baseStart_6170467 baseEnd_6170467 := by
    simpa [prefixWord, tailWord_6170467, baseEnd_6170467] using wordTrace_append hprefix tailTrace_6170467
  have hstable : (prefixWord ++ tailWord_6170467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170467).length < 2 ^ (prefixWord ++ tailWord_6170467).sum := by decide
  have hdescent : baseEnd_6170467 < baseStart_6170467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170483 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 3]
def baseStart_6170483 : Nat := 118140960795 + 6170483 * 2 ^ 59
def prefixEnd_6170483 : Nat := 4983230072969 + 3 ^ 40 * 6170483 * 2
def baseEnd_6170483 : Nat := 3168423649397086690584971

theorem tailTrace_6170483 : CollatzResearch.WordTrace tailWord_6170483 prefixEnd_6170483 3168423649397086690584971 := by
  unfold tailWord_6170483
  simp only [CollatzResearch.WordTrace]
  refine ⟨225056004104401400441452103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150037336069600933627634735 225056004104401400441452103)
  ·
    refine ⟨337584006156602100662178155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225056004104401400441452103 337584006156602100662178155)
    ·
      refine ⟨506376009234903150993267233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337584006156602100662178155 506376009234903150993267233)
      ·
        refine ⟨379782006926177363244950425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506376009234903150993267233 379782006926177363244950425)
        ·
          refine ⟨284836505194633022433712819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379782006926177363244950425 284836505194633022433712819)
          ·
            refine ⟨427254757791949533650569229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284836505194633022433712819 427254757791949533650569229)
            ·
              refine ⟨160220534171981075118963461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427254757791949533650569229 160220534171981075118963461)
              ·
                refine ⟨30041350157246451584805649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160220534171981075118963461 30041350157246451584805649)
                ·
                  refine ⟨22531012617934838688604237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30041350157246451584805649 22531012617934838688604237)
                  ·
                    refine ⟨8449129731725564508226589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22531012617934838688604237 8449129731725564508226589)
                    ·
                      refine ⟨3168423649397086690584971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8449129731725564508226589 3168423649397086690584971)
                      ·
                        rfl

theorem cell23_6170483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_6170483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170483 prefixEnd_6170483 := by exact prefixLift 6170483
  have htrace : WordTrace (prefixWord ++ tailWord_6170483) baseStart_6170483 baseEnd_6170483 := by
    simpa [prefixWord, tailWord_6170483, baseEnd_6170483] using wordTrace_append hprefix tailTrace_6170483
  have hstable : (prefixWord ++ tailWord_6170483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170483).length < 2 ^ (prefixWord ++ tailWord_6170483).sum := by decide
  have hdescent : baseEnd_6170483 < baseStart_6170483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170497 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6170497 : Nat := 118140960795 + 6170497 * 2 ^ 59
def prefixEnd_6170497 : Nat := 4983230072969 + 3 ^ 40 * 6170497 * 2
def baseEnd_6170497 : Nat := 3168430838126249635809907

theorem tailTrace_6170497 : CollatzResearch.WordTrace tailWord_6170497 prefixEnd_6170497 3168430838126249635809907 := by
  unfold tailWord_6170497
  simp only [CollatzResearch.WordTrace]
  refine ⟨225056514726350680832461745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150037676484233787221641163 225056514726350680832461745)
  ·
    refine ⟨168792386044763010624346309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225056514726350680832461745 168792386044763010624346309)
    ·
      refine ⟨31648572383393064492064933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168792386044763010624346309 31648572383393064492064933)
      ·
        refine ⟨5934107321886199592262175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31648572383393064492064933 5934107321886199592262175)
        ·
          refine ⟨8901160982829299388393263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934107321886199592262175 8901160982829299388393263)
          ·
            refine ⟨13351741474243949082589895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901160982829299388393263 13351741474243949082589895)
            ·
              refine ⟨20027612211365923623884843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13351741474243949082589895 20027612211365923623884843)
              ·
                refine ⟨30041418317048885435827265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20027612211365923623884843 30041418317048885435827265)
                ·
                  refine ⟨22531063737786664076870449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30041418317048885435827265 22531063737786664076870449)
                  ·
                    refine ⟨16898297803339998057652837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22531063737786664076870449 16898297803339998057652837)
                    ·
                      refine ⟨3168430838126249635809907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16898297803339998057652837 3168430838126249635809907)
                      ·
                        rfl

theorem cell23_6170497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6170497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170497 prefixEnd_6170497 := by exact prefixLift 6170497
  have htrace : WordTrace (prefixWord ++ tailWord_6170497) baseStart_6170497 baseEnd_6170497 := by
    simpa [prefixWord, tailWord_6170497, baseEnd_6170497] using wordTrace_append hprefix tailTrace_6170497
  have hstable : (prefixWord ++ tailWord_6170497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170497).length < 2 ^ (prefixWord ++ tailWord_6170497).sum := by decide
  have hdescent : baseEnd_6170497 < baseStart_6170497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170553 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6170553 : Nat := 118140960795 + 6170553 * 2 ^ 59
def prefixEnd_6170553 : Nat := 4983230072969 + 3 ^ 40 * 6170553 * 2
def baseEnd_6170553 : Nat := 3168459593042901416709649

theorem tailTrace_6170553 : CollatzResearch.WordTrace tailWord_6170553 prefixEnd_6170553 3168459593042901416709649 := by
  unfold tailWord_6170553
  simp only [CollatzResearch.WordTrace]
  refine ⟨225058557214147802396500313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150039038142765201597666875 225058557214147802396500313)
  ·
    refine ⟨168793917910610851797375235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225058557214147802396500313 168793917910610851797375235)
    ·
      refine ⟨253190876865916277696062853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168793917910610851797375235 253190876865916277696062853)
      ·
        refine ⟨47473289412359302068011785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253190876865916277696062853 47473289412359302068011785)
        ·
          refine ⟨35604967059269476551008839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47473289412359302068011785 35604967059269476551008839)
          ·
            refine ⟨53407450588904214826513259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35604967059269476551008839 53407450588904214826513259)
            ·
              refine ⟨80111175883356322239769889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53407450588904214826513259 80111175883356322239769889)
              ·
                refine ⟨60083381912517241679827417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80111175883356322239769889 60083381912517241679827417)
                ·
                  refine ⟨45062536434387931259870563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60083381912517241679827417 45062536434387931259870563)
                  ·
                    refine ⟨67593804651581896889805845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45062536434387931259870563 67593804651581896889805845)
                    ·
                      refine ⟨3168459593042901416709649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67593804651581896889805845 3168459593042901416709649)
                      ·
                        rfl

theorem cell23_6170553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6170553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170553 prefixEnd_6170553 := by exact prefixLift 6170553
  have htrace : WordTrace (prefixWord ++ tailWord_6170553) baseStart_6170553 baseEnd_6170553 := by
    simpa [prefixWord, tailWord_6170553, baseEnd_6170553] using wordTrace_append hprefix tailTrace_6170553
  have hstable : (prefixWord ++ tailWord_6170553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170553).length < 2 ^ (prefixWord ++ tailWord_6170553).sum := by decide
  have hdescent : baseEnd_6170553 < baseStart_6170553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170557 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_6170557 : Nat := 118140960795 + 6170557 * 2 ^ 59
def prefixEnd_6170557 : Nat := 4983230072969 + 3 ^ 40 * 6170557 * 2
def baseEnd_6170557 : Nat := 3168461646965519401059631

theorem tailTrace_6170557 : CollatzResearch.WordTrace tailWord_6170557 prefixEnd_6170557 3168461646965519401059631 := by
  unfold tailWord_6170557
  simp only [CollatzResearch.WordTrace]
  refine ⟨225058703106133311079645925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150039135404088874053097283 225058703106133311079645925)
  ·
    refine ⟨42198506832399995827433611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225058703106133311079645925 42198506832399995827433611)
    ·
      refine ⟨63297760248599993741150417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42198506832399995827433611 63297760248599993741150417)
      ·
        refine ⟨47473320186449995305862813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63297760248599993741150417 47473320186449995305862813)
        ·
          refine ⟨17802495069918748239698555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47473320186449995305862813 17802495069918748239698555)
          ·
            refine ⟨26703742604878122359547833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17802495069918748239698555 26703742604878122359547833)
            ·
              refine ⟨20027806953658591769660875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26703742604878122359547833 20027806953658591769660875)
              ·
                refine ⟨30041710430487887654491313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20027806953658591769660875 30041710430487887654491313)
                ·
                  refine ⟨22531282822865915740868485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30041710430487887654491313 22531282822865915740868485)
                  ·
                    refine ⟨4224615529287359201412841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22531282822865915740868485 4224615529287359201412841)
                    ·
                      refine ⟨3168461646965519401059631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4224615529287359201412841 3168461646965519401059631)
                      ·
                        rfl

theorem cell23_6170557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_6170557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170557 prefixEnd_6170557 := by exact prefixLift 6170557
  have htrace : WordTrace (prefixWord ++ tailWord_6170557) baseStart_6170557 baseEnd_6170557 := by
    simpa [prefixWord, tailWord_6170557, baseEnd_6170557] using wordTrace_append hprefix tailTrace_6170557
  have hstable : (prefixWord ++ tailWord_6170557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170557).length < 2 ^ (prefixWord ++ tailWord_6170557).sum := by decide
  have hdescent : baseEnd_6170557 < baseStart_6170557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170623 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 5, 6]
def baseStart_6170623 : Nat := 118140960795 + 6170623 * 2 ^ 59
def prefixEnd_6170623 : Nat := 4983230072969 + 3 ^ 40 * 6170623 * 2
def baseEnd_6170623 : Nat := 1056165178896238714278109

theorem tailTrace_6170623 : CollatzResearch.WordTrace tailWord_6170623 prefixEnd_6170623 1056165178896238714278109 := by
  unfold tailWord_6170623
  simp only [CollatzResearch.WordTrace]
  refine ⟨225061110323894204351548523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150040740215929469567699015 225061110323894204351548523)
  ·
    refine ⟨337591665485841306527322785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225061110323894204351548523 337591665485841306527322785)
    ·
      refine ⟨253193749114380979895492089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337591665485841306527322785 253193749114380979895492089)
      ·
        refine ⟨189895311835785734921619067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253193749114380979895492089 189895311835785734921619067)
        ·
          refine ⟨284842967753678602382428601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189895311835785734921619067 284842967753678602382428601)
          ·
            refine ⟨213632225815258951786821451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284842967753678602382428601 213632225815258951786821451)
            ·
              refine ⟨320448338722888427680232177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213632225815258951786821451 320448338722888427680232177)
              ·
                refine ⟨240336254042166320760174133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320448338722888427680232177 240336254042166320760174133)
                ·
                  refine ⟨22531523816453092571266325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240336254042166320760174133 22531523816453092571266325)
                  ·
                    refine ⟨1056165178896238714278109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22531523816453092571266325 1056165178896238714278109)
                    ·
                      rfl

theorem cell23_6170623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_6170623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170623 prefixEnd_6170623 := by exact prefixLift 6170623
  have htrace : WordTrace (prefixWord ++ tailWord_6170623) baseStart_6170623 baseEnd_6170623 := by
    simpa [prefixWord, tailWord_6170623, baseEnd_6170623] using wordTrace_append hprefix tailTrace_6170623
  have hstable : (prefixWord ++ tailWord_6170623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170623).length < 2 ^ (prefixWord ++ tailWord_6170623).sum := by decide
  have hdescent : baseEnd_6170623 < baseStart_6170623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170633 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_6170633 : Nat := 118140960795 + 6170633 * 2 ^ 59
def prefixEnd_6170633 : Nat := 4983230072969 + 3 ^ 40 * 6170633 * 2
def baseEnd_6170633 : Nat := 3168500671495261103709281

theorem tailTrace_6170633 : CollatzResearch.WordTrace tailWord_6170633 prefixEnd_6170633 3168500671495261103709281 := by
  unfold tailWord_6170633
  simp only [CollatzResearch.WordTrace]
  refine ⟨225061475053857976059412553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150040983369238650706275035 225061475053857976059412553)
  ·
    refine ⟨168796106290393482044559415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225061475053857976059412553 168796106290393482044559415)
    ·
      refine ⟨253194159435590223066839123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168796106290393482044559415 253194159435590223066839123)
      ·
        refine ⟨379791239153385334600258685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253194159435590223066839123 379791239153385334600258685)
        ·
          refine ⟨142421714682519500475097007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379791239153385334600258685 142421714682519500475097007)
          ·
            refine ⟨213632572023779250712645511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142421714682519500475097007 213632572023779250712645511)
            ·
              refine ⟨320448858035668876068968267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213632572023779250712645511 320448858035668876068968267)
              ·
                refine ⟨480673287053503314103452401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320448858035668876068968267 480673287053503314103452401)
                ·
                  refine ⟨360504965290127485577589301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480673287053503314103452401 360504965290127485577589301)
                  ·
                    refine ⟨33797340495949451772898997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 360504965290127485577589301 33797340495949451772898997)
                    ·
                      refine ⟨3168500671495261103709281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33797340495949451772898997 3168500671495261103709281)
                      ·
                        rfl

theorem cell23_6170633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_6170633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170633 prefixEnd_6170633 := by exact prefixLift 6170633
  have htrace : WordTrace (prefixWord ++ tailWord_6170633) baseStart_6170633 baseEnd_6170633 := by
    simpa [prefixWord, tailWord_6170633, baseEnd_6170633] using wordTrace_append hprefix tailTrace_6170633
  have hstable : (prefixWord ++ tailWord_6170633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170633).length < 2 ^ (prefixWord ++ tailWord_6170633).sum := by decide
  have hdescent : baseEnd_6170633 < baseStart_6170633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170681 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6170681 : Nat := 118140960795 + 6170681 * 2 ^ 59
def prefixEnd_6170681 : Nat := 4983230072969 + 3 ^ 40 * 6170681 * 2
def baseEnd_6170681 : Nat := 3168525318566676915909061

theorem tailTrace_6170681 : CollatzResearch.WordTrace tailWord_6170681 prefixEnd_6170681 3168525318566676915909061 := by
  unfold tailWord_6170681
  simp only [CollatzResearch.WordTrace]
  refine ⟨225063225757684080257159897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150042150505122720171439931 225063225757684080257159897)
  ·
    refine ⟨168797419318263060192869923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225063225757684080257159897 168797419318263060192869923)
    ·
      refine ⟨253196128977394590289304885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168797419318263060192869923 253196128977394590289304885)
      ·
        refine ⟨23737137091630742839622333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253196128977394590289304885 23737137091630742839622333)
        ·
          refine ⟨8901426409361528564858375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23737137091630742839622333 8901426409361528564858375)
          ·
            refine ⟨13352139614042292847287563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901426409361528564858375 13352139614042292847287563)
            ·
              refine ⟨20028209421063439270931345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13352139614042292847287563 20028209421063439270931345)
              ·
                refine ⟨15021157065797579453198509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20028209421063439270931345 15021157065797579453198509)
                ·
                  refine ⟨5632933899674092294949441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15021157065797579453198509 5632933899674092294949441)
                  ·
                    refine ⟨4224700424755569221212081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5632933899674092294949441 4224700424755569221212081)
                    ·
                      refine ⟨3168525318566676915909061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4224700424755569221212081 3168525318566676915909061)
                      ·
                        rfl

theorem cell23_6170681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6170681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170681 prefixEnd_6170681 := by exact prefixLift 6170681
  have htrace : WordTrace (prefixWord ++ tailWord_6170681) baseStart_6170681 baseEnd_6170681 := by
    simpa [prefixWord, tailWord_6170681, baseEnd_6170681] using wordTrace_append hprefix tailTrace_6170681
  have hstable : (prefixWord ++ tailWord_6170681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170681).length < 2 ^ (prefixWord ++ tailWord_6170681).sum := by decide
  have hdescent : baseEnd_6170681 < baseStart_6170681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170694 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6170694 : Nat := 118140960795 + 6170694 * 2 ^ 59
def prefixEnd_6170694 : Nat := 4983230072969 + 3 ^ 40 * 6170694 * 2
def baseEnd_6170694 : Nat := 3168531993815185365046501

theorem tailTrace_6170694 : CollatzResearch.WordTrace tailWord_6170694 prefixEnd_6170694 3168531993815185365046501 := by
  unfold tailWord_6170694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7033240622082405733668223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150042466604424655651588757 7033240622082405733668223)
  ·
    refine ⟨10549860933123608600502335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7033240622082405733668223 10549860933123608600502335)
    ·
      refine ⟨15824791399685412900753503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10549860933123608600502335 15824791399685412900753503)
      ·
        refine ⟨23737187099528119351130255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15824791399685412900753503 23737187099528119351130255)
        ·
          refine ⟨35605780649292179026695383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23737187099528119351130255 35605780649292179026695383)
          ·
            refine ⟨53408670973938268540043075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35605780649292179026695383 53408670973938268540043075)
            ·
              refine ⟨80113006460907402810064613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53408670973938268540043075 80113006460907402810064613)
              ·
                refine ⟨15021188711420138026887115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80113006460907402810064613 15021188711420138026887115)
                ·
                  refine ⟨22531783067130207040330673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15021188711420138026887115 22531783067130207040330673)
                  ·
                    refine ⟨16898837300347655280248005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22531783067130207040330673 16898837300347655280248005)
                    ·
                      refine ⟨3168531993815185365046501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16898837300347655280248005 3168531993815185365046501)
                      ·
                        rfl

theorem cell23_6170694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6170694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170694 prefixEnd_6170694 := by exact prefixLift 6170694
  have htrace : WordTrace (prefixWord ++ tailWord_6170694) baseStart_6170694 baseEnd_6170694 := by
    simpa [prefixWord, tailWord_6170694, baseEnd_6170694] using wordTrace_append hprefix tailTrace_6170694
  have hstable : (prefixWord ++ tailWord_6170694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170694).length < 2 ^ (prefixWord ++ tailWord_6170694).sum := by decide
  have hdescent : baseEnd_6170694 < baseStart_6170694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170697 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 3]
def baseStart_6170697 : Nat := 118140960795 + 6170697 * 2 ^ 59
def prefixEnd_6170697 : Nat := 4983230072969 + 3 ^ 40 * 6170697 * 2
def baseEnd_6170697 : Nat := 3168533534257148853308987

theorem tailTrace_6170697 : CollatzResearch.WordTrace tailWord_6170697 prefixEnd_6170697 3168533534257148853308987 := by
  unfold tailWord_6170697
  simp only [CollatzResearch.WordTrace]
  refine ⟨225063809325626114989742345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150042539550417409993161563 225063809325626114989742345)
  ·
    refine ⟨168797856994219586242306759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225063809325626114989742345 168797856994219586242306759)
    ·
      refine ⟨253196785491329379363460139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168797856994219586242306759 253196785491329379363460139)
      ·
        refine ⟨379795178236994069045190209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253196785491329379363460139 379795178236994069045190209)
        ·
          refine ⟨284846383677745551783892657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379795178236994069045190209 284846383677745551783892657)
          ·
            refine ⟨213634787758309163837919493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284846383677745551783892657 213634787758309163837919493)
            ·
              refine ⟨40056522704682968219609905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213634787758309163837919493 40056522704682968219609905)
              ·
                refine ⟨30042392028512226164707429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40056522704682968219609905 30042392028512226164707429)
                ·
                  refine ⟨5632948505346042405882643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30042392028512226164707429 5632948505346042405882643)
                  ·
                    refine ⟨8449422758019063608823965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5632948505346042405882643 8449422758019063608823965)
                    ·
                      refine ⟨3168533534257148853308987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8449422758019063608823965 3168533534257148853308987)
                      ·
                        rfl

theorem cell23_6170697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 3].length) (baseStart_6170697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170697 prefixEnd_6170697 := by exact prefixLift 6170697
  have htrace : WordTrace (prefixWord ++ tailWord_6170697) baseStart_6170697 baseEnd_6170697 := by
    simpa [prefixWord, tailWord_6170697, baseEnd_6170697] using wordTrace_append hprefix tailTrace_6170697
  have hstable : (prefixWord ++ tailWord_6170697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170697).length < 2 ^ (prefixWord ++ tailWord_6170697).sum := by decide
  have hdescent : baseEnd_6170697 < baseStart_6170697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170757 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_6170757 : Nat := 118140960795 + 6170757 * 2 ^ 59
def prefixEnd_6170757 : Nat := 4983230072969 + 3 ^ 40 * 6170757 * 2
def baseEnd_6170757 : Nat := 3168564343096418618558711

theorem tailTrace_6170757 : CollatzResearch.WordTrace tailWord_6170757 prefixEnd_6170757 3168564343096418618558711 := by
  unfold tailWord_6170757
  simp only [CollatzResearch.WordTrace]
  refine ⟨225065997705408745236926525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150043998470272496824617683 225065997705408745236926525)
  ·
    refine ⟨84399749139528279463847447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225065997705408745236926525 84399749139528279463847447)
    ·
      refine ⟨126599623709292419195771171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84399749139528279463847447 126599623709292419195771171)
      ·
        refine ⟨189899435563938628793656757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126599623709292419195771171 189899435563938628793656757)
        ·
          refine ⟨17803072084119246449405321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189899435563938628793656757 17803072084119246449405321)
          ·
            refine ⟨13352304063089434837053991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17803072084119246449405321 13352304063089434837053991)
            ·
              refine ⟨20028456094634152255580987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13352304063089434837053991 20028456094634152255580987)
              ·
                refine ⟨30042684141951228383371481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20028456094634152255580987 30042684141951228383371481)
                ·
                  refine ⟨22532013106463421287528611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30042684141951228383371481 22532013106463421287528611)
                  ·
                    refine ⟨33798019659695131931292917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22532013106463421287528611 33798019659695131931292917)
                    ·
                      refine ⟨3168564343096418618558711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33798019659695131931292917 3168564343096418618558711)
                      ·
                        rfl

theorem cell23_6170757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_6170757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170757 prefixEnd_6170757 := by exact prefixLift 6170757
  have htrace : WordTrace (prefixWord ++ tailWord_6170757) baseStart_6170757 baseEnd_6170757 := by
    simpa [prefixWord, tailWord_6170757, baseEnd_6170757] using wordTrace_append hprefix tailTrace_6170757
  have hstable : (prefixWord ++ tailWord_6170757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170757).length < 2 ^ (prefixWord ++ tailWord_6170757).sum := by decide
  have hdescent : baseEnd_6170757 < baseStart_6170757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170777 : List Nat := [1, 2, 1, 2, 1, 2, 1, 8, 5]
def baseStart_6170777 : Nat := 118140960795 + 6170777 * 2 ^ 59
def prefixEnd_6170777 : Nat := 4983230072969 + 3 ^ 40 * 6170777 * 2
def baseEnd_6170777 : Nat := 352063845856612060034291

theorem tailTrace_6170777 : CollatzResearch.WordTrace tailWord_6170777 prefixEnd_6170777 352063845856612060034291 := by
  unfold tailWord_6170777
  simp only [CollatzResearch.WordTrace]
  refine ⟨225066727165336288652654585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150044484776890859101769723 225066727165336288652654585)
  ·
    refine ⟨168800045374002216489490939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225066727165336288652654585 168800045374002216489490939)
    ·
      refine ⟨253200068061003324734236409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168800045374002216489490939 253200068061003324734236409)
      ·
        refine ⟨189900051045752493550677307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253200068061003324734236409 189900051045752493550677307)
        ·
          refine ⟨284850076568628740326015961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189900051045752493550677307 284850076568628740326015961)
          ·
            refine ⟨213637557426471555244511971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284850076568628740326015961 213637557426471555244511971)
            ·
              refine ⟨320456336139707332866767957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213637557426471555244511971 320456336139707332866767957)
              ·
                refine ⟨3755347689137195307032437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 320456336139707332866767957 3755347689137195307032437)
                ·
                  refine ⟨352063845856612060034291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3755347689137195307032437 352063845856612060034291)
                  ·
                    rfl

theorem cell23_6170777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 5].length) (baseStart_6170777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170777 prefixEnd_6170777 := by exact prefixLift 6170777
  have htrace : WordTrace (prefixWord ++ tailWord_6170777) baseStart_6170777 baseEnd_6170777 := by
    simpa [prefixWord, tailWord_6170777, baseEnd_6170777] using wordTrace_append hprefix tailTrace_6170777
  have hstable : (prefixWord ++ tailWord_6170777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170777).length < 2 ^ (prefixWord ++ tailWord_6170777).sum := by decide
  have hdescent : baseEnd_6170777 < baseStart_6170777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170782 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_6170782 : Nat := 118140960795 + 6170782 * 2 ^ 59
def prefixEnd_6170782 : Nat := 4983230072969 + 3 ^ 40 * 6170782 * 2
def baseEnd_6170782 : Nat := 3168577180112781020746097

theorem tailTrace_6170782 : CollatzResearch.WordTrace tailWord_6170782 prefixEnd_6170782 3168577180112781020746097 := by
  unfold tailWord_6170782
  simp only [CollatzResearch.WordTrace]
  refine ⟨28133363691289771813323325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150044606353545449671057733 28133363691289771813323325)
  ·
    refine ⟨10550011384233664429996247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28133363691289771813323325 10550011384233664429996247)
    ·
      refine ⟨15825017076350496644994371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10550011384233664429996247 15825017076350496644994371)
      ·
        refine ⟨23737525614525744967491557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15825017076350496644994371 23737525614525744967491557)
        ·
          refine ⟨4450786052723577181404667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23737525614525744967491557 4450786052723577181404667)
          ·
            refine ⟨6676179079085365772107001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450786052723577181404667 6676179079085365772107001)
            ·
              refine ⟨5007134309314024329080251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6676179079085365772107001 5007134309314024329080251)
              ·
                refine ⟨7510701463971036493620377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5007134309314024329080251 7510701463971036493620377)
                ·
                  refine ⟨5633026097978277370215283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7510701463971036493620377 5633026097978277370215283)
                  ·
                    refine ⟨8449539146967416055322925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5633026097978277370215283 8449539146967416055322925)
                    ·
                      refine ⟨3168577180112781020746097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8449539146967416055322925 3168577180112781020746097)
                      ·
                        rfl

theorem cell23_6170782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_6170782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170782 prefixEnd_6170782 := by exact prefixLift 6170782
  have htrace : WordTrace (prefixWord ++ tailWord_6170782) baseStart_6170782 baseEnd_6170782 := by
    simpa [prefixWord, tailWord_6170782, baseEnd_6170782] using wordTrace_append hprefix tailTrace_6170782
  have hstable : (prefixWord ++ tailWord_6170782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170782).length < 2 ^ (prefixWord ++ tailWord_6170782).sum := by decide
  have hdescent : baseEnd_6170782 < baseStart_6170782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170788 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_6170788 : Nat := 118140960795 + 6170788 * 2 ^ 59
def prefixEnd_6170788 : Nat := 4983230072969 + 3 ^ 40 * 6170788 * 2
def baseEnd_6170788 : Nat := 3168580260996707997271069

theorem tailTrace_6170788 : CollatzResearch.WordTrace tailWord_6170788 prefixEnd_6170788 3168580260996707997271069 := by
  unfold tailWord_6170788
  simp only [CollatzResearch.WordTrace]
  refine ⟨112533564184148218765652509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150044752245530958354203345 112533564184148218765652509)
  ·
    refine ⟨42200086569055582037119691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112533564184148218765652509 42200086569055582037119691)
    ·
      refine ⟨63300129853583373055679537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42200086569055582037119691 63300129853583373055679537)
      ·
        refine ⟨47475097390187529791759653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63300129853583373055679537 47475097390187529791759653)
        ·
          refine ⟨8901580760660161835954935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47475097390187529791759653 8901580760660161835954935)
          ·
            refine ⟨13352371140990242753932403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901580760660161835954935 13352371140990242753932403)
            ·
              refine ⟨20028556711485364130898605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13352371140990242753932403 20028556711485364130898605)
              ·
                refine ⟨7510708766807011549086977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20028556711485364130898605 7510708766807011549086977)
                ·
                  refine ⟨5633031575105258661815233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7510708766807011549086977 5633031575105258661815233)
                  ·
                    refine ⟨4224773681328943996361425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5633031575105258661815233 4224773681328943996361425)
                    ·
                      refine ⟨3168580260996707997271069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4224773681328943996361425 3168580260996707997271069)
                      ·
                        rfl

theorem cell23_6170788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_6170788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170788 prefixEnd_6170788 := by exact prefixLift 6170788
  have htrace : WordTrace (prefixWord ++ tailWord_6170788) baseStart_6170788 baseEnd_6170788 := by
    simpa [prefixWord, tailWord_6170788, baseEnd_6170788] using wordTrace_append hprefix tailTrace_6170788
  have hstable : (prefixWord ++ tailWord_6170788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170788).length < 2 ^ (prefixWord ++ tailWord_6170788).sum := by decide
  have hdescent : baseEnd_6170788 < baseStart_6170788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170800 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_6170800 : Nat := 118140960795 + 6170800 * 2 ^ 59
def prefixEnd_6170800 : Nat := 4983230072969 + 3 ^ 40 * 6170800 * 2
def baseEnd_6170800 : Nat := 3168586422764561950321013

theorem tailTrace_6170800 : CollatzResearch.WordTrace tailWord_6170800 prefixEnd_6170800 3168586422764561950321013 := by
  unfold tailWord_6170800
  simp only [CollatzResearch.WordTrace]
  refine ⟨112533783022126481790370927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150045044029501975720494569 112533783022126481790370927)
  ·
    refine ⟨168800674533189722685556391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112533783022126481790370927 168800674533189722685556391)
    ·
      refine ⟨253201011799784584028334587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168800674533189722685556391 253201011799784584028334587)
      ·
        refine ⟨379801517699676876042501881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253201011799784584028334587 379801517699676876042501881)
        ·
          refine ⟨284851138274757657031876411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379801517699676876042501881 284851138274757657031876411)
          ·
            refine ⟨427276707412136485547814617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284851138274757657031876411 427276707412136485547814617)
            ·
              refine ⟨320457530559102364160860963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427276707412136485547814617 320457530559102364160860963)
              ·
                refine ⟨480686295838653546241291445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320457530559102364160860963 480686295838653546241291445)
                ·
                  refine ⟨45064340234873769960121073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480686295838653546241291445 45064340234873769960121073)
                  ·
                    refine ⟨33798255176155327470090805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45064340234873769960121073 33798255176155327470090805)
                    ·
                      refine ⟨3168586422764561950321013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33798255176155327470090805 3168586422764561950321013)
                      ·
                        rfl

theorem cell23_6170800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_6170800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170800 prefixEnd_6170800 := by exact prefixLift 6170800
  have htrace : WordTrace (prefixWord ++ tailWord_6170800) baseStart_6170800 baseEnd_6170800 := by
    simpa [prefixWord, tailWord_6170800, baseEnd_6170800] using wordTrace_append hprefix tailTrace_6170800
  have hstable : (prefixWord ++ tailWord_6170800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170800).length < 2 ^ (prefixWord ++ tailWord_6170800).sum := by decide
  have hdescent : baseEnd_6170800 < baseStart_6170800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170807 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 2, 5]
def baseStart_6170807 : Nat := 118140960795 + 6170807 * 2 ^ 59
def prefixEnd_6170807 : Nat := 4983230072969 + 3 ^ 40 * 6170807 * 2
def baseEnd_6170807 : Nat := 1056196672376381140977827

theorem tailTrace_6170807 : CollatzResearch.WordTrace tailWord_6170807 prefixEnd_6170807 1056196672376381140977827 := by
  unfold tailWord_6170807
  simp only [CollatzResearch.WordTrace]
  refine ⟨225067821355227603776246675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150045214236818402517497783 225067821355227603776246675)
  ·
    refine ⟨337601732032841405664370013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225067821355227603776246675 337601732032841405664370013)
    ·
      refine ⟨126600649512315527124138755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337601732032841405664370013 126600649512315527124138755)
      ·
        refine ⟨189900974268473290686208133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126600649512315527124138755 189900974268473290686208133)
        ·
          refine ⟨35606432675338742003664025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189900974268473290686208133 35606432675338742003664025)
          ·
            refine ⟨26704824506504056502748019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35606432675338742003664025 26704824506504056502748019)
            ·
              refine ⟨40057236759756084754122029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26704824506504056502748019 40057236759756084754122029)
              ·
                refine ⟨15021463784908531782795761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40057236759756084754122029 15021463784908531782795761)
                ·
                  refine ⟨11266097838681398837096821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15021463784908531782795761 11266097838681398837096821)
                  ·
                    refine ⟨1056196672376381140977827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11266097838681398837096821 1056196672376381140977827)
                    ·
                      rfl

theorem cell23_6170807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_6170807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170807 prefixEnd_6170807 := by exact prefixLift 6170807
  have htrace : WordTrace (prefixWord ++ tailWord_6170807) baseStart_6170807 baseEnd_6170807 := by
    simpa [prefixWord, tailWord_6170807, baseEnd_6170807] using wordTrace_append hprefix tailTrace_6170807
  have hstable : (prefixWord ++ tailWord_6170807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170807).length < 2 ^ (prefixWord ++ tailWord_6170807).sum := by decide
  have hdescent : baseEnd_6170807 < baseStart_6170807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170827 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 4]
def baseStart_6170827 : Nat := 118140960795 + 6170827 * 2 ^ 59
def prefixEnd_6170827 : Nat := 4983230072969 + 3 ^ 40 * 6170827 * 2
def baseEnd_6170827 : Nat := 3168600286742233344683389

theorem tailTrace_6170827 : CollatzResearch.WordTrace tailWord_6170827 prefixEnd_6170827 3168600286742233344683389 := by
  unfold tailWord_6170827
  simp only [CollatzResearch.WordTrace]
  refine ⟨225068550815155147191974735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150045700543436764794649823 225068550815155147191974735)
  ·
    refine ⟨337602826222732720787962103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225068550815155147191974735 337602826222732720787962103)
    ·
      refine ⟨506404239334099081181943155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337602826222732720787962103 506404239334099081181943155)
      ·
        refine ⟨759606359001148621772914733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506404239334099081181943155 759606359001148621772914733)
        ·
          refine ⟨284852384625430733164843025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 759606359001148621772914733 284852384625430733164843025)
          ·
            refine ⟨213639288469073049873632269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284852384625430733164843025 213639288469073049873632269)
            ·
              refine ⟨80114733175902393702612101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213639288469073049873632269 80114733175902393702612101)
              ·
                refine ⟨15021512470481698819239769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80114733175902393702612101 15021512470481698819239769)
                ·
                  refine ⟨11266134352861274114429827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15021512470481698819239769 11266134352861274114429827)
                  ·
                    refine ⟨16899201529291911171644741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11266134352861274114429827 16899201529291911171644741)
                    ·
                      refine ⟨3168600286742233344683389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16899201529291911171644741 3168600286742233344683389)
                      ·
                        rfl

theorem cell23_6170827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 4].length) (baseStart_6170827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170827 prefixEnd_6170827 := by exact prefixLift 6170827
  have htrace : WordTrace (prefixWord ++ tailWord_6170827) baseStart_6170827 baseEnd_6170827 := by
    simpa [prefixWord, tailWord_6170827, baseEnd_6170827] using wordTrace_append hprefix tailTrace_6170827
  have hstable : (prefixWord ++ tailWord_6170827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170827).length < 2 ^ (prefixWord ++ tailWord_6170827).sum := by decide
  have hdescent : baseEnd_6170827 < baseStart_6170827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170847 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 3]
def baseStart_6170847 : Nat := 118140960795 + 6170847 * 2 ^ 59
def prefixEnd_6170847 : Nat := 4983230072969 + 3 ^ 40 * 6170847 * 2
def baseEnd_6170847 : Nat := 3168610556355323266433297

theorem tailTrace_6170847 : CollatzResearch.WordTrace tailWord_6170847 prefixEnd_6170847 3168610556355323266433297 := by
  unfold tailWord_6170847
  simp only [CollatzResearch.WordTrace]
  refine ⟨225069280275082690607702795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150046186850055127071801863 225069280275082690607702795)
  ·
    refine ⟨337603920412624035911554193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225069280275082690607702795 337603920412624035911554193)
    ·
      refine ⟨253202940309468026933665645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337603920412624035911554193 253202940309468026933665645)
      ·
        refine ⟨94951102616050510100124617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253202940309468026933665645 94951102616050510100124617)
        ·
          refine ⟨71213326962037882575093463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94951102616050510100124617 71213326962037882575093463)
          ·
            refine ⟨106819990443056823862640195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71213326962037882575093463 106819990443056823862640195)
            ·
              refine ⟨160229985664585235793960293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106819990443056823862640195 160229985664585235793960293)
              ·
                refine ⟨30043122312109731711367555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160229985664585235793960293 30043122312109731711367555)
                ·
                  refine ⟨45064683468164597567051333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30043122312109731711367555 45064683468164597567051333)
                  ·
                    refine ⟨8449628150280862043822125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45064683468164597567051333 8449628150280862043822125)
                    ·
                      refine ⟨3168610556355323266433297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8449628150280862043822125 3168610556355323266433297)
                      ·
                        rfl

theorem cell23_6170847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_6170847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170847 prefixEnd_6170847 := by exact prefixLift 6170847
  have htrace : WordTrace (prefixWord ++ tailWord_6170847) baseStart_6170847 baseEnd_6170847 := by
    simpa [prefixWord, tailWord_6170847, baseEnd_6170847] using wordTrace_append hprefix tailTrace_6170847
  have hstable : (prefixWord ++ tailWord_6170847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170847).length < 2 ^ (prefixWord ++ tailWord_6170847).sum := by decide
  have hdescent : baseEnd_6170847 < baseStart_6170847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170877 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_6170877 : Nat := 118140960795 + 6170877 * 2 ^ 59
def prefixEnd_6170877 : Nat := 4983230072969 + 3 ^ 40 * 6170877 * 2
def baseEnd_6170877 : Nat := 3168625960774958149058159

theorem tailTrace_6170877 : CollatzResearch.WordTrace tailWord_6170877 prefixEnd_6170877 3168625960774958149058159 := by
  unfold tailWord_6170877
  simp only [CollatzResearch.WordTrace]
  refine ⟨225070374464974005731294885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150046916309982670487529923 225070374464974005731294885)
  ·
    refine ⟨42200695212182626074617791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225070374464974005731294885 42200695212182626074617791)
    ·
      refine ⟨63301042818273939111926687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42200695212182626074617791 63301042818273939111926687)
      ·
        refine ⟨94951564227410908667890031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63301042818273939111926687 94951564227410908667890031)
        ·
          refine ⟨142427346341116363001835047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94951564227410908667890031 142427346341116363001835047)
          ·
            refine ⟨213641019511674544502752571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142427346341116363001835047 213641019511674544502752571)
            ·
              refine ⟨320461529267511816754128857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213641019511674544502752571 320461529267511816754128857)
              ·
                refine ⟨240346146950633862565596643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320461529267511816754128857 240346146950633862565596643)
                ·
                  refine ⟨360519220425950793848394965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240346146950633862565596643 360519220425950793848394965)
                  ·
                    refine ⟨8449669228733221730821757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 360519220425950793848394965 8449669228733221730821757)
                    ·
                      refine ⟨3168625960774958149058159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8449669228733221730821757 3168625960774958149058159)
                      ·
                        rfl

theorem cell23_6170877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_6170877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170877 prefixEnd_6170877 := by exact prefixLift 6170877
  have htrace : WordTrace (prefixWord ++ tailWord_6170877) baseStart_6170877 baseEnd_6170877 := by
    simpa [prefixWord, tailWord_6170877, baseEnd_6170877] using wordTrace_append hprefix tailTrace_6170877
  have hstable : (prefixWord ++ tailWord_6170877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170877).length < 2 ^ (prefixWord ++ tailWord_6170877).sum := by decide
  have hdescent : baseEnd_6170877 < baseStart_6170877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170884 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 8]
def baseStart_6170884 : Nat := 118140960795 + 6170884 * 2 ^ 59
def prefixEnd_6170884 : Nat := 4983230072969 + 3 ^ 40 * 6170884 * 2
def baseEnd_6170884 : Nat := 352069950571059957963403

theorem tailTrace_6170884 : CollatzResearch.WordTrace tailWord_6170884 prefixEnd_6170884 352069950571059957963403 := by
  unfold tailWord_6170884
  simp only [CollatzResearch.WordTrace]
  refine ⟨112535314887974322963399853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150047086517299097284533137 112535314887974322963399853)
  ·
    refine ⟨42200743082990371111274945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112535314887974322963399853 42200743082990371111274945)
    ·
      refine ⟨31650557312242778333456209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42200743082990371111274945 31650557312242778333456209)
      ·
        refine ⟨23737917984182083750092157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31650557312242778333456209 23737917984182083750092157)
        ·
          refine ⟨8901719244068281406284559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23737917984182083750092157 8901719244068281406284559)
          ·
            refine ⟨13352578866102422109426839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901719244068281406284559 13352578866102422109426839)
            ·
              refine ⟨20028868299153633164140259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13352578866102422109426839 20028868299153633164140259)
              ·
                refine ⟨30043302448730449746210389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20028868299153633164140259 30043302448730449746210389)
                ·
                  refine ⟨352069950571059957963403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30043302448730449746210389 352069950571059957963403)
                  ·
                    rfl

theorem cell23_6170884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_6170884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170884 prefixEnd_6170884 := by exact prefixLift 6170884
  have htrace : WordTrace (prefixWord ++ tailWord_6170884) baseStart_6170884 baseEnd_6170884 := by
    simpa [prefixWord, tailWord_6170884, baseEnd_6170884] using wordTrace_append hprefix tailTrace_6170884
  have hstable : (prefixWord ++ tailWord_6170884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170884).length < 2 ^ (prefixWord ++ tailWord_6170884).sum := by decide
  have hdescent : baseEnd_6170884 < baseStart_6170884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170904 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 3, 5, 2]
def baseStart_6170904 : Nat := 118140960795 + 6170904 * 2 ^ 59
def prefixEnd_6170904 : Nat := 4983230072969 + 3 ^ 40 * 6170904 * 2
def baseEnd_6170904 : Nat := 3168639824752629543420535

theorem tailTrace_6170904 : CollatzResearch.WordTrace tailWord_6170904 prefixEnd_6170904 3168639824752629543420535 := by
  unfold tailWord_6170904
  simp only [CollatzResearch.WordTrace]
  refine ⟨112535679617938094671263883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150047572823917459561685177 112535679617938094671263883)
  ·
    refine ⟨168803519426907142006895825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112535679617938094671263883 168803519426907142006895825)
    ·
      refine ⟨126602639570180356505171869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168803519426907142006895825 126602639570180356505171869)
      ·
        refine ⟨47475989838817633689439451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126602639570180356505171869 47475989838817633689439451)
        ·
          refine ⟨71213984758226450534159177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47475989838817633689439451 71213984758226450534159177)
          ·
            refine ⟨53410488568669837900619383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71213984758226450534159177 53410488568669837900619383)
            ·
              refine ⟨80115732853004756850929075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53410488568669837900619383 80115732853004756850929075)
              ·
                refine ⟨120173599279507135276393613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80115732853004756850929075 120173599279507135276393613)
                ·
                  refine ⟨45065099729815175728647605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120173599279507135276393613 45065099729815175728647605)
                  ·
                    refine ⟨4224853099670172724560713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45065099729815175728647605 4224853099670172724560713)
                    ·
                      refine ⟨3168639824752629543420535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4224853099670172724560713 3168639824752629543420535)
                      ·
                        rfl

theorem cell23_6170904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_6170904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170904 prefixEnd_6170904 := by exact prefixLift 6170904
  have htrace : WordTrace (prefixWord ++ tailWord_6170904) baseStart_6170904 baseEnd_6170904 := by
    simpa [prefixWord, tailWord_6170904, baseEnd_6170904] using wordTrace_append hprefix tailTrace_6170904
  have hstable : (prefixWord ++ tailWord_6170904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170904).length < 2 ^ (prefixWord ++ tailWord_6170904).sum := by decide
  have hdescent : baseEnd_6170904 < baseStart_6170904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170911 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 3]
def baseStart_6170911 : Nat := 118140960795 + 6170911 * 2 ^ 59
def prefixEnd_6170911 : Nat := 4983230072969 + 3 ^ 40 * 6170911 * 2
def baseEnd_6170911 : Nat := 3168643419117211016033003

theorem tailTrace_6170911 : CollatzResearch.WordTrace tailWord_6170911 prefixEnd_6170911 3168643419117211016033003 := by
  unfold tailWord_6170911
  simp only [CollatzResearch.WordTrace]
  refine ⟨225071614546850829538032587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150047743031233886358688391 225071614546850829538032587)
  ·
    refine ⟨337607421820276244307048881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225071614546850829538032587 337607421820276244307048881)
    ·
      refine ⟨253205566365207183230286661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337607421820276244307048881 253205566365207183230286661)
      ·
        refine ⟨47476043693476346855678749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253205566365207183230286661 47476043693476346855678749)
        ·
          refine ⟨17803516385053630070879531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47476043693476346855678749 17803516385053630070879531)
          ·
            refine ⟨26705274577580445106319297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17803516385053630070879531 26705274577580445106319297)
            ·
              refine ⟨20028955933185333829739473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26705274577580445106319297 20028955933185333829739473)
              ·
                refine ⟨15021716949889000372304605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20028955933185333829739473 15021716949889000372304605)
                ·
                  refine ⟨5633143856208375139614227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15021716949889000372304605 5633143856208375139614227)
                  ·
                    refine ⟨8449715784312562709421341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5633143856208375139614227 8449715784312562709421341)
                    ·
                      refine ⟨3168643419117211016033003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8449715784312562709421341 3168643419117211016033003)
                      ·
                        rfl

theorem cell23_6170911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_6170911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170911 prefixEnd_6170911 := by exact prefixLift 6170911
  have htrace : WordTrace (prefixWord ++ tailWord_6170911) baseStart_6170911 baseEnd_6170911 := by
    simpa [prefixWord, tailWord_6170911, baseEnd_6170911] using wordTrace_append hprefix tailTrace_6170911
  have hstable : (prefixWord ++ tailWord_6170911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170911).length < 2 ^ (prefixWord ++ tailWord_6170911).sum := by decide
  have hdescent : baseEnd_6170911 < baseStart_6170911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170922 : List Nat := [3, 1, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_6170922 : Nat := 118140960795 + 6170922 * 2 ^ 59
def prefixEnd_6170922 : Nat := 4983230072969 + 3 ^ 40 * 6170922 * 2
def baseEnd_6170922 : Nat := 1056216355801470157665151

theorem tailTrace_6170922 : CollatzResearch.WordTrace tailWord_6170922 prefixEnd_6170922 1056216355801470157665151 := by
  unfold tailWord_6170922
  simp only [CollatzResearch.WordTrace]
  refine ⟨56268003937452744604170755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150048010499873985611122013 56268003937452744604170755)
  ·
    refine ⟨84402005906179116906256133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56268003937452744604170755 84402005906179116906256133)
    ·
      refine ⟨15825376107408584419923025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84402005906179116906256133 15825376107408584419923025)
      ·
        refine ⟨11869032080556438314942269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15825376107408584419923025 11869032080556438314942269)
        ·
          refine ⟨4450887030208664368103351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11869032080556438314942269 4450887030208664368103351)
          ·
            refine ⟨6676330545312996552155027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450887030208664368103351 6676330545312996552155027)
            ·
              refine ⟨10014495817969494828232541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676330545312996552155027 10014495817969494828232541)
              ·
                refine ⟨3755435931738560560587203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10014495817969494828232541 3755435931738560560587203)
                ·
                  refine ⟨5633153897607840840880805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755435931738560560587203 5633153897607840840880805)
                  ·
                    refine ⟨1056216355801470157665151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5633153897607840840880805 1056216355801470157665151)
                    ·
                      rfl

theorem cell23_6170922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_6170922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170922 prefixEnd_6170922 := by exact prefixLift 6170922
  have htrace : WordTrace (prefixWord ++ tailWord_6170922) baseStart_6170922 baseEnd_6170922 := by
    simpa [prefixWord, tailWord_6170922, baseEnd_6170922] using wordTrace_append hprefix tailTrace_6170922
  have hstable : (prefixWord ++ tailWord_6170922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170922).length < 2 ^ (prefixWord ++ tailWord_6170922).sum := by decide
  have hdescent : baseEnd_6170922 < baseStart_6170922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170927 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 1, 6]
def baseStart_6170927 : Nat := 118140960795 + 6170927 * 2 ^ 59
def prefixEnd_6170927 : Nat := 4983230072969 + 3 ^ 40 * 6170927 * 2
def baseEnd_6170927 : Nat := 1056217211602560984477643

theorem tailTrace_6170927 : CollatzResearch.WordTrace tailWord_6170927 prefixEnd_6170927 1056217211602560984477643 := by
  unfold tailWord_6170927
  simp only [CollatzResearch.WordTrace]
  refine ⟨225072198114792864270615035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150048132076528576180410023 225072198114792864270615035)
  ·
    refine ⟨337608297172189296405922553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225072198114792864270615035 337608297172189296405922553)
    ·
      refine ⟨253206222879141972304441915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337608297172189296405922553 253206222879141972304441915)
      ·
        refine ⟨379809334318712958456662873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253206222879141972304441915 379809334318712958456662873)
        ·
          refine ⟨284857000739034718842497155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379809334318712958456662873 284857000739034718842497155)
          ·
            refine ⟨427285501108552078263745733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284857000739034718842497155 427285501108552078263745733)
            ·
              refine ⟨80116031457853514674452325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 427285501108552078263745733 80116031457853514674452325)
              ·
                refine ⟨15021755898347534001459811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80116031457853514674452325 15021755898347534001459811)
                ·
                  refine ⟨22532633847521301002189717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15021755898347534001459811 22532633847521301002189717)
                  ·
                    refine ⟨1056217211602560984477643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22532633847521301002189717 1056217211602560984477643)
                    ·
                      rfl

theorem cell23_6170927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_6170927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170927 prefixEnd_6170927 := by exact prefixLift 6170927
  have htrace : WordTrace (prefixWord ++ tailWord_6170927) baseStart_6170927 baseEnd_6170927 := by
    simpa [prefixWord, tailWord_6170927, baseEnd_6170927] using wordTrace_append hprefix tailTrace_6170927
  have hstable : (prefixWord ++ tailWord_6170927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170927).length < 2 ^ (prefixWord ++ tailWord_6170927).sum := by decide
  have hdescent : baseEnd_6170927 < baseStart_6170927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170945 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6170945 : Nat := 118140960795 + 6170945 * 2 ^ 59
def prefixEnd_6170945 : Nat := 4983230072969 + 3 ^ 40 * 6170945 * 2
def baseEnd_6170945 : Nat := 3168660877459463883007847

theorem tailTrace_6170945 : CollatzResearch.WordTrace tailWord_6170945 prefixEnd_6170945 3168660877459463883007847 := by
  unfold tailWord_6170945
  simp only [CollatzResearch.WordTrace]
  refine ⟨225072854628727653344770289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150048569752485102229846859 225072854628727653344770289)
  ·
    refine ⟨168804640971545740008577717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225072854628727653344770289 168804640971545740008577717)
    ·
      refine ⟨15825435091082413125804161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168804640971545740008577717 15825435091082413125804161)
      ·
        refine ⟨11869076318311809844353121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15825435091082413125804161 11869076318311809844353121)
        ·
          refine ⟨8901807238733857383264841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11869076318311809844353121 8901807238733857383264841)
          ·
            refine ⟨6676355429050393037448631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8901807238733857383264841 6676355429050393037448631)
            ·
              refine ⟨10014533143575589556172947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676355429050393037448631 10014533143575589556172947)
              ·
                refine ⟨15021799715363384334259421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10014533143575589556172947 15021799715363384334259421)
                ·
                  refine ⟨5633174893261269125347283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15021799715363384334259421 5633174893261269125347283)
                  ·
                    refine ⟨8449762339891903688020925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5633174893261269125347283 8449762339891903688020925)
                    ·
                      refine ⟨3168660877459463883007847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8449762339891903688020925 3168660877459463883007847)
                      ·
                        rfl

theorem cell23_6170945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6170945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170945 prefixEnd_6170945 := by exact prefixLift 6170945
  have htrace : WordTrace (prefixWord ++ tailWord_6170945) baseStart_6170945 baseEnd_6170945 := by
    simpa [prefixWord, tailWord_6170945, baseEnd_6170945] using wordTrace_append hprefix tailTrace_6170945
  have hstable : (prefixWord ++ tailWord_6170945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170945).length < 2 ^ (prefixWord ++ tailWord_6170945).sum := by decide
  have hdescent : baseEnd_6170945 < baseStart_6170945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170947 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6]
def baseStart_6170947 : Nat := 118140960795 + 6170947 * 2 ^ 59
def prefixEnd_6170947 : Nat := 4983230072969 + 3 ^ 40 * 6170947 * 2
def baseEnd_6170947 : Nat := 3168661904420772875182837

theorem tailTrace_6170947 : CollatzResearch.WordTrace tailWord_6170947 prefixEnd_6170947 3168661904420772875182837 := by
  unfold tailWord_6170947
  simp only [CollatzResearch.WordTrace]
  refine ⟨225072927574720407686343095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150048618383146938457562063 225072927574720407686343095)
  ·
    refine ⟨337609391362080611529514643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225072927574720407686343095 337609391362080611529514643)
    ·
      refine ⟨506414087043120917294271965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337609391362080611529514643 506414087043120917294271965)
      ·
        refine ⟨189905282641170343985351987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506414087043120917294271965 189905282641170343985351987)
        ·
          refine ⟨284857923961755515978027981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189905282641170343985351987 284857923961755515978027981)
          ·
            refine ⟨106821721485658318491760493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284857923961755515978027981 106821721485658318491760493)
            ·
              refine ⟨40058145557121869434410185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106821721485658318491760493 40058145557121869434410185)
              ·
                refine ⟨30043609167841402075807639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40058145557121869434410185 30043609167841402075807639)
                ·
                  refine ⟨45065413751762103113711459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30043609167841402075807639 45065413751762103113711459)
                  ·
                    refine ⟨67598120627643154670567189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45065413751762103113711459 67598120627643154670567189)
                    ·
                      refine ⟨3168661904420772875182837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67598120627643154670567189 3168661904420772875182837)
                      ·
                        rfl

theorem cell23_6170947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_6170947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170947 prefixEnd_6170947 := by exact prefixLift 6170947
  have htrace : WordTrace (prefixWord ++ tailWord_6170947) baseStart_6170947 baseEnd_6170947 := by
    simpa [prefixWord, tailWord_6170947, baseEnd_6170947] using wordTrace_append hprefix tailTrace_6170947
  have hstable : (prefixWord ++ tailWord_6170947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170947).length < 2 ^ (prefixWord ++ tailWord_6170947).sum := by decide
  have hdescent : baseEnd_6170947 < baseStart_6170947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170961 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 2, 4]
def baseStart_6170961 : Nat := 118140960795 + 6170961 * 2 ^ 59
def prefixEnd_6170961 : Nat := 4983230072969 + 3 ^ 40 * 6170961 * 2
def baseEnd_6170961 : Nat := 1056223031049978606802591

theorem tailTrace_6170961 : CollatzResearch.WordTrace tailWord_6170961 prefixEnd_6170961 1056223031049978606802591 := by
  unfold tailWord_6170961
  simp only [CollatzResearch.WordTrace]
  refine ⟨225073438196669688077352737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150048958797779792051568491 225073438196669688077352737)
  ·
    refine ⟨168805078647502266058014553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225073438196669688077352737 168805078647502266058014553)
    ·
      refine ⟨126603808985626699543510915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168805078647502266058014553 126603808985626699543510915)
      ·
        refine ⟨189905713478440049315266373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126603808985626699543510915 189905713478440049315266373)
        ·
          refine ⟨35607321277207509246612445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189905713478440049315266373 35607321277207509246612445)
          ·
            refine ⟨13352745478952815967479667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35607321277207509246612445 13352745478952815967479667)
            ·
              refine ⟨20029118218429223951219501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13352745478952815967479667 20029118218429223951219501)
              ·
                refine ⟨7510919331910958981707313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20029118218429223951219501 7510919331910958981707313)
                ·
                  refine ⟨5633189498933219236280485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7510919331910958981707313 5633189498933219236280485)
                  ·
                    refine ⟨1056223031049978606802591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5633189498933219236280485 1056223031049978606802591)
                    ·
                      rfl

theorem cell23_6170961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_6170961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170961 prefixEnd_6170961 := by exact prefixLift 6170961
  have htrace : WordTrace (prefixWord ++ tailWord_6170961) baseStart_6170961 baseEnd_6170961 := by
    simpa [prefixWord, tailWord_6170961, baseEnd_6170961] using wordTrace_append hprefix tailTrace_6170961
  have hstable : (prefixWord ++ tailWord_6170961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170961).length < 2 ^ (prefixWord ++ tailWord_6170961).sum := by decide
  have hdescent : baseEnd_6170961 < baseStart_6170961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170964 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6170964 : Nat := 118140960795 + 6170964 * 2 ^ 59
def prefixEnd_6170964 : Nat := 4983230072969 + 3 ^ 40 * 6170964 * 2
def baseEnd_6170964 : Nat := 3168670633591899308670259

theorem tailTrace_6170964 : CollatzResearch.WordTrace tailWord_6170964 prefixEnd_6170964 3168670633591899308670259 := by
  unfold tailWord_6170964
  simp only [CollatzResearch.WordTrace]
  refine ⟨112536773807829409794855973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150049031743772546393141297 112536773807829409794855973)
  ·
    refine ⟨21100645088968014336535495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112536773807829409794855973 21100645088968014336535495)
    ·
      refine ⟨31650967633452021504803243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21100645088968014336535495 31650967633452021504803243)
      ·
        refine ⟨47476451450178032257204865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31650967633452021504803243 47476451450178032257204865)
        ·
          refine ⟨35607338587633524192903649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47476451450178032257204865 35607338587633524192903649)
          ·
            refine ⟨26705503940725143144677737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35607338587633524192903649 26705503940725143144677737)
            ·
              refine ⟨20029127955543857358508303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26705503940725143144677737 20029127955543857358508303)
              ·
                refine ⟨30043691933315786037762455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20029127955543857358508303 30043691933315786037762455)
                ·
                  refine ⟨45065537899973679056643683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30043691933315786037762455 45065537899973679056643683)
                  ·
                    refine ⟨67598306849960518584965525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45065537899973679056643683 67598306849960518584965525)
                    ·
                      refine ⟨3168670633591899308670259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67598306849960518584965525 3168670633591899308670259)
                      ·
                        rfl

theorem cell23_6170964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6170964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170964 prefixEnd_6170964 := by exact prefixLift 6170964
  have htrace : WordTrace (prefixWord ++ tailWord_6170964) baseStart_6170964 baseEnd_6170964 := by
    simpa [prefixWord, tailWord_6170964, baseEnd_6170964] using wordTrace_append hprefix tailTrace_6170964
  have hstable : (prefixWord ++ tailWord_6170964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170964).length < 2 ^ (prefixWord ++ tailWord_6170964).sum := by decide
  have hdescent : baseEnd_6170964 < baseStart_6170964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170988 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 1, 1, 5]
def baseStart_6170988 : Nat := 118140960795 + 6170988 * 2 ^ 59
def prefixEnd_6170988 : Nat := 4983230072969 + 3 ^ 40 * 6170988 * 2
def baseEnd_6170988 : Nat := 3168682957127607214770149

theorem tailTrace_6170988 : CollatzResearch.WordTrace tailWord_6170988 prefixEnd_6170988 3168682957127607214770149 := by
  unfold tailWord_6170988
  simp only [CollatzResearch.WordTrace]
  refine ⟨112537211483785935844292809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150049615311714581125723745 112537211483785935844292809)
  ·
    refine ⟨84402908612839451883219607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112537211483785935844292809 84402908612839451883219607)
    ·
      refine ⟨126604362919259177824829411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84402908612839451883219607 126604362919259177824829411)
      ·
        refine ⟨189906544378888766737244117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126604362919259177824829411 189906544378888766737244117)
        ·
          refine ⟨4450934633880205470404159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189906544378888766737244117 4450934633880205470404159)
          ·
            refine ⟨6676401950820308205606239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450934633880205470404159 6676401950820308205606239)
            ·
              refine ⟨10014602926230462308409359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676401950820308205606239 10014602926230462308409359)
              ·
                refine ⟨15021904389345693462614039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10014602926230462308409359 15021904389345693462614039)
                ·
                  refine ⟨22532856584018540193921059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15021904389345693462614039 22532856584018540193921059)
                  ·
                    refine ⟨33799284876027810290881589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22532856584018540193921059 33799284876027810290881589)
                    ·
                      refine ⟨3168682957127607214770149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33799284876027810290881589 3168682957127607214770149)
                      ·
                        rfl

theorem cell23_6170988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_6170988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6170988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6170988 prefixEnd_6170988 := by exact prefixLift 6170988
  have htrace : WordTrace (prefixWord ++ tailWord_6170988) baseStart_6170988 baseEnd_6170988 := by
    simpa [prefixWord, tailWord_6170988, baseEnd_6170988] using wordTrace_append hprefix tailTrace_6170988
  have hstable : (prefixWord ++ tailWord_6170988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170988).length < 2 ^ (prefixWord ++ tailWord_6170988).sum := by decide
  have hdescent : baseEnd_6170988 < baseStart_6170988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171044 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_6171044 : Nat := 118140960795 + 6171044 * 2 ^ 59
def prefixEnd_6171044 : Nat := 4983230072969 + 3 ^ 40 * 6171044 * 2
def baseEnd_6171044 : Nat := 3168711712044258995669891

theorem tailTrace_6171044 : CollatzResearch.WordTrace tailWord_6171044 prefixEnd_6171044 3168711712044258995669891 := by
  unfold tailWord_6171044
  simp only [CollatzResearch.WordTrace]
  refine ⟨112538232727684496626312093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150050976970245995501749457 112538232727684496626312093)
  ·
    refine ⟨42201837272881686234867035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112538232727684496626312093 42201837272881686234867035)
    ·
      refine ⟨63302755909322529352300553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42201837272881686234867035 63302755909322529352300553)
      ·
        refine ⟨47477066931991897014225415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63302755909322529352300553 47477066931991897014225415)
        ·
          refine ⟨71215600397987845521338123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47477066931991897014225415 71215600397987845521338123)
          ·
            refine ⟨106823400596981768282007185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71215600397987845521338123 106823400596981768282007185)
            ·
              refine ⟨80117550447736326211505389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106823400596981768282007185 80117550447736326211505389)
              ·
                refine ⟨30044081417901122329314521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80117550447736326211505389 30044081417901122329314521)
                ·
                  refine ⟨22533061063425841746985891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30044081417901122329314521 22533061063425841746985891)
                  ·
                    refine ⟨33799591595138762620478837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22533061063425841746985891 33799591595138762620478837)
                    ·
                      refine ⟨3168711712044258995669891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33799591595138762620478837 3168711712044258995669891)
                      ·
                        rfl

theorem cell23_6171044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_6171044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171044 prefixEnd_6171044 := by exact prefixLift 6171044
  have htrace : WordTrace (prefixWord ++ tailWord_6171044) baseStart_6171044 baseEnd_6171044 := by
    simpa [prefixWord, tailWord_6171044, baseEnd_6171044] using wordTrace_append hprefix tailTrace_6171044
  have hstable : (prefixWord ++ tailWord_6171044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171044).length < 2 ^ (prefixWord ++ tailWord_6171044).sum := by decide
  have hdescent : baseEnd_6171044 < baseStart_6171044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171058 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_6171058 : Nat := 118140960795 + 6171058 * 2 ^ 59
def prefixEnd_6171058 : Nat := 4983230072969 + 3 ^ 40 * 6171058 * 2
def baseEnd_6171058 : Nat := 3168718900773421940894827

theorem tailTrace_6171058 : CollatzResearch.WordTrace tailWord_6171058 prefixEnd_6171058 3168718900773421940894827 := by
  unfold tailWord_6171058
  simp only [CollatzResearch.WordTrace]
  refine ⟨56269244019329568410908457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150051317384878849095755885 56269244019329568410908457)
  ·
    refine ⟨42201933014497176308181343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56269244019329568410908457 42201933014497176308181343)
    ·
      refine ⟨63302899521745764462272015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42201933014497176308181343 63302899521745764462272015)
      ·
        refine ⟨94954349282618646693408023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63302899521745764462272015 94954349282618646693408023)
        ·
          refine ⟨142431523923927970040112035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94954349282618646693408023 142431523923927970040112035)
          ·
            refine ⟨213647285885891955060168053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142431523923927970040112035 213647285885891955060168053)
            ·
              refine ⟨20029433051802370786890755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213647285885891955060168053 20029433051802370786890755)
              ·
                refine ⟨30044149577703556180336133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20029433051802370786890755 30044149577703556180336133)
                ·
                  refine ⟨5633278045819416783813025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30044149577703556180336133 5633278045819416783813025)
                  ·
                    refine ⟨4224958534364562587859769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5633278045819416783813025 4224958534364562587859769)
                    ·
                      refine ⟨3168718900773421940894827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4224958534364562587859769 3168718900773421940894827)
                      ·
                        rfl

theorem cell23_6171058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_6171058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171058 prefixEnd_6171058 := by exact prefixLift 6171058
  have htrace : WordTrace (prefixWord ++ tailWord_6171058) baseStart_6171058 baseEnd_6171058 := by
    simpa [prefixWord, tailWord_6171058, baseEnd_6171058] using wordTrace_append hprefix tailTrace_6171058
  have hstable : (prefixWord ++ tailWord_6171058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171058).length < 2 ^ (prefixWord ++ tailWord_6171058).sum := by decide
  have hdescent : baseEnd_6171058 < baseStart_6171058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171104 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_6171104 : Nat := 118140960795 + 6171104 * 2 ^ 59
def prefixEnd_6171104 : Nat := 4983230072969 + 3 ^ 40 * 6171104 * 2
def baseEnd_6171104 : Nat := 3168742520883528760919615

theorem tailTrace_6171104 : CollatzResearch.WordTrace tailWord_6171104 prefixEnd_6171104 3168742520883528760919615 := by
  unfold tailWord_6171104
  simp only [CollatzResearch.WordTrace]
  refine ⟨112539326917575811749904183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150052435890101082333205577 112539326917575811749904183)
  ·
    refine ⟨168808990376363717624856275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112539326917575811749904183 168808990376363717624856275)
    ·
      refine ⟨253213485564545576437284413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168808990376363717624856275 253213485564545576437284413)
      ·
        refine ⟨94955057086704591163981655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253213485564545576437284413 94955057086704591163981655)
        ·
          refine ⟨142432585630056886745972483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94955057086704591163981655 142432585630056886745972483)
          ·
            refine ⟨213648878445085330118958725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142432585630056886745972483 213648878445085330118958725)
            ·
              refine ⟨40059164708453499397304761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213648878445085330118958725 40059164708453499397304761)
              ·
                refine ⟨30044373531340124547978571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40059164708453499397304761 30044373531340124547978571)
                ·
                  refine ⟨45066560297010186821967857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30044373531340124547978571 45066560297010186821967857)
                  ·
                    refine ⟨33799920222757640116475893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45066560297010186821967857 33799920222757640116475893)
                    ·
                      refine ⟨3168742520883528760919615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33799920222757640116475893 3168742520883528760919615)
                      ·
                        rfl

theorem cell23_6171104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_6171104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171104 prefixEnd_6171104 := by exact prefixLift 6171104
  have htrace : WordTrace (prefixWord ++ tailWord_6171104) baseStart_6171104 baseEnd_6171104 := by
    simpa [prefixWord, tailWord_6171104, baseEnd_6171104] using wordTrace_append hprefix tailTrace_6171104
  have hstable : (prefixWord ++ tailWord_6171104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171104).length < 2 ^ (prefixWord ++ tailWord_6171104).sum := by decide
  have hdescent : baseEnd_6171104 < baseStart_6171104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171111 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 2, 5]
def baseStart_6171111 : Nat := 118140960795 + 6171111 * 2 ^ 59
def prefixEnd_6171111 : Nat := 4983230072969 + 3 ^ 40 * 6171111 * 2
def baseEnd_6171111 : Nat := 1056248705082703411177361

theorem tailTrace_6171111 : CollatzResearch.WordTrace tailWord_6171111 prefixEnd_6171111 1056248705082703411177361 := by
  unfold tailWord_6171111
  simp only [CollatzResearch.WordTrace]
  refine ⟨225078909146126263695313187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150052606097417509130208791 225078909146126263695313187)
  ·
    refine ⟨337618363719189395542969781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225078909146126263695313187 337618363719189395542969781)
    ·
      refine ⟨31651721598674005832153417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 337618363719189395542969781 31651721598674005832153417)
      ·
        refine ⟨23738791199005504374115063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31651721598674005832153417 23738791199005504374115063)
        ·
          refine ⟨35608186798508256561172595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23738791199005504374115063 35608186798508256561172595)
          ·
            refine ⟨53412280197762384841758893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35608186798508256561172595 53412280197762384841758893)
            ·
              refine ⟨20029605074160894315659585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53412280197762384841758893 20029605074160894315659585)
              ·
                refine ⟨15022203805620670736744689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20029605074160894315659585 15022203805620670736744689)
                ·
                  refine ⟨11266652854215503052558517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15022203805620670736744689 11266652854215503052558517)
                  ·
                    refine ⟨1056248705082703411177361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11266652854215503052558517 1056248705082703411177361)
                    ·
                      rfl

theorem cell23_6171111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_6171111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171111 prefixEnd_6171111 := by exact prefixLift 6171111
  have htrace : WordTrace (prefixWord ++ tailWord_6171111) baseStart_6171111 baseEnd_6171111 := by
    simpa [prefixWord, tailWord_6171111, baseEnd_6171111] using wordTrace_append hprefix tailTrace_6171111
  have hstable : (prefixWord ++ tailWord_6171111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171111).length < 2 ^ (prefixWord ++ tailWord_6171111).sum := by decide
  have hdescent : baseEnd_6171111 < baseStart_6171111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171141 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_6171141 : Nat := 118140960795 + 6171141 * 2 ^ 59
def prefixEnd_6171141 : Nat := 4983230072969 + 3 ^ 40 * 6171141 * 2
def baseEnd_6171141 : Nat := 1056253839889248372052315

theorem tailTrace_6171141 : CollatzResearch.WordTrace tailWord_6171141 prefixEnd_6171141 1056253839889248372052315 := by
  unfold tailWord_6171141
  simp only [CollatzResearch.WordTrace]
  refine ⟨225080003336017578818905277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150053335557345052545936851 225080003336017578818905277)
  ·
    refine ⟨84405001251006592057089479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225080003336017578818905277 84405001251006592057089479)
    ·
      refine ⟨126607501876509888085634219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84405001251006592057089479 126607501876509888085634219)
      ·
        refine ⟨189911252814764832128451329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126607501876509888085634219 189911252814764832128451329)
        ·
          refine ⟨142433439611073624096338497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189911252814764832128451329 142433439611073624096338497)
          ·
            refine ⟨106825079708305218072253873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142433439611073624096338497 106825079708305218072253873)
            ·
              refine ⟨80118809781228913554190405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106825079708305218072253873 80118809781228913554190405)
              ·
                refine ⟨15022276833980421291410701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80118809781228913554190405 15022276833980421291410701)
                ·
                  refine ⟨5633353812742657984279013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15022276833980421291410701 5633353812742657984279013)
                  ·
                    refine ⟨1056253839889248372052315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5633353812742657984279013 1056253839889248372052315)
                    ·
                      rfl

theorem cell23_6171141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_6171141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171141 prefixEnd_6171141 := by exact prefixLift 6171141
  have htrace : WordTrace (prefixWord ++ tailWord_6171141) baseStart_6171141 baseEnd_6171141 := by
    simpa [prefixWord, tailWord_6171141, baseEnd_6171141] using wordTrace_append hprefix tailTrace_6171141
  have hstable : (prefixWord ++ tailWord_6171141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171141).length < 2 ^ (prefixWord ++ tailWord_6171141).sum := by decide
  have hdescent : baseEnd_6171141 < baseStart_6171141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171144 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_6171144 : Nat := 118140960795 + 6171144 * 2 ^ 59
def prefixEnd_6171144 : Nat := 4983230072969 + 3 ^ 40 * 6171144 * 2
def baseEnd_6171144 : Nat := 3168763060109708604419431

theorem tailTrace_6171144 : CollatzResearch.WordTrace tailWord_6171144 prefixEnd_6171144 3168763060109708604419431 := by
  unfold tailWord_6171144
  simp only [CollatzResearch.WordTrace]
  refine ⟨112540056377503355165632243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150053408503337806887509657 112540056377503355165632243)
  ·
    refine ⟨168810084566255032748448365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112540056377503355165632243 168810084566255032748448365)
    ·
      refine ⟨63303781712345637280668137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168810084566255032748448365 63303781712345637280668137)
      ·
        refine ⟨47477836284259227960501103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63303781712345637280668137 47477836284259227960501103)
        ·
          refine ⟨71216754426388841940751655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47477836284259227960501103 71216754426388841940751655)
          ·
            refine ⟨106825131639583262911127483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71216754426388841940751655 106825131639583262911127483)
            ·
              refine ⟨160237697459374894366691225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106825131639583262911127483 160237697459374894366691225)
              ·
                refine ⟨120178273094531170775018419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160237697459374894366691225 120178273094531170775018419)
                ·
                  refine ⟨180267409641796756162527629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120178273094531170775018419 180267409641796756162527629)
                  ·
                    refine ⟨67600278615673783560947861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 180267409641796756162527629 67600278615673783560947861)
                    ·
                      refine ⟨3168763060109708604419431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67600278615673783560947861 3168763060109708604419431)
                      ·
                        rfl

theorem cell23_6171144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_6171144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171144 prefixEnd_6171144 := by exact prefixLift 6171144
  have htrace : WordTrace (prefixWord ++ tailWord_6171144) baseStart_6171144 baseEnd_6171144 := by
    simpa [prefixWord, tailWord_6171144, baseEnd_6171144] using wordTrace_append hprefix tailTrace_6171144
  have hstable : (prefixWord ++ tailWord_6171144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171144).length < 2 ^ (prefixWord ++ tailWord_6171144).sum := by decide
  have hdescent : baseEnd_6171144 < baseStart_6171144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171148 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_6171148 : Nat := 118140960795 + 6171148 * 2 ^ 59
def prefixEnd_6171148 : Nat := 4983230072969 + 3 ^ 40 * 6171148 * 2
def baseEnd_6171148 : Nat := 3168765114032326588769413

theorem tailTrace_6171148 : CollatzResearch.WordTrace tailWord_6171148 prefixEnd_6171148 3168765114032326588769413 := by
  unfold tailWord_6171148
  simp only [CollatzResearch.WordTrace]
  refine ⟨112540129323496109507205049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150053505764661479342940065 112540129323496109507205049)
  ·
    refine ⟨84405096992622082130403787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112540129323496109507205049 84405096992622082130403787)
    ·
      refine ⟨126607645488933123195605681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84405096992622082130403787 126607645488933123195605681)
      ·
        refine ⟨94955734116699842396704261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126607645488933123195605681 94955734116699842396704261)
        ·
          refine ⟨17804200146881220449382049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94955734116699842396704261 17804200146881220449382049)
          ·
            refine ⟨13353150110160915337036537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17804200146881220449382049 13353150110160915337036537)
            ·
              refine ⟨10014862582620686502777403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13353150110160915337036537 10014862582620686502777403)
              ·
                refine ⟨15022293873931029754166105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10014862582620686502777403 15022293873931029754166105)
                ·
                  refine ⟨11266720405448272315624579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15022293873931029754166105 11266720405448272315624579)
                  ·
                    refine ⟨16900080608172408473436869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11266720405448272315624579 16900080608172408473436869)
                    ·
                      refine ⟨3168765114032326588769413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16900080608172408473436869 3168765114032326588769413)
                      ·
                        rfl

theorem cell23_6171148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_6171148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171148 prefixEnd_6171148 := by exact prefixLift 6171148
  have htrace : WordTrace (prefixWord ++ tailWord_6171148) baseStart_6171148 baseEnd_6171148 := by
    simpa [prefixWord, tailWord_6171148, baseEnd_6171148] using wordTrace_append hprefix tailTrace_6171148
  have hstable : (prefixWord ++ tailWord_6171148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171148).length < 2 ^ (prefixWord ++ tailWord_6171148).sum := by decide
  have hdescent : baseEnd_6171148 < baseStart_6171148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171151 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 3]
def baseStart_6171151 : Nat := 118140960795 + 6171151 * 2 ^ 59
def prefixEnd_6171151 : Nat := 4983230072969 + 3 ^ 40 * 6171151 * 2
def baseEnd_6171151 : Nat := 3168766654474290077031899

theorem tailTrace_6171151 : CollatzResearch.WordTrace tailWord_6171151 prefixEnd_6171151 3168766654474290077031899 := by
  unfold tailWord_6171151
  simp only [CollatzResearch.WordTrace]
  refine ⟨225080368065981350526769307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150053578710654233684512871 225080368065981350526769307)
  ·
    refine ⟨337620552098972025790153961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225080368065981350526769307 337620552098972025790153961)
    ·
      refine ⟨253215414074229019342615471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337620552098972025790153961 253215414074229019342615471)
      ·
        refine ⟨379823121111343529013923207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253215414074229019342615471 379823121111343529013923207)
        ·
          refine ⟨569734681667015293520884811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379823121111343529013923207 569734681667015293520884811)
          ·
            refine ⟨854602022500522940281327217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569734681667015293520884811 854602022500522940281327217)
            ·
              refine ⟨640951516875392205210995413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854602022500522940281327217 640951516875392205210995413)
              ·
                refine ⟨15022301176767004809632705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 640951516875392205210995413 15022301176767004809632705)
                ·
                  refine ⟨11266725882575253607224529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15022301176767004809632705 11266725882575253607224529)
                  ·
                    refine ⟨8450044411931440205418397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11266725882575253607224529 8450044411931440205418397)
                    ·
                      refine ⟨3168766654474290077031899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8450044411931440205418397 3168766654474290077031899)
                      ·
                        rfl

theorem cell23_6171151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_6171151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171151 prefixEnd_6171151 := by exact prefixLift 6171151
  have htrace : WordTrace (prefixWord ++ tailWord_6171151) baseStart_6171151 baseEnd_6171151 := by
    simpa [prefixWord, tailWord_6171151, baseEnd_6171151] using wordTrace_append hprefix tailTrace_6171151
  have hstable : (prefixWord ++ tailWord_6171151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171151).length < 2 ^ (prefixWord ++ tailWord_6171151).sum := by decide
  have hdescent : baseEnd_6171151 < baseStart_6171151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171171 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 6]
def baseStart_6171171 : Nat := 118140960795 + 6171171 * 2 ^ 59
def prefixEnd_6171171 : Nat := 4983230072969 + 3 ^ 40 * 6171171 * 2
def baseEnd_6171171 : Nat := 352086324898597777642423

theorem tailTrace_6171171 : CollatzResearch.WordTrace tailWord_6171171 prefixEnd_6171171 352086324898597777642423 := by
  unfold tailWord_6171171
  simp only [CollatzResearch.WordTrace]
  refine ⟨225081097525908893942497367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150054065017272595961664911 225081097525908893942497367)
  ·
    refine ⟨337621646288863340913746051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225081097525908893942497367 337621646288863340913746051)
    ·
      refine ⟨506432469433295011370619077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337621646288863340913746051 506432469433295011370619077)
      ·
        refine ⟨94956088018742814631991077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506432469433295011370619077 94956088018742814631991077)
        ·
          refine ⟨17804266503514277743498327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94956088018742814631991077 17804266503514277743498327)
          ·
            refine ⟨26706399755271416615247491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17804266503514277743498327 26706399755271416615247491)
            ·
              refine ⟨40059599632907124922871237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26706399755271416615247491 40059599632907124922871237)
              ·
                refine ⟨7511174931170085923038357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40059599632907124922871237 7511174931170085923038357)
                ·
                  refine ⟨352086324898597777642423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7511174931170085923038357 352086324898597777642423)
                  ·
                    rfl

theorem cell23_6171171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 6].length) (baseStart_6171171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171171 prefixEnd_6171171 := by exact prefixLift 6171171
  have htrace : WordTrace (prefixWord ++ tailWord_6171171) baseStart_6171171 baseEnd_6171171 := by
    simpa [prefixWord, tailWord_6171171, baseEnd_6171171] using wordTrace_append hprefix tailTrace_6171171
  have hstable : (prefixWord ++ tailWord_6171171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171171).length < 2 ^ (prefixWord ++ tailWord_6171171).sum := by decide
  have hdescent : baseEnd_6171171 < baseStart_6171171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171215 : List Nat := [1, 1, 2, 1, 1, 2, 5, 5, 1, 1, 3]
def baseStart_6171215 : Nat := 118140960795 + 6171215 * 2 ^ 59
def prefixEnd_6171215 : Nat := 4983230072969 + 3 ^ 40 * 6171215 * 2
def baseEnd_6171215 : Nat := 3168799517236177826631605

theorem tailTrace_6171215 : CollatzResearch.WordTrace tailWord_6171215 prefixEnd_6171215 3168799517236177826631605 := by
  unfold tailWord_6171215
  simp only [CollatzResearch.WordTrace]
  refine ⟨225082702337749489457099099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150055134891832992971399399 225082702337749489457099099)
  ·
    refine ⟨337624053506624234185648649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225082702337749489457099099 337624053506624234185648649)
    ·
      refine ⟨253218040129968175639236487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337624053506624234185648649 253218040129968175639236487)
      ·
        refine ⟨379827060194952263458854731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253218040129968175639236487 379827060194952263458854731)
        ·
          refine ⟨569740590292428395188282097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379827060194952263458854731 569740590292428395188282097)
          ·
            refine ⟨427305442719321296391211573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569740590292428395188282097 427305442719321296391211573)
            ·
              refine ⟨40059885254936371536676085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 427305442719321296391211573 40059885254936371536676085)
              ·
                refine ⟨3755614242650284831563383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40059885254936371536676085 3755614242650284831563383)
                ·
                  refine ⟨5633421363975427247345075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755614242650284831563383 5633421363975427247345075)
                  ·
                    refine ⟨8450132045963140871017613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5633421363975427247345075 8450132045963140871017613)
                    ·
                      refine ⟨3168799517236177826631605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8450132045963140871017613 3168799517236177826631605)
                      ·
                        rfl

theorem cell23_6171215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5, 1, 1, 3].length) (baseStart_6171215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171215 prefixEnd_6171215 := by exact prefixLift 6171215
  have htrace : WordTrace (prefixWord ++ tailWord_6171215) baseStart_6171215 baseEnd_6171215 := by
    simpa [prefixWord, tailWord_6171215, baseEnd_6171215] using wordTrace_append hprefix tailTrace_6171215
  have hstable : (prefixWord ++ tailWord_6171215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171215).length < 2 ^ (prefixWord ++ tailWord_6171215).sum := by decide
  have hdescent : baseEnd_6171215 < baseStart_6171215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171218 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_6171218 : Nat := 118140960795 + 6171218 * 2 ^ 59
def prefixEnd_6171218 : Nat := 4983230072969 + 3 ^ 40 * 6171218 * 2
def baseEnd_6171218 : Nat := 1056267019226047104964697

theorem tailTrace_6171218 : CollatzResearch.WordTrace tailWord_6171218 prefixEnd_6171218 1056267019226047104964697 := by
  unfold tailWord_6171218
  simp only [CollatzResearch.WordTrace]
  refine ⟨56270702939184655242364577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150055207837825747312972205 56270702939184655242364577)
  ·
    refine ⟨42203027204388491431773433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56270702939184655242364577 42203027204388491431773433)
    ·
      refine ⟨31652270403291368573830075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42203027204388491431773433 31652270403291368573830075)
      ·
        refine ⟨47478405604937052860745113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31652270403291368573830075 47478405604937052860745113)
        ·
          refine ⟨35608804203702789645558835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47478405604937052860745113 35608804203702789645558835)
          ·
            refine ⟨53413206305554184468338253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35608804203702789645558835 53413206305554184468338253)
            ·
              refine ⟨20029952364582819175626845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53413206305554184468338253 20029952364582819175626845)
              ·
                refine ⟨7511232136718557190860067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20029952364582819175626845 7511232136718557190860067)
                ·
                  refine ⟨11266848205077835786290101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511232136718557190860067 11266848205077835786290101)
                  ·
                    refine ⟨1056267019226047104964697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11266848205077835786290101 1056267019226047104964697)
                    ·
                      rfl

theorem cell23_6171218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_6171218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171218 prefixEnd_6171218 := by exact prefixLift 6171218
  have htrace : WordTrace (prefixWord ++ tailWord_6171218) baseStart_6171218 baseEnd_6171218 := by
    simpa [prefixWord, tailWord_6171218, baseEnd_6171218] using wordTrace_append hprefix tailTrace_6171218
  have hstable : (prefixWord ++ tailWord_6171218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171218).length < 2 ^ (prefixWord ++ tailWord_6171218).sum := by decide
  have hdescent : baseEnd_6171218 < baseStart_6171218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171251 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4]
def baseStart_6171251 : Nat := 118140960795 + 6171251 * 2 ^ 59
def prefixEnd_6171251 : Nat := 4983230072969 + 3 ^ 40 * 6171251 * 2
def baseEnd_6171251 : Nat := 3168818002539739685781439

theorem tailTrace_6171251 : CollatzResearch.WordTrace tailWord_6171251 prefixEnd_6171251 3168818002539739685781439 := by
  unfold tailWord_6171251
  simp only [CollatzResearch.WordTrace]
  refine ⟨225084015365619067605409607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150056010243746045070273071 225084015365619067605409607)
  ·
    refine ⟨337626023048428601408114411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225084015365619067605409607 337626023048428601408114411)
    ·
      refine ⟨506439034572642902112171617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337626023048428601408114411 506439034572642902112171617)
      ·
        refine ⟨379829275929482176584128713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506439034572642902112171617 379829275929482176584128713)
        ·
          refine ⟨284871956947111632438096535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379829275929482176584128713 284871956947111632438096535)
          ·
            refine ⟨427307935420667448657144803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284871956947111632438096535 427307935420667448657144803)
            ·
              refine ⟨640961903131001172985717205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427307935420667448657144803 640961903131001172985717205)
              ·
                refine ⟨15022544604632839991852747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 640961903131001172985717205 15022544604632839991852747)
                ·
                  refine ⟨22533816906949259987779121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15022544604632839991852747 22533816906949259987779121)
                  ·
                    refine ⟨16900362680211944990834341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22533816906949259987779121 16900362680211944990834341)
                    ·
                      refine ⟨3168818002539739685781439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16900362680211944990834341 3168818002539739685781439)
                      ·
                        rfl

theorem cell23_6171251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_6171251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171251 prefixEnd_6171251 := by exact prefixLift 6171251
  have htrace : WordTrace (prefixWord ++ tailWord_6171251) baseStart_6171251 baseEnd_6171251 := by
    simpa [prefixWord, tailWord_6171251, baseEnd_6171251] using wordTrace_append hprefix tailTrace_6171251
  have hstable : (prefixWord ++ tailWord_6171251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171251).length < 2 ^ (prefixWord ++ tailWord_6171251).sum := by decide
  have hdescent : baseEnd_6171251 < baseStart_6171251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171255 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 3, 2, 2]
def baseStart_6171255 : Nat := 118140960795 + 6171255 * 2 ^ 59
def prefixEnd_6171255 : Nat := 4983230072969 + 3 ^ 40 * 6171255 * 2
def baseEnd_6171255 : Nat := 3168820056462357670131421

theorem tailTrace_6171255 : CollatzResearch.WordTrace tailWord_6171255 prefixEnd_6171255 3168820056462357670131421 := by
  unfold tailWord_6171255
  simp only [CollatzResearch.WordTrace]
  refine ⟨225084161257604576288555219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150056107505069717525703479 225084161257604576288555219)
  ·
    refine ⟨337626241886406864432832829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225084161257604576288555219 337626241886406864432832829)
    ·
      refine ⟨126609840707402574162312311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337626241886406864432832829 126609840707402574162312311)
      ·
        refine ⟨189914761061103861243468467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126609840707402574162312311 189914761061103861243468467)
        ·
          refine ⟨284872141591655791865202701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189914761061103861243468467 284872141591655791865202701)
          ·
            refine ⟨106827053096870921949451013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284872141591655791865202701 106827053096870921949451013)
            ·
              refine ⟨20030072455663297865522065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106827053096870921949451013 20030072455663297865522065)
              ·
                refine ⟨15022554341747473399141549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20030072455663297865522065 15022554341747473399141549)
                ·
                  refine ⟨5633457878155302524678081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15022554341747473399141549 5633457878155302524678081)
                  ·
                    refine ⟨4225093408616476893508561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5633457878155302524678081 4225093408616476893508561)
                    ·
                      refine ⟨3168820056462357670131421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225093408616476893508561 3168820056462357670131421)
                      ·
                        rfl

theorem cell23_6171255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_6171255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171255 prefixEnd_6171255 := by exact prefixLift 6171255
  have htrace : WordTrace (prefixWord ++ tailWord_6171255) baseStart_6171255 baseEnd_6171255 := by
    simpa [prefixWord, tailWord_6171255, baseEnd_6171255] using wordTrace_append hprefix tailTrace_6171255
  have hstable : (prefixWord ++ tailWord_6171255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171255).length < 2 ^ (prefixWord ++ tailWord_6171255).sum := by decide
  have hdescent : baseEnd_6171255 < baseStart_6171255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171289 : List Nat := [1, 2, 1, 2, 1, 2, 7, 2, 1, 2, 2]
def baseStart_6171289 : Nat := 118140960795 + 6171289 * 2 ^ 59
def prefixEnd_6171289 : Nat := 4983230072969 + 3 ^ 40 * 6171289 * 2
def baseEnd_6171289 : Nat := 3168837514804610537106265

theorem tailTrace_6171289 : CollatzResearch.WordTrace tailWord_6171289 prefixEnd_6171289 3168837514804610537106265 := by
  unfold tailWord_6171289
  simp only [CollatzResearch.WordTrace]
  refine ⟨225085401339481400095292921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150056934226320933396861947 225085401339481400095292921)
  ·
    refine ⟨168814051004611050071469691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225085401339481400095292921 168814051004611050071469691)
    ·
      refine ⟨253221076506916575107204537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168814051004611050071469691 253221076506916575107204537)
      ·
        refine ⟨189915807380187431330403403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253221076506916575107204537 189915807380187431330403403)
        ·
          refine ⟨284873711070281146995605105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189915807380187431330403403 284873711070281146995605105)
          ·
            refine ⟨213655283302710860246703829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284873711070281146995605105 213655283302710860246703829)
            ·
              refine ⟨5007545702407285787032121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 213655283302710860246703829 5007545702407285787032121)
              ·
                refine ⟨3755659276805464340274091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5007545702407285787032121 3755659276805464340274091)
                ·
                  refine ⟨5633488915208196510411137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755659276805464340274091 5633488915208196510411137)
                  ·
                    refine ⟨4225116686406147382808353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5633488915208196510411137 4225116686406147382808353)
                    ·
                      refine ⟨3168837514804610537106265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225116686406147382808353 3168837514804610537106265)
                      ·
                        rfl

theorem cell23_6171289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_6171289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171289 prefixEnd_6171289 := by exact prefixLift 6171289
  have htrace : WordTrace (prefixWord ++ tailWord_6171289) baseStart_6171289 baseEnd_6171289 := by
    simpa [prefixWord, tailWord_6171289, baseEnd_6171289] using wordTrace_append hprefix tailTrace_6171289
  have hstable : (prefixWord ++ tailWord_6171289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171289).length < 2 ^ (prefixWord ++ tailWord_6171289).sum := by decide
  have hdescent : baseEnd_6171289 < baseStart_6171289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171306 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6171306 : Nat := 118140960795 + 6171306 * 2 ^ 59
def prefixEnd_6171306 : Nat := 4983230072969 + 3 ^ 40 * 6171306 * 2
def baseEnd_6171306 : Nat := 3168846243975736970593687

theorem tailTrace_6171306 : CollatzResearch.WordTrace tailWord_6171306 prefixEnd_6171306 3168846243975736970593687 := by
  unfold tailWord_6171306
  simp only [CollatzResearch.WordTrace]
  refine ⟨56271505345104952999665443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150057347586946541332441181 56271505345104952999665443)
  ·
    refine ⟨84407258017657429499498165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56271505345104952999665443 84407258017657429499498165)
    ·
      refine ⟨7913180439155384015577953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84407258017657429499498165 7913180439155384015577953)
      ·
        refine ⟨5934885329366538011683465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7913180439155384015577953 5934885329366538011683465)
        ·
          refine ⟨4451163997024903508762599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5934885329366538011683465 4451163997024903508762599)
          ·
            refine ⟨6676745995537355263143899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451163997024903508762599 6676745995537355263143899)
            ·
              refine ⟨10015118993306032894715849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6676745995537355263143899 10015118993306032894715849)
              ·
                refine ⟨7511339244979524671036887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10015118993306032894715849 7511339244979524671036887)
                ·
                  refine ⟨11267008867469287006555331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511339244979524671036887 11267008867469287006555331)
                  ·
                    refine ⟨16900513301203930509832997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11267008867469287006555331 16900513301203930509832997)
                    ·
                      refine ⟨3168846243975736970593687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16900513301203930509832997 3168846243975736970593687)
                      ·
                        rfl

theorem cell23_6171306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6171306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171306 prefixEnd_6171306 := by exact prefixLift 6171306
  have htrace : WordTrace (prefixWord ++ tailWord_6171306) baseStart_6171306 baseEnd_6171306 := by
    simpa [prefixWord, tailWord_6171306, baseEnd_6171306] using wordTrace_append hprefix tailTrace_6171306
  have hstable : (prefixWord ++ tailWord_6171306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171306).length < 2 ^ (prefixWord ++ tailWord_6171306).sum := by decide
  have hdescent : baseEnd_6171306 < baseStart_6171306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171315 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 3, 3, 2]
def baseStart_6171315 : Nat := 118140960795 + 6171315 * 2 ^ 59
def prefixEnd_6171315 : Nat := 4983230072969 + 3 ^ 40 * 6171315 * 2
def baseEnd_6171315 : Nat := 3168850865301627435381145

theorem tailTrace_6171315 : CollatzResearch.WordTrace tailWord_6171315 prefixEnd_6171315 3168850865301627435381145 := by
  unfold tailWord_6171315
  simp only [CollatzResearch.WordTrace]
  refine ⟨225086349637387206535739399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150057566424924804357159599 225086349637387206535739399)
  ·
    refine ⟨337629524456080809803609099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225086349637387206535739399 337629524456080809803609099)
    ·
      refine ⟨506444286684121214705413649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337629524456080809803609099 506444286684121214705413649)
      ·
        refine ⟨379833215013090911029060237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506444286684121214705413649 379833215013090911029060237)
        ·
          refine ⟨142437455629909091635897589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 379833215013090911029060237 142437455629909091635897589)
          ·
            refine ⟨13353511465303977340865399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142437455629909091635897589 13353511465303977340865399)
            ·
              refine ⟨20030267197955966011298099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13353511465303977340865399 20030267197955966011298099)
              ·
                refine ⟨30045400796933949016947149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20030267197955966011298099 30045400796933949016947149)
                ·
                  refine ⟨11267025298850230881355181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30045400796933949016947149 11267025298850230881355181)
                  ·
                    refine ⟨4225134487068836580508193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11267025298850230881355181 4225134487068836580508193)
                    ·
                      refine ⟨3168850865301627435381145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225134487068836580508193 3168850865301627435381145)
                      ·
                        rfl

theorem cell23_6171315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3, 2].length) (baseStart_6171315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171315 prefixEnd_6171315 := by exact prefixLift 6171315
  have htrace : WordTrace (prefixWord ++ tailWord_6171315) baseStart_6171315 baseEnd_6171315 := by
    simpa [prefixWord, tailWord_6171315, baseEnd_6171315] using wordTrace_append hprefix tailTrace_6171315
  have hstable : (prefixWord ++ tailWord_6171315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171315).length < 2 ^ (prefixWord ++ tailWord_6171315).sum := by decide
  have hdescent : baseEnd_6171315 < baseStart_6171315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171321 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 4, 6]
def baseStart_6171321 : Nat := 118140960795 + 6171321 * 2 ^ 59
def prefixEnd_6171321 : Nat := 4983230072969 + 3 ^ 40 * 6171321 * 2
def baseEnd_6171321 : Nat := 1056284648728518137302039

theorem tailTrace_6171321 : CollatzResearch.WordTrace tailWord_6171321 prefixEnd_6171321 1056284648728518137302039 := by
  unfold tailWord_6171321
  simp only [CollatzResearch.WordTrace]
  refine ⟨225086568475365469560457817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150057712316910313040305211 225086568475365469560457817)
  ·
    refine ⟨168814926356524102170343363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225086568475365469560457817 168814926356524102170343363)
    ·
      refine ⟨253222389534786153255515045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168814926356524102170343363 253222389534786153255515045)
      ·
        refine ⟨47479198037772403735409071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253222389534786153255515045 47479198037772403735409071)
        ·
          refine ⟨71218797056658605603113607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47479198037772403735409071 71218797056658605603113607)
          ·
            refine ⟨106828195584987908404670411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71218797056658605603113607 106828195584987908404670411)
            ·
              refine ⟨160242293377481862607005617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106828195584987908404670411 160242293377481862607005617)
              ·
                refine ⟨120181720033111396955254213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160242293377481862607005617 120181720033111396955254213)
                ·
                  refine ⟨22534072506208386929110165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120181720033111396955254213 22534072506208386929110165)
                  ·
                    refine ⟨1056284648728518137302039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22534072506208386929110165 1056284648728518137302039)
                    ·
                      rfl

theorem cell23_6171321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_6171321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171321 prefixEnd_6171321 := by exact prefixLift 6171321
  have htrace : WordTrace (prefixWord ++ tailWord_6171321) baseStart_6171321 baseEnd_6171321 := by
    simpa [prefixWord, tailWord_6171321, baseEnd_6171321] using wordTrace_append hprefix tailTrace_6171321
  have hstable : (prefixWord ++ tailWord_6171321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171321).length < 2 ^ (prefixWord ++ tailWord_6171321).sum := by decide
  have hdescent : baseEnd_6171321 < baseStart_6171321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171418 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_6171418 : Nat := 118140960795 + 6171418 * 2 ^ 59
def prefixEnd_6171418 : Nat := 4983230072969 + 3 ^ 40 * 6171418 * 2
def baseEnd_6171418 : Nat := 3168903753809040532393171

theorem tailTrace_6171418 : CollatzResearch.WordTrace tailWord_6171418 prefixEnd_6171418 3168903753809040532393171 := by
  unfold tailWord_6171418
  simp only [CollatzResearch.WordTrace]
  refine ⟨56272526589003513781684727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150060070904009370084492605 56272526589003513781684727)
  ·
    refine ⟨84408789883505270672527091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56272526589003513781684727 84408789883505270672527091)
    ·
      refine ⟨126613184825257906008790637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84408789883505270672527091 126613184825257906008790637)
      ·
        refine ⟨47479944309471714753296489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126613184825257906008790637 47479944309471714753296489)
        ·
          refine ⟨35609958232103786064972367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47479944309471714753296489 35609958232103786064972367)
          ·
            refine ⟨53414937348155679097458551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35609958232103786064972367 53414937348155679097458551)
            ·
              refine ⟨80122406022233518646187827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53414937348155679097458551 80122406022233518646187827)
              ·
                refine ⟨120183609033350277969281741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80122406022233518646187827 120183609033350277969281741)
                ·
                  refine ⟨45068853387506354238480653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120183609033350277969281741 45068853387506354238480653)
                  ·
                    refine ⟨16900820020314882839430245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45068853387506354238480653 16900820020314882839430245)
                    ·
                      refine ⟨3168903753809040532393171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16900820020314882839430245 3168903753809040532393171)
                      ·
                        rfl

theorem cell23_6171418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_6171418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171418 prefixEnd_6171418 := by exact prefixLift 6171418
  have htrace : WordTrace (prefixWord ++ tailWord_6171418) baseStart_6171418 baseEnd_6171418 := by
    simpa [prefixWord, tailWord_6171418, baseEnd_6171418] using wordTrace_append hprefix tailTrace_6171418
  have hstable : (prefixWord ++ tailWord_6171418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171418).length < 2 ^ (prefixWord ++ tailWord_6171418).sum := by decide
  have hdescent : baseEnd_6171418 < baseStart_6171418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171455 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 3]
def baseStart_6171455 : Nat := 118140960795 + 6171455 * 2 ^ 59
def prefixEnd_6171455 : Nat := 4983230072969 + 3 ^ 40 * 6171455 * 2
def baseEnd_6171455 : Nat := 3168922752593256887630501

theorem tailTrace_6171455 : CollatzResearch.WordTrace tailWord_6171455 prefixEnd_6171455 3168922752593256887630501 := by
  unfold tailWord_6171455
  simp only [CollatzResearch.WordTrace]
  refine ⟨225091455856880010445835819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150060970571253340297223879 225091455856880010445835819)
  ·
    refine ⟨337637183785320015668753729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225091455856880010445835819 337637183785320015668753729)
    ·
      refine ⟨253227887838990011751565297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337637183785320015668753729 253227887838990011751565297)
      ·
        refine ⟨189920915879242508813673973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253227887838990011751565297 189920915879242508813673973)
        ·
          refine ⟨17805085863678985201281935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189920915879242508813673973 17805085863678985201281935)
          ·
            refine ⟨26707628795518477801922903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17805085863678985201281935 26707628795518477801922903)
            ·
              refine ⟨40061443193277716702884355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26707628795518477801922903 40061443193277716702884355)
              ·
                refine ⟨60092164789916575054326533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40061443193277716702884355 60092164789916575054326533)
                ·
                  refine ⟨11267280898109357822686225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60092164789916575054326533 11267280898109357822686225)
                  ·
                    refine ⟨8450460673582018367014669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11267280898109357822686225 8450460673582018367014669)
                    ·
                      refine ⟨3168922752593256887630501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8450460673582018367014669 3168922752593256887630501)
                      ·
                        rfl

theorem cell23_6171455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_6171455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171455 prefixEnd_6171455 := by exact prefixLift 6171455
  have htrace : WordTrace (prefixWord ++ tailWord_6171455) baseStart_6171455 baseEnd_6171455 := by
    simpa [prefixWord, tailWord_6171455, baseEnd_6171455] using wordTrace_append hprefix tailTrace_6171455
  have hstable : (prefixWord ++ tailWord_6171455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171455).length < 2 ^ (prefixWord ++ tailWord_6171455).sum := by decide
  have hdescent : baseEnd_6171455 < baseStart_6171455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171525 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_6171525 : Nat := 118140960795 + 6171525 * 2 ^ 59
def prefixEnd_6171525 : Nat := 4983230072969 + 3 ^ 40 * 6171525 * 2
def baseEnd_6171525 : Nat := 3168958696239071613755179

theorem tailTrace_6171525 : CollatzResearch.WordTrace tailWord_6171525 prefixEnd_6171525 3168958696239071613755179 := by
  unfold tailWord_6171525
  simp only [CollatzResearch.WordTrace]
  refine ⟨225094008966626412400884029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150062672644417608267256019 225094008966626412400884029)
  ·
    refine ⟨84410253362484904650331511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225094008966626412400884029 84410253362484904650331511)
    ·
      refine ⟨126615380043727356975497267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84410253362484904650331511 126615380043727356975497267)
      ·
        refine ⟨189923070065591035463245901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126615380043727356975497267 189923070065591035463245901)
        ·
          refine ⟨71221151274596638298717213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189923070065591035463245901 71221151274596638298717213)
          ·
            refine ⟨26707931727973739362018955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71221151274596638298717213 26707931727973739362018955)
            ·
              refine ⟨40061897591960609043028433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26707931727973739362018955 40061897591960609043028433)
              ·
                refine ⟨30046423193970456782271325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40061897591960609043028433 30046423193970456782271325)
                ·
                  refine ⟨11267408697738921293351747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30046423193970456782271325 11267408697738921293351747)
                  ·
                    refine ⟨16901113046608381940027621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11267408697738921293351747 16901113046608381940027621)
                    ·
                      refine ⟨3168958696239071613755179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16901113046608381940027621 3168958696239071613755179)
                      ·
                        rfl

theorem cell23_6171525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_6171525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171525 prefixEnd_6171525 := by exact prefixLift 6171525
  have htrace : WordTrace (prefixWord ++ tailWord_6171525) baseStart_6171525 baseEnd_6171525 := by
    simpa [prefixWord, tailWord_6171525, baseEnd_6171525] using wordTrace_append hprefix tailTrace_6171525
  have hstable : (prefixWord ++ tailWord_6171525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171525).length < 2 ^ (prefixWord ++ tailWord_6171525).sum := by decide
  have hdescent : baseEnd_6171525 < baseStart_6171525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171546 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2]
def baseStart_6171546 : Nat := 118140960795 + 6171546 * 2 ^ 59
def prefixEnd_6171546 : Nat := 4983230072969 + 3 ^ 40 * 6171546 * 2
def baseEnd_6171546 : Nat := 3168969479332816031592583

theorem tailTrace_6171546 : CollatzResearch.WordTrace tailWord_6171546 prefixEnd_6171546 3168969479332816031592583 := by
  unfold tailWord_6171546
  simp only [CollatzResearch.WordTrace]
  refine ⟨56273693724887583246849623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150063183266366888658265661 56273693724887583246849623)
  ·
    refine ⟨84410540587331374870274435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56273693724887583246849623 84410540587331374870274435)
    ·
      refine ⟨126615810880997062305411653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84410540587331374870274435 126615810880997062305411653)
      ·
        refine ⟨23740464540186949182264685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126615810880997062305411653 23740464540186949182264685)
        ·
          refine ⟨8902674202570105943349257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23740464540186949182264685 8902674202570105943349257)
          ·
            refine ⟨6677005651927579457511943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8902674202570105943349257 6677005651927579457511943)
            ·
              refine ⟨10015508477891369186267915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6677005651927579457511943 10015508477891369186267915)
              ·
                refine ⟨15023262716837053779401873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10015508477891369186267915 15023262716837053779401873)
                ·
                  refine ⟨11267447037627790334551405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15023262716837053779401873 11267447037627790334551405)
                  ·
                    refine ⟨4225292639110421375456777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11267447037627790334551405 4225292639110421375456777)
                    ·
                      refine ⟨3168969479332816031592583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225292639110421375456777 3168969479332816031592583)
                      ·
                        rfl

theorem cell23_6171546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_6171546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171546 prefixEnd_6171546 := by exact prefixLift 6171546
  have htrace : WordTrace (prefixWord ++ tailWord_6171546) baseStart_6171546 baseEnd_6171546 := by
    simpa [prefixWord, tailWord_6171546, baseEnd_6171546] using wordTrace_append hprefix tailTrace_6171546
  have hstable : (prefixWord ++ tailWord_6171546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171546).length < 2 ^ (prefixWord ++ tailWord_6171546).sum := by decide
  have hdescent : baseEnd_6171546 < baseStart_6171546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171555 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4]
def baseStart_6171555 : Nat := 118140960795 + 6171555 * 2 ^ 59
def prefixEnd_6171555 : Nat := 4983230072969 + 3 ^ 40 * 6171555 * 2
def baseEnd_6171555 : Nat := 3168974100658706496380041

theorem tailTrace_6171555 : CollatzResearch.WordTrace tailWord_6171555 prefixEnd_6171555 3168974100658706496380041 := by
  unfold tailWord_6171555
  simp only [CollatzResearch.WordTrace]
  refine ⟨225095103156517727524476119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150063402104345151682984079 225095103156517727524476119)
  ·
    refine ⟨337642654734776591286714179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225095103156517727524476119 337642654734776591286714179)
    ·
      refine ⟨506463982102164886930071269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337642654734776591286714179 506463982102164886930071269)
      ·
        refine ⟨94961996644155916299388363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 506463982102164886930071269 94961996644155916299388363)
        ·
          refine ⟨142442994966233874449082545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94961996644155916299388363 142442994966233874449082545)
          ·
            refine ⟨106832246224675405836811909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142442994966233874449082545 106832246224675405836811909)
            ·
              refine ⟨20031046167126638594402233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106832246224675405836811909 20031046167126638594402233)
              ·
                refine ⟨15023284625344978945801675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20031046167126638594402233 15023284625344978945801675)
                ·
                  refine ⟨22534926938017468418702513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15023284625344978945801675 22534926938017468418702513)
                  ·
                    refine ⟨16901195203513101314026885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22534926938017468418702513 16901195203513101314026885)
                    ·
                      refine ⟨3168974100658706496380041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16901195203513101314026885 3168974100658706496380041)
                      ·
                        rfl

theorem cell23_6171555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_6171555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171555 prefixEnd_6171555 := by exact prefixLift 6171555
  have htrace : WordTrace (prefixWord ++ tailWord_6171555) baseStart_6171555 baseEnd_6171555 := by
    simpa [prefixWord, tailWord_6171555, baseEnd_6171555] using wordTrace_append hprefix tailTrace_6171555
  have hstable : (prefixWord ++ tailWord_6171555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171555).length < 2 ^ (prefixWord ++ tailWord_6171555).sum := by decide
  have hdescent : baseEnd_6171555 < baseStart_6171555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171559 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_6171559 : Nat := 118140960795 + 6171559 * 2 ^ 59
def prefixEnd_6171559 : Nat := 4983230072969 + 3 ^ 40 * 6171559 * 2
def baseEnd_6171559 : Nat := 3168976154581324480730023

theorem tailTrace_6171559 : CollatzResearch.WordTrace tailWord_6171559 prefixEnd_6171559 3168976154581324480730023 := by
  unfold tailWord_6171559
  simp only [CollatzResearch.WordTrace]
  refine ⟨225095249048503236207621731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150063499365668824138414487 225095249048503236207621731)
  ·
    refine ⟨337642873572754854311432597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225095249048503236207621731 337642873572754854311432597)
    ·
      refine ⟨15827009698722883795848403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 337642873572754854311432597 15827009698722883795848403)
      ·
        refine ⟨23740514548084325693772605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15827009698722883795848403 23740514548084325693772605)
        ·
          refine ⟨8902692955531622135164727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23740514548084325693772605 8902692955531622135164727)
          ·
            refine ⟨13354039433297433202747091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8902692955531622135164727 13354039433297433202747091)
            ·
              refine ⟨20031059149946149804120637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13354039433297433202747091 20031059149946149804120637)
              ·
                refine ⟨7511647181229806176545239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20031059149946149804120637 7511647181229806176545239)
                ·
                  refine ⟨11267470771844709264817859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511647181229806176545239 11267470771844709264817859)
                  ·
                    refine ⟨16901206157767063897226789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11267470771844709264817859 16901206157767063897226789)
                    ·
                      refine ⟨3168976154581324480730023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16901206157767063897226789 3168976154581324480730023)
                      ·
                        rfl

theorem cell23_6171559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_6171559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171559 prefixEnd_6171559 := by exact prefixLift 6171559
  have htrace : WordTrace (prefixWord ++ tailWord_6171559) baseStart_6171559 baseEnd_6171559 := by
    simpa [prefixWord, tailWord_6171559, baseEnd_6171559] using wordTrace_append hprefix tailTrace_6171559
  have hstable : (prefixWord ++ tailWord_6171559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171559).length < 2 ^ (prefixWord ++ tailWord_6171559).sum := by decide
  have hdescent : baseEnd_6171559 < baseStart_6171559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171575 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_6171575 : Nat := 118140960795 + 6171575 * 2 ^ 59
def prefixEnd_6171575 : Nat := 4983230072969 + 3 ^ 40 * 6171575 * 2
def baseEnd_6171575 : Nat := 3168984370271796418129949

theorem tailTrace_6171575 : CollatzResearch.WordTrace tailWord_6171575 prefixEnd_6171575 3168984370271796418129949 := by
  unfold tailWord_6171575
  simp only [CollatzResearch.WordTrace]
  refine ⟨225095832616445270940204179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150063888410963513960136119 225095832616445270940204179)
  ·
    refine ⟨337643748924667906410306269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225095832616445270940204179 337643748924667906410306269)
    ·
      refine ⟨126616405846750464903864851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337643748924667906410306269 126616405846750464903864851)
      ·
        refine ⟨189924608770125697355797277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126616405846750464903864851 189924608770125697355797277)
        ·
          refine ⟨71221728288797136508423979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189924608770125697355797277 71221728288797136508423979)
          ·
            refine ⟨106832592433195704762635969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71221728288797136508423979 106832592433195704762635969)
            ·
              refine ⟨80124444324896778571976977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106832592433195704762635969 80124444324896778571976977)
              ·
                refine ⟨60093333243672583928982733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80124444324896778571976977 60093333243672583928982733)
                ·
                  refine ⟨22534999966377218973368525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60093333243672583928982733 22534999966377218973368525)
                  ·
                    refine ⟨8450624987391457115013197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22534999966377218973368525 8450624987391457115013197)
                    ·
                      refine ⟨3168984370271796418129949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8450624987391457115013197 3168984370271796418129949)
                      ·
                        rfl

theorem cell23_6171575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_6171575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171575 prefixEnd_6171575 := by exact prefixLift 6171575
  have htrace : WordTrace (prefixWord ++ tailWord_6171575) baseStart_6171575 baseEnd_6171575 := by
    simpa [prefixWord, tailWord_6171575, baseEnd_6171575] using wordTrace_append hprefix tailTrace_6171575
  have hstable : (prefixWord ++ tailWord_6171575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171575).length < 2 ^ (prefixWord ++ tailWord_6171575).sum := by decide
  have hdescent : baseEnd_6171575 < baseStart_6171575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171576 : List Nat := [2, 1, 2, 1, 2, 4, 2, 4, 1, 2, 2]
def baseStart_6171576 : Nat := 118140960795 + 6171576 * 2 ^ 59
def prefixEnd_6171576 : Nat := 4983230072969 + 3 ^ 40 * 6171576 * 2
def baseEnd_6171576 : Nat := 3168984883752450914217445

theorem tailTrace_6171576 : CollatzResearch.WordTrace tailWord_6171576 prefixEnd_6171576 3168984883752450914217445 := by
  unfold tailWord_6171576
  simp only [CollatzResearch.WordTrace]
  refine ⟨112547934544720824055495291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150063912726294432073993721 112547934544720824055495291)
  ·
    refine ⟨168821901817081236083242937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112547934544720824055495291 168821901817081236083242937)
    ·
      refine ⟨126616426362810927062432203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168821901817081236083242937 126616426362810927062432203)
      ·
        refine ⟨189924639544216390593648305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126616426362810927062432203 189924639544216390593648305)
        ·
          refine ⟨142443479658162292945236229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189924639544216390593648305 142443479658162292945236229)
          ·
            refine ⟨26708152435905429927231793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142443479658162292945236229 26708152435905429927231793)
            ·
              refine ⟨20031114326929072445423845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26708152435905429927231793 20031114326929072445423845)
              ·
                refine ⟨3755833936299201083516971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20031114326929072445423845 3755833936299201083516971)
                ·
                  refine ⟨5633750904448801625275457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755833936299201083516971 5633750904448801625275457)
                  ·
                    refine ⟨4225313178336601218956593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5633750904448801625275457 4225313178336601218956593)
                    ·
                      refine ⟨3168984883752450914217445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225313178336601218956593 3168984883752450914217445)
                      ·
                        rfl

theorem cell23_6171576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_6171576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171576 prefixEnd_6171576 := by exact prefixLift 6171576
  have htrace : WordTrace (prefixWord ++ tailWord_6171576) baseStart_6171576 baseEnd_6171576 := by
    simpa [prefixWord, tailWord_6171576, baseEnd_6171576] using wordTrace_append hprefix tailTrace_6171576
  have hstable : (prefixWord ++ tailWord_6171576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171576).length < 2 ^ (prefixWord ++ tailWord_6171576).sum := by decide
  have hdescent : baseEnd_6171576 < baseStart_6171576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171590 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6171590 : Nat := 118140960795 + 6171590 * 2 ^ 59
def prefixEnd_6171590 : Nat := 4983230072969 + 3 ^ 40 * 6171590 * 2
def baseEnd_6171590 : Nat := 1056330690827204619814127

theorem tailTrace_6171590 : CollatzResearch.WordTrace tailWord_6171590 prefixEnd_6171590 1056330690827204619814127 := by
  unfold tailWord_6171590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7034261865980966515687507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150064253140927285668000149 7034261865980966515687507)
  ·
    refine ⟨10551392798971449773531261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7034261865980966515687507 10551392798971449773531261)
    ·
      refine ⟨3956772299614293665074223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10551392798971449773531261 3956772299614293665074223)
      ·
        refine ⟨5935158449421440497611335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3956772299614293665074223 5935158449421440497611335)
        ·
          refine ⟨8902737674132160746417003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5935158449421440497611335 8902737674132160746417003)
          ·
            refine ⟨13354106511198241119625505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8902737674132160746417003 13354106511198241119625505)
            ·
              refine ⟨10015579883398680839719129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13354106511198241119625505 10015579883398680839719129)
              ·
                refine ⟨7511684912549010629789347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10015579883398680839719129 7511684912549010629789347)
                ·
                  refine ⟨11267527368823515944684021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511684912549010629789347 11267527368823515944684021)
                  ·
                    refine ⟨1056330690827204619814127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11267527368823515944684021 1056330690827204619814127)
                    ·
                      rfl

theorem cell23_6171590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6171590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171590 prefixEnd_6171590 := by exact prefixLift 6171590
  have htrace : WordTrace (prefixWord ++ tailWord_6171590) baseStart_6171590 baseEnd_6171590 := by
    simpa [prefixWord, tailWord_6171590, baseEnd_6171590] using wordTrace_append hprefix tailTrace_6171590
  have hstable : (prefixWord ++ tailWord_6171590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171590).length < 2 ^ (prefixWord ++ tailWord_6171590).sum := by decide
  have hdescent : baseEnd_6171590 < baseStart_6171590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171619 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 1, 3, 2]
def baseStart_6171619 : Nat := 118140960795 + 6171619 * 2 ^ 59
def prefixEnd_6171619 : Nat := 4983230072969 + 3 ^ 40 * 6171619 * 2
def baseEnd_6171619 : Nat := 3169006963420594245979747

theorem tailTrace_6171619 : CollatzResearch.WordTrace tailWord_6171619 prefixEnd_6171619 3169006963420594245979747 := by
  unfold tailWord_6171619
  simp only [CollatzResearch.WordTrace]
  refine ⟨225097437428285866454805911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150064958285523910969870607 225097437428285866454805911)
  ·
    refine ⟨337646156142428799682208867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225097437428285866454805911 337646156142428799682208867)
    ·
      refine ⟨506469234213643199523313301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337646156142428799682208867 506469234213643199523313301)
      ·
        refine ⟨23740745353764524977655311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 506469234213643199523313301 23740745353764524977655311)
        ·
          refine ⟨35611118030646787466482967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23740745353764524977655311 35611118030646787466482967)
          ·
            refine ⟨53416677045970181199724451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35611118030646787466482967 53416677045970181199724451)
            ·
              refine ⟨80125015568955271799586677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53416677045970181199724451 80125015568955271799586677)
              ·
                refine ⟨7511720209589556731211251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80125015568955271799586677 7511720209589556731211251)
                ·
                  refine ⟨11267580314384335096816877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511720209589556731211251 11267580314384335096816877)
                  ·
                    refine ⟨4225342617894125661306329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11267580314384335096816877 4225342617894125661306329)
                    ·
                      refine ⟨3169006963420594245979747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225342617894125661306329 3169006963420594245979747)
                      ·
                        rfl

theorem cell23_6171619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_6171619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171619 prefixEnd_6171619 := by exact prefixLift 6171619
  have htrace : WordTrace (prefixWord ++ tailWord_6171619) baseStart_6171619 baseEnd_6171619 := by
    simpa [prefixWord, tailWord_6171619, baseEnd_6171619] using wordTrace_append hprefix tailTrace_6171619
  have hstable : (prefixWord ++ tailWord_6171619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171619).length < 2 ^ (prefixWord ++ tailWord_6171619).sum := by decide
  have hdescent : baseEnd_6171619 < baseStart_6171619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171645 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_6171645 : Nat := 118140960795 + 6171645 * 2 ^ 59
def prefixEnd_6171645 : Nat := 4983230072969 + 3 ^ 40 * 6171645 * 2
def baseEnd_6171645 : Nat := 3169020313917611144254627

theorem tailTrace_6171645 : CollatzResearch.WordTrace tailWord_6171645 prefixEnd_6171645 3169020313917611144254627 := by
  unfold tailWord_6171645
  simp only [CollatzResearch.WordTrace]
  refine ⟨225098385726191672895252389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150065590484127781930168259 225098385726191672895252389)
  ·
    refine ⟨42205947323660938667859823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225098385726191672895252389 42205947323660938667859823)
    ·
      refine ⟨63308920985491408001789735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42205947323660938667859823 63308920985491408001789735)
      ·
        refine ⟨94963381478237112002684603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63308920985491408001789735 94963381478237112002684603)
        ·
          refine ⟨142445072217355668004026905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94963381478237112002684603 142445072217355668004026905)
          ·
            refine ⟨106833804163016751003020179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142445072217355668004026905 106833804163016751003020179)
            ·
              refine ⟨160250706244525126504530269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106833804163016751003020179 160250706244525126504530269)
              ·
                refine ⟨60094014841696922439198851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160250706244525126504530269 60094014841696922439198851)
                ·
                  refine ⟨90141022262545383658798277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60094014841696922439198851 90141022262545383658798277)
                  ·
                    refine ⟨16901441674227259436024677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90141022262545383658798277 16901441674227259436024677)
                    ·
                      refine ⟨3169020313917611144254627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16901441674227259436024677 3169020313917611144254627)
                      ·
                        rfl

theorem cell23_6171645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_6171645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171645 prefixEnd_6171645 := by exact prefixLift 6171645
  have htrace : WordTrace (prefixWord ++ tailWord_6171645) baseStart_6171645 baseEnd_6171645 := by
    simpa [prefixWord, tailWord_6171645, baseEnd_6171645] using wordTrace_append hprefix tailTrace_6171645
  have hstable : (prefixWord ++ tailWord_6171645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171645).length < 2 ^ (prefixWord ++ tailWord_6171645).sum := by decide
  have hdescent : baseEnd_6171645 < baseStart_6171645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171655 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 9]
def baseStart_6171655 : Nat := 118140960795 + 6171655 * 2 ^ 59
def prefixEnd_6171655 : Nat := 4983230072969 + 3 ^ 40 * 6171655 * 2
def baseEnd_6171655 : Nat := 352113938747128456125509

theorem tailTrace_6171655 : CollatzResearch.WordTrace tailWord_6171655 prefixEnd_6171655 352113938747128456125509 := by
  unfold tailWord_6171655
  simp only [CollatzResearch.WordTrace]
  refine ⟨225098750456155444603116419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150065833637436963068744279 225098750456155444603116419)
  ·
    refine ⟨337648125684233166904674629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225098750456155444603116419 337648125684233166904674629)
    ·
      refine ⟨63309023565793718794626493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337648125684233166904674629 63309023565793718794626493)
      ·
        refine ⟨23740883837172644547984935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63309023565793718794626493 23740883837172644547984935)
        ·
          refine ⟨35611325755758966821977403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23740883837172644547984935 35611325755758966821977403)
          ·
            refine ⟨53416988633638450232966105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35611325755758966821977403 53416988633638450232966105)
            ·
              refine ⟨40062741475228837674724579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53416988633638450232966105 40062741475228837674724579)
              ·
                refine ⟨60094112212843256512086869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40062741475228837674724579 60094112212843256512086869)
                ·
                  refine ⟨352113938747128456125509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60094112212843256512086869 352113938747128456125509)
                  ·
                    rfl

theorem cell23_6171655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 9].length) (baseStart_6171655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171655 prefixEnd_6171655 := by exact prefixLift 6171655
  have htrace : WordTrace (prefixWord ++ tailWord_6171655) baseStart_6171655 baseEnd_6171655 := by
    simpa [prefixWord, tailWord_6171655, baseEnd_6171655] using wordTrace_append hprefix tailTrace_6171655
  have hstable : (prefixWord ++ tailWord_6171655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171655).length < 2 ^ (prefixWord ++ tailWord_6171655).sum := by decide
  have hdescent : baseEnd_6171655 < baseStart_6171655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171692 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 7, 2]
def baseStart_6171692 : Nat := 118140960795 + 6171692 * 2 ^ 59
def prefixEnd_6171692 : Nat := 4983230072969 + 3 ^ 40 * 6171692 * 2
def baseEnd_6171692 : Nat := 3169044447508372460366911

theorem tailTrace_6171692 : CollatzResearch.WordTrace tailWord_6171692 prefixEnd_6171692 3169044447508372460366911 := by
  unfold tailWord_6171692
  simp only [CollatzResearch.WordTrace]
  refine ⟨112550049978510699961106665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150066733304680933281475553 112550049978510699961106665)
  ·
    refine ⟨84412537483883024970829999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112550049978510699961106665 84412537483883024970829999)
    ·
      refine ⟨126618806225824537456244999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84412537483883024970829999 126618806225824537456244999)
      ·
        refine ⟨189928209338736806184367499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126618806225824537456244999 189928209338736806184367499)
        ·
          refine ⟨284892314008105209276551249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189928209338736806184367499 284892314008105209276551249)
          ·
            refine ⟨213669235506078906957413437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284892314008105209276551249 213669235506078906957413437)
            ·
              refine ⟨80125963314779590109030039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213669235506078906957413437 80125963314779590109030039)
              ·
                refine ⟨120188944972169385163545059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80125963314779590109030039 120188944972169385163545059)
                ·
                  refine ⟨180283417458254077745317589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120188944972169385163545059 180283417458254077745317589)
                  ·
                    refine ⟨4225392596677829947155881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 180283417458254077745317589 4225392596677829947155881)
                    ·
                      refine ⟨3169044447508372460366911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225392596677829947155881 3169044447508372460366911)
                      ·
                        rfl

theorem cell23_6171692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_6171692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171692 prefixEnd_6171692 := by exact prefixLift 6171692
  have htrace : WordTrace (prefixWord ++ tailWord_6171692) baseStart_6171692 baseEnd_6171692 := by
    simpa [prefixWord, tailWord_6171692, baseEnd_6171692] using wordTrace_append hprefix tailTrace_6171692
  have hstable : (prefixWord ++ tailWord_6171692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171692).length < 2 ^ (prefixWord ++ tailWord_6171692).sum := by decide
  have hdescent : baseEnd_6171692 < baseStart_6171692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171719 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 2, 5]
def baseStart_6171719 : Nat := 118140960795 + 6171719 * 2 ^ 59
def prefixEnd_6171719 : Nat := 4983230072969 + 3 ^ 40 * 6171719 * 2
def baseEnd_6171719 : Nat := 1056352770495347951576429

theorem tailTrace_6171719 : CollatzResearch.WordTrace tailWord_6171719 prefixEnd_6171719 1056352770495347951576429 := by
  unfold tailWord_6171719
  simp only [CollatzResearch.WordTrace]
  refine ⟨225101084727923583533446211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150067389818615722355630807 225101084727923583533446211)
  ·
    refine ⟨337651627091885375300169317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225101084727923583533446211 337651627091885375300169317)
    ·
      refine ⟨63309680079728507868781747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337651627091885375300169317 63309680079728507868781747)
      ·
        refine ⟨94964520119592761803172621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63309680079728507868781747 94964520119592761803172621)
        ·
          refine ⟨35611695044847285676189733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94964520119592761803172621 35611695044847285676189733)
          ·
            refine ⟨6677192820908866064285575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35611695044847285676189733 6677192820908866064285575)
            ·
              refine ⟨10015789231363299096428363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6677192820908866064285575 10015789231363299096428363)
              ·
                refine ⟨15023683847044948644642545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10015789231363299096428363 15023683847044948644642545)
                ·
                  refine ⟨11267762885283711483481909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15023683847044948644642545 11267762885283711483481909)
                  ·
                    refine ⟨1056352770495347951576429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11267762885283711483481909 1056352770495347951576429)
                    ·
                      rfl

theorem cell23_6171719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_6171719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171719 prefixEnd_6171719 := by exact prefixLift 6171719
  have htrace : WordTrace (prefixWord ++ tailWord_6171719) baseStart_6171719 baseEnd_6171719 := by
    simpa [prefixWord, tailWord_6171719, baseEnd_6171719] using wordTrace_append hprefix tailTrace_6171719
  have hstable : (prefixWord ++ tailWord_6171719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171719).length < 2 ^ (prefixWord ++ tailWord_6171719).sum := by decide
  have hdescent : baseEnd_6171719 < baseStart_6171719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171734 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6171734 : Nat := 118140960795 + 6171734 * 2 ^ 59
def prefixEnd_6171734 : Nat := 4983230072969 + 3 ^ 40 * 6171734 * 2
def baseEnd_6171734 : Nat := 3169066013695861296041719

theorem tailTrace_6171734 : CollatzResearch.WordTrace tailWord_6171734 prefixEnd_6171734 3169066013695861296041719 := by
  unfold tailWord_6171734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068851988929327568452641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150067754548579494063494837 14068851988929327568452641)
  ·
    refine ⟨10551638991696995676339481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14068851988929327568452641 10551638991696995676339481)
    ·
      refine ⟨7913729243772746757254611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10551638991696995676339481 7913729243772746757254611)
      ·
        refine ⟨11870593865659120135881917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913729243772746757254611 11870593865659120135881917)
        ·
          refine ⟨4451472699622170050955719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11870593865659120135881917 4451472699622170050955719)
          ·
            refine ⟨6677209049433255076433579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451472699622170050955719 6677209049433255076433579)
            ·
              refine ⟨10015813574149882614650369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6677209049433255076433579 10015813574149882614650369)
              ·
                refine ⟨7511860180612411960987777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10015813574149882614650369 7511860180612411960987777)
                ·
                  refine ⟨5633895135459308970740833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7511860180612411960987777 5633895135459308970740833)
                  ·
                    refine ⟨4225421351594481728055625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5633895135459308970740833 4225421351594481728055625)
                    ·
                      refine ⟨3169066013695861296041719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225421351594481728055625 3169066013695861296041719)
                      ·
                        rfl

theorem cell23_6171734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6171734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171734 prefixEnd_6171734 := by exact prefixLift 6171734
  have htrace : WordTrace (prefixWord ++ tailWord_6171734) baseStart_6171734 baseEnd_6171734 := by
    simpa [prefixWord, tailWord_6171734, baseEnd_6171734] using wordTrace_append hprefix tailTrace_6171734
  have hstable : (prefixWord ++ tailWord_6171734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171734).length < 2 ^ (prefixWord ++ tailWord_6171734).sum := by decide
  have hdescent : baseEnd_6171734 < baseStart_6171734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171749 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_6171749 : Nat := 118140960795 + 6171749 * 2 ^ 59
def prefixEnd_6171749 : Nat := 4983230072969 + 3 ^ 40 * 6171749 * 2
def baseEnd_6171749 : Nat := 1056357905301892912451383

theorem tailTrace_6171749 : CollatzResearch.WordTrace tailWord_6171749 prefixEnd_6171749 1056357905301892912451383 := by
  unfold tailWord_6171749
  simp only [CollatzResearch.WordTrace]
  refine ⟨225102178917814898657038301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150068119278543265771358867 225102178917814898657038301)
  ·
    refine ⟨84413317094180586996389363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225102178917814898657038301 84413317094180586996389363)
    ·
      refine ⟨126619975641270880494584045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84413317094180586996389363 126619975641270880494584045)
      ·
        refine ⟨47482490865476580185469017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126619975641270880494584045 47482490865476580185469017)
        ·
          refine ⟨35611868149107435139101763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47482490865476580185469017 35611868149107435139101763)
          ·
            refine ⟨53417802223661152708652645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35611868149107435139101763 53417802223661152708652645)
            ·
              refine ⟨10015837916936466132872371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53417802223661152708652645 10015837916936466132872371)
              ·
                refine ⟨15023756875404699199308557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10015837916936466132872371 15023756875404699199308557)
                ·
                  refine ⟨5633908828276762199740709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15023756875404699199308557 5633908828276762199740709)
                  ·
                    refine ⟨1056357905301892912451383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5633908828276762199740709 1056357905301892912451383)
                    ·
                      rfl

theorem cell23_6171749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_6171749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171749 prefixEnd_6171749 := by exact prefixLift 6171749
  have htrace : WordTrace (prefixWord ++ tailWord_6171749) baseStart_6171749 baseEnd_6171749 := by
    simpa [prefixWord, tailWord_6171749, baseEnd_6171749] using wordTrace_append hprefix tailTrace_6171749
  have hstable : (prefixWord ++ tailWord_6171749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171749).length < 2 ^ (prefixWord ++ tailWord_6171749).sum := by decide
  have hdescent : baseEnd_6171749 < baseStart_6171749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171772 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_6171772 : Nat := 118140960795 + 6171772 * 2 ^ 59
def prefixEnd_6171772 : Nat := 4983230072969 + 3 ^ 40 * 6171772 * 2
def baseEnd_6171772 : Nat := 3169085525960732147366543

theorem tailTrace_6171772 : CollatzResearch.WordTrace tailWord_6171772 prefixEnd_6171772 3169085525960732147366543 := by
  unfold tailWord_6171772
  simp only [CollatzResearch.WordTrace]
  refine ⟨112551508898365786792562785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150068678531154382390083713 112551508898365786792562785)
  ·
    refine ⟨84413631673774340094422089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112551508898365786792562785 84413631673774340094422089)
    ·
      refine ⟨63310223755330755070816567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84413631673774340094422089 63310223755330755070816567)
      ·
        refine ⟨94965335632996132606224851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63310223755330755070816567 94965335632996132606224851)
        ·
          refine ⟨142448003449494198909337277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94965335632996132606224851 142448003449494198909337277)
          ·
            refine ⟨53418001293560324591001479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142448003449494198909337277 53418001293560324591001479)
            ·
              refine ⟨80127001940340486886502219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53418001293560324591001479 80127001940340486886502219)
              ·
                refine ⟨120190502910510730329753329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80127001940340486886502219 120190502910510730329753329)
                ·
                  refine ⟨90142877182883047747314997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120190502910510730329753329 90142877182883047747314997)
                  ·
                    refine ⟨8450894735895285726310781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90142877182883047747314997 8450894735895285726310781)
                    ·
                      refine ⟨3169085525960732147366543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8450894735895285726310781 3169085525960732147366543)
                      ·
                        rfl

theorem cell23_6171772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_6171772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171772 prefixEnd_6171772 := by exact prefixLift 6171772
  have htrace : WordTrace (prefixWord ++ tailWord_6171772) baseStart_6171772 baseEnd_6171772 := by
    simpa [prefixWord, tailWord_6171772, baseEnd_6171772] using wordTrace_append hprefix tailTrace_6171772
  have hstable : (prefixWord ++ tailWord_6171772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171772).length < 2 ^ (prefixWord ++ tailWord_6171772).sum := by decide
  have hdescent : baseEnd_6171772 < baseStart_6171772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171775 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 9]
def baseStart_6171775 : Nat := 118140960795 + 6171775 * 2 ^ 59
def prefixEnd_6171775 : Nat := 4983230072969 + 3 ^ 40 * 6171775 * 2
def baseEnd_6171775 : Nat := 1056362355467565211876343

theorem tailTrace_6171775 : CollatzResearch.WordTrace tailWord_6171775 prefixEnd_6171775 1056362355467565211876343 := by
  unfold tailWord_6171775
  simp only [CollatzResearch.WordTrace]
  refine ⟨225103127215720705097484779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150068751477147136731656519 225103127215720705097484779)
  ·
    refine ⟨337654690823581057646227169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225103127215720705097484779 337654690823581057646227169)
    ·
      refine ⟨253241018117685793234670377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337654690823581057646227169 253241018117685793234670377)
      ·
        refine ⟨189930763588264344926002783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253241018117685793234670377 189930763588264344926002783)
        ·
          refine ⟨284896145382396517389004175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189930763588264344926002783 284896145382396517389004175)
          ·
            refine ⟨427344218073594776083506263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284896145382396517389004175 427344218073594776083506263)
            ·
              refine ⟨641016327110392164125259395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427344218073594776083506263 641016327110392164125259395)
              ·
                refine ⟨961524490665588246187889093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641016327110392164125259395 961524490665588246187889093)
                ·
                  refine ⟨180285841999797796160229205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961524490665588246187889093 180285841999797796160229205)
                  ·
                    refine ⟨1056362355467565211876343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180285841999797796160229205 1056362355467565211876343)
                    ·
                      rfl

theorem cell23_6171775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_6171775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171775 prefixEnd_6171775 := by exact prefixLift 6171775
  have htrace : WordTrace (prefixWord ++ tailWord_6171775) baseStart_6171775 baseEnd_6171775 := by
    simpa [prefixWord, tailWord_6171775, baseEnd_6171775] using wordTrace_append hprefix tailTrace_6171775
  have hstable : (prefixWord ++ tailWord_6171775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171775).length < 2 ^ (prefixWord ++ tailWord_6171775).sum := by decide
  have hdescent : baseEnd_6171775 < baseStart_6171775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171826 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_6171826 : Nat := 118140960795 + 6171826 * 2 ^ 59
def prefixEnd_6171826 : Nat := 4983230072969 + 3 ^ 40 * 6171826 * 2
def baseEnd_6171826 : Nat := 1056371084638691645363765

theorem tailTrace_6171826 : CollatzResearch.WordTrace tailWord_6171826 prefixEnd_6171826 1056371084638691645363765 := by
  unfold tailWord_6171826
  simp only [CollatzResearch.WordTrace]
  refine ⟨56276246834633985201897833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150069991559023960538394221 56276246834633985201897833)
  ·
    refine ⟨42207185125975488901423375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56276246834633985201897833 42207185125975488901423375)
    ·
      refine ⟨63310777688963233352135063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42207185125975488901423375 63310777688963233352135063)
      ·
        refine ⟨94966166533444850028202595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63310777688963233352135063 94966166533444850028202595)
        ·
          refine ⟨142449249800167275042303893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94966166533444850028202595 142449249800167275042303893)
          ·
            refine ⟨6677308584382841017607995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142449249800167275042303893 6677308584382841017607995)
            ·
              refine ⟨10015962876574261526411993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6677308584382841017607995 10015962876574261526411993)
              ·
                refine ⟨7511972157430696144808995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10015962876574261526411993 7511972157430696144808995)
                ·
                  refine ⟨11267958236146044217213493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7511972157430696144808995 11267958236146044217213493)
                  ·
                    refine ⟨1056371084638691645363765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11267958236146044217213493 1056371084638691645363765)
                    ·
                      rfl

theorem cell23_6171826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_6171826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171826 prefixEnd_6171826 := by exact prefixLift 6171826
  have htrace : WordTrace (prefixWord ++ tailWord_6171826) baseStart_6171826 baseEnd_6171826 := by
    simpa [prefixWord, tailWord_6171826, baseEnd_6171826] using wordTrace_append hprefix tailTrace_6171826
  have hstable : (prefixWord ++ tailWord_6171826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171826).length < 2 ^ (prefixWord ++ tailWord_6171826).sum := by decide
  have hdescent : baseEnd_6171826 < baseStart_6171826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171900 : List Nat := [2, 2, 2, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_6171900 : Nat := 118140960795 + 6171900 * 2 ^ 59
def prefixEnd_6171900 : Nat := 4983230072969 + 3 ^ 40 * 6171900 * 2
def baseEnd_6171900 : Nat := 3169151251484507646565955

theorem tailTrace_6171900 : CollatzResearch.WordTrace tailWord_6171900 prefixEnd_6171900 3169151251484507646565955 := by
  unfold tailWord_6171900
  simp only [CollatzResearch.WordTrace]
  refine ⟨112553843170133925722892577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150071790893511900963856769 112553843170133925722892577)
  ·
    refine ⟨84415382377600444292169433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112553843170133925722892577 84415382377600444292169433)
    ·
      refine ⟨63311536783200333219127075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84415382377600444292169433 63311536783200333219127075)
      ·
        refine ⟨94967305174800499828690613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63311536783200333219127075 94967305174800499828690613)
        ·
          refine ⟨8903184860137546858939745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94967305174800499828690613 8903184860137546858939745)
          ·
            refine ⟨6677388645103160144204809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8903184860137546858939745 6677388645103160144204809)
            ·
              refine ⟨5008041483827370108153607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6677388645103160144204809 5008041483827370108153607)
              ·
                refine ⟨7512062225741055162230411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008041483827370108153607 7512062225741055162230411)
                ·
                  refine ⟨11268093338611582743345617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7512062225741055162230411 11268093338611582743345617)
                  ·
                    refine ⟨8451070003958687057509213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11268093338611582743345617 8451070003958687057509213)
                    ·
                      refine ⟨3169151251484507646565955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451070003958687057509213 3169151251484507646565955)
                      ·
                        rfl

theorem cell23_6171900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_6171900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171900 prefixEnd_6171900 := by exact prefixLift 6171900
  have htrace : WordTrace (prefixWord ++ tailWord_6171900) baseStart_6171900 baseEnd_6171900 := by
    simpa [prefixWord, tailWord_6171900, baseEnd_6171900] using wordTrace_append hprefix tailTrace_6171900
  have hstable : (prefixWord ++ tailWord_6171900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171900).length < 2 ^ (prefixWord ++ tailWord_6171900).sum := by decide
  have hdescent : baseEnd_6171900 < baseStart_6171900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171919 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 8, 2]
def baseStart_6171919 : Nat := 118140960795 + 6171919 * 2 ^ 59
def prefixEnd_6171919 : Nat := 4983230072969 + 3 ^ 40 * 6171919 * 2
def baseEnd_6171919 : Nat := 3169161007616943072228367

theorem tailTrace_6171919 : CollatzResearch.WordTrace tailWord_6171919 prefixEnd_6171919 3169161007616943072228367 := by
  unfold tailWord_6171919
  simp only [CollatzResearch.WordTrace]
  refine ⟨225108379327199017690726811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150072252884799345127151207 225108379327199017690726811)
  ·
    refine ⟨337662568990798526536090217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225108379327199017690726811 337662568990798526536090217)
    ·
      refine ⟨253246926743098894902067663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337662568990798526536090217 253246926743098894902067663)
      ·
        refine ⟨379870390114648342353101495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253246926743098894902067663 379870390114648342353101495)
        ·
          refine ⟨569805585171972513529652243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379870390114648342353101495 569805585171972513529652243)
          ·
            refine ⟨854708377757958770294478365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569805585171972513529652243 854708377757958770294478365)
            ·
              refine ⟨320515641659234538860429387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 854708377757958770294478365 320515641659234538860429387)
              ·
                refine ⟨480773462488851808290644081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320515641659234538860429387 480773462488851808290644081)
                ·
                  refine ⟨360580096866638856217983061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 480773462488851808290644081 360580096866638856217983061)
                  ·
                    refine ⟨4225548010155924096304489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 360580096866638856217983061 4225548010155924096304489)
                    ·
                      refine ⟨3169161007616943072228367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225548010155924096304489 3169161007616943072228367)
                      ·
                        rfl

theorem cell23_6171919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8, 2].length) (baseStart_6171919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171919 prefixEnd_6171919 := by exact prefixLift 6171919
  have htrace : WordTrace (prefixWord ++ tailWord_6171919) baseStart_6171919 baseEnd_6171919 := by
    simpa [prefixWord, tailWord_6171919, baseEnd_6171919] using wordTrace_append hprefix tailTrace_6171919
  have hstable : (prefixWord ++ tailWord_6171919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171919).length < 2 ^ (prefixWord ++ tailWord_6171919).sum := by decide
  have hdescent : baseEnd_6171919 < baseStart_6171919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171930 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3]
def baseStart_6171930 : Nat := 118140960795 + 6171930 * 2 ^ 59
def prefixEnd_6171930 : Nat := 4983230072969 + 3 ^ 40 * 6171930 * 2
def baseEnd_6171930 : Nat := 3169166655904142529190817

theorem tailTrace_6171930 : CollatzResearch.WordTrace tailWord_6171930 prefixEnd_6171930 3169166655904142529190817 := by
  unfold tailWord_6171930
  simp only [CollatzResearch.WordTrace]
  refine ⟨56277195132539791642344311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150072520353439444379584829 56277195132539791642344311)
  ·
    refine ⟨84415792698809687463516467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56277195132539791642344311 84415792698809687463516467)
    ·
      refine ⟨126623689048214531195274701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84415792698809687463516467 126623689048214531195274701)
      ·
        refine ⟨47483883393080449198228013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126623689048214531195274701 47483883393080449198228013)
        ·
          refine ⟨17806456272405168449335505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47483883393080449198228013 17806456272405168449335505)
          ·
            refine ⟨13354842204303876337001629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17806456272405168449335505 13354842204303876337001629)
            ·
              refine ⟨5008065826613953626375611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13354842204303876337001629 5008065826613953626375611)
              ·
                refine ⟨7512098739920930439563417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008065826613953626375611 7512098739920930439563417)
                ·
                  refine ⟨5634074054940697829672563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7512098739920930439563417 5634074054940697829672563)
                  ·
                    refine ⟨8451111082411046744508845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5634074054940697829672563 8451111082411046744508845)
                    ·
                      refine ⟨3169166655904142529190817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451111082411046744508845 3169166655904142529190817)
                      ·
                        rfl

theorem cell23_6171930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_6171930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171930 prefixEnd_6171930 := by exact prefixLift 6171930
  have htrace : WordTrace (prefixWord ++ tailWord_6171930) baseStart_6171930 baseEnd_6171930 := by
    simpa [prefixWord, tailWord_6171930, baseEnd_6171930] using wordTrace_append hprefix tailTrace_6171930
  have hstable : (prefixWord ++ tailWord_6171930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171930).length < 2 ^ (prefixWord ++ tailWord_6171930).sum := by decide
  have hdescent : baseEnd_6171930 < baseStart_6171930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171953 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 4, 2, 2]
def baseStart_6171953 : Nat := 118140960795 + 6171953 * 2 ^ 59
def prefixEnd_6171953 : Nat := 4983230072969 + 3 ^ 40 * 6171953 * 2
def baseEnd_6171953 : Nat := 3169178465959195939203211

theorem tailTrace_6171953 : CollatzResearch.WordTrace tailWord_6171953 prefixEnd_6171953 3169178465959195939203211 := by
  unfold tailWord_6171953
  simp only [CollatzResearch.WordTrace]
  refine ⟨225109619409075841497464513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150073079606050560998309675 225109619409075841497464513)
  ·
    refine ⟨168832214556806881123098385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225109619409075841497464513 168832214556806881123098385)
    ·
      refine ⟨126624160917605160842323789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168832214556806881123098385 126624160917605160842323789)
      ·
        refine ⟨47484060344101935315871421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126624160917605160842323789 47484060344101935315871421)
        ·
          refine ⟨17806522629038225743451783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47484060344101935315871421 17806522629038225743451783)
          ·
            refine ⟨26709783943557338615177675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17806522629038225743451783 26709783943557338615177675)
            ·
              refine ⟨40064675915336007922766513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26709783943557338615177675 40064675915336007922766513)
              ·
                refine ⟨30048506936502005942074885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40064675915336007922766513 30048506936502005942074885)
                ·
                  refine ⟨5634095050594126114139041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30048506936502005942074885 5634095050594126114139041)
                  ·
                    refine ⟨4225571287945594585604281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5634095050594126114139041 4225571287945594585604281)
                    ·
                      refine ⟨3169178465959195939203211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225571287945594585604281 3169178465959195939203211)
                      ·
                        rfl

theorem cell23_6171953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_6171953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171953 prefixEnd_6171953 := by exact prefixLift 6171953
  have htrace : WordTrace (prefixWord ++ tailWord_6171953) baseStart_6171953 baseEnd_6171953 := by
    simpa [prefixWord, tailWord_6171953, baseEnd_6171953] using wordTrace_append hprefix tailTrace_6171953
  have hstable : (prefixWord ++ tailWord_6171953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171953).length < 2 ^ (prefixWord ++ tailWord_6171953).sum := by decide
  have hdescent : baseEnd_6171953 < baseStart_6171953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171956 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6171956 : Nat := 118140960795 + 6171956 * 2 ^ 59
def prefixEnd_6171956 : Nat := 4983230072969 + 3 ^ 40 * 6171956 * 2
def baseEnd_6171956 : Nat := 3169180006401159427465697

theorem tailTrace_6171956 : CollatzResearch.WordTrace tailWord_6171956 prefixEnd_6171956 3169180006401159427465697 := by
  unfold tailWord_6171956
  simp only [CollatzResearch.WordTrace]
  refine ⟨112554864414032486504911861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150073152552043315339882481 112554864414032486504911861)
  ·
    refine ⟨10552018538815545609835487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112554864414032486504911861 10552018538815545609835487)
    ·
      refine ⟨15828027808223318414753231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552018538815545609835487 15828027808223318414753231)
      ·
        refine ⟨23742041712334977622129847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15828027808223318414753231 23742041712334977622129847)
        ·
          refine ⟨35613062568502466433194771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23742041712334977622129847 35613062568502466433194771)
          ·
            refine ⟨53419593852753699649792157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35613062568502466433194771 53419593852753699649792157)
            ·
              refine ⟨20032347694782637368672059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53419593852753699649792157 20032347694782637368672059)
              ·
                refine ⟨30048521542173956053008089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20032347694782637368672059 30048521542173956053008089)
                ·
                  refine ⟨22536391156630467039756067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30048521542173956053008089 22536391156630467039756067)
                  ·
                    refine ⟨33804586734945700559634101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22536391156630467039756067 33804586734945700559634101)
                    ·
                      refine ⟨3169180006401159427465697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33804586734945700559634101 3169180006401159427465697)
                      ·
                        rfl

theorem cell23_6171956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6171956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171956 prefixEnd_6171956 := by exact prefixLift 6171956
  have htrace : WordTrace (prefixWord ++ tailWord_6171956) baseStart_6171956 baseEnd_6171956 := by
    simpa [prefixWord, tailWord_6171956, baseEnd_6171956] using wordTrace_append hprefix tailTrace_6171956
  have hstable : (prefixWord ++ tailWord_6171956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171956).length < 2 ^ (prefixWord ++ tailWord_6171956).sum := by decide
  have hdescent : baseEnd_6171956 < baseStart_6171956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6171981 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6171981 : Nat := 118140960795 + 6171981 * 2 ^ 59
def prefixEnd_6171981 : Nat := 4983230072969 + 3 ^ 40 * 6171981 * 2
def baseEnd_6171981 : Nat := 3169192843417521829653083

theorem tailTrace_6171981 : CollatzResearch.WordTrace tailWord_6171981 prefixEnd_6171981 3169192843417521829653083 := by
  unfold tailWord_6171981
  simp only [CollatzResearch.WordTrace]
  refine ⟨225110640652974402279483797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150073760435316268186322531 225110640652974402279483797)
  ·
    refine ⟨10552061280608175106850803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 225110640652974402279483797 10552061280608175106850803)
    ·
      refine ⟨15828091920912262660276205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552061280608175106850803 15828091920912262660276205)
      ·
        refine ⟨5935534470342098497603577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15828091920912262660276205 5935534470342098497603577)
        ·
          refine ⟨4451650852756573873202683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5935534470342098497603577 4451650852756573873202683)
          ·
            refine ⟨6677476279134860809804025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451650852756573873202683 6677476279134860809804025)
            ·
              refine ⟨5008107209351145607353019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6677476279134860809804025 5008107209351145607353019)
              ·
                refine ⟨7512160814026718411029529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008107209351145607353019 7512160814026718411029529)
                ·
                  refine ⟨5634120610520038808272147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7512160814026718411029529 5634120610520038808272147)
                  ·
                    refine ⟨8451180915780058212408221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5634120610520038808272147 8451180915780058212408221)
                    ·
                      refine ⟨3169192843417521829653083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451180915780058212408221 3169192843417521829653083)
                      ·
                        rfl

theorem cell23_6171981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6171981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6171981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6171981 prefixEnd_6171981 := by exact prefixLift 6171981
  have htrace : WordTrace (prefixWord ++ tailWord_6171981) baseStart_6171981 baseEnd_6171981 := by
    simpa [prefixWord, tailWord_6171981, baseEnd_6171981] using wordTrace_append hprefix tailTrace_6171981
  have hstable : (prefixWord ++ tailWord_6171981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6171981).length < 2 ^ (prefixWord ++ tailWord_6171981).sum := by decide
  have hdescent : baseEnd_6171981 < baseStart_6171981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6171981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172026 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2]
def baseStart_6172026 : Nat := 118140960795 + 6172026 * 2 ^ 59
def prefixEnd_6172026 : Nat := 4983230072969 + 3 ^ 40 * 6172026 * 2
def baseEnd_6172026 : Nat := 3169215950046974153590375

theorem tailTrace_6172026 : CollatzResearch.WordTrace tailWord_6172026 prefixEnd_6172026 3169215950046974153590375 := by
  unfold tailWord_6172026
  simp only [CollatzResearch.WordTrace]
  refine ⟨56278070484452843741217983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150074854625207583309914621 56278070484452843741217983)
  ·
    refine ⟨84417105726679265611826975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56278070484452843741217983 84417105726679265611826975)
    ·
      refine ⟨126625658590018898417740463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84417105726679265611826975 126625658590018898417740463)
      ·
        refine ⟨189938487885028347626610695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126625658590018898417740463 189938487885028347626610695)
        ·
          refine ⟨284907731827542521439916043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189938487885028347626610695 284907731827542521439916043)
          ·
            refine ⟨427361597741313782159874065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284907731827542521439916043 427361597741313782159874065)
            ·
              refine ⟨320521198305985336619905549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427361597741313782159874065 320521198305985336619905549)
              ·
                refine ⟨120195449364744501232464581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320521198305985336619905549 120195449364744501232464581)
                ·
                  refine ⟨22536646755889593981087109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120195449364744501232464581 22536646755889593981087109)
                  ·
                    refine ⟨4225621266729298871453833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22536646755889593981087109 4225621266729298871453833)
                    ·
                      refine ⟨3169215950046974153590375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225621266729298871453833 3169215950046974153590375)
                      ·
                        rfl

theorem cell23_6172026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_6172026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172026 prefixEnd_6172026 := by exact prefixLift 6172026
  have htrace : WordTrace (prefixWord ++ tailWord_6172026) baseStart_6172026 baseEnd_6172026 := by
    simpa [prefixWord, tailWord_6172026, baseEnd_6172026] using wordTrace_append hprefix tailTrace_6172026
  have hstable : (prefixWord ++ tailWord_6172026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172026).length < 2 ^ (prefixWord ++ tailWord_6172026).sum := by decide
  have hdescent : baseEnd_6172026 < baseStart_6172026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172029 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_6172029 : Nat := 118140960795 + 6172029 * 2 ^ 59
def prefixEnd_6172029 : Nat := 4983230072969 + 3 ^ 40 * 6172029 * 2
def baseEnd_6172029 : Nat := 3169217490488937641852861

theorem tailTrace_6172029 : CollatzResearch.WordTrace tailWord_6172029 prefixEnd_6172029 3169217490488937641852861 := by
  unfold tailWord_6172029
  simp only [CollatzResearch.WordTrace]
  refine ⟨225112391356800506477231141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150074927571200337651487427 225112391356800506477231141)
  ·
    refine ⟨42208573379400094964480839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225112391356800506477231141 42208573379400094964480839)
    ·
      refine ⟨63312860069100142446721259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42208573379400094964480839 63312860069100142446721259)
      ·
        refine ⟨94969290103650213670081889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63312860069100142446721259 94969290103650213670081889)
        ·
          refine ⟨71226967577737660252561417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94969290103650213670081889 71226967577737660252561417)
          ·
            refine ⟨53420225683303245189421063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71226967577737660252561417 53420225683303245189421063)
            ·
              refine ⟨80130338524954867784131595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53420225683303245189421063 80130338524954867784131595)
              ·
                refine ⟨120195507787432301676197393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80130338524954867784131595 120195507787432301676197393)
                ·
                  refine ⟨90146630840574226257148045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120195507787432301676197393 90146630840574226257148045)
                  ·
                    refine ⟨33804986565215334846430517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90146630840574226257148045 33804986565215334846430517)
                    ·
                      refine ⟨3169217490488937641852861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33804986565215334846430517 3169217490488937641852861)
                      ·
                        rfl

theorem cell23_6172029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_6172029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172029 prefixEnd_6172029 := by exact prefixLift 6172029
  have htrace : WordTrace (prefixWord ++ tailWord_6172029) baseStart_6172029 baseEnd_6172029 := by
    simpa [prefixWord, tailWord_6172029, baseEnd_6172029] using wordTrace_append hprefix tailTrace_6172029
  have hstable : (prefixWord ++ tailWord_6172029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172029).length < 2 ^ (prefixWord ++ tailWord_6172029).sum := by decide
  have hdescent : baseEnd_6172029 < baseStart_6172029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172063 : List Nat := [1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 3]
def baseStart_6172063 : Nat := 118140960795 + 6172063 * 2 ^ 59
def prefixEnd_6172063 : Nat := 4983230072969 + 3 ^ 40 * 6172063 * 2
def baseEnd_6172063 : Nat := 3169234948831190508827705

theorem tailTrace_6172063 : CollatzResearch.WordTrace tailWord_6172063 prefixEnd_6172063 3169234948831190508827705 := by
  unfold tailWord_6172063
  simp only [CollatzResearch.WordTrace]
  refine ⟨225113631438677330283968843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150075754292451553522645895 225113631438677330283968843)
  ·
    refine ⟨337670447158015995425953265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225113631438677330283968843 337670447158015995425953265)
    ·
      refine ⟨253252835368511996569464949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337670447158015995425953265 253252835368511996569464949)
      ·
        refine ⟨23742453315797999678387339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253252835368511996569464949 23742453315797999678387339)
        ·
          refine ⟨35613679973696999517581009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23742453315797999678387339 35613679973696999517581009)
          ·
            refine ⟨26710259980272749638185757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35613679973696999517581009 26710259980272749638185757)
            ·
              refine ⟨10016347492602281114319659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26710259980272749638185757 10016347492602281114319659)
              ·
                refine ⟨15024521238903421671479489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10016347492602281114319659 15024521238903421671479489)
                ·
                  refine ⟨11268390929177566253609617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15024521238903421671479489 11268390929177566253609617)
                  ·
                    refine ⟨8451293196883174690207213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11268390929177566253609617 8451293196883174690207213)
                    ·
                      refine ⟨3169234948831190508827705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451293196883174690207213 3169234948831190508827705)
                      ·
                        rfl

theorem cell23_6172063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_6172063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172063 prefixEnd_6172063 := by exact prefixLift 6172063
  have htrace : WordTrace (prefixWord ++ tailWord_6172063) baseStart_6172063 baseEnd_6172063 := by
    simpa [prefixWord, tailWord_6172063, baseEnd_6172063] using wordTrace_append hprefix tailTrace_6172063
  have hstable : (prefixWord ++ tailWord_6172063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172063).length < 2 ^ (prefixWord ++ tailWord_6172063).sum := by decide
  have hdescent : baseEnd_6172063 < baseStart_6172063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172100 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 6]
def baseStart_6172100 : Nat := 118140960795 + 6172100 * 2 ^ 59
def prefixEnd_6172100 : Nat := 4983230072969 + 3 ^ 40 * 6172100 * 2
def baseEnd_6172100 : Nat := 352139327512822984896115

theorem tailTrace_6172100 : CollatzResearch.WordTrace tailWord_6172100 prefixEnd_6172100 352139327512822984896115 := by
  unfold tailWord_6172100
  simp only [CollatzResearch.WordTrace]
  refine ⟨112557490469771642801532877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150076653959695523735377169 112557490469771642801532877)
  ·
    refine ⟨42209058926164366050574829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112557490469771642801532877 42209058926164366050574829)
    ·
      refine ⟨15828397097311637268965561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42209058926164366050574829 15828397097311637268965561)
      ·
        refine ⟨11871297822983727951724171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15828397097311637268965561 11871297822983727951724171)
        ·
          refine ⟨17806946734475591927586257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11871297822983727951724171 17806946734475591927586257)
          ·
            refine ⟨13355210050856693945689693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17806946734475591927586257 13355210050856693945689693)
            ·
              refine ⟨5008203769071260229633635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13355210050856693945689693 5008203769071260229633635)
              ·
                refine ⟨7512305653606890344450453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008203769071260229633635 7512305653606890344450453)
                ·
                  refine ⟨352139327512822984896115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7512305653606890344450453 352139327512822984896115)
                  ·
                    rfl

theorem cell23_6172100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_6172100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172100 prefixEnd_6172100 := by exact prefixLift 6172100
  have htrace : WordTrace (prefixWord ++ tailWord_6172100) baseStart_6172100 baseEnd_6172100 := by
    simpa [prefixWord, tailWord_6172100, baseEnd_6172100] using wordTrace_append hprefix tailTrace_6172100
  have hstable : (prefixWord ++ tailWord_6172100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172100).length < 2 ^ (prefixWord ++ tailWord_6172100).sum := by decide
  have hdescent : baseEnd_6172100 < baseStart_6172100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172170 : List Nat := [3, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_6172170 : Nat := 118140960795 + 6172170 * 2 ^ 59
def prefixEnd_6172170 : Nat := 4983230072969 + 3 ^ 40 * 6172170 * 2
def baseEnd_6172170 : Nat := 3169289891261221590189713

theorem tailTrace_6172170 : CollatzResearch.WordTrace tailWord_6172170 prefixEnd_6172170 3169289891261221590189713 := by
  unfold tailWord_6172170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56279383512322421889528491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150078356032859791705409309 56279383512322421889528491)
  ·
    refine ⟨84419075268483632834292737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56279383512322421889528491 84419075268483632834292737)
    ·
      refine ⟨63314306451362724625719553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84419075268483632834292737 63314306451362724625719553)
      ·
        refine ⟨47485729838522043469289665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63314306451362724625719553 47485729838522043469289665)
        ·
          refine ⟨35614297378891532601967249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47485729838522043469289665 35614297378891532601967249)
          ·
            refine ⟨26710723034168649451475437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35614297378891532601967249 26710723034168649451475437)
            ·
              refine ⟨10016521137813243544303289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26710723034168649451475437 10016521137813243544303289)
              ·
                refine ⟨7512390853359932658227467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10016521137813243544303289 7512390853359932658227467)
                ·
                  refine ⟨11268586280039898987341201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7512390853359932658227467 11268586280039898987341201)
                  ·
                    refine ⟨8451439710029924240505901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11268586280039898987341201 8451439710029924240505901)
                    ·
                      refine ⟨3169289891261221590189713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451439710029924240505901 3169289891261221590189713)
                      ·
                        rfl

theorem cell23_6172170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_6172170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172170 prefixEnd_6172170 := by exact prefixLift 6172170
  have htrace : WordTrace (prefixWord ++ tailWord_6172170) baseStart_6172170 baseEnd_6172170 := by
    simpa [prefixWord, tailWord_6172170, baseEnd_6172170] using wordTrace_append hprefix tailTrace_6172170
  have hstable : (prefixWord ++ tailWord_6172170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172170).length < 2 ^ (prefixWord ++ tailWord_6172170).sum := by decide
  have hdescent : baseEnd_6172170 < baseStart_6172170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172190 : List Nat := [4, 3, 3, 1, 12]
def baseStart_6172190 : Nat := 118140960795 + 6172190 * 2 ^ 59
def prefixEnd_6172190 : Nat := 4983230072969 + 3 ^ 40 * 6172190 * 2
def baseEnd_6172190 : Nat := 4347462497769974639149

theorem tailTrace_6172190 : CollatzResearch.WordTrace tailWord_6172190 prefixEnd_6172190 4347462497769974639149 := by
  unfold tailWord_6172190
  simp only [CollatzResearch.WordTrace]
  refine ⟨28139782938652153871730253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150078842339478153982561349 28139782938652153871730253)
  ·
    refine ⟨10552418601994557701898845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28139782938652153871730253 10552418601994557701898845)
    ·
      refine ⟨3957156975747959138212067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10552418601994557701898845 3957156975747959138212067)
      ·
        refine ⟨5935735463621938707318101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957156975747959138212067 5935735463621938707318101)
        ·
          refine ⟨4347462497769974639149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5935735463621938707318101 4347462497769974639149)
          ·
            rfl

theorem cell23_6172190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 12].length) (baseStart_6172190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172190 prefixEnd_6172190 := by exact prefixLift 6172190
  have htrace : WordTrace (prefixWord ++ tailWord_6172190) baseStart_6172190 baseEnd_6172190 := by
    simpa [prefixWord, tailWord_6172190, baseEnd_6172190] using wordTrace_append hprefix tailTrace_6172190
  have hstable : (prefixWord ++ tailWord_6172190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172190).length < 2 ^ (prefixWord ++ tailWord_6172190).sum := by decide
  have hdescent : baseEnd_6172190 < baseStart_6172190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172216 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 1, 8]
def baseStart_6172216 : Nat := 118140960795 + 6172216 * 2 ^ 59
def prefixEnd_6172216 : Nat := 4983230072969 + 3 ^ 40 * 6172216 * 2
def baseEnd_6172216 : Nat := 1056437837123776136738167

theorem tailTrace_6172216 : CollatzResearch.WordTrace tailWord_6172216 prefixEnd_6172216 1056437837123776136738167 := by
  unfold tailWord_6172216
  simp only [CollatzResearch.WordTrace]
  refine ⟨112559605903561518707144251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150079474538082024942859001 112559605903561518707144251)
  ·
    refine ⟨168839408855342278060716377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112559605903561518707144251 168839408855342278060716377)
    ·
      refine ⟨126629556641506708545537283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168839408855342278060716377 126629556641506708545537283)
      ·
        refine ⟨189944334962260062818305925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126629556641506708545537283 189944334962260062818305925)
        ·
          refine ⟨35614562805423761778432361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189944334962260062818305925 35614562805423761778432361)
          ·
            refine ⟨26710922104067821333824271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35614562805423761778432361 26710922104067821333824271)
            ·
              refine ⟨40066383156101732000736407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26710922104067821333824271 40066383156101732000736407)
              ·
                refine ⟨60099574734152598001104611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40066383156101732000736407 60099574734152598001104611)
                ·
                  refine ⟨90149362101228897001656917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60099574734152598001104611 90149362101228897001656917)
                  ·
                    refine ⟨1056437837123776136738167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90149362101228897001656917 1056437837123776136738167)
                    ·
                      rfl

theorem cell23_6172216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_6172216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172216 prefixEnd_6172216 := by exact prefixLift 6172216
  have htrace : WordTrace (prefixWord ++ tailWord_6172216) baseStart_6172216 baseEnd_6172216 := by
    simpa [prefixWord, tailWord_6172216, baseEnd_6172216] using wordTrace_append hprefix tailTrace_6172216
  have hstable : (prefixWord ++ tailWord_6172216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172216).length < 2 ^ (prefixWord ++ tailWord_6172216).sum := by decide
  have hdescent : baseEnd_6172216 < baseStart_6172216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172240 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 4, 2, 2]
def baseStart_6172240 : Nat := 118140960795 + 6172240 * 2 ^ 59
def prefixEnd_6172240 : Nat := 4983230072969 + 3 ^ 40 * 6172240 * 2
def baseEnd_6172240 : Nat := 3169325834907036316314391

theorem tailTrace_6172240 : CollatzResearch.WordTrace tailWord_6172240 prefixEnd_6172240 3169325834907036316314391 := by
  unfold tailWord_6172240
  simp only [CollatzResearch.WordTrace]
  refine ⟨112560043579518044756581087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150080058106024059675441449 112560043579518044756581087)
  ·
    refine ⟨168840065369277067134871631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112560043579518044756581087 168840065369277067134871631)
    ·
      refine ⟨253260098053915600702307447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168840065369277067134871631 253260098053915600702307447)
      ·
        refine ⟨379890147080873401053461171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253260098053915600702307447 379890147080873401053461171)
        ·
          refine ⟨569835220621310101580191757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379890147080873401053461171 569835220621310101580191757)
          ·
            refine ⟨213688207732991288092571909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 569835220621310101580191757 213688207732991288092571909)
            ·
              refine ⟨40066538949935866517357233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 213688207732991288092571909 40066538949935866517357233)
              ·
                refine ⟨30049904212451899888017925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40066538949935866517357233 30049904212451899888017925)
                ·
                  refine ⟨5634357039834731229003361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30049904212451899888017925 5634357039834731229003361)
                  ·
                    refine ⟨4225767779876048421752521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5634357039834731229003361 4225767779876048421752521)
                    ·
                      refine ⟨3169325834907036316314391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225767779876048421752521 3169325834907036316314391)
                      ·
                        rfl

theorem cell23_6172240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4, 2, 2].length) (baseStart_6172240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172240 prefixEnd_6172240 := by exact prefixLift 6172240
  have htrace : WordTrace (prefixWord ++ tailWord_6172240) baseStart_6172240 baseEnd_6172240 := by
    simpa [prefixWord, tailWord_6172240, baseEnd_6172240] using wordTrace_append hprefix tailTrace_6172240
  have hstable : (prefixWord ++ tailWord_6172240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172240).length < 2 ^ (prefixWord ++ tailWord_6172240).sum := by decide
  have hdescent : baseEnd_6172240 < baseStart_6172240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172293 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_6172293 : Nat := 118140960795 + 6172293 * 2 ^ 59
def prefixEnd_6172293 : Nat := 4983230072969 + 3 ^ 40 * 6172293 * 2
def baseEnd_6172293 : Nat := 1056451016460574869650549

theorem tailTrace_6172293 : CollatzResearch.WordTrace tailWord_6172293 prefixEnd_6172293 1056451016460574869650549 := by
  unfold tailWord_6172293
  simp only [CollatzResearch.WordTrace]
  refine ⟨225122020227844079564841533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150081346818562719709894355 225122020227844079564841533)
  ·
    refine ⟨84420757585441529836815575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225122020227844079564841533 84420757585441529836815575)
    ·
      refine ⟨126631136378162294755223363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84420757585441529836815575 126631136378162294755223363)
      ·
        refine ⟨189946704567243442132835045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126631136378162294755223363 189946704567243442132835045)
        ·
          refine ⟨35615007106358145399906571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189946704567243442132835045 35615007106358145399906571)
          ·
            refine ⟨53422510659537218099859857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35615007106358145399906571 53422510659537218099859857)
            ·
              refine ⟨40066882994652913574894893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53422510659537218099859857 40066882994652913574894893)
              ·
                refine ⟨15025081122994842590585585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40066882994652913574894893 15025081122994842590585585)
                ·
                  refine ⟨11268810842246131942939189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15025081122994842590585585 11268810842246131942939189)
                  ·
                    refine ⟨1056451016460574869650549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11268810842246131942939189 1056451016460574869650549)
                    ·
                      rfl

theorem cell23_6172293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_6172293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172293 prefixEnd_6172293 := by exact prefixLift 6172293
  have htrace : WordTrace (prefixWord ++ tailWord_6172293) baseStart_6172293 baseEnd_6172293 := by
    simpa [prefixWord, tailWord_6172293, baseEnd_6172293] using wordTrace_append hprefix tailTrace_6172293
  have hstable : (prefixWord ++ tailWord_6172293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172293).length < 2 ^ (prefixWord ++ tailWord_6172293).sum := by decide
  have hdescent : baseEnd_6172293 < baseStart_6172293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172370 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 6]
def baseStart_6172370 : Nat := 118140960795 + 6172370 * 2 ^ 59
def prefixEnd_6172370 : Nat := 4983230072969 + 3 ^ 40 * 6172370 * 2
def baseEnd_6172370 : Nat := 352154731932457867520977

theorem tailTrace_6172370 : CollatzResearch.WordTrace tailWord_6172370 prefixEnd_6172370 352154731932457867520977 := by
  unfold tailWord_6172370
  simp only [CollatzResearch.WordTrace]
  refine ⟨56281207162141280428848641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150083219099043414476929709 56281207162141280428848641)
  ·
    refine ⟨42210905371605960321636481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56281207162141280428848641 42210905371605960321636481)
    ·
      refine ⟨31658179028704470241227361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42210905371605960321636481 31658179028704470241227361)
      ·
        refine ⟨23743634271528352680920521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31658179028704470241227361 23743634271528352680920521)
        ·
          refine ⟨17807725703646264510690391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23743634271528352680920521 17807725703646264510690391)
          ·
            refine ⟨26711588555469396766035587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17807725703646264510690391 26711588555469396766035587)
            ·
              refine ⟨40067382833204095149053381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26711588555469396766035587 40067382833204095149053381)
              ·
                refine ⟨7512634281225767840447509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40067382833204095149053381 7512634281225767840447509)
                ·
                  refine ⟨352154731932457867520977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7512634281225767840447509 352154731932457867520977)
                  ·
                    rfl

theorem cell23_6172370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_6172370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172370 prefixEnd_6172370 := by exact prefixLift 6172370
  have htrace : WordTrace (prefixWord ++ tailWord_6172370) baseStart_6172370 baseEnd_6172370 := by
    simpa [prefixWord, tailWord_6172370, baseEnd_6172370] using wordTrace_append hprefix tailTrace_6172370
  have hstable : (prefixWord ++ tailWord_6172370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172370).length < 2 ^ (prefixWord ++ tailWord_6172370).sum := by decide
  have hdescent : baseEnd_6172370 < baseStart_6172370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172383 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 5, 5]
def baseStart_6172383 : Nat := 118140960795 + 6172383 * 2 ^ 59
def prefixEnd_6172383 : Nat := 4983230072969 + 3 ^ 40 * 6172383 * 2
def baseEnd_6172383 : Nat := 1056466420880209752275411

theorem tailTrace_6172383 : CollatzResearch.WordTrace tailWord_6172383 prefixEnd_6172383 1056466420880209752275411 := by
  unfold tailWord_6172383
  simp only [CollatzResearch.WordTrace]
  refine ⟨225125302797518024935617803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150083535198345349957078535 225125302797518024935617803)
  ·
    refine ⟨337687954196277037403426705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225125302797518024935617803 337687954196277037403426705)
    ·
      refine ⟨253265965647207778052570029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337687954196277037403426705 253265965647207778052570029)
      ·
        refine ⟨94974737117702916769713761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253265965647207778052570029 94974737117702916769713761)
        ·
          refine ⟨71231052838277187577285321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94974737117702916769713761 71231052838277187577285321)
          ·
            refine ⟨53423289628707890682963991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71231052838277187577285321 53423289628707890682963991)
            ·
              refine ⟨80134934443061836024445987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53423289628707890682963991 80134934443061836024445987)
              ·
                refine ⟨120202401664592754036668981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80134934443061836024445987 120202401664592754036668981)
                ·
                  refine ⟨11268975156055570690937717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120202401664592754036668981 11268975156055570690937717)
                  ·
                    refine ⟨1056466420880209752275411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11268975156055570690937717 1056466420880209752275411)
                    ·
                      rfl

theorem cell23_6172383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_6172383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172383 prefixEnd_6172383 := by exact prefixLift 6172383
  have htrace : WordTrace (prefixWord ++ tailWord_6172383) baseStart_6172383 baseEnd_6172383 := by
    simpa [prefixWord, tailWord_6172383, baseEnd_6172383] using wordTrace_append hprefix tailTrace_6172383
  have hstable : (prefixWord ++ tailWord_6172383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172383).length < 2 ^ (prefixWord ++ tailWord_6172383).sum := by decide
  have hdescent : baseEnd_6172383 < baseStart_6172383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172397 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6172397 : Nat := 118140960795 + 6172397 * 2 ^ 59
def prefixEnd_6172397 : Nat := 4983230072969 + 3 ^ 40 * 6172397 * 2
def baseEnd_6172397 : Nat := 3169406451369792202051169

theorem tailTrace_6172397 : CollatzResearch.WordTrace tailWord_6172397 prefixEnd_6172397 3169406451369792202051169 := by
  unfold tailWord_6172397
  simp only [CollatzResearch.WordTrace]
  refine ⟨225125813419467305326627445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150083875612978203551084963 225125813419467305326627445)
  ·
    refine ⟨21105545008075059874371323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225125813419467305326627445 21105545008075059874371323)
    ·
      refine ⟨31658317512112589811556985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21105545008075059874371323 31658317512112589811556985)
      ·
        refine ⟨23743738134084442358667739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31658317512112589811556985 23743738134084442358667739)
        ·
          refine ⟨35615607201126663538001609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23743738134084442358667739 35615607201126663538001609)
          ·
            refine ⟨26711705400844997653501207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35615607201126663538001609 26711705400844997653501207)
            ·
              refine ⟨40067558101267496480251811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26711705400844997653501207 40067558101267496480251811)
              ·
                refine ⟨60101337151901244720377717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40067558101267496480251811 60101337151901244720377717)
                ·
                  refine ⟨5634500357990741692535411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60101337151901244720377717 5634500357990741692535411)
                  ·
                    refine ⟨8451750536986112538803117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5634500357990741692535411 8451750536986112538803117)
                    ·
                      refine ⟨3169406451369792202051169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451750536986112538803117 3169406451369792202051169)
                      ·
                        rfl

theorem cell23_6172397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6172397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172397 prefixEnd_6172397 := by exact prefixLift 6172397
  have htrace : WordTrace (prefixWord ++ tailWord_6172397) baseStart_6172397 baseEnd_6172397 := by
    simpa [prefixWord, tailWord_6172397, baseEnd_6172397] using wordTrace_append hprefix tailTrace_6172397
  have hstable : (prefixWord ++ tailWord_6172397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172397).length < 2 ^ (prefixWord ++ tailWord_6172397).sum := by decide
  have hdescent : baseEnd_6172397 < baseStart_6172397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172407 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 2, 3, 2]
def baseStart_6172407 : Nat := 118140960795 + 6172407 * 2 ^ 59
def prefixEnd_6172407 : Nat := 4983230072969 + 3 ^ 40 * 6172407 * 2
def baseEnd_6172407 : Nat := 3169411586176337162926123

theorem tailTrace_6172407 : CollatzResearch.WordTrace tailWord_6172407 prefixEnd_6172407 3169411586176337162926123 := by
  unfold tailWord_6172407
  simp only [CollatzResearch.WordTrace]
  refine ⟨225126178149431077034491475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150084118766287384689660983 225126178149431077034491475)
  ·
    refine ⟨337689267224146615551737213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225126178149431077034491475 337689267224146615551737213)
    ·
      refine ⟨126633475209054980831901455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337689267224146615551737213 126633475209054980831901455)
      ·
        refine ⟨189950212813582471247852183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126633475209054980831901455 189950212813582471247852183)
        ·
          refine ⟨284925319220373706871778275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189950212813582471247852183 284925319220373706871778275)
          ·
            refine ⟨427387978830560560307667413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284925319220373706871778275 427387978830560560307667413)
            ·
              refine ⟨10016905753841263132210955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 427387978830560560307667413 10016905753841263132210955)
              ·
                refine ⟨15025358630761894698316433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10016905753841263132210955 15025358630761894698316433)
                ·
                  refine ⟨11269018973071421023737325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15025358630761894698316433 11269018973071421023737325)
                  ·
                    refine ⟨4225882114901782883901497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11269018973071421023737325 4225882114901782883901497)
                    ·
                      refine ⟨3169411586176337162926123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225882114901782883901497 3169411586176337162926123)
                      ·
                        rfl

theorem cell23_6172407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_6172407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172407 prefixEnd_6172407 := by exact prefixLift 6172407
  have htrace : WordTrace (prefixWord ++ tailWord_6172407) baseStart_6172407 baseEnd_6172407 := by
    simpa [prefixWord, tailWord_6172407, baseEnd_6172407] using wordTrace_append hprefix tailTrace_6172407
  have hstable : (prefixWord ++ tailWord_6172407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172407).length < 2 ^ (prefixWord ++ tailWord_6172407).sum := by decide
  have hdescent : baseEnd_6172407 < baseStart_6172407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172413 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_6172413 : Nat := 118140960795 + 6172413 * 2 ^ 59
def prefixEnd_6172413 : Nat := 4983230072969 + 3 ^ 40 * 6172413 * 2
def baseEnd_6172413 : Nat := 1056471555686754713150365

theorem tailTrace_6172413 : CollatzResearch.WordTrace tailWord_6172413 prefixEnd_6172413 1056471555686754713150365 := by
  unfold tailWord_6172413
  simp only [CollatzResearch.WordTrace]
  refine ⟨225126396987409340059209893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150084264658272893372806595 225126396987409340059209893)
  ·
    refine ⟨42211199435139251261101855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225126396987409340059209893 42211199435139251261101855)
    ·
      refine ⟨63316799152708876891652783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42211199435139251261101855 63316799152708876891652783)
      ·
        refine ⟨94975198729063315337479175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63316799152708876891652783 94975198729063315337479175)
        ·
          refine ⟨142462798093594973006218763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94975198729063315337479175 142462798093594973006218763)
          ·
            refine ⟨213694197140392459509328145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142462798093594973006218763 213694197140392459509328145)
            ·
              refine ⟨160270647855294344631996109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213694197140392459509328145 160270647855294344631996109)
              ·
                refine ⟨60101492945735379236998541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160270647855294344631996109 60101492945735379236998541)
                ·
                  refine ⟨22538059854650767213874453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60101492945735379236998541 22538059854650767213874453)
                  ·
                    refine ⟨1056471555686754713150365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22538059854650767213874453 1056471555686754713150365)
                    ·
                      rfl

theorem cell23_6172413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_6172413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172413 prefixEnd_6172413 := by exact prefixLift 6172413
  have htrace : WordTrace (prefixWord ++ tailWord_6172413) baseStart_6172413 baseEnd_6172413 := by
    simpa [prefixWord, tailWord_6172413, baseEnd_6172413] using wordTrace_append hprefix tailTrace_6172413
  have hstable : (prefixWord ++ tailWord_6172413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172413).length < 2 ^ (prefixWord ++ tailWord_6172413).sum := by decide
  have hdescent : baseEnd_6172413 < baseStart_6172413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172417 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 1, 5]
def baseStart_6172417 : Nat := 118140960795 + 6172417 * 2 ^ 59
def prefixEnd_6172417 : Nat := 4983230072969 + 3 ^ 40 * 6172417 * 2
def baseEnd_6172417 : Nat := 1056472240327627374600359

theorem tailTrace_6172417 : CollatzResearch.WordTrace tailWord_6172417 prefixEnd_6172417 1056472240327627374600359 := by
  unfold tailWord_6172417
  simp only [CollatzResearch.WordTrace]
  refine ⟨225126542879394848742355505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150084361919596565828237003 225126542879394848742355505)
  ·
    refine ⟨168844907159546136556766629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225126542879394848742355505 168844907159546136556766629)
    ·
      refine ⟨31658420092414900604393743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168844907159546136556766629 31658420092414900604393743)
      ·
        refine ⟨47487630138622350906590615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31658420092414900604393743 47487630138622350906590615)
        ·
          refine ⟨71231445207933526359885923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47487630138622350906590615 71231445207933526359885923)
          ·
            refine ⟨106847167811900289539828885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71231445207933526359885923 106847167811900289539828885)
            ·
              refine ⟨5008460991182826072179479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106847167811900289539828885 5008460991182826072179479)
              ·
                refine ⟨7512691486774239108269219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008460991182826072179479 7512691486774239108269219)
                ·
                  refine ⟨11269037230161358662403829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7512691486774239108269219 11269037230161358662403829)
                  ·
                    refine ⟨1056472240327627374600359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11269037230161358662403829 1056472240327627374600359)
                    ·
                      rfl

theorem cell23_6172417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_6172417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172417 prefixEnd_6172417 := by exact prefixLift 6172417
  have htrace : WordTrace (prefixWord ++ tailWord_6172417) baseStart_6172417 baseEnd_6172417 := by
    simpa [prefixWord, tailWord_6172417, baseEnd_6172417] using wordTrace_append hprefix tailTrace_6172417
  have hstable : (prefixWord ++ tailWord_6172417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172417).length < 2 ^ (prefixWord ++ tailWord_6172417).sum := by decide
  have hdescent : baseEnd_6172417 < baseStart_6172417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172433 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_6172433 : Nat := 118140960795 + 6172433 * 2 ^ 59
def prefixEnd_6172433 : Nat := 4983230072969 + 3 ^ 40 * 6172433 * 2
def baseEnd_6172433 : Nat := 3169424936673354061201003

theorem tailTrace_6172433 : CollatzResearch.WordTrace tailWord_6172433 prefixEnd_6172433 3169424936673354061201003 := by
  unfold tailWord_6172433
  simp only [CollatzResearch.WordTrace]
  refine ⟨225127126447336883474937953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150084750964891255649958635 225127126447336883474937953)
  ·
    refine ⟨168845344835502662606203465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225127126447336883474937953 168845344835502662606203465)
    ·
      refine ⟨126634008626626996954652599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168845344835502662606203465 126634008626626996954652599)
      ·
        refine ⟨189951012939940495431978899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126634008626626996954652599 189951012939940495431978899)
        ·
          refine ⟨284926519409910743147968349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189951012939940495431978899 284926519409910743147968349)
          ·
            refine ⟨106847444778716528680488131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 284926519409910743147968349 106847444778716528680488131)
            ·
              refine ⟨160271167168074793020732197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106847444778716528680488131 160271167168074793020732197)
              ·
                refine ⟨30050843844014023691387287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160271167168074793020732197 30050843844014023691387287)
                ·
                  refine ⟨45076265766021035537080931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30050843844014023691387287 45076265766021035537080931)
                  ·
                    refine ⟨67614398649031553305621397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45076265766021035537080931 67614398649031553305621397)
                    ·
                      refine ⟨3169424936673354061201003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67614398649031553305621397 3169424936673354061201003)
                      ·
                        rfl

theorem cell23_6172433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_6172433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172433 prefixEnd_6172433 := by exact prefixLift 6172433
  have htrace : WordTrace (prefixWord ++ tailWord_6172433) baseStart_6172433 baseEnd_6172433 := by
    simpa [prefixWord, tailWord_6172433, baseEnd_6172433] using wordTrace_append hprefix tailTrace_6172433
  have hstable : (prefixWord ++ tailWord_6172433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172433).length < 2 ^ (prefixWord ++ tailWord_6172433).sum := by decide
  have hdescent : baseEnd_6172433 < baseStart_6172433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172440 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_6172440 : Nat := 118140960795 + 6172440 * 2 ^ 59
def prefixEnd_6172440 : Nat := 4983230072969 + 3 ^ 40 * 6172440 * 2
def baseEnd_6172440 : Nat := 3169428531037935533813471

theorem tailTrace_6172440 : CollatzResearch.WordTrace tailWord_6172440 prefixEnd_6172440 3169428531037935533813471 := by
  unfold tailWord_6172440
  simp only [CollatzResearch.WordTrace]
  refine ⟨112563690879155761835221387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150084921172207682446961849 112563690879155761835221387)
  ·
    refine ⟨168845536318733642752832081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112563690879155761835221387 168845536318733642752832081)
    ·
      refine ⟨126634152239050232064624061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168845536318733642752832081 126634152239050232064624061)
      ·
        refine ⟨47487807089643837024234023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126634152239050232064624061 47487807089643837024234023)
        ·
          refine ⟨71231710634465755536351035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47487807089643837024234023 71231710634465755536351035)
          ·
            refine ⟨106847565951698633304526553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71231710634465755536351035 106847565951698633304526553)
            ·
              refine ⟨80135674463773974978394915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106847565951698633304526553 80135674463773974978394915)
              ·
                refine ⟨120203511695660962467592373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80135674463773974978394915 120203511695660962467592373)
                ·
                  refine ⟨11269079221468215231336785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120203511695660962467592373 11269079221468215231336785)
                  ·
                    refine ⟨8451809416101161423502589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11269079221468215231336785 8451809416101161423502589)
                    ·
                      refine ⟨3169428531037935533813471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451809416101161423502589 3169428531037935533813471)
                      ·
                        rfl

theorem cell23_6172440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_6172440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172440 prefixEnd_6172440 := by exact prefixLift 6172440
  have htrace : WordTrace (prefixWord ++ tailWord_6172440) baseStart_6172440 baseEnd_6172440 := by
    simpa [prefixWord, tailWord_6172440, baseEnd_6172440] using wordTrace_append hprefix tailTrace_6172440
  have hstable : (prefixWord ++ tailWord_6172440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172440).length < 2 ^ (prefixWord ++ tailWord_6172440).sum := by decide
  have hdescent : baseEnd_6172440 < baseStart_6172440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172450 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_6172450 : Nat := 118140960795 + 6172450 * 2 ^ 59
def prefixEnd_6172450 : Nat := 4983230072969 + 3 ^ 40 * 6172450 * 2
def baseEnd_6172450 : Nat := 3169433665844480494688425

theorem tailTrace_6172450 : CollatzResearch.WordTrace tailWord_6172450 prefixEnd_6172450 3169433665844480494688425 := by
  unfold tailWord_6172450
  simp only [CollatzResearch.WordTrace]
  refine ⟨56281936622068823844576701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150085164325516863585537869 56281936622068823844576701)
  ·
    refine ⟨21105726233275808941716263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56281936622068823844576701 21105726233275808941716263)
    ·
      refine ⟨31658589349913713412574395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21105726233275808941716263 31658589349913713412574395)
      ·
        refine ⟨47487884024870570118861593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31658589349913713412574395 47487884024870570118861593)
        ·
          refine ⟨35615913018652927589146195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47487884024870570118861593 35615913018652927589146195)
          ·
            refine ⟨53423869527979391383719293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35615913018652927589146195 53423869527979391383719293)
            ·
              refine ⟨20033951072992271768894735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53423869527979391383719293 20033951072992271768894735)
              ·
                refine ⟨30050926609488407653342103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20033951072992271768894735 30050926609488407653342103)
                ·
                  refine ⟨45076389914232611480013155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30050926609488407653342103 45076389914232611480013155)
                  ·
                    refine ⟨67614584871348917220019733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45076389914232611480013155 67614584871348917220019733)
                    ·
                      refine ⟨3169433665844480494688425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67614584871348917220019733 3169433665844480494688425)
                      ·
                        rfl

theorem cell23_6172450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_6172450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172450 prefixEnd_6172450 := by exact prefixLift 6172450
  have htrace : WordTrace (prefixWord ++ tailWord_6172450) baseStart_6172450 baseEnd_6172450 := by
    simpa [prefixWord, tailWord_6172450, baseEnd_6172450] using wordTrace_append hprefix tailTrace_6172450
  have hstable : (prefixWord ++ tailWord_6172450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172450).length < 2 ^ (prefixWord ++ tailWord_6172450).sum := by decide
  have hdescent : baseEnd_6172450 < baseStart_6172450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172460 : List Nat := [2, 2, 1, 1, 1, 5, 4, 7]
def baseStart_6172460 : Nat := 118140960795 + 6172460 * 2 ^ 59
def prefixEnd_6172460 : Nat := 4983230072969 + 3 ^ 40 * 6172460 * 2
def baseEnd_6172460 : Nat := 117386622246334276131977

theorem tailTrace_6172460 : CollatzResearch.WordTrace tailWord_6172460 prefixEnd_6172460 117386622246334276131977 := by
  unfold tailWord_6172460
  simp only [CollatzResearch.WordTrace]
  refine ⟨112564055609119533543085417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150085407478826044724113889 112564055609119533543085417)
  ·
    refine ⟨84423041706839650157314063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112564055609119533543085417 84423041706839650157314063)
    ·
      refine ⟨126634562560259475235971095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84423041706839650157314063 126634562560259475235971095)
      ·
        refine ⟨189951843840389212853956643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126634562560259475235971095 189951843840389212853956643)
        ·
          refine ⟨284927765760583819280934965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189951843840389212853956643 284927765760583819280934965)
          ·
            refine ⟨26711978040054733057587653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 284927765760583819280934965 26711978040054733057587653)
            ·
              refine ⟨5008495882510262448297685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26711978040054733057587653 5008495882510262448297685)
              ·
                refine ⟨117386622246334276131977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5008495882510262448297685 117386622246334276131977)
                ·
                  rfl

theorem cell23_6172460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 7].length) (baseStart_6172460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172460 prefixEnd_6172460 := by exact prefixLift 6172460
  have htrace : WordTrace (prefixWord ++ tailWord_6172460) baseStart_6172460 baseEnd_6172460 := by
    simpa [prefixWord, tailWord_6172460, baseEnd_6172460] using wordTrace_append hprefix tailTrace_6172460
  have hstable : (prefixWord ++ tailWord_6172460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172460).length < 2 ^ (prefixWord ++ tailWord_6172460).sum := by decide
  have hdescent : baseEnd_6172460 < baseStart_6172460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172487 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_6172487 : Nat := 118140960795 + 6172487 * 2 ^ 59
def prefixEnd_6172487 : Nat := 4983230072969 + 3 ^ 40 * 6172487 * 2
def baseEnd_6172487 : Nat := 3169452664628696849925755

theorem tailTrace_6172487 : CollatzResearch.WordTrace tailWord_6172487 prefixEnd_6172487 3169452664628696849925755 := by
  unfold tailWord_6172487
  simp only [CollatzResearch.WordTrace]
  refine ⟨225129095989141250697403715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150086063992760833798269143 225129095989141250697403715)
  ·
    refine ⟨337693643983711876046105573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225129095989141250697403715 337693643983711876046105573)
    ·
      refine ⟨63317558246945976758644795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337693643983711876046105573 63317558246945976758644795)
      ·
        refine ⟨94976337370418965137967193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63317558246945976758644795 94976337370418965137967193)
        ·
          refine ⟨71232253027814223853475395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94976337370418965137967193 71232253027814223853475395)
          ·
            refine ⟨106848379541721335780213093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71232253027814223853475395 106848379541721335780213093)
            ·
              refine ⟨20034071164072750458789955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106848379541721335780213093 20034071164072750458789955)
              ·
                refine ⟨30051106746109125688184933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20034071164072750458789955 30051106746109125688184933)
                ·
                  refine ⟨5634582514895461066534675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30051106746109125688184933 5634582514895461066534675)
                  ·
                    refine ⟨8451873772343191599802013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5634582514895461066534675 8451873772343191599802013)
                    ·
                      refine ⟨3169452664628696849925755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451873772343191599802013 3169452664628696849925755)
                      ·
                        rfl

theorem cell23_6172487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_6172487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172487 prefixEnd_6172487 := by exact prefixLift 6172487
  have htrace : WordTrace (prefixWord ++ tailWord_6172487) baseStart_6172487 baseEnd_6172487 := by
    simpa [prefixWord, tailWord_6172487, baseEnd_6172487] using wordTrace_append hprefix tailTrace_6172487
  have hstable : (prefixWord ++ tailWord_6172487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172487).length < 2 ^ (prefixWord ++ tailWord_6172487).sum := by decide
  have hdescent : baseEnd_6172487 < baseStart_6172487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172488 : List Nat := [2, 1, 3, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_6172488 : Nat := 118140960795 + 6172488 * 2 ^ 59
def prefixEnd_6172488 : Nat := 4983230072969 + 3 ^ 40 * 6172488 * 2
def baseEnd_6172488 : Nat := 3169453178109351346013251

theorem tailTrace_6172488 : CollatzResearch.WordTrace tailWord_6172488 prefixEnd_6172488 3169453178109351346013251 := by
  unfold tailWord_6172488
  simp only [CollatzResearch.WordTrace]
  refine ⟨112564566231068813934095059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150086088308091751912126745 112564566231068813934095059)
  ·
    refine ⟨168846849346603220901142589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112564566231068813934095059 168846849346603220901142589)
    ·
      refine ⟨63317568504976207837928471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168846849346603220901142589 63317568504976207837928471)
      ·
        refine ⟨94976352757464311756892707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63317568504976207837928471 94976352757464311756892707)
        ·
          refine ⟨142464529136196467635339061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94976352757464311756892707 142464529136196467635339061)
          ·
            refine ⟨13356049606518418840813037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142464529136196467635339061 13356049606518418840813037)
            ·
              refine ⟨5008518602444407065304889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13356049606518418840813037 5008518602444407065304889)
              ·
                refine ⟨3756388951833305298978667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008518602444407065304889 3756388951833305298978667)
                ·
                  refine ⟨5634583427749957948468001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3756388951833305298978667 5634583427749957948468001)
                  ·
                    refine ⟨4225937570812468461351001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5634583427749957948468001 4225937570812468461351001)
                    ·
                      refine ⟨3169453178109351346013251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4225937570812468461351001 3169453178109351346013251)
                      ·
                        rfl

theorem cell23_6172488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_6172488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172488 prefixEnd_6172488 := by exact prefixLift 6172488
  have htrace : WordTrace (prefixWord ++ tailWord_6172488) baseStart_6172488 baseEnd_6172488 := by
    simpa [prefixWord, tailWord_6172488, baseEnd_6172488] using wordTrace_append hprefix tailTrace_6172488
  have hstable : (prefixWord ++ tailWord_6172488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172488).length < 2 ^ (prefixWord ++ tailWord_6172488).sum := by decide
  have hdescent : baseEnd_6172488 < baseStart_6172488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172508 : List Nat := [2, 2, 4, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6172508 : Nat := 118140960795 + 6172508 * 2 ^ 59
def prefixEnd_6172508 : Nat := 4983230072969 + 3 ^ 40 * 6172508 * 2
def baseEnd_6172508 : Nat := 3169463447722441267763159

theorem tailTrace_6172508 : CollatzResearch.WordTrace tailWord_6172508 prefixEnd_6172508 3169463447722441267763159 := by
  unfold tailWord_6172508
  simp only [CollatzResearch.WordTrace]
  refine ⟨112564930961032585641959089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150086574614710114189278785 112564930961032585641959089)
  ·
    refine ⟨84423698220774439231469317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112564930961032585641959089 84423698220774439231469317)
    ·
      refine ⟨15829443416395207355900497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84423698220774439231469317 15829443416395207355900497)
      ·
        refine ⟨11872082562296405516925373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15829443416395207355900497 11872082562296405516925373)
        ·
          refine ⟨4452030960861152068847015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11872082562296405516925373 4452030960861152068847015)
          ·
            refine ⟨6678046441291728103270523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452030960861152068847015 6678046441291728103270523)
            ·
              refine ⟨10017069661937592154905785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678046441291728103270523 10017069661937592154905785)
              ·
                refine ⟨7512802246453194116179339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10017069661937592154905785 7512802246453194116179339)
                ·
                  refine ⟨11269203369679791174269009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7512802246453194116179339 11269203369679791174269009)
                  ·
                    refine ⟨8451902527259843380701757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11269203369679791174269009 8451902527259843380701757)
                    ·
                      refine ⟨3169463447722441267763159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451902527259843380701757 3169463447722441267763159)
                      ·
                        rfl

theorem cell23_6172508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6172508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172508 prefixEnd_6172508 := by exact prefixLift 6172508
  have htrace : WordTrace (prefixWord ++ tailWord_6172508) baseStart_6172508 baseEnd_6172508 := by
    simpa [prefixWord, tailWord_6172508, baseEnd_6172508] using wordTrace_append hprefix tailTrace_6172508
  have hstable : (prefixWord ++ tailWord_6172508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172508).length < 2 ^ (prefixWord ++ tailWord_6172508).sum := by decide
  have hdescent : baseEnd_6172508 < baseStart_6172508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172560 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3]
def baseStart_6172560 : Nat := 118140960795 + 6172560 * 2 ^ 59
def prefixEnd_6172560 : Nat := 4983230072969 + 3 ^ 40 * 6172560 * 2
def baseEnd_6172560 : Nat := 3169490148716475064312919

theorem tailTrace_6172560 : CollatzResearch.WordTrace tailWord_6172560 prefixEnd_6172560 3169490148716475064312919 := by
  unfold tailWord_6172560
  simp only [CollatzResearch.WordTrace]
  refine ⟨112565879258938392082405567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150087839011917856109874089 112565879258938392082405567)
  ·
    refine ⟨168848818888407588123608351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112565879258938392082405567 168848818888407588123608351)
    ·
      refine ⟨253273228332611382185412527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168848818888407588123608351 253273228332611382185412527)
      ·
        refine ⟨379909842498917073278118791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253273228332611382185412527 379909842498917073278118791)
        ·
          refine ⟨569864763748375609917178187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379909842498917073278118791 569864763748375609917178187)
          ·
            refine ⟨854797145622563414875767281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569864763748375609917178187 854797145622563414875767281)
            ·
              refine ⟨641097859216922561156825461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854797145622563414875767281 641097859216922561156825461)
              ·
                refine ⟨60102924301586490108452387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 641097859216922561156825461 60102924301586490108452387)
                ·
                  refine ⟨90154386452379735162678581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60102924301586490108452387 90154386452379735162678581)
                  ·
                    refine ⟨8451973729910600171501117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90154386452379735162678581 8451973729910600171501117)
                    ·
                      refine ⟨3169490148716475064312919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8451973729910600171501117 3169490148716475064312919)
                      ·
                        rfl

theorem cell23_6172560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_6172560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172560 prefixEnd_6172560 := by exact prefixLift 6172560
  have htrace : WordTrace (prefixWord ++ tailWord_6172560) baseStart_6172560 baseEnd_6172560 := by
    simpa [prefixWord, tailWord_6172560, baseEnd_6172560] using wordTrace_append hprefix tailTrace_6172560
  have hstable : (prefixWord ++ tailWord_6172560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172560).length < 2 ^ (prefixWord ++ tailWord_6172560).sum := by decide
  have hdescent : baseEnd_6172560 < baseStart_6172560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172654 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_6172654 : Nat := 118140960795 + 6172654 * 2 ^ 59
def prefixEnd_6172654 : Nat := 4983230072969 + 3 ^ 40 * 6172654 * 2
def baseEnd_6172654 : Nat := 3169538415897997696537487

theorem tailTrace_6172654 : CollatzResearch.WordTrace tailWord_6172654 prefixEnd_6172654 3169538415897997696537487 := by
  unfold tailWord_6172654
  simp only [CollatzResearch.WordTrace]
  refine ⟨28141898372442029777341627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150090124653024158812488677 28141898372442029777341627)
  ·
    refine ⟨42212847558663044666012441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28141898372442029777341627 42212847558663044666012441)
    ·
      refine ⟨31659635668997283499509331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42212847558663044666012441 31659635668997283499509331)
      ·
        refine ⟨47489453503495925249263997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31659635668997283499509331 47489453503495925249263997)
        ·
          refine ⟨17808545063810971968473999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47489453503495925249263997 17808545063810971968473999)
          ·
            refine ⟨26712817595716457952710999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17808545063810971968473999 26712817595716457952710999)
            ·
              refine ⟨40069226393574686929066499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26712817595716457952710999 40069226393574686929066499)
              ·
                refine ⟨60103839590362030393599749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40069226393574686929066499 60103839590362030393599749)
                ·
                  refine ⟨11269469923192880698799953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60103839590362030393599749 11269469923192880698799953)
                  ·
                    refine ⟨8452102442394660524099965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11269469923192880698799953 8452102442394660524099965)
                    ·
                      refine ⟨3169538415897997696537487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8452102442394660524099965 3169538415897997696537487)
                      ·
                        rfl

theorem cell23_6172654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_6172654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172654 prefixEnd_6172654 := by exact prefixLift 6172654
  have htrace : WordTrace (prefixWord ++ tailWord_6172654) baseStart_6172654 baseEnd_6172654 := by
    simpa [prefixWord, tailWord_6172654, baseEnd_6172654] using wordTrace_append hprefix tailTrace_6172654
  have hstable : (prefixWord ++ tailWord_6172654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172654).length < 2 ^ (prefixWord ++ tailWord_6172654).sum := by decide
  have hdescent : baseEnd_6172654 < baseStart_6172654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172684 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_6172684 : Nat := 118140960795 + 6172684 * 2 ^ 59
def prefixEnd_6172684 : Nat := 4983230072969 + 3 ^ 40 * 6172684 * 2
def baseEnd_6172684 : Nat := 3169553820317632579162349

theorem tailTrace_6172684 : CollatzResearch.WordTrace tailWord_6172684 prefixEnd_6172684 3169553820317632579162349 := by
  unfold tailWord_6172684
  simp only [CollatzResearch.WordTrace]
  refine ⟨112568140584713776671162553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150090854112951702228216737 112568140584713776671162553)
  ·
    refine ⟨84426105438535332503371915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112568140584713776671162553 84426105438535332503371915)
    ·
      refine ⟨126639158157802998755057873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84426105438535332503371915 126639158157802998755057873)
      ·
        refine ⟨94979368618352249066293405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126639158157802998755057873 94979368618352249066293405)
        ·
          refine ⟨35617263231882093399860027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94979368618352249066293405 35617263231882093399860027)
          ·
            refine ⟨53425894847823140099790041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35617263231882093399860027 53425894847823140099790041)
            ·
              refine ⟨40069421135867355074842531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53425894847823140099790041 40069421135867355074842531)
              ·
                refine ⟨60104131703801032612263797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40069421135867355074842531 60104131703801032612263797)
                ·
                  refine ⟨5634762347231346807399731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60104131703801032612263797 5634762347231346807399731)
                  ·
                    refine ⟨8452143520847020211099597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5634762347231346807399731 8452143520847020211099597)
                    ·
                      refine ⟨3169553820317632579162349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8452143520847020211099597 3169553820317632579162349)
                      ·
                        rfl

theorem cell23_6172684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_6172684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172684 prefixEnd_6172684 := by exact prefixLift 6172684
  have htrace : WordTrace (prefixWord ++ tailWord_6172684) baseStart_6172684 baseEnd_6172684 := by
    simpa [prefixWord, tailWord_6172684, baseEnd_6172684] using wordTrace_append hprefix tailTrace_6172684
  have hstable : (prefixWord ++ tailWord_6172684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172684).length < 2 ^ (prefixWord ++ tailWord_6172684).sum := by decide
  have hdescent : baseEnd_6172684 < baseStart_6172684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172685 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6172685 : Nat := 118140960795 + 6172685 * 2 ^ 59
def prefixEnd_6172685 : Nat := 4983230072969 + 3 ^ 40 * 6172685 * 2
def baseEnd_6172685 : Nat := 3169554333798287075249845

theorem tailTrace_6172685 : CollatzResearch.WordTrace tailWord_6172685 prefixEnd_6172685 3169554333798287075249845 := by
  unfold tailWord_6172685
  simp only [CollatzResearch.WordTrace]
  refine ⟨225136317642423930513111509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150090878428282620342074339 225136317642423930513111509)
  ·
    refine ⟨5276632444744310871401051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 225136317642423930513111509 5276632444744310871401051)
    ·
      refine ⟨7914948667116466307101577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5276632444744310871401051 7914948667116466307101577)
      ·
        refine ⟨5936211500337349730326183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7914948667116466307101577 5936211500337349730326183)
        ·
          refine ⟨8904317250506024595489275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936211500337349730326183 8904317250506024595489275)
          ·
            refine ⟨13356475875759036893233913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8904317250506024595489275 13356475875759036893233913)
            ·
              refine ⟨10017356906819277669925435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13356475875759036893233913 10017356906819277669925435)
              ·
                refine ⟨15026035360228916504888153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10017356906819277669925435 15026035360228916504888153)
                ·
                  refine ⟨11269526520171687378666115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15026035360228916504888153 11269526520171687378666115)
                  ·
                    refine ⟨16904289780257531067999173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11269526520171687378666115 16904289780257531067999173)
                    ·
                      refine ⟨3169554333798287075249845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16904289780257531067999173 3169554333798287075249845)
                      ·
                        rfl

theorem cell23_6172685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6172685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172685 prefixEnd_6172685 := by exact prefixLift 6172685
  have htrace : WordTrace (prefixWord ++ tailWord_6172685) baseStart_6172685 baseEnd_6172685 := by
    simpa [prefixWord, tailWord_6172685, baseEnd_6172685] using wordTrace_append hprefix tailTrace_6172685
  have hstable : (prefixWord ++ tailWord_6172685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172685).length < 2 ^ (prefixWord ++ tailWord_6172685).sum := by decide
  have hdescent : baseEnd_6172685 < baseStart_6172685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172712 : List Nat := [2, 1, 5, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6172712 : Nat := 118140960795 + 6172712 * 2 ^ 59
def prefixEnd_6172712 : Nat := 4983230072969 + 3 ^ 40 * 6172712 * 2
def baseEnd_6172712 : Nat := 1056522732591986156537407

theorem tailTrace_6172712 : CollatzResearch.WordTrace tailWord_6172712 prefixEnd_6172712 1056522732591986156537407 := by
  unfold tailWord_6172712
  simp only [CollatzResearch.WordTrace]
  refine ⟨112568651206663057062172195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150091534942217409416229593 112568651206663057062172195)
  ·
    refine ⟨168852976809994585593258293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112568651206663057062172195 168852976809994585593258293)
    ·
      refine ⟨15829966575936992399367965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168852976809994585593258293 15829966575936992399367965)
      ·
        refine ⟨5936237465976372149762987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15829966575936992399367965 5936237465976372149762987)
        ·
          refine ⟨8904356198964558224644481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936237465976372149762987 8904356198964558224644481)
          ·
            refine ⟨6678267149223418668483361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8904356198964558224644481 6678267149223418668483361)
            ·
              refine ⟨5008700361917564001362521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6678267149223418668483361 5008700361917564001362521)
              ·
                refine ⟨3756525271438173001021891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008700361917564001362521 3756525271438173001021891)
                ·
                  refine ⟨5634787907157259501532837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3756525271438173001021891 5634787907157259501532837)
                  ·
                    refine ⟨1056522732591986156537407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5634787907157259501532837 1056522732591986156537407)
                    ·
                      rfl

theorem cell23_6172712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6172712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172712 prefixEnd_6172712 := by exact prefixLift 6172712
  have htrace : WordTrace (prefixWord ++ tailWord_6172712) baseStart_6172712 baseEnd_6172712 := by
    simpa [prefixWord, tailWord_6172712, baseEnd_6172712] using wordTrace_append hprefix tailTrace_6172712
  have hstable : (prefixWord ++ tailWord_6172712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172712).length < 2 ^ (prefixWord ++ tailWord_6172712).sum := by decide
  have hdescent : baseEnd_6172712 < baseStart_6172712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172727 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_6172727 : Nat := 118140960795 + 6172727 * 2 ^ 59
def prefixEnd_6172727 : Nat := 4983230072969 + 3 ^ 40 * 6172727 * 2
def baseEnd_6172727 : Nat := 3169575899985775910924651

theorem tailTrace_6172727 : CollatzResearch.WordTrace tailWord_6172727 prefixEnd_6172727 3169575899985775910924651 := by
  unfold tailWord_6172727
  simp only [CollatzResearch.WordTrace]
  refine ⟨225137849508271771686140435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150091899672181181124093623 225137849508271771686140435)
  ·
    refine ⟨337706774262407657529210653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225137849508271771686140435 337706774262407657529210653)
    ·
      refine ⟨126640040348402871573453995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337706774262407657529210653 126640040348402871573453995)
      ·
        refine ⟨189960060522604307360180993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126640040348402871573453995 189960060522604307360180993)
        ·
          refine ⟨142470045391953230520135745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189960060522604307360180993 142470045391953230520135745)
          ·
            refine ⟨106852534043964922890101809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142470045391953230520135745 106852534043964922890101809)
            ·
              refine ⟨80139400532973692167576357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106852534043964922890101809 80139400532973692167576357)
              ·
                refine ⟨15026137599932567281420567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80139400532973692167576357 15026137599932567281420567)
                ·
                  refine ⟨22539206399898850922130851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15026137599932567281420567 22539206399898850922130851)
                  ·
                    refine ⟨33808809599848276383196277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22539206399898850922130851 33808809599848276383196277)
                    ·
                      refine ⟨3169575899985775910924651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33808809599848276383196277 3169575899985775910924651)
                      ·
                        rfl

theorem cell23_6172727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_6172727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172727 prefixEnd_6172727 := by exact prefixLift 6172727
  have htrace : WordTrace (prefixWord ++ tailWord_6172727) baseStart_6172727 baseEnd_6172727 := by
    simpa [prefixWord, tailWord_6172727, baseEnd_6172727] using wordTrace_append hprefix tailTrace_6172727
  have hstable : (prefixWord ++ tailWord_6172727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172727).length < 2 ^ (prefixWord ++ tailWord_6172727).sum := by decide
  have hdescent : baseEnd_6172727 < baseStart_6172727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172791 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_6172791 : Nat := 118140960795 + 6172791 * 2 ^ 59
def prefixEnd_6172791 : Nat := 4983230072969 + 3 ^ 40 * 6172791 * 2
def baseEnd_6172791 : Nat := 3169608762747663660524357

theorem tailTrace_6172791 : CollatzResearch.WordTrace tailWord_6172791 prefixEnd_6172791 3169608762747663660524357 := by
  unfold tailWord_6172791
  simp only [CollatzResearch.WordTrace]
  refine ⟨225140183780039910616470227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150093455853359940410980151 225140183780039910616470227)
  ·
    refine ⟨337710275670059865924705341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225140183780039910616470227 337710275670059865924705341)
    ·
      refine ⟨126641353376272449721764503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337710275670059865924705341 126641353376272449721764503)
      ·
        refine ⟨189962030064408674582646755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126641353376272449721764503 189962030064408674582646755)
        ·
          refine ⟨284943045096613011873970133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189962030064408674582646755 284943045096613011873970133)
          ·
            refine ⟨6678352619451867465796175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 284943045096613011873970133 6678352619451867465796175)
            ·
              refine ⟨10017528929177801198694263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678352619451867465796175 10017528929177801198694263)
              ·
                refine ⟨15026293393766701798041395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10017528929177801198694263 15026293393766701798041395)
                ·
                  refine ⟨22539440090650052697062093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15026293393766701798041395 22539440090650052697062093)
                  ·
                    refine ⟨8452290033993769761398285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22539440090650052697062093 8452290033993769761398285)
                    ·
                      refine ⟨3169608762747663660524357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8452290033993769761398285 3169608762747663660524357)
                      ·
                        rfl

theorem cell23_6172791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_6172791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172791 prefixEnd_6172791 := by exact prefixLift 6172791
  have htrace : WordTrace (prefixWord ++ tailWord_6172791) baseStart_6172791 baseEnd_6172791 := by
    simpa [prefixWord, tailWord_6172791, baseEnd_6172791] using wordTrace_append hprefix tailTrace_6172791
  have hstable : (prefixWord ++ tailWord_6172791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172791).length < 2 ^ (prefixWord ++ tailWord_6172791).sum := by decide
  have hdescent : baseEnd_6172791 < baseStart_6172791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172807 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 1, 8]
def baseStart_6172807 : Nat := 118140960795 + 6172807 * 2 ^ 59
def prefixEnd_6172807 : Nat := 4983230072969 + 3 ^ 40 * 6172807 * 2
def baseEnd_6172807 : Nat := 1056538992812711865974761

theorem tailTrace_6172807 : CollatzResearch.WordTrace tailWord_6172807 prefixEnd_6172807 1056538992812711865974761 := by
  unfold tailWord_6172807
  simp only [CollatzResearch.WordTrace]
  refine ⟨225140767347981945349052675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150093844898654630232701783 225140767347981945349052675)
  ·
    refine ⟨337711151021972918023579013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225140767347981945349052675 337711151021972918023579013)
    ·
      refine ⟨63320840816619922129421065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337711151021972918023579013 63320840816619922129421065)
      ·
        refine ⟨47490630612464941597065799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63320840816619922129421065 47490630612464941597065799)
        ·
          refine ⟨71235945918697412395598699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47490630612464941597065799 71235945918697412395598699)
          ·
            refine ⟨106853918878046118593398049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71235945918697412395598699 106853918878046118593398049)
            ·
              refine ⟨80140439158534588945048537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106853918878046118593398049 80140439158534588945048537)
              ·
                refine ⟨60105329368900941708786403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80140439158534588945048537 60105329368900941708786403)
                ·
                  refine ⟨90157994053351412563179605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60105329368900941708786403 90157994053351412563179605)
                  ·
                    refine ⟨1056538992812711865974761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90157994053351412563179605 1056538992812711865974761)
                    ·
                      rfl

theorem cell23_6172807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_6172807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172807 prefixEnd_6172807 := by exact prefixLift 6172807
  have htrace : WordTrace (prefixWord ++ tailWord_6172807) baseStart_6172807 baseEnd_6172807 := by
    simpa [prefixWord, tailWord_6172807, baseEnd_6172807] using wordTrace_append hprefix tailTrace_6172807
  have hstable : (prefixWord ++ tailWord_6172807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172807).length < 2 ^ (prefixWord ++ tailWord_6172807).sum := by decide
  have hdescent : baseEnd_6172807 < baseStart_6172807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172818 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_6172818 : Nat := 118140960795 + 6172818 * 2 ^ 59
def prefixEnd_6172818 : Nat := 4983230072969 + 3 ^ 40 * 6172818 * 2
def baseEnd_6172818 : Nat := 3169622626725335054886733

theorem tailTrace_6172818 : CollatzResearch.WordTrace tailWord_6172818 prefixEnd_6172818 3169622626725335054886733 := by
  unfold tailWord_6172818
  simp only [CollatzResearch.WordTrace]
  refine ⟨56285292137735523556925777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150094112367294729485135405 56285292137735523556925777)
  ·
    refine ⟨42213969103301642667694333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56285292137735523556925777 42213969103301642667694333)
    ·
      refine ⟨15830238413738116000385375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42213969103301642667694333 15830238413738116000385375)
      ·
        refine ⟨23745357620607174000578063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15830238413738116000385375 23745357620607174000578063)
        ·
          refine ⟨35618036430910761000867095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23745357620607174000578063 35618036430910761000867095)
          ·
            refine ⟨53427054646366141501300643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35618036430910761000867095 53427054646366141501300643)
            ·
              refine ⟨80140581969549212251950965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53427054646366141501300643 80140581969549212251950965)
              ·
                refine ⟨7513179559645238648620403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80140581969549212251950965 7513179559645238648620403)
                ·
                  refine ⟨11269769339467857972930605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7513179559645238648620403 11269769339467857972930605)
                  ·
                    refine ⟨4226163502300446739848977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11269769339467857972930605 4226163502300446739848977)
                    ·
                      refine ⟨3169622626725335054886733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226163502300446739848977 3169622626725335054886733)
                      ·
                        rfl

theorem cell23_6172818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_6172818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172818 prefixEnd_6172818 := by exact prefixLift 6172818
  have htrace : WordTrace (prefixWord ++ tailWord_6172818) baseStart_6172818 baseEnd_6172818 := by
    simpa [prefixWord, tailWord_6172818, baseEnd_6172818] using wordTrace_append hprefix tailTrace_6172818
  have hstable : (prefixWord ++ tailWord_6172818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172818).length < 2 ^ (prefixWord ++ tailWord_6172818).sum := by decide
  have hdescent : baseEnd_6172818 < baseStart_6172818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172827 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4]
def baseStart_6172827 : Nat := 118140960795 + 6172827 * 2 ^ 59
def prefixEnd_6172827 : Nat := 4983230072969 + 3 ^ 40 * 6172827 * 2
def baseEnd_6172827 : Nat := 3169627248051225519674191

theorem tailTrace_6172827 : CollatzResearch.WordTrace tailWord_6172827 prefixEnd_6172827 3169627248051225519674191 := by
  unfold tailWord_6172827
  simp only [CollatzResearch.WordTrace]
  refine ⟨225141496807909488764780735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150094331205272992509853823 225141496807909488764780735)
  ·
    refine ⟨337712245211864233147171103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225141496807909488764780735 337712245211864233147171103)
    ·
      refine ⟨506568367817796349720756655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337712245211864233147171103 506568367817796349720756655)
      ·
        refine ⟨759852551726694524581134983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506568367817796349720756655 759852551726694524581134983)
        ·
          refine ⟨1139778827590041786871702475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759852551726694524581134983 1139778827590041786871702475)
          ·
            refine ⟨1709668241385062680307553713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139778827590041786871702475 1709668241385062680307553713)
            ·
              refine ⟨1282251181038797010230665285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709668241385062680307553713 1282251181038797010230665285)
              ·
                refine ⟨240422096444774439418249741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1282251181038797010230665285 240422096444774439418249741)
                ·
                  refine ⟨90158286166790414781843653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240422096444774439418249741 90158286166790414781843653)
                  ·
                    refine ⟨16904678656273202771595685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90158286166790414781843653 16904678656273202771595685)
                    ·
                      refine ⟨3169627248051225519674191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16904678656273202771595685 3169627248051225519674191)
                      ·
                        rfl

theorem cell23_6172827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_6172827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172827 prefixEnd_6172827 := by exact prefixLift 6172827
  have htrace : WordTrace (prefixWord ++ tailWord_6172827) baseStart_6172827 baseEnd_6172827 := by
    simpa [prefixWord, tailWord_6172827, baseEnd_6172827] using wordTrace_append hprefix tailTrace_6172827
  have hstable : (prefixWord ++ tailWord_6172827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172827).length < 2 ^ (prefixWord ++ tailWord_6172827).sum := by decide
  have hdescent : baseEnd_6172827 < baseStart_6172827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172865 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6172865 : Nat := 118140960795 + 6172865 * 2 ^ 59
def prefixEnd_6172865 : Nat := 4983230072969 + 3 ^ 40 * 6172865 * 2
def baseEnd_6172865 : Nat := 3169646760316096370999017

theorem tailTrace_6172865 : CollatzResearch.WordTrace tailWord_6172865 prefixEnd_6172865 3169646760316096370999017 := by
  unfold tailWord_6172865
  simp only [CollatzResearch.WordTrace]
  refine ⟨225142882781771821254664049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150095255187847880836442699 225142882781771821254664049)
  ·
    refine ⟨168857162086328865940998037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225142882781771821254664049 168857162086328865940998037)
    ·
      refine ⟨7915179472796665590984283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168857162086328865940998037 7915179472796665590984283)
      ·
        refine ⟨11872769209194998386476425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915179472796665590984283 11872769209194998386476425)
        ·
          refine ⟨8904576906896248789857319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11872769209194998386476425 8904576906896248789857319)
          ·
            refine ⟨13356865360344373184785979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8904576906896248789857319 13356865360344373184785979)
            ·
              refine ⟨20035298040516559777178969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13356865360344373184785979 20035298040516559777178969)
              ·
                refine ⟨15026473530387419832884227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20035298040516559777178969 15026473530387419832884227)
                ·
                  refine ⟨22539710295581129749326341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15026473530387419832884227 22539710295581129749326341)
                  ·
                    refine ⟨4226195680421461827998689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22539710295581129749326341 4226195680421461827998689)
                    ·
                      refine ⟨3169646760316096370999017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226195680421461827998689 3169646760316096370999017)
                      ·
                        rfl

theorem cell23_6172865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6172865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172865 prefixEnd_6172865 := by exact prefixLift 6172865
  have htrace : WordTrace (prefixWord ++ tailWord_6172865) baseStart_6172865 baseEnd_6172865 := by
    simpa [prefixWord, tailWord_6172865, baseEnd_6172865] using wordTrace_append hprefix tailTrace_6172865
  have hstable : (prefixWord ++ tailWord_6172865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172865).length < 2 ^ (prefixWord ++ tailWord_6172865).sum := by decide
  have hdescent : baseEnd_6172865 < baseStart_6172865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172867 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 5, 7]
def baseStart_6172867 : Nat := 118140960795 + 6172867 * 2 ^ 59
def prefixEnd_6172867 : Nat := 4983230072969 + 3 ^ 40 * 6172867 * 2
def baseEnd_6172867 : Nat := 1056549262425801787724669

theorem tailTrace_6172867 : CollatzResearch.WordTrace tailWord_6172867 prefixEnd_6172867 1056549262425801787724669 := by
  unfold tailWord_6172867
  simp only [CollatzResearch.WordTrace]
  refine ⟨225142955727764575596236855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150095303818509717064157903 225142955727764575596236855)
  ·
    refine ⟨337714433591646863394355283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225142955727764575596236855 337714433591646863394355283)
    ·
      refine ⟨506571650387470295091532925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337714433591646863394355283 506571650387470295091532925)
      ·
        refine ⟨189964368895301360659324847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506571650387470295091532925 189964368895301360659324847)
        ·
          refine ⟨284946553342952040988987271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189964368895301360659324847 284946553342952040988987271)
          ·
            refine ⟨427419830014428061483480907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284946553342952040988987271 427419830014428061483480907)
            ·
              refine ⟨641129745021642092225221361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427419830014428061483480907 641129745021642092225221361)
              ·
                refine ⟨480847308766231569168916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641129745021642092225221361 480847308766231569168916021)
                ·
                  refine ⟨45079435196834209609585877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480847308766231569168916021 45079435196834209609585877)
                  ·
                    refine ⟨1056549262425801787724669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45079435196834209609585877 1056549262425801787724669)
                    ·
                      rfl

theorem cell23_6172867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 7].length) (baseStart_6172867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172867 prefixEnd_6172867 := by exact prefixLift 6172867
  have htrace : WordTrace (prefixWord ++ tailWord_6172867) baseStart_6172867 baseEnd_6172867 := by
    simpa [prefixWord, tailWord_6172867, baseEnd_6172867] using wordTrace_append hprefix tailTrace_6172867
  have hstable : (prefixWord ++ tailWord_6172867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172867).length < 2 ^ (prefixWord ++ tailWord_6172867).sum := by decide
  have hdescent : baseEnd_6172867 < baseStart_6172867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172888 : List Nat := [2, 1, 2, 2, 4, 1, 4, 2, 5]
def baseStart_6172888 : Nat := 118140960795 + 6172888 * 2 ^ 59
def prefixEnd_6172888 : Nat := 4983230072969 + 3 ^ 40 * 6172888 * 2
def baseEnd_6172888 : Nat := 352184285596794420112379

theorem tailTrace_6172888 : CollatzResearch.WordTrace tailWord_6172888 prefixEnd_6172888 352184285596794420112379 := by
  unfold tailWord_6172888
  simp only [CollatzResearch.WordTrace]
  refine ⟨112571860830344248091375659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150095814440458997455167545 112571860830344248091375659)
  ·
    refine ⟨168857791245516372137063489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112571860830344248091375659 168857791245516372137063489)
    ·
      refine ⟨126643343434137279102797617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168857791245516372137063489 126643343434137279102797617)
      ·
        refine ⟨94982507575602959327098213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126643343434137279102797617 94982507575602959327098213)
        ·
          refine ⟨17809220170425554873830915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94982507575602959327098213 17809220170425554873830915)
          ·
            refine ⟨26713830255638332310746373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17809220170425554873830915 26713830255638332310746373)
            ·
              refine ⟨5008843172932187308264945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26713830255638332310746373 5008843172932187308264945)
              ·
                refine ⟨3756632379699140481198709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008843172932187308264945 3756632379699140481198709)
                ·
                  refine ⟨352184285596794420112379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3756632379699140481198709 352184285596794420112379)
                  ·
                    rfl

theorem cell23_6172888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 5].length) (baseStart_6172888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172888 prefixEnd_6172888 := by exact prefixLift 6172888
  have htrace : WordTrace (prefixWord ++ tailWord_6172888) baseStart_6172888 baseEnd_6172888 := by
    simpa [prefixWord, tailWord_6172888, baseEnd_6172888] using wordTrace_append hprefix tailTrace_6172888
  have hstable : (prefixWord ++ tailWord_6172888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172888).length < 2 ^ (prefixWord ++ tailWord_6172888).sum := by decide
  have hdescent : baseEnd_6172888 < baseStart_6172888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6172991 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 1, 5]
def baseStart_6172991 : Nat := 118140960795 + 6172991 * 2 ^ 59
def prefixEnd_6172991 : Nat := 4983230072969 + 3 ^ 40 * 6172991 * 2
def baseEnd_6172991 : Nat := 1056570486292854292674479

theorem tailTrace_6172991 : CollatzResearch.WordTrace tailWord_6172991 prefixEnd_6172991 1056570486292854292674479 := by
  unfold tailWord_6172991
  simp only [CollatzResearch.WordTrace]
  refine ⟨225147478379315344773750827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150098318919543563182500551 225147478379315344773750827)
  ·
    refine ⟨337721217568973017160626241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225147478379315344773750827 337721217568973017160626241)
    ·
      refine ⟨253290913176729762870469681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337721217568973017160626241 253290913176729762870469681)
      ·
        refine ⟨189968184882547322152852261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253290913176729762870469681 189968184882547322152852261)
        ·
          refine ⟨35619034665477622903659799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189968184882547322152852261 35619034665477622903659799)
          ·
            refine ⟨53428551998216434355489699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35619034665477622903659799 53428551998216434355489699)
            ·
              refine ⟨80142827997324651533234549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53428551998216434355489699 80142827997324651533234549)
              ·
                refine ⟨7513390124749186081240739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80142827997324651533234549 7513390124749186081240739)
                ·
                  refine ⟨11270085187123779121861109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7513390124749186081240739 11270085187123779121861109)
                  ·
                    refine ⟨1056570486292854292674479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11270085187123779121861109 1056570486292854292674479)
                    ·
                      rfl

theorem cell23_6172991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_6172991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6172991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6172991 prefixEnd_6172991 := by exact prefixLift 6172991
  have htrace : WordTrace (prefixWord ++ tailWord_6172991) baseStart_6172991 baseEnd_6172991 := by
    simpa [prefixWord, tailWord_6172991, baseEnd_6172991] using wordTrace_append hprefix tailTrace_6172991
  have hstable : (prefixWord ++ tailWord_6172991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6172991).length < 2 ^ (prefixWord ++ tailWord_6172991).sum := by decide
  have hdescent : baseEnd_6172991 < baseStart_6172991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6172991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173011 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 2, 6, 2]
def baseStart_6173011 : Nat := 118140960795 + 6173011 * 2 ^ 59
def prefixEnd_6173011 : Nat := 4983230072969 + 3 ^ 40 * 6173011 * 2
def baseEnd_6173011 : Nat := 3169721728491652799773345

theorem tailTrace_6173011 : CollatzResearch.WordTrace tailWord_6173011 prefixEnd_6173011 3169721728491652799773345 := by
  unfold tailWord_6173011
  simp only [CollatzResearch.WordTrace]
  refine ⟨225148207839242888189478887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150098805226161925459652591 225148207839242888189478887)
  ·
    refine ⟨337722311758864332284218331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225148207839242888189478887 337722311758864332284218331)
    ·
      refine ⟨506583467638296498426327497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337722311758864332284218331 506583467638296498426327497)
      ·
        refine ⟨379937600728722373819745623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506583467638296498426327497 379937600728722373819745623)
        ·
          refine ⟨569906401093083560729618435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379937600728722373819745623 569906401093083560729618435)
          ·
            refine ⟨854859601639625341094427653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569906401093083560729618435 854859601639625341094427653)
            ·
              refine ⟨160286175307429751455205185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 854859601639625341094427653 160286175307429751455205185)
              ·
                refine ⟨120214631480572313591403889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160286175307429751455205185 120214631480572313591403889)
                ·
                  refine ⟨90160973610429235193552917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120214631480572313591403889 90160973610429235193552917)
                  ·
                    refine ⟨4226295637988870399697793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90160973610429235193552917 4226295637988870399697793)
                    ·
                      refine ⟨3169721728491652799773345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226295637988870399697793 3169721728491652799773345)
                      ·
                        rfl

theorem cell23_6173011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6, 2].length) (baseStart_6173011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173011 prefixEnd_6173011 := by exact prefixLift 6173011
  have htrace : WordTrace (prefixWord ++ tailWord_6173011) baseStart_6173011 baseEnd_6173011 := by
    simpa [prefixWord, tailWord_6173011, baseEnd_6173011] using wordTrace_append hprefix tailTrace_6173011
  have hstable : (prefixWord ++ tailWord_6173011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173011).length < 2 ^ (prefixWord ++ tailWord_6173011).sum := by decide
  have hdescent : baseEnd_6173011 < baseStart_6173011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173061 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_6173061 : Nat := 118140960795 + 6173061 * 2 ^ 59
def prefixEnd_6173061 : Nat := 4983230072969 + 3 ^ 40 * 6173061 * 2
def baseEnd_6173061 : Nat := 3169747402524377604148115

theorem tailTrace_6173061 : CollatzResearch.WordTrace tailWord_6173061 prefixEnd_6173061 3169747402524377604148115 := by
  unfold tailWord_6173061
  simp only [CollatzResearch.WordTrace]
  refine ⟨225150031489061746728799037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150100020992707831152532691 225150031489061746728799037)
  ·
    refine ⟨84431261808398155023299639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225150031489061746728799037 84431261808398155023299639)
    ·
      refine ⟨126646892712597232534949459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84431261808398155023299639 126646892712597232534949459)
      ·
        refine ⟨189970339068895848802424189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126646892712597232534949459 189970339068895848802424189)
        ·
          refine ⟨71238877150835943300909071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189970339068895848802424189 71238877150835943300909071)
          ·
            refine ⟨106858315726253914951363607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71238877150835943300909071 106858315726253914951363607)
            ·
              refine ⟨160287473589380872427045411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106858315726253914951363607 160287473589380872427045411)
              ·
                refine ⟨240431210384071308640568117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160287473589380872427045411 240431210384071308640568117)
                ·
                  refine ⟨22540425973506685185053261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240431210384071308640568117 22540425973506685185053261)
                  ·
                    refine ⟨8452659740065006944394973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22540425973506685185053261 8452659740065006944394973)
                    ·
                      refine ⟨3169747402524377604148115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8452659740065006944394973 3169747402524377604148115)
                      ·
                        rfl

theorem cell23_6173061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_6173061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173061 prefixEnd_6173061 := by exact prefixLift 6173061
  have htrace : WordTrace (prefixWord ++ tailWord_6173061) baseStart_6173061 baseEnd_6173061 := by
    simpa [prefixWord, tailWord_6173061, baseEnd_6173061] using wordTrace_append hprefix tailTrace_6173061
  have hstable : (prefixWord ++ tailWord_6173061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173061).length < 2 ^ (prefixWord ++ tailWord_6173061).sum := by decide
  have hdescent : baseEnd_6173061 < baseStart_6173061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173096 : List Nat := [2, 1, 6, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6173096 : Nat := 118140960795 + 6173096 * 2 ^ 59
def prefixEnd_6173096 : Nat := 4983230072969 + 3 ^ 40 * 6173096 * 2
def baseEnd_6173096 : Nat := 3169765374347284967210455

theorem tailTrace_6173096 : CollatzResearch.WordTrace tailWord_6173096 prefixEnd_6173096 3169765374347284967210455 := by
  unfold tailWord_6173096
  simp only [CollatzResearch.WordTrace]
  refine ⟨112575654021967473853161571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150100872029289965137548761 112575654021967473853161571)
  ·
    refine ⟨168863481032951210779742357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112575654021967473853161571 168863481032951210779742357)
    ·
      refine ⟨7915475673419588005300423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168863481032951210779742357 7915475673419588005300423)
      ·
        refine ⟨11873213510129382007950635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915475673419588005300423 11873213510129382007950635)
        ·
          refine ⟨17809820265194073011925953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11873213510129382007950635 17809820265194073011925953)
          ·
            refine ⟨13357365198895554758944465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17809820265194073011925953 13357365198895554758944465)
            ·
              refine ⟨10018023899171666069208349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13357365198895554758944465 10018023899171666069208349)
              ·
                refine ⟨3756758962189374775953131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10018023899171666069208349 3756758962189374775953131)
                ·
                  refine ⟨5635138443284062163929697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3756758962189374775953131 5635138443284062163929697)
                  ·
                    refine ⟨4226353832463046622947273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5635138443284062163929697 4226353832463046622947273)
                    ·
                      refine ⟨3169765374347284967210455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226353832463046622947273 3169765374347284967210455)
                      ·
                        rfl

theorem cell23_6173096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6173096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173096 prefixEnd_6173096 := by exact prefixLift 6173096
  have htrace : WordTrace (prefixWord ++ tailWord_6173096) baseStart_6173096 baseEnd_6173096 := by
    simpa [prefixWord, tailWord_6173096, baseEnd_6173096] using wordTrace_append hprefix tailTrace_6173096
  have hstable : (prefixWord ++ tailWord_6173096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173096).length < 2 ^ (prefixWord ++ tailWord_6173096).sum := by decide
  have hdescent : baseEnd_6173096 < baseStart_6173096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173111 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 2, 6]
def baseStart_6173111 : Nat := 118140960795 + 6173111 * 2 ^ 59
def prefixEnd_6173111 : Nat := 4983230072969 + 3 ^ 40 * 6173111 * 2
def baseEnd_6173111 : Nat := 1056591025519034136174295

theorem tailTrace_6173111 : CollatzResearch.WordTrace tailWord_6173111 prefixEnd_6173111 1056591025519034136174295 := by
  unfold tailWord_6173111
  simp only [CollatzResearch.WordTrace]
  refine ⟨225151855138880605268119187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150101236759253736845412791 225151855138880605268119187)
  ·
    refine ⟨337727782708320907902178781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225151855138880605268119187 337727782708320907902178781)
    ·
      refine ⟨126647918515620340463317043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337727782708320907902178781 126647918515620340463317043)
      ·
        refine ⟨189971877773430510694975565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126647918515620340463317043 189971877773430510694975565)
        ·
          refine ⟨71239454165036441510615837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189971877773430510694975565 71239454165036441510615837)
          ·
            refine ⟨26714795311888665566480939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71239454165036441510615837 26714795311888665566480939)
            ·
              refine ⟨40072192967832998349721409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26714795311888665566480939 40072192967832998349721409)
              ·
                refine ⟨30054144725874748762291057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40072192967832998349721409 30054144725874748762291057)
                ·
                  refine ⟨22540608544406061571718293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30054144725874748762291057 22540608544406061571718293)
                  ·
                    refine ⟨1056591025519034136174295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22540608544406061571718293 1056591025519034136174295)
                    ·
                      rfl

theorem cell23_6173111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_6173111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173111 prefixEnd_6173111 := by exact prefixLift 6173111
  have htrace : WordTrace (prefixWord ++ tailWord_6173111) baseStart_6173111 baseEnd_6173111 := by
    simpa [prefixWord, tailWord_6173111, baseEnd_6173111] using wordTrace_append hprefix tailTrace_6173111
  have hstable : (prefixWord ++ tailWord_6173111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173111).length < 2 ^ (prefixWord ++ tailWord_6173111).sum := by decide
  have hdescent : baseEnd_6173111 < baseStart_6173111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173186 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6173186 : Nat := 118140960795 + 6173186 * 2 ^ 59
def prefixEnd_6173186 : Nat := 4983230072969 + 3 ^ 40 * 6173186 * 2
def baseEnd_6173186 : Nat := 3169811587606189615085041

theorem tailTrace_6173186 : CollatzResearch.WordTrace tailWord_6173186 prefixEnd_6173186 3169811587606189615085041 := by
  unfold tailWord_6173186
  simp only [CollatzResearch.WordTrace]
  refine ⟨56288647653402223269274853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150103060409072595384732941 56288647653402223269274853)
  ·
    refine ⟨10554121435012916862989035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56288647653402223269274853 10554121435012916862989035)
    ·
      refine ⟨15831182152519375294483553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10554121435012916862989035 15831182152519375294483553)
      ·
        refine ⟨11873386614389531470862665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15831182152519375294483553 11873386614389531470862665)
        ·
          refine ⟨8905039960792148603146999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11873386614389531470862665 8905039960792148603146999)
          ·
            refine ⟨13357559941188222904720499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8905039960792148603146999 13357559941188222904720499)
            ·
              refine ⟨20036339911782334357080749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13357559941188222904720499 20036339911782334357080749)
              ·
                refine ⟨7513627466918375383905281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20036339911782334357080749 7513627466918375383905281)
                ·
                  refine ⟨5635220600188781537928961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7513627466918375383905281 5635220600188781537928961)
                  ·
                    refine ⟨4226415450141586153446721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5635220600188781537928961 4226415450141586153446721)
                    ·
                      refine ⟨3169811587606189615085041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226415450141586153446721 3169811587606189615085041)
                      ·
                        rfl

theorem cell23_6173186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6173186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173186 prefixEnd_6173186 := by exact prefixLift 6173186
  have htrace : WordTrace (prefixWord ++ tailWord_6173186) baseStart_6173186 baseEnd_6173186 := by
    simpa [prefixWord, tailWord_6173186, baseEnd_6173186] using wordTrace_append hprefix tailTrace_6173186
  have hstable : (prefixWord ++ tailWord_6173186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173186).length < 2 ^ (prefixWord ++ tailWord_6173186).sum := by decide
  have hdescent : baseEnd_6173186 < baseStart_6173186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173248 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 6]
def baseStart_6173248 : Nat := 118140960795 + 6173248 * 2 ^ 59
def prefixEnd_6173248 : Nat := 4983230072969 + 3 ^ 40 * 6173248 * 2
def baseEnd_6173248 : Nat := 352204824822974263612195

theorem tailTrace_6173248 : CollatzResearch.WordTrace tailWord_6173248 prefixEnd_6173248 352204824822974263612195 := by
  unfold tailWord_6173248
  simp only [CollatzResearch.WordTrace]
  refine ⟨112578425969692138832928199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150104567959589518443904265 112578425969692138832928199)
  ·
    refine ⟨168867638954538208249392299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112578425969692138832928199 168867638954538208249392299)
    ·
      refine ⟨253301458431807312374088449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168867638954538208249392299 253301458431807312374088449)
      ·
        refine ⟨189976093823855484280566337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253301458431807312374088449 189976093823855484280566337)
        ·
          refine ⟨142482070367891613210424753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189976093823855484280566337 142482070367891613210424753)
          ·
            refine ⟨106861552775918709907818565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142482070367891613210424753 106861552775918709907818565)
            ·
              refine ⟨20036541145484758107715981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106861552775918709907818565 20036541145484758107715981)
              ·
                refine ⟨7513702929556784290393493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20036541145484758107715981 7513702929556784290393493)
                ·
                  refine ⟨352204824822974263612195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7513702929556784290393493 352204824822974263612195)
                  ·
                    rfl

theorem cell23_6173248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 6].length) (baseStart_6173248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173248 prefixEnd_6173248 := by exact prefixLift 6173248
  have htrace : WordTrace (prefixWord ++ tailWord_6173248) baseStart_6173248 baseEnd_6173248 := by
    simpa [prefixWord, tailWord_6173248, baseEnd_6173248] using wordTrace_append hprefix tailTrace_6173248
  have hstable : (prefixWord ++ tailWord_6173248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173248).length < 2 ^ (prefixWord ++ tailWord_6173248).sum := by decide
  have hdescent : baseEnd_6173248 < baseStart_6173248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173282 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 8]
def baseStart_6173282 : Nat := 118140960795 + 6173282 * 2 ^ 59
def prefixEnd_6173282 : Nat := 4983230072969 + 3 ^ 40 * 6173282 * 2
def baseEnd_6173282 : Nat := 352206764638780137720511

theorem tailTrace_6173282 : CollatzResearch.WordTrace tailWord_6173282 prefixEnd_6173282 352206764638780137720511 := by
  unfold tailWord_6173282
  simp only [CollatzResearch.WordTrace]
  refine ⟨56289523005315275368148525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150105394680840734315062733 56289523005315275368148525)
  ·
    refine ⟨21108571126993228263055697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56289523005315275368148525 21108571126993228263055697)
    ·
      refine ⟨15831428345244921197291773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21108571126993228263055697 15831428345244921197291773)
      ·
        refine ⟨5936785629466845448984415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15831428345244921197291773 5936785629466845448984415)
        ·
          refine ⟨8905178444200268173476623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936785629466845448984415 8905178444200268173476623)
          ·
            refine ⟨13357767666300402260214935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8905178444200268173476623 13357767666300402260214935)
            ·
              refine ⟨20036651499450603390322403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13357767666300402260214935 20036651499450603390322403)
              ·
                refine ⟨30054977249175905085483605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20036651499450603390322403 30054977249175905085483605)
                ·
                  refine ⟨352206764638780137720511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30054977249175905085483605 352206764638780137720511)
                  ·
                    rfl

theorem cell23_6173282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_6173282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173282 prefixEnd_6173282 := by exact prefixLift 6173282
  have htrace : WordTrace (prefixWord ++ tailWord_6173282) baseStart_6173282 baseEnd_6173282 := by
    simpa [prefixWord, tailWord_6173282, baseEnd_6173282] using wordTrace_append hprefix tailTrace_6173282
  have hstable : (prefixWord ++ tailWord_6173282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173282).length < 2 ^ (prefixWord ++ tailWord_6173282).sum := by decide
  have hdescent : baseEnd_6173282 < baseStart_6173282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173315 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 4]
def baseStart_6173315 : Nat := 118140960795 + 6173315 * 2 ^ 59
def prefixEnd_6173315 : Nat := 4983230072969 + 3 ^ 40 * 6173315 * 2
def baseEnd_6173315 : Nat := 3169877826610619610371947

theorem tailTrace_6173315 : CollatzResearch.WordTrace tailWord_6173315 prefixEnd_6173315 3169877826610619610371947 := by
  unfold tailWord_6173315
  simp only [CollatzResearch.WordTrace]
  refine ⟨225159295630141548108545399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150106197086761032072363599 225159295630141548108545399)
  ·
    refine ⟨337738943445212322162818099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225159295630141548108545399 337738943445212322162818099)
    ·
      refine ⟨506608415167818483244227149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337738943445212322162818099 506608415167818483244227149)
      ·
        refine ⟨189978155687931931216585181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506608415167818483244227149 189978155687931931216585181)
        ·
          refine ⟨71241808382974474206219443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189978155687931931216585181 71241808382974474206219443)
          ·
            refine ⟨106862712574461711309329165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71241808382974474206219443 106862712574461711309329165)
            ·
              refine ⟨40073517215423141740998437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106862712574461711309329165 40073517215423141740998437)
              ·
                refine ⟨7513784477891839076437207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40073517215423141740998437 7513784477891839076437207)
                ·
                  refine ⟨11270676716837758614655811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7513784477891839076437207 11270676716837758614655811)
                  ·
                    refine ⟨16906015075256637921983717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11270676716837758614655811 16906015075256637921983717)
                    ·
                      refine ⟨3169877826610619610371947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16906015075256637921983717 3169877826610619610371947)
                      ·
                        rfl

theorem cell23_6173315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_6173315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173315 prefixEnd_6173315 := by exact prefixLift 6173315
  have htrace : WordTrace (prefixWord ++ tailWord_6173315) baseStart_6173315 baseEnd_6173315 := by
    simpa [prefixWord, tailWord_6173315, baseEnd_6173315] using wordTrace_append hprefix tailTrace_6173315
  have hstable : (prefixWord ++ tailWord_6173315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173315).length < 2 ^ (prefixWord ++ tailWord_6173315).sum := by decide
  have hdescent : baseEnd_6173315 < baseStart_6173315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173335 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_6173335 : Nat := 118140960795 + 6173335 * 2 ^ 59
def prefixEnd_6173335 : Nat := 4983230072969 + 3 ^ 40 * 6173335 * 2
def baseEnd_6173335 : Nat := 3169888096223709532121855

theorem tailTrace_6173335 : CollatzResearch.WordTrace tailWord_6173335 prefixEnd_6173335 3169888096223709532121855 := by
  unfold tailWord_6173335
  simp only [CollatzResearch.WordTrace]
  refine ⟨225160025090069091524273459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150106683393379394349515639 225160025090069091524273459)
  ·
    refine ⟨337740037635103637286410189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225160025090069091524273459 337740037635103637286410189)
    ·
      refine ⟨126652514113163863982403821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337740037635103637286410189 126652514113163863982403821)
      ·
        refine ⟨47494692792436448993401433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126652514113163863982403821 47494692792436448993401433)
        ·
          refine ⟨35621019594327336745051075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47494692792436448993401433 35621019594327336745051075)
          ·
            refine ⟨53431529391491005117576613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35621019594327336745051075 53431529391491005117576613)
            ·
              refine ⟨10018411760904563459545615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53431529391491005117576613 10018411760904563459545615)
              ·
                refine ⟨15027617641356845189318423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10018411760904563459545615 15027617641356845189318423)
                ·
                  refine ⟨22541426462035267783977635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15027617641356845189318423 22541426462035267783977635)
                  ·
                    refine ⟨33812139693052901675966453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22541426462035267783977635 33812139693052901675966453)
                    ·
                      refine ⟨3169888096223709532121855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33812139693052901675966453 3169888096223709532121855)
                      ·
                        rfl

theorem cell23_6173335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_6173335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173335 prefixEnd_6173335 := by exact prefixLift 6173335
  have htrace : WordTrace (prefixWord ++ tailWord_6173335) baseStart_6173335 baseEnd_6173335 := by
    simpa [prefixWord, tailWord_6173335, baseEnd_6173335] using wordTrace_append hprefix tailTrace_6173335
  have hstable : (prefixWord ++ tailWord_6173335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173335).length < 2 ^ (prefixWord ++ tailWord_6173335).sum := by decide
  have hdescent : baseEnd_6173335 < baseStart_6173335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173342 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_6173342 : Nat := 118140960795 + 6173342 * 2 ^ 59
def prefixEnd_6173342 : Nat := 4983230072969 + 3 ^ 40 * 6173342 * 2
def baseEnd_6173342 : Nat := 1056630563529430334911441

theorem tailTrace_6173342 : CollatzResearch.WordTrace tailWord_6173342 prefixEnd_6173342 1056630563529430334911441 := by
  unfold tailWord_6173342
  simp only [CollatzResearch.WordTrace]
  refine ⟨28145035050130466464972285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150106853600695821146518853 28145035050130466464972285)
  ·
    refine ⟨10554388143798924924364607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28145035050130466464972285 10554388143798924924364607)
    ·
      refine ⟨15831582215698387386546911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10554388143798924924364607 15831582215698387386546911)
      ·
        refine ⟨23747373323547581079820367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15831582215698387386546911 23747373323547581079820367)
        ·
          refine ⟨35621059985321371619730551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23747373323547581079820367 35621059985321371619730551)
          ·
            refine ⟨53431589977982057429595827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35621059985321371619730551 53431589977982057429595827)
            ·
              refine ⟨80147384966973086144393741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53431589977982057429595827 80147384966973086144393741)
              ·
                refine ⟨30055269362614907304147653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80147384966973086144393741 30055269362614907304147653)
                ·
                  refine ⟨5635363005490295119527685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30055269362614907304147653 5635363005490295119527685)
                  ·
                    refine ⟨1056630563529430334911441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635363005490295119527685 1056630563529430334911441)
                    ·
                      rfl

theorem cell23_6173342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_6173342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173342 prefixEnd_6173342 := by exact prefixLift 6173342
  have htrace : WordTrace (prefixWord ++ tailWord_6173342) baseStart_6173342 baseEnd_6173342 := by
    simpa [prefixWord, tailWord_6173342, baseEnd_6173342] using wordTrace_append hprefix tailTrace_6173342
  have hstable : (prefixWord ++ tailWord_6173342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173342).length < 2 ^ (prefixWord ++ tailWord_6173342).sum := by decide
  have hdescent : baseEnd_6173342 < baseStart_6173342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173359 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 2, 4]
def baseStart_6173359 : Nat := 118140960795 + 6173359 * 2 ^ 59
def prefixEnd_6173359 : Nat := 4983230072969 + 3 ^ 40 * 6173359 * 2
def baseEnd_6173359 : Nat := 1056633473253139146073915

theorem tailTrace_6173359 : CollatzResearch.WordTrace tailWord_6173359 prefixEnd_6173359 1056633473253139146073915 := by
  unfold tailWord_6173359
  simp only [CollatzResearch.WordTrace]
  refine ⟨225160900441982143623147131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150107266961321429082098087 225160900441982143623147131)
  ·
    refine ⟨337741350662973215434720697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225160900441982143623147131 337741350662973215434720697)
    ·
      refine ⟨253306012997229911576040523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337741350662973215434720697 253306012997229911576040523)
      ·
        refine ⟨379959019495844867364060785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253306012997229911576040523 379959019495844867364060785)
        ·
          refine ⟨284969264621883650523045589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379959019495844867364060785 284969264621883650523045589)
          ·
            refine ⟨6678967139575398059133881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 284969264621883650523045589 6678967139575398059133881)
            ·
              refine ⟨5009225354681548544350411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6678967139575398059133881 5009225354681548544350411)
              ·
                refine ⟨7513838032022322816525617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009225354681548544350411 7513838032022322816525617)
                ·
                  refine ⟨5635378524016742112394213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7513838032022322816525617 5635378524016742112394213)
                  ·
                    refine ⟨1056633473253139146073915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635378524016742112394213 1056633473253139146073915)
                    ·
                      rfl

theorem cell23_6173359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 2, 4].length) (baseStart_6173359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173359 prefixEnd_6173359 := by exact prefixLift 6173359
  have htrace : WordTrace (prefixWord ++ tailWord_6173359) baseStart_6173359 baseEnd_6173359 := by
    simpa [prefixWord, tailWord_6173359, baseEnd_6173359] using wordTrace_append hprefix tailTrace_6173359
  have hstable : (prefixWord ++ tailWord_6173359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173359).length < 2 ^ (prefixWord ++ tailWord_6173359).sum := by decide
  have hdescent : baseEnd_6173359 < baseStart_6173359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173399 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_6173399 : Nat := 118140960795 + 6173399 * 2 ^ 59
def prefixEnd_6173399 : Nat := 4983230072969 + 3 ^ 40 * 6173399 * 2
def baseEnd_6173399 : Nat := 3169920958985597281721561

theorem tailTrace_6173399 : CollatzResearch.WordTrace tailWord_6173399 prefixEnd_6173399 3169920958985597281721561 := by
  unfold tailWord_6173399
  simp only [CollatzResearch.WordTrace]
  refine ⟨225162359361837230454603251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150108239574558153636402167 225162359361837230454603251)
  ·
    refine ⟨337743539042755845681904877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225162359361837230454603251 337743539042755845681904877)
    ·
      refine ⟨126653827141033442130714329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337743539042755845681904877 126653827141033442130714329)
      ·
        refine ⟨94990370355775081598035747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126653827141033442130714329 94990370355775081598035747)
        ·
          refine ⟨142485555533662622397053621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94990370355775081598035747 142485555533662622397053621)
          ·
            refine ⟨13358020831280870849723777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142485555533662622397053621 13358020831280870849723777)
            ·
              refine ⟨10018515623460653137292833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13358020831280870849723777 10018515623460653137292833)
              ·
                refine ⟨7513886717595489852969625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10018515623460653137292833 7513886717595489852969625)
                ·
                  refine ⟨5635415038196617389727219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7513886717595489852969625 5635415038196617389727219)
                  ·
                    refine ⟨8453122557294926084590829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5635415038196617389727219 8453122557294926084590829)
                    ·
                      refine ⟨3169920958985597281721561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8453122557294926084590829 3169920958985597281721561)
                      ·
                        rfl

theorem cell23_6173399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_6173399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173399 prefixEnd_6173399 := by exact prefixLift 6173399
  have htrace : WordTrace (prefixWord ++ tailWord_6173399) baseStart_6173399 baseEnd_6173399 := by
    simpa [prefixWord, tailWord_6173399, baseEnd_6173399] using wordTrace_append hprefix tailTrace_6173399
  have hstable : (prefixWord ++ tailWord_6173399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173399).length < 2 ^ (prefixWord ++ tailWord_6173399).sum := by decide
  have hdescent : baseEnd_6173399 < baseStart_6173399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173425 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_6173425 : Nat := 118140960795 + 6173425 * 2 ^ 59
def prefixEnd_6173425 : Nat := 4983230072969 + 3 ^ 40 * 6173425 * 2
def baseEnd_6173425 : Nat := 3169934309482614179996441

theorem tailTrace_6173425 : CollatzResearch.WordTrace tailWord_6173425 prefixEnd_6173425 3169934309482614179996441 := by
  unfold tailWord_6173425
  simp only [CollatzResearch.WordTrace]
  refine ⟨225163307659743036895049729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150108871773162024596699819 225163307659743036895049729)
  ·
    refine ⟨168872480744807277671287297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225163307659743036895049729 168872480744807277671287297)
    ·
      refine ⟨126654360558605458253465473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168872480744807277671287297 126654360558605458253465473)
      ·
        refine ⟨94990770418954093690099105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126654360558605458253465473 94990770418954093690099105)
        ·
          refine ⟨71243077814215570267574329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94990770418954093690099105 71243077814215570267574329)
          ·
            refine ⟨53432308360661677700680747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71243077814215570267574329 53432308360661677700680747)
            ·
              refine ⟨80148462540992516551021121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53432308360661677700680747 80148462540992516551021121)
              ·
                refine ⟨60111346905744387413265841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80148462540992516551021121 60111346905744387413265841)
                ·
                  refine ⟨45083510179308290559949381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60111346905744387413265841 45083510179308290559949381)
                  ·
                    refine ⟨8453158158620304479990509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45083510179308290559949381 8453158158620304479990509)
                    ·
                      refine ⟨3169934309482614179996441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8453158158620304479990509 3169934309482614179996441)
                      ·
                        rfl

theorem cell23_6173425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_6173425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173425 prefixEnd_6173425 := by exact prefixLift 6173425
  have htrace : WordTrace (prefixWord ++ tailWord_6173425) baseStart_6173425 baseEnd_6173425 := by
    simpa [prefixWord, tailWord_6173425, baseEnd_6173425] using wordTrace_append hprefix tailTrace_6173425
  have hstable : (prefixWord ++ tailWord_6173425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173425).length < 2 ^ (prefixWord ++ tailWord_6173425).sum := by decide
  have hdescent : baseEnd_6173425 < baseStart_6173425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173455 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 3]
def baseStart_6173455 : Nat := 118140960795 + 6173455 * 2 ^ 59
def prefixEnd_6173455 : Nat := 4983230072969 + 3 ^ 40 * 6173455 * 2
def baseEnd_6173455 : Nat := 3169949713902249062621303

theorem tailTrace_6173455 : CollatzResearch.WordTrace tailWord_6173455 prefixEnd_6173455 3169949713902249062621303 := by
  unfold tailWord_6173455
  simp only [CollatzResearch.WordTrace]
  refine ⟨225164401849634352018641819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150109601233089568012427879 225164401849634352018641819)
  ·
    refine ⟨337746602774451528027962729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225164401849634352018641819 337746602774451528027962729)
    ·
      refine ⟨253309952080838646020972047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337746602774451528027962729 253309952080838646020972047)
      ·
        refine ⟨379964928121257969031458071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253309952080838646020972047 379964928121257969031458071)
        ·
          refine ⟨569947392181886953547187107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379964928121257969031458071 569947392181886953547187107)
          ·
            refine ⟨854921088272830430320780661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569947392181886953547187107 854921088272830430320780661)
            ·
              refine ⟨80148852025577852842573187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 854921088272830430320780661 80148852025577852842573187)
              ·
                refine ⟨120223278038366779263859781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80148852025577852842573187 120223278038366779263859781)
                ·
                  refine ⟨22541864632193771111973709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120223278038366779263859781 22541864632193771111973709)
                  ·
                    refine ⟨8453199237072664166990141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22541864632193771111973709 8453199237072664166990141)
                    ·
                      refine ⟨3169949713902249062621303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8453199237072664166990141 3169949713902249062621303)
                      ·
                        rfl

theorem cell23_6173455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_6173455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173455 prefixEnd_6173455 := by exact prefixLift 6173455
  have htrace : WordTrace (prefixWord ++ tailWord_6173455) baseStart_6173455 baseEnd_6173455 := by
    simpa [prefixWord, tailWord_6173455, baseEnd_6173455] using wordTrace_append hprefix tailTrace_6173455
  have hstable : (prefixWord ++ tailWord_6173455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173455).length < 2 ^ (prefixWord ++ tailWord_6173455).sum := by decide
  have hdescent : baseEnd_6173455 < baseStart_6173455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173472 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6173472 : Nat := 118140960795 + 6173472 * 2 ^ 59
def prefixEnd_6173472 : Nat := 4983230072969 + 3 ^ 40 * 6173472 * 2
def baseEnd_6173472 : Nat := 3169958443073375496108725

theorem tailTrace_6173472 : CollatzResearch.WordTrace tailWord_6173472 prefixEnd_6173472 3169958443073375496108725 := by
  unfold tailWord_6173472
  simp only [CollatzResearch.WordTrace]
  refine ⟨112582510945286381961005335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150110014593715175948007113 112582510945286381961005335)
  ·
    refine ⟨168873766417929572941508003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112582510945286381961005335 168873766417929572941508003)
    ·
      refine ⟨253310649626894359412262005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168873766417929572941508003 253310649626894359412262005)
      ·
        refine ⟨23747873402521346194899563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253310649626894359412262005 23747873402521346194899563)
        ·
          refine ⟨35621810103782019292349345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23747873402521346194899563 35621810103782019292349345)
          ·
            refine ⟨26716357577836514469262009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35621810103782019292349345 26716357577836514469262009)
            ·
              refine ⟨20037268183377385851946507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26716357577836514469262009 20037268183377385851946507)
              ·
                refine ⟨30055902275066078777919761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20037268183377385851946507 30055902275066078777919761)
                ·
                  refine ⟨22541926706299559083439821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30055902275066078777919761 22541926706299559083439821)
                  ·
                    refine ⟨8453222514862334656289933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22541926706299559083439821 8453222514862334656289933)
                    ·
                      refine ⟨3169958443073375496108725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8453222514862334656289933 3169958443073375496108725)
                      ·
                        rfl

theorem cell23_6173472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6173472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173472 prefixEnd_6173472 := by exact prefixLift 6173472
  have htrace : WordTrace (prefixWord ++ tailWord_6173472) baseStart_6173472 baseEnd_6173472 := by
    simpa [prefixWord, tailWord_6173472, baseEnd_6173472] using wordTrace_append hprefix tailTrace_6173472
  have hstable : (prefixWord ++ tailWord_6173472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173472).length < 2 ^ (prefixWord ++ tailWord_6173472).sum := by decide
  have hdescent : baseEnd_6173472 < baseStart_6173472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173495 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_6173495 : Nat := 118140960795 + 6173495 * 2 ^ 59
def prefixEnd_6173495 : Nat := 4983230072969 + 3 ^ 40 * 6173495 * 2
def baseEnd_6173495 : Nat := 3169970253128428906121119

theorem tailTrace_6173495 : CollatzResearch.WordTrace tailWord_6173495 prefixEnd_6173495 3169970253128428906121119 := by
  unfold tailWord_6173495
  simp only [CollatzResearch.WordTrace]
  refine ⟨225165860769489438850097939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150110573846326292566731959 225165860769489438850097939)
  ·
    refine ⟨337748791154234158275146909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225165860769489438850097939 337748791154234158275146909)
    ·
      refine ⟨126655796682837809353180091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337748791154234158275146909 126655796682837809353180091)
      ·
        refine ⟨189983695024256714029770137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126655796682837809353180091 189983695024256714029770137)
        ·
          refine ⟨142487771268192535522327603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189983695024256714029770137 142487771268192535522327603)
          ·
            refine ⟨213731656902288803283491405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142487771268192535522327603 213731656902288803283491405)
            ·
              refine ⟨80149371338358301231309277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213731656902288803283491405 80149371338358301231309277)
              ·
                refine ⟨30056014251884362961740979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80149371338358301231309277 30056014251884362961740979)
                ·
                  refine ⟨45084021377826544442611469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30056014251884362961740979 45084021377826544442611469)
                  ·
                    refine ⟨16906508016684954165979301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45084021377826544442611469 16906508016684954165979301)
                    ·
                      refine ⟨3169970253128428906121119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16906508016684954165979301 3169970253128428906121119)
                      ·
                        rfl

theorem cell23_6173495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_6173495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173495 prefixEnd_6173495 := by exact prefixLift 6173495
  have htrace : WordTrace (prefixWord ++ tailWord_6173495) baseStart_6173495 baseEnd_6173495 := by
    simpa [prefixWord, tailWord_6173495, baseEnd_6173495] using wordTrace_append hprefix tailTrace_6173495
  have hstable : (prefixWord ++ tailWord_6173495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173495).length < 2 ^ (prefixWord ++ tailWord_6173495).sum := by decide
  have hdescent : baseEnd_6173495 < baseStart_6173495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173512 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_6173512 : Nat := 118140960795 + 6173512 * 2 ^ 59
def prefixEnd_6173512 : Nat := 4983230072969 + 3 ^ 40 * 6173512 * 2
def baseEnd_6173512 : Nat := 3169978982299555339608541

theorem tailTrace_6173512 : CollatzResearch.WordTrace tailWord_6173512 prefixEnd_6173512 3169978982299555339608541 := by
  unfold tailWord_6173512
  simp only [CollatzResearch.WordTrace]
  refine ⟨112583240405213925376733395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150110987206951900502311193 112583240405213925376733395)
  ·
    refine ⟨168874860607820888065100093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112583240405213925376733395 168874860607820888065100093)
    ·
      refine ⟨63328072727932833024412535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168874860607820888065100093 63328072727932833024412535)
      ·
        refine ⟨94992109091899249536618803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63328072727932833024412535 94992109091899249536618803)
        ·
          refine ⟨142488163637848874304928205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94992109091899249536618803 142488163637848874304928205)
          ·
            refine ⟨53433061364193327864348077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142488163637848874304928205 53433061364193327864348077)
            ·
              refine ⟨20037398011572497949130529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53433061364193327864348077 20037398011572497949130529)
              ·
                refine ⟨15028048508679373461847897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20037398011572497949130529 15028048508679373461847897)
                ·
                  refine ⟨11271036381509530096385923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15028048508679373461847897 11271036381509530096385923)
                  ·
                    refine ⟨16906554572264295144578885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11271036381509530096385923 16906554572264295144578885)
                    ·
                      refine ⟨3169978982299555339608541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16906554572264295144578885 3169978982299555339608541)
                      ·
                        rfl

theorem cell23_6173512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_6173512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173512 prefixEnd_6173512 := by exact prefixLift 6173512
  have htrace : WordTrace (prefixWord ++ tailWord_6173512) baseStart_6173512 baseEnd_6173512 := by
    simpa [prefixWord, tailWord_6173512, baseEnd_6173512] using wordTrace_append hprefix tailTrace_6173512
  have hstable : (prefixWord ++ tailWord_6173512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173512).length < 2 ^ (prefixWord ++ tailWord_6173512).sum := by decide
  have hdescent : baseEnd_6173512 < baseStart_6173512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173515 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 3]
def baseStart_6173515 : Nat := 118140960795 + 6173515 * 2 ^ 59
def prefixEnd_6173515 : Nat := 4983230072969 + 3 ^ 40 * 6173515 * 2
def baseEnd_6173515 : Nat := 3169980522741518827871027

theorem tailTrace_6173515 : CollatzResearch.WordTrace tailWord_6173515 prefixEnd_6173515 3169980522741518827871027 := by
  unfold tailWord_6173515
  simp only [CollatzResearch.WordTrace]
  refine ⟨225166590229416982265825999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150111060152944654843883999 225166590229416982265825999)
  ·
    refine ⟨337749885344125473398738999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225166590229416982265825999 337749885344125473398738999)
    ·
      refine ⟨506624828016188210098108499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337749885344125473398738999 506624828016188210098108499)
      ·
        refine ⟨759937242024282315147162749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506624828016188210098108499 759937242024282315147162749)
        ·
          refine ⟨284976465759105868180186031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 759937242024282315147162749 284976465759105868180186031)
          ·
            refine ⟨427464698638658802270279047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284976465759105868180186031 427464698638658802270279047)
            ·
              refine ⟨641197047957988203405418571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427464698638658802270279047 641197047957988203405418571)
              ·
                refine ⟨961795571936982305108127857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641197047957988203405418571 961795571936982305108127857)
                ·
                  refine ⟨721346678952736728831095893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961795571936982305108127857 721346678952736728831095893)
                  ·
                    refine ⟨8453281393977383540989405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 721346678952736728831095893 8453281393977383540989405)
                    ·
                      refine ⟨3169980522741518827871027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8453281393977383540989405 3169980522741518827871027)
                      ·
                        rfl

theorem cell23_6173515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 3].length) (baseStart_6173515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173515 prefixEnd_6173515 := by exact prefixLift 6173515
  have htrace : WordTrace (prefixWord ++ tailWord_6173515) baseStart_6173515 baseEnd_6173515 := by
    simpa [prefixWord, tailWord_6173515, baseEnd_6173515] using wordTrace_append hprefix tailTrace_6173515
  have hstable : (prefixWord ++ tailWord_6173515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173515).length < 2 ^ (prefixWord ++ tailWord_6173515).sum := by decide
  have hdescent : baseEnd_6173515 < baseStart_6173515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173573 : List Nat := [1, 3, 1, 1, 3, 5, 2, 2, 1, 4]
def baseStart_6173573 : Nat := 118140960795 + 6173573 * 2 ^ 59
def prefixEnd_6173573 : Nat := 4983230072969 + 3 ^ 40 * 6173573 * 2
def baseEnd_6173573 : Nat := 1056670101539826533648587

theorem tailTrace_6173573 : CollatzResearch.WordTrace tailWord_6173573 prefixEnd_6173573 1056670101539826533648587 := by
  unfold tailWord_6173573
  simp only [CollatzResearch.WordTrace]
  refine ⟨225168705663206858171437373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150112470442137905447624915 225168705663206858171437373)
  ·
    refine ⟨84438264623702571814289015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225168705663206858171437373 84438264623702571814289015)
    ·
      refine ⟨126657396935553857721433523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84438264623702571814289015 126657396935553857721433523)
      ·
        refine ⟨189986095403330786582150285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126657396935553857721433523 189986095403330786582150285)
        ·
          refine ⟨71244785776249044968306357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189986095403330786582150285 71244785776249044968306357)
          ·
            refine ⟨6679198666523347965778721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71244785776249044968306357 6679198666523347965778721)
            ·
              refine ⟨5009398999892510974334041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6679198666523347965778721 5009398999892510974334041)
              ·
                refine ⟨3757049249919383230750531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009398999892510974334041 3757049249919383230750531)
                ·
                  refine ⟨5635573874879074846125797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757049249919383230750531 5635573874879074846125797)
                  ·
                    refine ⟨1056670101539826533648587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635573874879074846125797 1056670101539826533648587)
                    ·
                      rfl

theorem cell23_6173573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_6173573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173573 prefixEnd_6173573 := by exact prefixLift 6173573
  have htrace : WordTrace (prefixWord ++ tailWord_6173573) baseStart_6173573 baseEnd_6173573 := by
    simpa [prefixWord, tailWord_6173573, baseEnd_6173573] using wordTrace_append hprefix tailTrace_6173573
  have hstable : (prefixWord ++ tailWord_6173573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173573).length < 2 ^ (prefixWord ++ tailWord_6173573).sum := by decide
  have hdescent : baseEnd_6173573 < baseStart_6173573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173612 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_6173612 : Nat := 118140960795 + 6173612 * 2 ^ 59
def prefixEnd_6173612 : Nat := 4983230072969 + 3 ^ 40 * 6173612 * 2
def baseEnd_6173612 : Nat := 1056676776788334982786027

theorem tailTrace_6173612 : CollatzResearch.WordTrace tailWord_6173612 prefixEnd_6173612 1056676776788334982786027 := by
  unfold tailWord_6173612
  simp only [CollatzResearch.WordTrace]
  refine ⟨112585064055032783916053545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150113418740043711888071393 112585064055032783916053545)
  ·
    refine ⟨84438798041274587937040159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112585064055032783916053545 84438798041274587937040159)
    ·
      refine ⟨126658197061911881905560239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84438798041274587937040159 126658197061911881905560239)
      ·
        refine ⟨189987295592867822858340359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126658197061911881905560239 189987295592867822858340359)
        ·
          refine ⟨284980943389301734287510539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189987295592867822858340359 284980943389301734287510539)
          ·
            refine ⟨427471415083952601431265809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284980943389301734287510539 427471415083952601431265809)
            ·
              refine ⟨320603561312964451073449357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427471415083952601431265809 320603561312964451073449357)
              ·
                refine ⟨120226335492361669152543509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320603561312964451073449357 120226335492361669152543509)
                ·
                  refine ⟨5635609476204453241525477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120226335492361669152543509 5635609476204453241525477)
                  ·
                    refine ⟨1056676776788334982786027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635609476204453241525477 1056676776788334982786027)
                    ·
                      rfl

theorem cell23_6173612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_6173612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173612 prefixEnd_6173612 := by exact prefixLift 6173612
  have htrace : WordTrace (prefixWord ++ tailWord_6173612) baseStart_6173612 baseEnd_6173612 := by
    simpa [prefixWord, tailWord_6173612, baseEnd_6173612] using wordTrace_append hprefix tailTrace_6173612
  have hstable : (prefixWord ++ tailWord_6173612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173612).length < 2 ^ (prefixWord ++ tailWord_6173612).sum := by decide
  have hdescent : baseEnd_6173612 < baseStart_6173612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173656 : List Nat := [2, 1, 2, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_6173656 : Nat := 118140960795 + 6173656 * 2 ^ 59
def prefixEnd_6173656 : Nat := 4983230072969 + 3 ^ 40 * 6173656 * 2
def baseEnd_6173656 : Nat := 3170052923513802776207879

theorem tailTrace_6173656 : CollatzResearch.WordTrace tailWord_6173656 prefixEnd_6173656 3170052923513802776207879 := by
  unfold tailWord_6173656
  simp only [CollatzResearch.WordTrace]
  refine ⟨112585866460953081673354411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150114488614604108897805881 112585866460953081673354411)
  ·
    refine ⟨168878799691429622510031617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112585866460953081673354411 168878799691429622510031617)
    ·
      refine ⟨126659099768572216882523713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168878799691429622510031617 126659099768572216882523713)
      ·
        refine ⟨94994324826429162661892785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126659099768572216882523713 94994324826429162661892785)
        ·
          refine ⟨71245743619821871996419589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94994324826429162661892785 71245743619821871996419589)
          ·
            refine ⟨13358576928716600999328673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71245743619821871996419589 13358576928716600999328673)
            ·
              refine ⟨10018932696537450749496505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13358576928716600999328673 10018932696537450749496505)
              ·
                refine ⟨7514199522403088062122379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10018932696537450749496505 7514199522403088062122379)
                ·
                  refine ⟨11271299283604632093183569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514199522403088062122379 11271299283604632093183569)
                  ·
                    refine ⟨8453474462703474069887677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11271299283604632093183569 8453474462703474069887677)
                    ·
                      refine ⟨3170052923513802776207879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8453474462703474069887677 3170052923513802776207879)
                      ·
                        rfl

theorem cell23_6173656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_6173656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173656 prefixEnd_6173656 := by exact prefixLift 6173656
  have htrace : WordTrace (prefixWord ++ tailWord_6173656) baseStart_6173656 baseEnd_6173656 := by
    simpa [prefixWord, tailWord_6173656, baseEnd_6173656] using wordTrace_append hprefix tailTrace_6173656
  have hstable : (prefixWord ++ tailWord_6173656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173656).length < 2 ^ (prefixWord ++ tailWord_6173656).sum := by decide
  have hdescent : baseEnd_6173656 < baseStart_6173656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173729 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6173729 : Nat := 118140960795 + 6173729 * 2 ^ 59
def prefixEnd_6173729 : Nat := 4983230072969 + 3 ^ 40 * 6173729 * 2
def baseEnd_6173729 : Nat := 3170090407601580990595043

theorem tailTrace_6173729 : CollatzResearch.WordTrace tailWord_6173729 prefixEnd_6173729 3170090407601580990595043 := by
  unfold tailWord_6173729
  simp only [CollatzResearch.WordTrace]
  refine ⟨225174395450641696814116241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150116263633761131209410827 225174395450641696814116241)
  ·
    refine ⟨168880796587981272610587181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225174395450641696814116241 168880796587981272610587181)
    ·
      refine ⟨63330298720492977228970193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168880796587981272610587181 63330298720492977228970193)
      ·
        refine ⟨47497724040369732921727645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63330298720492977228970193 47497724040369732921727645)
        ·
          refine ⟨17811646515138649845647867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47497724040369732921727645 17811646515138649845647867)
          ·
            refine ⟨26717469772707974768471801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17811646515138649845647867 26717469772707974768471801)
            ·
              refine ⟨20038102329530981076353851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26717469772707974768471801 20038102329530981076353851)
              ·
                refine ⟨30057153494296471614530777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20038102329530981076353851 30057153494296471614530777)
                ·
                  refine ⟨22542865120722353710898083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30057153494296471614530777 22542865120722353710898083)
                  ·
                    refine ⟨33814297681083530566347125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22542865120722353710898083 33814297681083530566347125)
                    ·
                      refine ⟨3170090407601580990595043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33814297681083530566347125 3170090407601580990595043)
                      ·
                        rfl

theorem cell23_6173729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6173729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173729 prefixEnd_6173729 := by exact prefixLift 6173729
  have htrace : WordTrace (prefixWord ++ tailWord_6173729) baseStart_6173729 baseEnd_6173729 := by
    simpa [prefixWord, tailWord_6173729, baseEnd_6173729] using wordTrace_append hprefix tailTrace_6173729
  have hstable : (prefixWord ++ tailWord_6173729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173729).length < 2 ^ (prefixWord ++ tailWord_6173729).sum := by decide
  have hdescent : baseEnd_6173729 < baseStart_6173729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173730 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_6173730 : Nat := 118140960795 + 6173730 * 2 ^ 59
def prefixEnd_6173730 : Nat := 4983230072969 + 3 ^ 40 * 6173730 * 2
def baseEnd_6173730 : Nat := 3170090921082235486682539

theorem tailTrace_6173730 : CollatzResearch.WordTrace tailWord_6173730 prefixEnd_6173730 3170090921082235486682539 := by
  unfold tailWord_6173730
  simp only [CollatzResearch.WordTrace]
  refine ⟨56293607980909518496225661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150116287949092049323268429 56293607980909518496225661)
  ·
    refine ⟨21110102992841069436084623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56293607980909518496225661 21110102992841069436084623)
    ·
      refine ⟨31665154489261604154126935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21110102992841069436084623 31665154489261604154126935)
      ·
        refine ⟨47497731733892406231190403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31665154489261604154126935 47497731733892406231190403)
        ·
          refine ⟨71246597600838609346785605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47497731733892406231190403 71246597600838609346785605)
          ·
            refine ⟨13358737050157239252522301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71246597600838609346785605 13358737050157239252522301)
            ·
              refine ⟨5009526393808964719695863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13358737050157239252522301 5009526393808964719695863)
              ·
                refine ⟨7514289590713447079543795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009526393808964719695863 7514289590713447079543795)
                ·
                  refine ⟨11271434386070170619315693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514289590713447079543795 11271434386070170619315693)
                  ·
                    refine ⟨4226787894776313982243385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11271434386070170619315693 4226787894776313982243385)
                    ·
                      refine ⟨3170090921082235486682539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226787894776313982243385 3170090921082235486682539)
                      ·
                        rfl

theorem cell23_6173730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_6173730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173730 prefixEnd_6173730 := by exact prefixLift 6173730
  have htrace : WordTrace (prefixWord ++ tailWord_6173730) baseStart_6173730 baseEnd_6173730 := by
    simpa [prefixWord, tailWord_6173730, baseEnd_6173730] using wordTrace_append hprefix tailTrace_6173730
  have hstable : (prefixWord ++ tailWord_6173730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173730).length < 2 ^ (prefixWord ++ tailWord_6173730).sum := by decide
  have hdescent : baseEnd_6173730 < baseStart_6173730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173766 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_6173766 : Nat := 118140960795 + 6173766 * 2 ^ 59
def prefixEnd_6173766 : Nat := 4983230072969 + 3 ^ 40 * 6173766 * 2
def baseEnd_6173766 : Nat := 352234378487310816203597

theorem tailTrace_6173766 : CollatzResearch.WordTrace tailWord_6173766 prefixEnd_6173766 352234378487310816203597 := by
  unfold tailWord_6173766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036742029734614129162911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150117163301005101422142101 7036742029734614129162911)
  ·
    refine ⟨10555113044601921193744367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7036742029734614129162911 10555113044601921193744367)
    ·
      refine ⟨15832669566902881790616551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10555113044601921193744367 15832669566902881790616551)
      ·
        refine ⟨23749004350354322685924827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15832669566902881790616551 23749004350354322685924827)
        ·
          refine ⟨35623506525531484028887241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23749004350354322685924827 35623506525531484028887241)
          ·
            refine ⟨26717629894148613021665431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35623506525531484028887241 26717629894148613021665431)
            ·
              refine ⟨40076444841222919532498147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26717629894148613021665431 40076444841222919532498147)
              ·
                refine ⟨60114667261834379298747221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40076444841222919532498147 60114667261834379298747221)
                ·
                  refine ⟨352234378487310816203597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60114667261834379298747221 352234378487310816203597)
                  ·
                    rfl

theorem cell23_6173766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_6173766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173766 prefixEnd_6173766 := by exact prefixLift 6173766
  have htrace : WordTrace (prefixWord ++ tailWord_6173766) baseStart_6173766 baseEnd_6173766 := by
    simpa [prefixWord, tailWord_6173766, baseEnd_6173766] using wordTrace_append hprefix tailTrace_6173766
  have hstable : (prefixWord ++ tailWord_6173766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173766).length < 2 ^ (prefixWord ++ tailWord_6173766).sum := by decide
  have hdescent : baseEnd_6173766 < baseStart_6173766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173816 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 2, 4, 2]
def baseStart_6173816 : Nat := 118140960795 + 6173816 * 2 ^ 59
def prefixEnd_6173816 : Nat := 4983230072969 + 3 ^ 40 * 6173816 * 2
def baseEnd_6173816 : Nat := 3170135080418522150207143

theorem tailTrace_6173816 : CollatzResearch.WordTrace tailWord_6173816 prefixEnd_6173816 3170135080418522150207143 := by
  unfold tailWord_6173816
  simp only [CollatzResearch.WordTrace]
  refine ⟨112588784300663255336266651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150118379067551007115022201 112588784300663255336266651)
  ·
    refine ⟨168883176450994883004399977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112588784300663255336266651 168883176450994883004399977)
    ·
      refine ⟨126662382338246162253299983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168883176450994883004399977 126662382338246162253299983)
      ·
        refine ⟨189993573507369243379949975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126662382338246162253299983 189993573507369243379949975)
        ·
          refine ⟨284990360261053865069924963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189993573507369243379949975 284990360261053865069924963)
          ·
            refine ⟨427485540391580797604887445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284990360261053865069924963 427485540391580797604887445)
            ·
              refine ⟨20038384705855349887729099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 427485540391580797604887445 20038384705855349887729099)
              ·
                refine ⟨30057577058783024831593649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20038384705855349887729099 30057577058783024831593649)
                ·
                  refine ⟨22543182794087268623695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30057577058783024831593649 22543182794087268623695237)
                  ·
                    refine ⟨4226846773891362866942857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22543182794087268623695237 4226846773891362866942857)
                    ·
                      refine ⟨3170135080418522150207143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226846773891362866942857 3170135080418522150207143)
                      ·
                        rfl

theorem cell23_6173816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_6173816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173816 prefixEnd_6173816 := by exact prefixLift 6173816
  have htrace : WordTrace (prefixWord ++ tailWord_6173816) baseStart_6173816 baseEnd_6173816 := by
    simpa [prefixWord, tailWord_6173816, baseEnd_6173816] using wordTrace_append hprefix tailTrace_6173816
  have hstable : (prefixWord ++ tailWord_6173816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173816).length < 2 ^ (prefixWord ++ tailWord_6173816).sum := by decide
  have hdescent : baseEnd_6173816 < baseStart_6173816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173843 : List Nat := [1, 1, 1, 2, 1, 2, 7, 3, 1, 4]
def baseStart_6173843 : Nat := 118140960795 + 6173843 * 2 ^ 59
def prefixEnd_6173843 : Nat := 4983230072969 + 3 ^ 40 * 6173843 * 2
def baseEnd_6173843 : Nat := 1056716314798731181523173

theorem tailTrace_6173843 : CollatzResearch.WordTrace tailWord_6173843 prefixEnd_6173843 1056716314798731181523173 := by
  unfold tailWord_6173843
  simp only [CollatzResearch.WordTrace]
  refine ⟨225178553372228694283766183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150119035581485796189177455 225178553372228694283766183)
  ·
    refine ⟨337767830058343041425649275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225178553372228694283766183 337767830058343041425649275)
    ·
      refine ⟨506651745087514562138473913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337767830058343041425649275 506651745087514562138473913)
      ·
        refine ⟨379988808815635921603855435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506651745087514562138473913 379988808815635921603855435)
        ·
          refine ⟨569983213223453882405783153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379988808815635921603855435 569983213223453882405783153)
          ·
            refine ⟨427487409917590411804337365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569983213223453882405783153 427487409917590411804337365)
            ·
              refine ⟨10019236169943525276664157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 427487409917590411804337365 10019236169943525276664157)
              ·
                refine ⟨3757213563728821978749059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10019236169943525276664157 3757213563728821978749059)
                ·
                  refine ⟨5635820345593232968123589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757213563728821978749059 5635820345593232968123589)
                  ·
                    refine ⟨1056716314798731181523173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5635820345593232968123589 1056716314798731181523173)
                    ·
                      rfl

theorem cell23_6173843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 1, 4].length) (baseStart_6173843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173843 prefixEnd_6173843 := by exact prefixLift 6173843
  have htrace : WordTrace (prefixWord ++ tailWord_6173843) baseStart_6173843 baseEnd_6173843 := by
    simpa [prefixWord, tailWord_6173843, baseEnd_6173843] using wordTrace_append hprefix tailTrace_6173843
  have hstable : (prefixWord ++ tailWord_6173843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173843).length < 2 ^ (prefixWord ++ tailWord_6173843).sum := by decide
  have hdescent : baseEnd_6173843 < baseStart_6173843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173873 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 6]
def baseStart_6173873 : Nat := 118140960795 + 6173873 * 2 ^ 59
def prefixEnd_6173873 : Nat := 4983230072969 + 3 ^ 40 * 6173873 * 2
def baseEnd_6173873 : Nat := 352240483201758714132709

theorem tailTrace_6173873 : CollatzResearch.WordTrace tailWord_6173873 prefixEnd_6173873 352240483201758714132709 := by
  unfold tailWord_6173873
  simp only [CollatzResearch.WordTrace]
  refine ⟨225179647562120009407358273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150119765041413339604905515 225179647562120009407358273)
  ·
    refine ⟨168884735671590007055518705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225179647562120009407358273 168884735671590007055518705)
    ·
      refine ⟨126663551753692505291639029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168884735671590007055518705 126663551753692505291639029)
      ·
        refine ⟨11874707976908672371091159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126663551753692505291639029 11874707976908672371091159)
        ·
          refine ⟨17812061965363008556636739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11874707976908672371091159 17812061965363008556636739)
          ·
            refine ⟨26718092948044512834955109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17812061965363008556636739 26718092948044512834955109)
            ·
              refine ⟨5009642427758346156554083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26718092948044512834955109 5009642427758346156554083)
              ·
                refine ⟨7514463641637519234831125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009642427758346156554083 7514463641637519234831125)
                ·
                  refine ⟨352240483201758714132709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7514463641637519234831125 352240483201758714132709)
                  ·
                    rfl

theorem cell23_6173873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 6].length) (baseStart_6173873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173873 prefixEnd_6173873 := by exact prefixLift 6173873
  have htrace : WordTrace (prefixWord ++ tailWord_6173873) baseStart_6173873 baseEnd_6173873 := by
    simpa [prefixWord, tailWord_6173873, baseEnd_6173873] using wordTrace_append hprefix tailTrace_6173873
  have hstable : (prefixWord ++ tailWord_6173873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173873).length < 2 ^ (prefixWord ++ tailWord_6173873).sum := by decide
  have hdescent : baseEnd_6173873 < baseStart_6173873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173919 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_6173919 : Nat := 118140960795 + 6173919 * 2 ^ 59
def prefixEnd_6173919 : Nat := 4983230072969 + 3 ^ 40 * 6173919 * 2
def baseEnd_6173919 : Nat := 3170187968925935247219169

theorem tailTrace_6173919 : CollatzResearch.WordTrace tailWord_6173919 prefixEnd_6173919 3170187968925935247219169 := by
  unfold tailWord_6173919
  simp only [CollatzResearch.WordTrace]
  refine ⟨225181325319953359263532811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150120883546635572842355207 225181325319953359263532811)
  ·
    refine ⟨337771987979930038895299217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225181325319953359263532811 337771987979930038895299217)
    ·
      refine ⟨253328990984947529171474413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337771987979930038895299217 253328990984947529171474413)
      ·
        refine ⟨94998371619355323439302905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253328990984947529171474413 94998371619355323439302905)
        ·
          refine ⟨71248778714516492579477179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94998371619355323439302905 71248778714516492579477179)
          ·
            refine ⟨106873168071774738869215769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71248778714516492579477179 106873168071774738869215769)
            ·
              refine ⟨80154876053831054151911827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106873168071774738869215769 80154876053831054151911827)
              ·
                refine ⟨120232314080746581227867741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80154876053831054151911827 120232314080746581227867741)
                ·
                  refine ⟨45087117780279967960450403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120232314080746581227867741 45087117780279967960450403)
                  ·
                    refine ⟨67630676670419951940675605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45087117780279967960450403 67630676670419951940675605)
                    ·
                      refine ⟨3170187968925935247219169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67630676670419951940675605 3170187968925935247219169)
                      ·
                        rfl

theorem cell23_6173919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_6173919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173919 prefixEnd_6173919 := by exact prefixLift 6173919
  have htrace : WordTrace (prefixWord ++ tailWord_6173919) baseStart_6173919 baseEnd_6173919 := by
    simpa [prefixWord, tailWord_6173919, baseEnd_6173919] using wordTrace_append hprefix tailTrace_6173919
  have hstable : (prefixWord ++ tailWord_6173919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173919).length < 2 ^ (prefixWord ++ tailWord_6173919).sum := by decide
  have hdescent : baseEnd_6173919 < baseStart_6173919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173933 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_6173933 : Nat := 118140960795 + 6173933 * 2 ^ 59
def prefixEnd_6173933 : Nat := 4983230072969 + 3 ^ 40 * 6173933 * 2
def baseEnd_6173933 : Nat := 1056731719218366064148035

theorem tailTrace_6173933 : CollatzResearch.WordTrace tailWord_6173933 prefixEnd_6173933 1056731719218366064148035 := by
  unfold tailWord_6173933
  simp only [CollatzResearch.WordTrace]
  refine ⟨225181835941902639654542453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150121223961268426436361635 225181835941902639654542453)
  ·
    refine ⟨21110797119553372467613355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225181835941902639654542453 21110797119553372467613355)
    ·
      refine ⟨31666195679330058701420033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21110797119553372467613355 31666195679330058701420033)
      ·
        refine ⟨23749646759497544026065025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31666195679330058701420033 23749646759497544026065025)
        ·
          refine ⟨17812235069623158019548769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23749646759497544026065025 17812235069623158019548769)
          ·
            refine ⟨13359176302217368514661577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17812235069623158019548769 13359176302217368514661577)
            ·
              refine ⟨10019382226663026385996183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13359176302217368514661577 10019382226663026385996183)
              ·
                refine ⟨15029073339994539578994275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10019382226663026385996183 15029073339994539578994275)
                ·
                  refine ⟨22543610009991809368491413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15029073339994539578994275 22543610009991809368491413)
                  ·
                    refine ⟨1056731719218366064148035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22543610009991809368491413 1056731719218366064148035)
                    ·
                      rfl

theorem cell23_6173933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_6173933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173933 prefixEnd_6173933 := by exact prefixLift 6173933
  have htrace : WordTrace (prefixWord ++ tailWord_6173933) baseStart_6173933 baseEnd_6173933 := by
    simpa [prefixWord, tailWord_6173933, baseEnd_6173933] using wordTrace_append hprefix tailTrace_6173933
  have hstable : (prefixWord ++ tailWord_6173933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173933).length < 2 ^ (prefixWord ++ tailWord_6173933).sum := by decide
  have hdescent : baseEnd_6173933 < baseStart_6173933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173946 : List Nat := [3, 1, 1, 1, 1, 4, 5, 7]
def baseStart_6173946 : Nat := 118140960795 + 6173946 * 2 ^ 59
def prefixEnd_6173946 : Nat := 4983230072969 + 3 ^ 40 * 6173946 * 2
def baseEnd_6173946 : Nat := 117414882700133579317835

theorem tailTrace_6173946 : CollatzResearch.WordTrace tailWord_6173946 prefixEnd_6173946 117414882700133579317835 := by
  unfold tailWord_6173946
  simp only [CollatzResearch.WordTrace]
  refine ⟨56295577522713885718691423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150121540060570361916510461 56295577522713885718691423)
  ·
    refine ⟨84443366284070828578037135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56295577522713885718691423 84443366284070828578037135)
    ·
      refine ⟨126665049426106242867055703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84443366284070828578037135 126665049426106242867055703)
      ·
        refine ⟨189997574139159364300583555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126665049426106242867055703 189997574139159364300583555)
        ·
          refine ⟨284996361208739046450875333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189997574139159364300583555 284996361208739046450875333)
          ·
            refine ⟨53436817726638571209539125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 284996361208739046450875333 53436817726638571209539125)
            ·
              refine ⟨5009701661872366050894293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53436817726638571209539125 5009701661872366050894293)
              ·
                refine ⟨117414882700133579317835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5009701661872366050894293 117414882700133579317835)
                ·
                  rfl

theorem cell23_6173946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_6173946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173946 prefixEnd_6173946 := by exact prefixLift 6173946
  have htrace : WordTrace (prefixWord ++ tailWord_6173946) baseStart_6173946 baseEnd_6173946 := by
    simpa [prefixWord, tailWord_6173946, baseEnd_6173946] using wordTrace_append hprefix tailTrace_6173946
  have hstable : (prefixWord ++ tailWord_6173946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173946).length < 2 ^ (prefixWord ++ tailWord_6173946).sum := by decide
  have hdescent : baseEnd_6173946 < baseStart_6173946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173954 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6173954 : Nat := 118140960795 + 6173954 * 2 ^ 59
def prefixEnd_6173954 : Nat := 4983230072969 + 3 ^ 40 * 6173954 * 2
def baseEnd_6173954 : Nat := 1056735313582947536760503

theorem tailTrace_6173954 : CollatzResearch.WordTrace tailWord_6173954 prefixEnd_6173954 1056735313582947536760503 := by
  unfold tailWord_6173954
  simp only [CollatzResearch.WordTrace]
  refine ⟨56295650468706640060264229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150121734583217706827371277 56295650468706640060264229)
  ·
    refine ⟨10555434462882495011299543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56295650468706640060264229 10555434462882495011299543)
    ·
      refine ⟨15833151694323742516949315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10555434462882495011299543 15833151694323742516949315)
      ·
        refine ⟨23749727541485613775423973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15833151694323742516949315 23749727541485613775423973)
        ·
          refine ⟨4453073914028552582891995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23749727541485613775423973 4453073914028552582891995)
          ·
            refine ⟨6679610871042828874337993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453073914028552582891995 6679610871042828874337993)
            ·
              refine ⟨5009708153282121655753495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6679610871042828874337993 5009708153282121655753495)
              ·
                refine ⟨7514562229923182483630243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009708153282121655753495 7514562229923182483630243)
                ·
                  refine ⟨11271843344884773725445365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514562229923182483630243 11271843344884773725445365)
                  ·
                    refine ⟨1056735313582947536760503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11271843344884773725445365 1056735313582947536760503)
                    ·
                      rfl

theorem cell23_6173954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6173954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173954 prefixEnd_6173954 := by exact prefixLift 6173954
  have htrace : WordTrace (prefixWord ++ tailWord_6173954) baseStart_6173954 baseEnd_6173954 := by
    simpa [prefixWord, tailWord_6173954, baseEnd_6173954] using wordTrace_append hprefix tailTrace_6173954
  have hstable : (prefixWord ++ tailWord_6173954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173954).length < 2 ^ (prefixWord ++ tailWord_6173954).sum := by decide
  have hdescent : baseEnd_6173954 < baseStart_6173954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173957 : List Nat := [1, 3, 1, 1, 2, 1, 6, 3, 1, 2, 2]
def baseStart_6173957 : Nat := 118140960795 + 6173957 * 2 ^ 59
def prefixEnd_6173957 : Nat := 4983230072969 + 3 ^ 40 * 6173957 * 2
def baseEnd_6173957 : Nat := 3170207481190806098543995

theorem tailTrace_6173957 : CollatzResearch.WordTrace tailWord_6173957 prefixEnd_6173957 3170207481190806098543995 := by
  unfold tailWord_6173957
  simp only [CollatzResearch.WordTrace]
  refine ⟨225182711293815691753416125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150121807529210461168944083 225182711293815691753416125)
  ·
    refine ⟨84443516735180884407531047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225182711293815691753416125 84443516735180884407531047)
    ·
      refine ⟨126665275102771326611296571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84443516735180884407531047 126665275102771326611296571)
      ·
        refine ⟨189997912654156989916944857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126665275102771326611296571 189997912654156989916944857)
        ·
          refine ⟨142498434490617742437708643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189997912654156989916944857 142498434490617742437708643)
          ·
            refine ⟨213747651735926613656562965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142498434490617742437708643 213747651735926613656562965)
            ·
              refine ⟨10019421175121560015151389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213747651735926613656562965 10019421175121560015151389)
              ·
                refine ⟨3757282940670585005681771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10019421175121560015151389 3757282940670585005681771)
                ·
                  refine ⟨5635924411005877508522657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757282940670585005681771 5635924411005877508522657)
                  ·
                    refine ⟨4226943308254408131391993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5635924411005877508522657 4226943308254408131391993)
                    ·
                      refine ⟨3170207481190806098543995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226943308254408131391993 3170207481190806098543995)
                      ·
                        rfl

theorem cell23_6173957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_6173957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173957 prefixEnd_6173957 := by exact prefixLift 6173957
  have htrace : WordTrace (prefixWord ++ tailWord_6173957) baseStart_6173957 baseEnd_6173957 := by
    simpa [prefixWord, tailWord_6173957, baseEnd_6173957] using wordTrace_append hprefix tailTrace_6173957
  have hstable : (prefixWord ++ tailWord_6173957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173957).length < 2 ^ (prefixWord ++ tailWord_6173957).sum := by decide
  have hdescent : baseEnd_6173957 < baseStart_6173957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6173960 : List Nat := [2, 1, 3, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_6173960 : Nat := 118140960795 + 6173960 * 2 ^ 59
def prefixEnd_6173960 : Nat := 4983230072969 + 3 ^ 40 * 6173960 * 2
def baseEnd_6173960 : Nat := 3170209021632769586806481

theorem tailTrace_6173960 : CollatzResearch.WordTrace tailWord_6173960 prefixEnd_6173960 3170209021632769586806481 := by
  unfold tailWord_6173960
  simp only [CollatzResearch.WordTrace]
  refine ⟨112591410356402411632887667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150121880475203215510516889 112591410356402411632887667)
  ·
    refine ⟨168887115534603617449331501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112591410356402411632887667 168887115534603617449331501)
    ·
      refine ⟨63332668325476356543499313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168887115534603617449331501 63332668325476356543499313)
      ·
        refine ⟨47499501244107267407624485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63332668325476356543499313 47499501244107267407624485)
        ·
          refine ⟨8906156483270112638929591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47499501244107267407624485 8906156483270112638929591)
          ·
            refine ⟨13359234724905168958394387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8906156483270112638929591 13359234724905168958394387)
            ·
              refine ⟨20038852087357753437591581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13359234724905168958394387 20038852087357753437591581)
              ·
                refine ⟨7514569532759157539096843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20038852087357753437591581 7514569532759157539096843)
                ·
                  refine ⟨11271854299138736308645265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514569532759157539096843 11271854299138736308645265)
                  ·
                    refine ⟨8453890724354052231483949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11271854299138736308645265 8453890724354052231483949)
                    ·
                      refine ⟨3170209021632769586806481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8453890724354052231483949 3170209021632769586806481)
                      ·
                        rfl

theorem cell23_6173960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_6173960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6173960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6173960 prefixEnd_6173960 := by exact prefixLift 6173960
  have htrace : WordTrace (prefixWord ++ tailWord_6173960) baseStart_6173960 baseEnd_6173960 := by
    simpa [prefixWord, tailWord_6173960, baseEnd_6173960] using wordTrace_append hprefix tailTrace_6173960
  have hstable : (prefixWord ++ tailWord_6173960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6173960).length < 2 ^ (prefixWord ++ tailWord_6173960).sum := by decide
  have hdescent : baseEnd_6173960 < baseStart_6173960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6173960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174000 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 1, 3, 2]
def baseStart_6174000 : Nat := 118140960795 + 6174000 * 2 ^ 59
def prefixEnd_6174000 : Nat := 4983230072969 + 3 ^ 40 * 6174000 * 2
def baseEnd_6174000 : Nat := 3170229560858949430306297

theorem tailTrace_6174000 : CollatzResearch.WordTrace tailWord_6174000 prefixEnd_6174000 3170229560858949430306297 := by
  unfold tailWord_6174000
  simp only [CollatzResearch.WordTrace]
  refine ⟨112592139816329955048615727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150122853088439940064820969 112592139816329955048615727)
  ·
    refine ⟨168888209724494932572923591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112592139816329955048615727 168888209724494932572923591)
    ·
      refine ⟨253332314586742398859385387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168888209724494932572923591 253332314586742398859385387)
      ·
        refine ⟨379998471880113598289078081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253332314586742398859385387 379998471880113598289078081)
        ·
          refine ⟨284998853910085198716808561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379998471880113598289078081 284998853910085198716808561)
          ·
            refine ⟨213749140432563899037606421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284998853910085198716808561 213749140432563899037606421)
            ·
              refine ⟨10019490957776432767387801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213749140432563899037606421 10019490957776432767387801)
              ·
                refine ⟨7514618218332324575540851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10019490957776432767387801 7514618218332324575540851)
                ·
                  refine ⟨11271927327498486863311277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514618218332324575540851 11271927327498486863311277)
                  ·
                    refine ⟨4226972747811932573741729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11271927327498486863311277 4226972747811932573741729)
                    ·
                      refine ⟨3170229560858949430306297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226972747811932573741729 3170229560858949430306297)
                      ·
                        rfl

theorem cell23_6174000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 1, 3, 2].length) (baseStart_6174000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174000 prefixEnd_6174000 := by exact prefixLift 6174000
  have htrace : WordTrace (prefixWord ++ tailWord_6174000) baseStart_6174000 baseEnd_6174000 := by
    simpa [prefixWord, tailWord_6174000, baseEnd_6174000] using wordTrace_append hprefix tailTrace_6174000
  have hstable : (prefixWord ++ tailWord_6174000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174000).length < 2 ^ (prefixWord ++ tailWord_6174000).sum := by decide
  have hdescent : baseEnd_6174000 < baseStart_6174000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174016 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_6174016 : Nat := 118140960795 + 6174016 * 2 ^ 59
def prefixEnd_6174016 : Nat := 4983230072969 + 3 ^ 40 * 6174016 * 2
def baseEnd_6174016 : Nat := 3170237776549421367706223

theorem tailTrace_6174016 : CollatzResearch.WordTrace tailWord_6174016 prefixEnd_6174016 3170237776549421367706223 := by
  unfold tailWord_6174016
  simp only [CollatzResearch.WordTrace]
  refine ⟨112592431600300972414906951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150123242133734629886542601 112592431600300972414906951)
  ·
    refine ⟨168888647400451458622360427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112592431600300972414906951 168888647400451458622360427)
    ·
      refine ⟨253332971100677187933540641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168888647400451458622360427 253332971100677187933540641)
      ·
        refine ⟨189999728325507890950155481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253332971100677187933540641 189999728325507890950155481)
        ·
          refine ⟨142499796244130918212616611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189999728325507890950155481 142499796244130918212616611)
          ·
            refine ⟨213749694366196377318924917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142499796244130918212616611 213749694366196377318924917)
            ·
              refine ⟨20039033846830910373649211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213749694366196377318924917 20039033846830910373649211)
              ·
                refine ⟨30058550770246365560473817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20039033846830910373649211 30058550770246365560473817)
                ·
                  refine ⟨22543913077684774170355363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30058550770246365560473817 22543913077684774170355363)
                  ·
                    refine ⟨33815869616527161255533045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22543913077684774170355363 33815869616527161255533045)
                    ·
                      refine ⟨3170237776549421367706223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33815869616527161255533045 3170237776549421367706223)
                      ·
                        rfl

theorem cell23_6174016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_6174016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174016 prefixEnd_6174016 := by exact prefixLift 6174016
  have htrace : WordTrace (prefixWord ++ tailWord_6174016) baseStart_6174016 baseEnd_6174016 := by
    simpa [prefixWord, tailWord_6174016, baseEnd_6174016] using wordTrace_append hprefix tailTrace_6174016
  have hstable : (prefixWord ++ tailWord_6174016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174016).length < 2 ^ (prefixWord ++ tailWord_6174016).sum := by decide
  have hdescent : baseEnd_6174016 < baseStart_6174016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174017 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6174017 : Nat := 118140960795 + 6174017 * 2 ^ 59
def prefixEnd_6174017 : Nat := 4983230072969 + 3 ^ 40 * 6174017 * 2
def baseEnd_6174017 : Nat := 3170238290030075863793719

theorem tailTrace_6174017 : CollatzResearch.WordTrace tailWord_6174017 prefixEnd_6174017 3170238290030075863793719 := by
  unfold tailWord_6174017
  simp only [CollatzResearch.WordTrace]
  refine ⟨225184899673598322000600305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150123266449065548000400203 225184899673598322000600305)
  ·
    refine ⟨168888674755198741500450229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225184899673598322000600305 168888674755198741500450229)
    ·
      refine ⟨15833313258299882015667209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168888674755198741500450229 15833313258299882015667209)
      ·
        refine ⟨11874984943724911511750407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15833313258299882015667209 11874984943724911511750407)
        ·
          refine ⟨17812477415587367267625611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11874984943724911511750407 17812477415587367267625611)
          ·
            refine ⟨26718716123381050901438417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17812477415587367267625611 26718716123381050901438417)
            ·
              refine ⟨20039037092535788176078813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26718716123381050901438417 20039037092535788176078813)
              ·
                refine ⟨7514638909700920566029555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20039037092535788176078813 7514638909700920566029555)
                ·
                  refine ⟨11271958364551380849044333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514638909700920566029555 11271958364551380849044333)
                  ·
                    refine ⟨4226984386706767818391625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11271958364551380849044333 4226984386706767818391625)
                    ·
                      refine ⟨3170238290030075863793719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226984386706767818391625 3170238290030075863793719)
                      ·
                        rfl

theorem cell23_6174017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6174017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174017 prefixEnd_6174017 := by exact prefixLift 6174017
  have htrace : WordTrace (prefixWord ++ tailWord_6174017) baseStart_6174017 baseEnd_6174017 := by
    simpa [prefixWord, tailWord_6174017, baseEnd_6174017] using wordTrace_append hprefix tailTrace_6174017
  have hstable : (prefixWord ++ tailWord_6174017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174017).length < 2 ^ (prefixWord ++ tailWord_6174017).sum := by decide
  have hdescent : baseEnd_6174017 < baseStart_6174017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174026 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_6174026 : Nat := 118140960795 + 6174026 * 2 ^ 59
def prefixEnd_6174026 : Nat := 4983230072969 + 3 ^ 40 * 6174026 * 2
def baseEnd_6174026 : Nat := 3170242911355966328581177

theorem tailTrace_6174026 : CollatzResearch.WordTrace tailWord_6174026 prefixEnd_6174026 3170242911355966328581177 := by
  unfold tailWord_6174026
  simp only [CollatzResearch.WordTrace]
  refine ⟨56296306982641429134419483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150123485287043811025118621 56296306982641429134419483)
  ·
    refine ⟨84444460473962143701629225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56296306982641429134419483 84444460473962143701629225)
    ·
      refine ⟨63333345355471607776221919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84444460473962143701629225 63333345355471607776221919)
      ·
        refine ⟨95000018033207411664332879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63333345355471607776221919 95000018033207411664332879)
        ·
          refine ⟨142500027049811117496499319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95000018033207411664332879 142500027049811117496499319)
          ·
            refine ⟨213750040574716676244748979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142500027049811117496499319 213750040574716676244748979)
            ·
              refine ⟨320625060862075014367123469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213750040574716676244748979 320625060862075014367123469)
              ·
                refine ⟨120234397823278130387671301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 320625060862075014367123469 120234397823278130387671301)
                ·
                  refine ⟨22543949591864649447688369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120234397823278130387671301 22543949591864649447688369)
                  ·
                    refine ⟨16907962193898487085766277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22543949591864649447688369 16907962193898487085766277)
                    ·
                      refine ⟨3170242911355966328581177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16907962193898487085766277 3170242911355966328581177)
                      ·
                        rfl

theorem cell23_6174026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_6174026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174026 prefixEnd_6174026 := by exact prefixLift 6174026
  have htrace : WordTrace (prefixWord ++ tailWord_6174026) baseStart_6174026 baseEnd_6174026 := by
    simpa [prefixWord, tailWord_6174026, baseEnd_6174026] using wordTrace_append hprefix tailTrace_6174026
  have hstable : (prefixWord ++ tailWord_6174026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174026).length < 2 ^ (prefixWord ++ tailWord_6174026).sum := by decide
  have hdescent : baseEnd_6174026 < baseStart_6174026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174030 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_6174030 : Nat := 118140960795 + 6174030 * 2 ^ 59
def prefixEnd_6174030 : Nat := 4983230072969 + 3 ^ 40 * 6174030 * 2
def baseEnd_6174030 : Nat := 3170244965278584312931159

theorem tailTrace_6174030 : CollatzResearch.WordTrace tailWord_6174030 prefixEnd_6174030 3170244965278584312931159 := by
  unfold tailWord_6174030
  simp only [CollatzResearch.WordTrace]
  refine ⟨28148171727818903152602943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150123582548367483480549029 28148171727818903152602943)
  ·
    refine ⟨42222257591728354728904415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28148171727818903152602943 42222257591728354728904415)
    ·
      refine ⟨63333386387592532093356623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42222257591728354728904415 63333386387592532093356623)
      ·
        refine ⟨95000079581388798140034935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63333386387592532093356623 95000079581388798140034935)
        ·
          refine ⟨142500119372083197210052403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95000079581388798140034935 142500119372083197210052403)
          ·
            refine ⟨213750179058124795815078605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142500119372083197210052403 213750179058124795815078605)
            ·
              refine ⟨80156317146796798430654477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213750179058124795815078605 80156317146796798430654477)
              ·
                refine ⟨30058618930048799411495429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80156317146796798430654477 30058618930048799411495429)
                ·
                  refine ⟨5635991049384149889655393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30058618930048799411495429 5635991049384149889655393)
                  ·
                    refine ⟨4226993287038112417241545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5635991049384149889655393 4226993287038112417241545)
                    ·
                      refine ⟨3170244965278584312931159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4226993287038112417241545 3170244965278584312931159)
                      ·
                        rfl

theorem cell23_6174030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_6174030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174030 prefixEnd_6174030 := by exact prefixLift 6174030
  have htrace : WordTrace (prefixWord ++ tailWord_6174030) baseStart_6174030 baseEnd_6174030 := by
    simpa [prefixWord, tailWord_6174030, baseEnd_6174030] using wordTrace_append hprefix tailTrace_6174030
  have hstable : (prefixWord ++ tailWord_6174030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174030).length < 2 ^ (prefixWord ++ tailWord_6174030).sum := by decide
  have hdescent : baseEnd_6174030 < baseStart_6174030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174076 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_6174076 : Nat := 118140960795 + 6174076 * 2 ^ 59
def prefixEnd_6174076 : Nat := 4983230072969 + 3 ^ 40 * 6174076 * 2
def baseEnd_6174076 : Nat := 3170268585388691132955947

theorem tailTrace_6174076 : CollatzResearch.WordTrace tailWord_6174076 prefixEnd_6174076 3170268585388691132955947 := by
  unfold tailWord_6174076
  simp only [CollatzResearch.WordTrace]
  refine ⟨112593525790192287538499041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150124701053589716717998721 112593525790192287538499041)
  ·
    refine ⟨84445144342644215653874281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112593525790192287538499041 84445144342644215653874281)
    ·
      refine ⟨63333858256983161740405711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84445144342644215653874281 63333858256983161740405711)
      ·
        refine ⟨95000787385474742610608567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63333858256983161740405711 95000787385474742610608567)
        ·
          refine ⟨142501181078212113915912851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95000787385474742610608567 142501181078212113915912851)
          ·
            refine ⟨213751771617318170873869277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142501181078212113915912851 213751771617318170873869277)
            ·
              refine ⟨80156914356494314077700979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213751771617318170873869277 80156914356494314077700979)
              ·
                refine ⟨120235371534741471116551469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80156914356494314077700979 120235371534741471116551469)
                ·
                  refine ⟨45088264325528051668706801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120235371534741471116551469 45088264325528051668706801)
                  ·
                    refine ⟨33816198244146038751530101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45088264325528051668706801 33816198244146038751530101)
                    ·
                      refine ⟨3170268585388691132955947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33816198244146038751530101 3170268585388691132955947)
                      ·
                        rfl

theorem cell23_6174076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_6174076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174076 prefixEnd_6174076 := by exact prefixLift 6174076
  have htrace : WordTrace (prefixWord ++ tailWord_6174076) baseStart_6174076 baseEnd_6174076 := by
    simpa [prefixWord, tailWord_6174076, baseEnd_6174076] using wordTrace_append hprefix tailTrace_6174076
  have hstable : (prefixWord ++ tailWord_6174076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174076).length < 2 ^ (prefixWord ++ tailWord_6174076).sum := by decide
  have hdescent : baseEnd_6174076 < baseStart_6174076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174083 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 2, 5]
def baseStart_6174083 : Nat := 118140960795 + 6174083 * 2 ^ 59
def prefixEnd_6174083 : Nat := 4983230072969 + 3 ^ 40 * 6174083 * 2
def baseEnd_6174083 : Nat := 1056757393251090868522805

theorem tailTrace_6174083 : CollatzResearch.WordTrace tailWord_6174083 prefixEnd_6174083 1056757393251090868522805 := by
  unfold tailWord_6174083
  simp only [CollatzResearch.WordTrace]
  refine ⟨225187306891359215272502903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150124871260906143515001935 225187306891359215272502903)
  ·
    refine ⟨337780960337038822908754355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225187306891359215272502903 337780960337038822908754355)
    ·
      refine ⟨506671440505558234363131533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337780960337038822908754355 506671440505558234363131533)
      ·
        refine ⟨190001790189584337886174325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 506671440505558234363131533 190001790189584337886174325)
        ·
          refine ⟨17812667830273531676828843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190001790189584337886174325 17812667830273531676828843)
          ·
            refine ⟨26719001745410297515243265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17812667830273531676828843 26719001745410297515243265)
            ·
              refine ⟨20039251309057723136432449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26719001745410297515243265 20039251309057723136432449)
              ·
                refine ⟨15029438481793292352324337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20039251309057723136432449 15029438481793292352324337)
                ·
                  refine ⟨11272078861344969264243253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15029438481793292352324337 11272078861344969264243253)
                  ·
                    refine ⟨1056757393251090868522805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11272078861344969264243253 1056757393251090868522805)
                    ·
                      rfl

theorem cell23_6174083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 5].length) (baseStart_6174083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174083 prefixEnd_6174083 := by exact prefixLift 6174083
  have htrace : WordTrace (prefixWord ++ tailWord_6174083) baseStart_6174083 baseEnd_6174083 := by
    simpa [prefixWord, tailWord_6174083, baseEnd_6174083] using wordTrace_append hprefix tailTrace_6174083
  have hstable : (prefixWord ++ tailWord_6174083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174083).length < 2 ^ (prefixWord ++ tailWord_6174083).sum := by decide
  have hdescent : baseEnd_6174083 < baseStart_6174083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174087 : List Nat := [1, 1, 4, 2, 2, 4, 2, 2, 5]
def baseStart_6174087 : Nat := 118140960795 + 6174087 * 2 ^ 59
def prefixEnd_6174087 : Nat := 4983230072969 + 3 ^ 40 * 6174087 * 2
def baseEnd_6174087 : Nat := 352252692630654509990933

theorem tailTrace_6174087 : CollatzResearch.WordTrace tailWord_6174087 prefixEnd_6174087 352252692630654509990933 := by
  unfold tailWord_6174087
  simp only [CollatzResearch.WordTrace]
  refine ⟨225187452783344723955648515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150124968522229815970432343 225187452783344723955648515)
  ·
    refine ⟨337781179175017085933472773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225187452783344723955648515 337781179175017085933472773)
    ·
      refine ⟨63333971095315703612526145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337781179175017085933472773 63333971095315703612526145)
      ·
        refine ⟨47500478321486777709394609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63333971095315703612526145 47500478321486777709394609)
        ·
          refine ⟨35625358741115083282045957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47500478321486777709394609 35625358741115083282045957)
          ·
            refine ⟨6679754763959078115383617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35625358741115083282045957 6679754763959078115383617)
            ·
              refine ⟨5009816072969308586537713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6679754763959078115383617 5009816072969308586537713)
              ·
                refine ⟨3757362054726981439903285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009816072969308586537713 3757362054726981439903285)
                ·
                  refine ⟨352252692630654509990933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3757362054726981439903285 352252692630654509990933)
                  ·
                    rfl

theorem cell23_6174087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 5].length) (baseStart_6174087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174087 prefixEnd_6174087 := by exact prefixLift 6174087
  have htrace : WordTrace (prefixWord ++ tailWord_6174087) baseStart_6174087 baseEnd_6174087 := by
    simpa [prefixWord, tailWord_6174087, baseEnd_6174087] using wordTrace_append hprefix tailTrace_6174087
  have hstable : (prefixWord ++ tailWord_6174087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174087).length < 2 ^ (prefixWord ++ tailWord_6174087).sum := by decide
  have hdescent : baseEnd_6174087 < baseStart_6174087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174133 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_6174133 : Nat := 118140960795 + 6174133 * 2 ^ 59
def prefixEnd_6174133 : Nat := 4983230072969 + 3 ^ 40 * 6174133 * 2
def baseEnd_6174133 : Nat := 3170297853785997409943185

theorem tailTrace_6174133 : CollatzResearch.WordTrace tailWord_6174133 prefixEnd_6174133 3170297853785997409943185 := by
  unfold tailWord_6174133
  simp only [CollatzResearch.WordTrace]
  refine ⟨225189130541178073811823053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150126087027452049207882035 225189130541178073811823053)
  ·
    refine ⟨84445923952941777679433645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225189130541178073811823053 84445923952941777679433645)
    ·
      refine ⟨31667221482353166629787617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84445923952941777679433645 31667221482353166629787617)
      ·
        refine ⟨23750416111764874972340713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31667221482353166629787617 23750416111764874972340713)
        ·
          refine ⟨17812812083823656229255535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23750416111764874972340713 17812812083823656229255535)
          ·
            refine ⟨26719218125735484343883303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17812812083823656229255535 26719218125735484343883303)
            ·
              refine ⟨40078827188603226515824955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26719218125735484343883303 40078827188603226515824955)
              ·
                refine ⟨60118240782904839773737433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40078827188603226515824955 60118240782904839773737433)
                ·
                  refine ⟨45088680587178629830303075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60118240782904839773737433 45088680587178629830303075)
                  ·
                    refine ⟨67633020880767944745454613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45088680587178629830303075 67633020880767944745454613)
                    ·
                      refine ⟨3170297853785997409943185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67633020880767944745454613 3170297853785997409943185)
                      ·
                        rfl

theorem cell23_6174133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_6174133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174133 prefixEnd_6174133 := by exact prefixLift 6174133
  have htrace : WordTrace (prefixWord ++ tailWord_6174133) baseStart_6174133 baseEnd_6174133 := by
    simpa [prefixWord, tailWord_6174133, baseEnd_6174133] using wordTrace_append hprefix tailTrace_6174133
  have hstable : (prefixWord ++ tailWord_6174133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174133).length < 2 ^ (prefixWord ++ tailWord_6174133).sum := by decide
  have hdescent : baseEnd_6174133 < baseStart_6174133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174180 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_6174180 : Nat := 118140960795 + 6174180 * 2 ^ 59
def prefixEnd_6174180 : Nat := 4983230072969 + 3 ^ 40 * 6174180 * 2
def baseEnd_6174180 : Nat := 3170321987376758726055469

theorem tailTrace_6174180 : CollatzResearch.WordTrace tailWord_6174180 prefixEnd_6174180 3170321987376758726055469 := by
  unfold tailWord_6174180
  simp only [CollatzResearch.WordTrace]
  refine ⟨112595422386003900419391997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150127229848005200559189329 112595422386003900419391997)
  ·
    refine ⟨42223283394751462657271999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112595422386003900419391997 42223283394751462657271999)
    ·
      refine ⟨63334925092127193985907999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42223283394751462657271999 63334925092127193985907999)
      ·
        refine ⟨95002387638190790978861999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63334925092127193985907999 95002387638190790978861999)
        ·
          refine ⟨142503581457286186468292999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95002387638190790978861999 142503581457286186468292999)
          ·
            refine ⟨213755372185929279702439499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142503581457286186468292999 213755372185929279702439499)
            ·
              refine ⟨320633058278893919553659249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213755372185929279702439499 320633058278893919553659249)
              ·
                refine ⟨240474793709170439665244437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320633058278893919553659249 240474793709170439665244437)
                ·
                  refine ⟨11272255955117364359308333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240474793709170439665244437 11272255955117364359308333)
                  ·
                    refine ⟨4227095983169011634740625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11272255955117364359308333 4227095983169011634740625)
                    ·
                      refine ⟨3170321987376758726055469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227095983169011634740625 3170321987376758726055469)
                      ·
                        rfl

theorem cell23_6174180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_6174180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174180 prefixEnd_6174180 := by exact prefixLift 6174180
  have htrace : WordTrace (prefixWord ++ tailWord_6174180) baseStart_6174180 baseEnd_6174180 := by
    simpa [prefixWord, tailWord_6174180, baseEnd_6174180] using wordTrace_append hprefix tailTrace_6174180
  have hstable : (prefixWord ++ tailWord_6174180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174180).length < 2 ^ (prefixWord ++ tailWord_6174180).sum := by decide
  have hdescent : baseEnd_6174180 < baseStart_6174180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174187 : List Nat := [1, 1, 1, 1, 2, 3, 2, 7, 1, 1, 3]
def baseStart_6174187 : Nat := 118140960795 + 6174187 * 2 ^ 59
def prefixEnd_6174187 : Nat := 4983230072969 + 3 ^ 40 * 6174187 * 2
def baseEnd_6174187 : Nat := 3170325581741340198667937

theorem tailTrace_6174187 : CollatzResearch.WordTrace tailWord_6174187 prefixEnd_6174187 3170325581741340198667937 := by
  unfold tailWord_6174187
  simp only [CollatzResearch.WordTrace]
  refine ⟨225191100082982441034288815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150127400055321627356192543 225191100082982441034288815)
  ·
    refine ⟨337786650124473661551433223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225191100082982441034288815 337786650124473661551433223)
    ·
      refine ⟨506679975186710492327149835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337786650124473661551433223 506679975186710492327149835)
      ·
        refine ⟨760019962780065738490724753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506679975186710492327149835 760019962780065738490724753)
        ·
          refine ⟨570014972085049303868043565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760019962780065738490724753 570014972085049303868043565)
          ·
            refine ⟨213755614531893488950516337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 570014972085049303868043565 213755614531893488950516337)
            ·
              refine ⟨160316710898920116712887253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 213755614531893488950516337 160316710898920116712887253)
              ·
                refine ⟨3757422911693440235458295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160316710898920116712887253 3757422911693440235458295)
                ·
                  refine ⟨5636134367540160353187443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757422911693440235458295 5636134367540160353187443)
                  ·
                    refine ⟨8454201551310240529781165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5636134367540160353187443 8454201551310240529781165)
                    ·
                      refine ⟨3170325581741340198667937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8454201551310240529781165 3170325581741340198667937)
                      ·
                        rfl

theorem cell23_6174187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 1, 3].length) (baseStart_6174187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174187 prefixEnd_6174187 := by exact prefixLift 6174187
  have htrace : WordTrace (prefixWord ++ tailWord_6174187) baseStart_6174187 baseEnd_6174187 := by
    simpa [prefixWord, tailWord_6174187, baseEnd_6174187] using wordTrace_append hprefix tailTrace_6174187
  have hstable : (prefixWord ++ tailWord_6174187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174187).length < 2 ^ (prefixWord ++ tailWord_6174187).sum := by decide
  have hdescent : baseEnd_6174187 < baseStart_6174187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174190 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_6174190 : Nat := 118140960795 + 6174190 * 2 ^ 59
def prefixEnd_6174190 : Nat := 4983230072969 + 3 ^ 40 * 6174190 * 2
def baseEnd_6174190 : Nat := 1056775707394434562310141

theorem tailTrace_6174190 : CollatzResearch.WordTrace tailWord_6174190 prefixEnd_6174190 1056775707394434562310141 := by
  unfold tailWord_6174190
  simp only [CollatzResearch.WordTrace]
  refine ⟨28148901187746446568331003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150127473001314381697765349 28148901187746446568331003)
  ·
    refine ⟨42223351781619669852496505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28148901187746446568331003 42223351781619669852496505)
    ·
      refine ⟨31667513836214752389372379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42223351781619669852496505 31667513836214752389372379)
      ·
        refine ⟨47501270754322128584058569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31667513836214752389372379 47501270754322128584058569)
        ·
          refine ⟨35625953065741596438043927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47501270754322128584058569 35625953065741596438043927)
          ·
            refine ⟨53438929598612394657065891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35625953065741596438043927 53438929598612394657065891)
            ·
              refine ⟨80158394397918591985598837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53438929598612394657065891 80158394397918591985598837)
              ·
                refine ⟨7514849474804867998649891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80158394397918591985598837 7514849474804867998649891)
                ·
                  refine ⟨11272274212207301997974837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514849474804867998649891 11272274212207301997974837)
                  ·
                    refine ⟨1056775707394434562310141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11272274212207301997974837 1056775707394434562310141)
                    ·
                      rfl

theorem cell23_6174190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_6174190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174190 prefixEnd_6174190 := by exact prefixLift 6174190
  have htrace : WordTrace (prefixWord ++ tailWord_6174190) baseStart_6174190 baseEnd_6174190 := by
    simpa [prefixWord, tailWord_6174190, baseEnd_6174190] using wordTrace_append hprefix tailTrace_6174190
  have hstable : (prefixWord ++ tailWord_6174190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174190).length < 2 ^ (prefixWord ++ tailWord_6174190).sum := by decide
  have hdescent : baseEnd_6174190 < baseStart_6174190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174213 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_6174213 : Nat := 118140960795 + 6174213 * 2 ^ 59
def prefixEnd_6174213 : Nat := 4983230072969 + 3 ^ 40 * 6174213 * 2
def baseEnd_6174213 : Nat := 3170338932238357096942817

theorem tailTrace_6174213 : CollatzResearch.WordTrace tailWord_6174213 prefixEnd_6174213 3170338932238357096942817 := by
  unfold tailWord_6174213
  simp only [CollatzResearch.WordTrace]
  refine ⟨225192048380888247474735293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150128032253925498316490195 225192048380888247474735293)
  ·
    refine ⟨84447018142833092803025735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225192048380888247474735293 84447018142833092803025735)
    ·
      refine ⟨126670527214249639204538603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84447018142833092803025735 126670527214249639204538603)
      ·
        refine ⟨190005790821374458806807905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126670527214249639204538603 190005790821374458806807905)
        ·
          refine ⟨142504343116030844105105929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190005790821374458806807905 142504343116030844105105929)
          ·
            refine ⟨106878257337023133078829447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142504343116030844105105929 106878257337023133078829447)
            ·
              refine ⟨160317386005534699618244171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106878257337023133078829447 160317386005534699618244171)
              ·
                refine ⟨240476079008302049427366257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160317386005534699618244171 240476079008302049427366257)
                ·
                  refine ⟨180357059256226537070524693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240476079008302049427366257 180357059256226537070524693)
                  ·
                    refine ⟨8454237152635618925180845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 180357059256226537070524693 8454237152635618925180845)
                    ·
                      refine ⟨3170338932238357096942817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8454237152635618925180845 3170338932238357096942817)
                      ·
                        rfl

theorem cell23_6174213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_6174213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174213 prefixEnd_6174213 := by exact prefixLift 6174213
  have htrace : WordTrace (prefixWord ++ tailWord_6174213) baseStart_6174213 baseEnd_6174213 := by
    simpa [prefixWord, tailWord_6174213, baseEnd_6174213] using wordTrace_append hprefix tailTrace_6174213
  have hstable : (prefixWord ++ tailWord_6174213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174213).length < 2 ^ (prefixWord ++ tailWord_6174213).sum := by decide
  have hdescent : baseEnd_6174213 < baseStart_6174213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174227 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 4]
def baseStart_6174227 : Nat := 118140960795 + 6174227 * 2 ^ 59
def prefixEnd_6174227 : Nat := 4983230072969 + 3 ^ 40 * 6174227 * 2
def baseEnd_6174227 : Nat := 3170346120967520042167753

theorem tailTrace_6174227 : CollatzResearch.WordTrace tailWord_6174227 prefixEnd_6174227 3170346120967520042167753 := by
  unfold tailWord_6174227
  simp only [CollatzResearch.WordTrace]
  refine ⟨225192559002837527865744935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150128372668558351910496623 225192559002837527865744935)
  ·
    refine ⟨337788838504256291798617403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225192559002837527865744935 337788838504256291798617403)
    ·
      refine ⟨506683257756384437697926105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337788838504256291798617403 506683257756384437697926105)
      ·
        refine ⟨380012443317288328273444579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506683257756384437697926105 380012443317288328273444579)
        ·
          refine ⟨570018664975932492410166869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380012443317288328273444579 570018664975932492410166869)
          ·
            refine ⟨6679906230186708895431643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 570018664975932492410166869 6679906230186708895431643)
            ·
              refine ⟨10019859345280063343147465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6679906230186708895431643 10019859345280063343147465)
              ·
                refine ⟨7514894508960047507360599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10019859345280063343147465 7514894508960047507360599)
                ·
                  refine ⟨11272341763440071261040899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514894508960047507360599 11272341763440071261040899)
                  ·
                    refine ⟨16908512645160106891561349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11272341763440071261040899 16908512645160106891561349)
                    ·
                      refine ⟨3170346120967520042167753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16908512645160106891561349 3170346120967520042167753)
                      ·
                        rfl

theorem cell23_6174227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_6174227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174227 prefixEnd_6174227 := by exact prefixLift 6174227
  have htrace : WordTrace (prefixWord ++ tailWord_6174227) baseStart_6174227 baseEnd_6174227 := by
    simpa [prefixWord, tailWord_6174227, baseEnd_6174227] using wordTrace_append hprefix tailTrace_6174227
  have hstable : (prefixWord ++ tailWord_6174227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174227).length < 2 ^ (prefixWord ++ tailWord_6174227).sum := by decide
  have hdescent : baseEnd_6174227 < baseStart_6174227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174240 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6174240 : Nat := 118140960795 + 6174240 * 2 ^ 59
def prefixEnd_6174240 : Nat := 4983230072969 + 3 ^ 40 * 6174240 * 2
def baseEnd_6174240 : Nat := 3170352796216028491305193

theorem tailTrace_6174240 : CollatzResearch.WordTrace tailWord_6174240 prefixEnd_6174240 3170352796216028491305193 := by
  unfold tailWord_6174240
  simp only [CollatzResearch.WordTrace]
  refine ⟨112596516575895215542984087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150128688767860287390645449 112596516575895215542984087)
  ·
    refine ⟨168894774863842823314476131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112596516575895215542984087 168894774863842823314476131)
    ·
      refine ⟨253342162295764234971714197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168894774863842823314476131 253342162295764234971714197)
      ·
        refine ⟨11875413857613948514299103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 253342162295764234971714197 11875413857613948514299103)
        ·
          refine ⟨17813120786420922771448655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11875413857613948514299103 17813120786420922771448655)
          ·
            refine ⟨26719681179631384157172983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17813120786420922771448655 26719681179631384157172983)
            ·
              refine ⟨40079521769447076235759475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26719681179631384157172983 40079521769447076235759475)
              ·
                refine ⟨60119282654170614353639213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40079521769447076235759475 60119282654170614353639213)
                ·
                  refine ⟨22544730995313980382614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60119282654170614353639213 22544730995313980382614705)
                  ·
                    refine ⟨16908548246485485286961029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22544730995313980382614705 16908548246485485286961029)
                    ·
                      refine ⟨3170352796216028491305193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16908548246485485286961029 3170352796216028491305193)
                      ·
                        rfl

theorem cell23_6174240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6174240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174240 prefixEnd_6174240 := by exact prefixLift 6174240
  have htrace : WordTrace (prefixWord ++ tailWord_6174240) baseStart_6174240 baseEnd_6174240 := by
    simpa [prefixWord, tailWord_6174240, baseEnd_6174240] using wordTrace_append hprefix tailTrace_6174240
  have hstable : (prefixWord ++ tailWord_6174240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174240).length < 2 ^ (prefixWord ++ tailWord_6174240).sum := by decide
  have hdescent : baseEnd_6174240 < baseStart_6174240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174254 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_6174254 : Nat := 118140960795 + 6174254 * 2 ^ 59
def prefixEnd_6174254 : Nat := 4983230072969 + 3 ^ 40 * 6174254 * 2
def baseEnd_6174254 : Nat := 1056786661648397145510043

theorem tailTrace_6174254 : CollatzResearch.WordTrace tailWord_6174254 prefixEnd_6174254 1056786661648397145510043 := by
  unfold tailWord_6174254
  simp only [CollatzResearch.WordTrace]
  refine ⟨28149192971717463934622227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150129029182493140984651877 28149192971717463934622227)
  ·
    refine ⟨42223789457576195901933341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28149192971717463934622227 42223789457576195901933341)
    ·
      refine ⟨15833921046591073463225003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42223789457576195901933341 15833921046591073463225003)
      ·
        refine ⟨23750881569886610194837505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15833921046591073463225003 23750881569886610194837505)
        ·
          refine ⟨17813161177414957646128129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23750881569886610194837505 17813161177414957646128129)
          ·
            refine ⟨13359870883061218234596097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17813161177414957646128129 13359870883061218234596097)
            ·
              refine ⟨10019903162295913675947073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13359870883061218234596097 10019903162295913675947073)
              ·
                refine ⟨7514927371721935256960305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10019903162295913675947073 7514927371721935256960305)
                ·
                  refine ⟨5636195528791451442720229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7514927371721935256960305 5636195528791451442720229)
                  ·
                    refine ⟨1056786661648397145510043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636195528791451442720229 1056786661648397145510043)
                    ·
                      rfl

theorem cell23_6174254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_6174254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174254 prefixEnd_6174254 := by exact prefixLift 6174254
  have htrace : WordTrace (prefixWord ++ tailWord_6174254) baseStart_6174254 baseEnd_6174254 := by
    simpa [prefixWord, tailWord_6174254, baseEnd_6174254] using wordTrace_append hprefix tailTrace_6174254
  have hstable : (prefixWord ++ tailWord_6174254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174254).length < 2 ^ (prefixWord ++ tailWord_6174254).sum := by decide
  have hdescent : baseEnd_6174254 < baseStart_6174254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174261 : List Nat := [1, 3, 3, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_6174261 : Nat := 118140960795 + 6174261 * 2 ^ 59
def prefixEnd_6174261 : Nat := 4983230072969 + 3 ^ 40 * 6174261 * 2
def baseEnd_6174261 : Nat := 3170363579309772909142597

theorem tailTrace_6174261 : CollatzResearch.WordTrace tailWord_6174261 prefixEnd_6174261 3170363579309772909142597 := by
  unfold tailWord_6174261
  simp only [CollatzResearch.WordTrace]
  refine ⟨225193799084714351672482637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150129199389809567781655091 225193799084714351672482637)
  ·
    refine ⟨84447674656767881877180989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225193799084714351672482637 84447674656767881877180989)
    ·
      refine ⟨31667877996287955703942871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84447674656767881877180989 31667877996287955703942871)
      ·
        refine ⟨47501816994431933555914307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31667877996287955703942871 47501816994431933555914307)
        ·
          refine ⟨71252725491647900333871461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47501816994431933555914307 71252725491647900333871461)
          ·
            refine ⟨13359886029683981312600899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71252725491647900333871461 13359886029683981312600899)
            ·
              refine ⟨20039829044525971968901349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13359886029683981312600899 20039829044525971968901349)
              ·
                refine ⟨3757467945848619744169003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20039829044525971968901349 3757467945848619744169003)
                ·
                  refine ⟨5636201918772929616253505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757467945848619744169003 5636201918772929616253505)
                  ·
                    refine ⟨4227151439079697212190129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5636201918772929616253505 4227151439079697212190129)
                    ·
                      refine ⟨3170363579309772909142597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227151439079697212190129 3170363579309772909142597)
                      ·
                        rfl

theorem cell23_6174261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_6174261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174261 prefixEnd_6174261 := by exact prefixLift 6174261
  have htrace : WordTrace (prefixWord ++ tailWord_6174261) baseStart_6174261 baseEnd_6174261 := by
    simpa [prefixWord, tailWord_6174261, baseEnd_6174261] using wordTrace_append hprefix tailTrace_6174261
  have hstable : (prefixWord ++ tailWord_6174261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174261).length < 2 ^ (prefixWord ++ tailWord_6174261).sum := by decide
  have hdescent : baseEnd_6174261 < baseStart_6174261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174263 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 2, 7]
def baseStart_6174263 : Nat := 118140960795 + 6174263 * 2 ^ 59
def prefixEnd_6174263 : Nat := 4983230072969 + 3 ^ 40 * 6174263 * 2
def baseEnd_6174263 : Nat := 1056788202090360633772529

theorem tailTrace_6174263 : CollatzResearch.WordTrace tailWord_6174263 prefixEnd_6174263 1056788202090360633772529 := by
  unfold tailWord_6174263
  simp only [CollatzResearch.WordTrace]
  refine ⟨225193872030707106014055443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150129248020471404009370295 225193872030707106014055443)
  ·
    refine ⟨337790808046060659021083165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225193872030707106014055443 337790808046060659021083165)
    ·
      refine ⟨126671553017272747132906187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 337790808046060659021083165 126671553017272747132906187)
      ·
        refine ⟨190007329525909120699359281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126671553017272747132906187 190007329525909120699359281)
        ·
          refine ⟨142505497144431840524519461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190007329525909120699359281 142505497144431840524519461)
          ·
            refine ⟨26719780714580970098347399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142505497144431840524519461 26719780714580970098347399)
            ·
              refine ⟨40079671071871455147521099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26719780714580970098347399 40079671071871455147521099)
              ·
                refine ⟨60119506607807182721281649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40079671071871455147521099 60119506607807182721281649)
                ·
                  refine ⟨45089629955855387040961237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60119506607807182721281649 45089629955855387040961237)
                  ·
                    refine ⟨1056788202090360633772529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45089629955855387040961237 1056788202090360633772529)
                    ·
                      rfl

theorem cell23_6174263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_6174263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174263 prefixEnd_6174263 := by exact prefixLift 6174263
  have htrace : WordTrace (prefixWord ++ tailWord_6174263) baseStart_6174263 baseEnd_6174263 := by
    simpa [prefixWord, tailWord_6174263, baseEnd_6174263] using wordTrace_append hprefix tailTrace_6174263
  have hstable : (prefixWord ++ tailWord_6174263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174263).length < 2 ^ (prefixWord ++ tailWord_6174263).sum := by decide
  have hdescent : baseEnd_6174263 < baseStart_6174263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174277 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_6174277 : Nat := 118140960795 + 6174277 * 2 ^ 59
def prefixEnd_6174277 : Nat := 4983230072969 + 3 ^ 40 * 6174277 * 2
def baseEnd_6174277 : Nat := 3170371795000244846542523

theorem tailTrace_6174277 : CollatzResearch.WordTrace tailWord_6174277 prefixEnd_6174277 3170371795000244846542523 := by
  unfold tailWord_6174277
  simp only [CollatzResearch.WordTrace]
  refine ⟨225194382652656386405065085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150129588435104257603376723 225194382652656386405065085)
  ·
    refine ⟨84447893494746144901899407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225194382652656386405065085 84447893494746144901899407)
    ·
      refine ⟨126671840242119217352849111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84447893494746144901899407 126671840242119217352849111)
      ·
        refine ⟨190007760363178826029273667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126671840242119217352849111 190007760363178826029273667)
        ·
          refine ⟨285011640544768239043910501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190007760363178826029273667 285011640544768239043910501)
          ·
            refine ⟨53439682602144044820733219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285011640544768239043910501 53439682602144044820733219)
            ·
              refine ⟨80159523903216067231099829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53439682602144044820733219 80159523903216067231099829)
              ·
                refine ⟨7514955365926506302915609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80159523903216067231099829 7514955365926506302915609)
                ·
                  refine ⟨5636216524444879727186707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7514955365926506302915609 5636216524444879727186707)
                  ·
                    refine ⟨8454324786667319590780061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5636216524444879727186707 8454324786667319590780061)
                    ·
                      refine ⟨3170371795000244846542523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8454324786667319590780061 3170371795000244846542523)
                      ·
                        rfl

theorem cell23_6174277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_6174277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174277 prefixEnd_6174277 := by exact prefixLift 6174277
  have htrace : WordTrace (prefixWord ++ tailWord_6174277) baseStart_6174277 baseEnd_6174277 := by
    simpa [prefixWord, tailWord_6174277, baseEnd_6174277] using wordTrace_append hprefix tailTrace_6174277
  have hstable : (prefixWord ++ tailWord_6174277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174277).length < 2 ^ (prefixWord ++ tailWord_6174277).sum := by decide
  have hdescent : baseEnd_6174277 < baseStart_6174277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174278 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6174278 : Nat := 118140960795 + 6174278 * 2 ^ 59
def prefixEnd_6174278 : Nat := 4983230072969 + 3 ^ 40 * 6174278 * 2
def baseEnd_6174278 : Nat := 3170372308480899342630019

theorem tailTrace_6174278 : CollatzResearch.WordTrace tailWord_6174278 prefixEnd_6174278 3170372308480899342630019 := by
  unfold tailWord_6174278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7037325597676648861745359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150129612750435175717234325 7037325597676648861745359)
  ·
    refine ⟨10555988396514973292618039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7037325597676648861745359 10555988396514973292618039)
    ·
      refine ⟨15833982594772459938927059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10555988396514973292618039 15833982594772459938927059)
      ·
        refine ⟨23750973892158689908390589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15833982594772459938927059 23750973892158689908390589)
        ·
          refine ⟨8906615209559508715646471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23750973892158689908390589 8906615209559508715646471)
          ·
            refine ⟨13359922814339263073469707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8906615209559508715646471 13359922814339263073469707)
            ·
              refine ⟨20039884221508894610204561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13359922814339263073469707 20039884221508894610204561)
              ·
                refine ⟨15029913166131670957653421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20039884221508894610204561 15029913166131670957653421)
                ·
                  refine ⟨5636217437299376609120033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15029913166131670957653421 5636217437299376609120033)
                  ·
                    refine ⟨4227163077974532456840025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5636217437299376609120033 4227163077974532456840025)
                    ·
                      refine ⟨3170372308480899342630019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227163077974532456840025 3170372308480899342630019)
                      ·
                        rfl

theorem cell23_6174278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6174278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174278 prefixEnd_6174278 := by exact prefixLift 6174278
  have htrace : WordTrace (prefixWord ++ tailWord_6174278) baseStart_6174278 baseEnd_6174278 := by
    simpa [prefixWord, tailWord_6174278, baseEnd_6174278] using wordTrace_append hprefix tailTrace_6174278
  have hstable : (prefixWord ++ tailWord_6174278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174278).length < 2 ^ (prefixWord ++ tailWord_6174278).sum := by decide
  have hdescent : baseEnd_6174278 < baseStart_6174278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174283 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4]
def baseStart_6174283 : Nat := 118140960795 + 6174283 * 2 ^ 59
def prefixEnd_6174283 : Nat := 4983230072969 + 3 ^ 40 * 6174283 * 2
def baseEnd_6174283 : Nat := 3170374875884171823067495

theorem tailTrace_6174283 : CollatzResearch.WordTrace tailWord_6174283 prefixEnd_6174283 3170374875884171823067495 := by
  unfold tailWord_6174283
  simp only [CollatzResearch.WordTrace]
  refine ⟨225194601490634649429783503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150129734327089766286522335 225194601490634649429783503)
  ·
    refine ⟨337791902235951974144675255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225194601490634649429783503 337791902235951974144675255)
    ·
      refine ⟨506687853353927961217012883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337791902235951974144675255 506687853353927961217012883)
      ·
        refine ⟨760031780030891941825519325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506687853353927961217012883 760031780030891941825519325)
        ·
          refine ⟨285011917511584478184569747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 760031780030891941825519325 285011917511584478184569747)
          ·
            refine ⟨427517876267376717276854621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285011917511584478184569747 427517876267376717276854621)
            ·
              refine ⟨160319203600266268978820483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427517876267376717276854621 160319203600266268978820483)
              ·
                refine ⟨240478805400399403468230725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160319203600266268978820483 240478805400399403468230725)
                ·
                  refine ⟨45089776012574888150293261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240478805400399403468230725 45089776012574888150293261)
                  ·
                    refine ⟨16908666004715583056359973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45089776012574888150293261 16908666004715583056359973)
                    ·
                      refine ⟨3170374875884171823067495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16908666004715583056359973 3170374875884171823067495)
                      ·
                        rfl

theorem cell23_6174283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_6174283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174283 prefixEnd_6174283 := by exact prefixLift 6174283
  have htrace : WordTrace (prefixWord ++ tailWord_6174283) baseStart_6174283 baseEnd_6174283 := by
    simpa [prefixWord, tailWord_6174283, baseEnd_6174283] using wordTrace_append hprefix tailTrace_6174283
  have hstable : (prefixWord ++ tailWord_6174283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174283).length < 2 ^ (prefixWord ++ tailWord_6174283).sum := by decide
  have hdescent : baseEnd_6174283 < baseStart_6174283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174287 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 1, 3, 2]
def baseStart_6174287 : Nat := 118140960795 + 6174287 * 2 ^ 59
def prefixEnd_6174287 : Nat := 4983230072969 + 3 ^ 40 * 6174287 * 2
def baseEnd_6174287 : Nat := 3170376929806789807417477

theorem tailTrace_6174287 : CollatzResearch.WordTrace tailWord_6174287 prefixEnd_6174287 3170376929806789807417477 := by
  unfold tailWord_6174287
  simp only [CollatzResearch.WordTrace]
  refine ⟨225194747382620158112929115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150129831588413438741952743 225194747382620158112929115)
  ·
    refine ⟨337792121073930237169393673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225194747382620158112929115 337792121073930237169393673)
    ·
      refine ⟨253344090805447677877045255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 337792121073930237169393673 253344090805447677877045255)
      ·
        refine ⟨380016136208171516815567883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253344090805447677877045255 380016136208171516815567883)
        ·
          refine ⟨570024204312257275223351825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380016136208171516815567883 570024204312257275223351825)
          ·
            refine ⟨427518153234192956417513869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570024204312257275223351825 427518153234192956417513869)
            ·
              refine ⟨160319307462822358656567701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 427518153234192956417513869 160319307462822358656567701)
              ·
                refine ⟨7514967537319798062026611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160319307462822358656567701 7514967537319798062026611)
                ·
                  refine ⟨11272451305979697093039917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7514967537319798062026611 11272451305979697093039917)
                  ·
                    refine ⟨4227169239742386409889969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11272451305979697093039917 4227169239742386409889969)
                    ·
                      refine ⟨3170376929806789807417477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227169239742386409889969 3170376929806789807417477)
                      ·
                        rfl

theorem cell23_6174287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 3, 2].length) (baseStart_6174287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174287 prefixEnd_6174287 := by exact prefixLift 6174287
  have htrace : WordTrace (prefixWord ++ tailWord_6174287) baseStart_6174287 baseEnd_6174287 := by
    simpa [prefixWord, tailWord_6174287, baseEnd_6174287] using wordTrace_append hprefix tailTrace_6174287
  have hstable : (prefixWord ++ tailWord_6174287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174287).length < 2 ^ (prefixWord ++ tailWord_6174287).sum := by decide
  have hdescent : baseEnd_6174287 < baseStart_6174287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174293 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_6174293 : Nat := 118140960795 + 6174293 * 2 ^ 59
def prefixEnd_6174293 : Nat := 4983230072969 + 3 ^ 40 * 6174293 * 2
def baseEnd_6174293 : Nat := 1056793336896905594647483

theorem tailTrace_6174293 : CollatzResearch.WordTrace tailWord_6174293 prefixEnd_6174293 1056793336896905594647483 := by
  unfold tailWord_6174293
  simp only [CollatzResearch.WordTrace]
  refine ⟨225194966220598421137647533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150129977480398947425098355 225194966220598421137647533)
  ·
    refine ⟨84448112332724407926617825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225194966220598421137647533 84448112332724407926617825)
    ·
      refine ⟨63336084249543305944963369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84448112332724407926617825 63336084249543305944963369)
      ·
        refine ⟨47502063187157479458722527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63336084249543305944963369 47502063187157479458722527)
        ·
          refine ⟨71253094780736219188083791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47502063187157479458722527 71253094780736219188083791)
          ·
            refine ⟨106879642171104328782125687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71253094780736219188083791 106879642171104328782125687)
            ·
              refine ⟨160319463256656493173188531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106879642171104328782125687 160319463256656493173188531)
              ·
                refine ⟨240479194884984739759782797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160319463256656493173188531 240479194884984739759782797)
                ·
                  refine ⟨90179698081869277409918549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240479194884984739759782797 90179698081869277409918549)
                  ·
                    refine ⟨1056793336896905594647483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90179698081869277409918549 1056793336896905594647483)
                    ·
                      rfl

theorem cell23_6174293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_6174293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174293 prefixEnd_6174293 := by exact prefixLift 6174293
  have htrace : WordTrace (prefixWord ++ tailWord_6174293) baseStart_6174293 baseEnd_6174293 := by
    simpa [prefixWord, tailWord_6174293, baseEnd_6174293] using wordTrace_append hprefix tailTrace_6174293
  have hstable : (prefixWord ++ tailWord_6174293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174293).length < 2 ^ (prefixWord ++ tailWord_6174293).sum := by decide
  have hdescent : baseEnd_6174293 < baseStart_6174293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174407 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_6174407 : Nat := 118140960795 + 6174407 * 2 ^ 59
def prefixEnd_6174407 : Nat := 4983230072969 + 3 ^ 40 * 6174407 * 2
def baseEnd_6174407 : Nat := 3170438547485329337916925

theorem tailTrace_6174407 : CollatzResearch.WordTrace tailWord_6174407 prefixEnd_6174407 3170438547485329337916925 := by
  unfold tailWord_6174407
  simp only [CollatzResearch.WordTrace]
  refine ⟨225199124142185418607297475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150132749428123612404864983 225199124142185418607297475)
  ·
    refine ⟨337798686213278127910946213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225199124142185418607297475 337798686213278127910946213)
    ·
      refine ⟨63337253664989648983302415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 337798686213278127910946213 63337253664989648983302415)
      ·
        refine ⟨95005880497484473474953623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63337253664989648983302415 95005880497484473474953623)
        ·
          refine ⟨142508820746226710212430435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95005880497484473474953623 142508820746226710212430435)
          ·
            refine ⟨213763231119340065318645653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142508820746226710212430435 213763231119340065318645653)
            ·
              refine ⟨10020151458719065561811515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 213763231119340065318645653 10020151458719065561811515)
              ·
                refine ⟨15030227188078598342717273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10020151458719065561811515 15030227188078598342717273)
                ·
                  refine ⟨11272670391058948757037955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15030227188078598342717273 11272670391058948757037955)
                  ·
                    refine ⟨16909005586588423135556933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11272670391058948757037955 16909005586588423135556933)
                    ·
                      refine ⟨3170438547485329337916925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16909005586588423135556933 3170438547485329337916925)
                      ·
                        rfl

theorem cell23_6174407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_6174407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174407 prefixEnd_6174407 := by exact prefixLift 6174407
  have htrace : WordTrace (prefixWord ++ tailWord_6174407) baseStart_6174407 baseEnd_6174407 := by
    simpa [prefixWord, tailWord_6174407, baseEnd_6174407] using wordTrace_append hprefix tailTrace_6174407
  have hstable : (prefixWord ++ tailWord_6174407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174407).length < 2 ^ (prefixWord ++ tailWord_6174407).sum := by decide
  have hdescent : baseEnd_6174407 < baseStart_6174407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174514 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_6174514 : Nat := 118140960795 + 6174514 * 2 ^ 59
def prefixEnd_6174514 : Nat := 4983230072969 + 3 ^ 40 * 6174514 * 2
def baseEnd_6174514 : Nat := 3170493489915360419278933

theorem tailTrace_6174514 : CollatzResearch.WordTrace tailWord_6174514 prefixEnd_6174514 3170493489915360419278933 := by
  unfold tailWord_6174514
  simp only [CollatzResearch.WordTrace]
  refine ⟨56300756688199443970360649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150135351168531850587628397 56300756688199443970360649)
  ·
    refine ⟨42225567516149582977770487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56300756688199443970360649 42225567516149582977770487)
    ·
      refine ⟨63338351274224374466655731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42225567516149582977770487 63338351274224374466655731)
      ·
        refine ⟨95007526911336561699983597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63338351274224374466655731 95007526911336561699983597)
        ·
          refine ⟨35627822591751210637493849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95007526911336561699983597 35627822591751210637493849)
          ·
            refine ⟨26720866943813407978120387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35627822591751210637493849 26720866943813407978120387)
            ·
              refine ⟨40081300415720111967180581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26720866943813407978120387 40081300415720111967180581)
              ·
                refine ⟨7515243827947520993846359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40081300415720111967180581 7515243827947520993846359)
                ·
                  refine ⟨11272865741921281490769539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7515243827947520993846359 11272865741921281490769539)
                  ·
                    refine ⟨16909298612881922236154309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11272865741921281490769539 16909298612881922236154309)
                    ·
                      refine ⟨3170493489915360419278933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16909298612881922236154309 3170493489915360419278933)
                      ·
                        rfl

theorem cell23_6174514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_6174514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174514 prefixEnd_6174514 := by exact prefixLift 6174514
  have htrace : WordTrace (prefixWord ++ tailWord_6174514) baseStart_6174514 baseEnd_6174514 := by
    simpa [prefixWord, tailWord_6174514, baseEnd_6174514] using wordTrace_append hprefix tailTrace_6174514
  have hstable : (prefixWord ++ tailWord_6174514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174514).length < 2 ^ (prefixWord ++ tailWord_6174514).sum := by decide
  have hdescent : baseEnd_6174514 < baseStart_6174514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174525 : List Nat := [1, 4, 1, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6174525 : Nat := 118140960795 + 6174525 * 2 ^ 59
def prefixEnd_6174525 : Nat := 4983230072969 + 3 ^ 40 * 6174525 * 2
def baseEnd_6174525 : Nat := 3170499138202559876241383

theorem tailTrace_6174525 : CollatzResearch.WordTrace tailWord_6174525 prefixEnd_6174525 3170499138202559876241383 := by
  unfold tailWord_6174525
  simp only [CollatzResearch.WordTrace]
  refine ⟨225203427955757924760093029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150135618637171949840062019 225203427955757924760093029)
  ·
    refine ⟨42225642741704610892517443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225203427955757924760093029 42225642741704610892517443)
    ·
      refine ⟨63338464112556916338776165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42225642741704610892517443 63338464112556916338776165)
      ·
        refine ⟨11875962021104421813520531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63338464112556916338776165 11875962021104421813520531)
        ·
          refine ⟨17813943031656632720280797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11875962021104421813520531 17813943031656632720280797)
          ·
            refine ⟨6680228636871237270105299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17813943031656632720280797 6680228636871237270105299)
            ·
              refine ⟨10020342955306855905157949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680228636871237270105299 10020342955306855905157949)
              ·
                refine ⟨3757628608240070964434231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10020342955306855905157949 3757628608240070964434231)
                ·
                  refine ⟨5636442912360106446651347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757628608240070964434231 5636442912360106446651347)
                  ·
                    refine ⟨8454664368540159669977021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5636442912360106446651347 8454664368540159669977021)
                    ·
                      refine ⟨3170499138202559876241383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8454664368540159669977021 3170499138202559876241383)
                      ·
                        rfl

theorem cell23_6174525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6174525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174525 prefixEnd_6174525 := by exact prefixLift 6174525
  have htrace : WordTrace (prefixWord ++ tailWord_6174525) baseStart_6174525 baseEnd_6174525 := by
    simpa [prefixWord, tailWord_6174525, baseEnd_6174525] using wordTrace_append hprefix tailTrace_6174525
  have hstable : (prefixWord ++ tailWord_6174525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174525).length < 2 ^ (prefixWord ++ tailWord_6174525).sum := by decide
  have hdescent : baseEnd_6174525 < baseStart_6174525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174541 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_6174541 : Nat := 118140960795 + 6174541 * 2 ^ 59
def prefixEnd_6174541 : Nat := 4983230072969 + 3 ^ 40 * 6174541 * 2
def baseEnd_6174541 : Nat := 1056835784631010604547103

theorem tailTrace_6174541 : CollatzResearch.WordTrace tailWord_6174541 prefixEnd_6174541 1056835784631010604547103 := by
  unfold tailWord_6174541
  simp only [CollatzResearch.WordTrace]
  refine ⟨225204011523699959492675477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150136007682466639661783651 225204011523699959492675477)
  ·
    refine ⟨10556438040173435601219163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 225204011523699959492675477 10556438040173435601219163)
    ·
      refine ⟨15834657060260153401828745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10556438040173435601219163 15834657060260153401828745)
      ·
        refine ⟨11875992795195115051371559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15834657060260153401828745 11875992795195115051371559)
        ·
          refine ⟨17813989192792672577057339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11875992795195115051371559 17813989192792672577057339)
          ·
            refine ⟨26720983789189008865586009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17813989192792672577057339 26720983789189008865586009)
            ·
              refine ⟨20040737841891756649189507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26720983789189008865586009 20040737841891756649189507)
              ·
                refine ⟨30061106762837634973784261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20040737841891756649189507 30061106762837634973784261)
                ·
                  refine ⟨5636457518032056557584549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30061106762837634973784261 5636457518032056557584549)
                  ·
                    refine ⟨1056835784631010604547103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636457518032056557584549 1056835784631010604547103)
                    ·
                      rfl

theorem cell23_6174541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_6174541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174541 prefixEnd_6174541 := by exact prefixLift 6174541
  have htrace : WordTrace (prefixWord ++ tailWord_6174541) baseStart_6174541 baseEnd_6174541 := by
    simpa [prefixWord, tailWord_6174541, baseEnd_6174541] using wordTrace_append hprefix tailTrace_6174541
  have hstable : (prefixWord ++ tailWord_6174541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174541).length < 2 ^ (prefixWord ++ tailWord_6174541).sum := by decide
  have hdescent : baseEnd_6174541 < baseStart_6174541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6174548 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_6174548 : Nat := 118140960795 + 6174548 * 2 ^ 59
def prefixEnd_6174548 : Nat := 4983230072969 + 3 ^ 40 * 6174548 * 2
def baseEnd_6174548 : Nat := 3170510948257613286253777

theorem tailTrace_6174548 : CollatzResearch.WordTrace tailWord_6174548 prefixEnd_6174548 3170510948257613286253777 := by
  unfold tailWord_6174548
  simp only [CollatzResearch.WordTrace]
  refine ⟨112602133417337299844090149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150136177889783066458786865 112602133417337299844090149)
  ·
    refine ⟨21112900015750743720766903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112602133417337299844090149 21112900015750743720766903)
    ·
      refine ⟨31669350023626115581150355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21112900015750743720766903 31669350023626115581150355)
      ·
        refine ⟨47504025035439173371725533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31669350023626115581150355 47504025035439173371725533)
        ·
          refine ⟨17814009388289690014397075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47504025035439173371725533 17814009388289690014397075)
          ·
            refine ⟨26721014082434535021595613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17814009388289690014397075 26721014082434535021595613)
            ·
              refine ⟨10020380280912950633098355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26721014082434535021595613 10020380280912950633098355)
              ·
                refine ⟨15030570421369425949647533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10020380280912950633098355 15030570421369425949647533)
                ·
                  refine ⟨5636463908013534731117825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15030570421369425949647533 5636463908013534731117825)
                  ·
                    refine ⟨4227347931010151048338369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5636463908013534731117825 4227347931010151048338369)
                    ·
                      refine ⟨3170510948257613286253777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4227347931010151048338369 3170510948257613286253777)
                      ·
                        rfl

theorem cell23_6174548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_6174548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6174548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6174548 prefixEnd_6174548 := by exact prefixLift 6174548
  have htrace : WordTrace (prefixWord ++ tailWord_6174548) baseStart_6174548 baseEnd_6174548 := by
    simpa [prefixWord, tailWord_6174548, baseEnd_6174548] using wordTrace_append hprefix tailTrace_6174548
  have hstable : (prefixWord ++ tailWord_6174548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6174548).length < 2 ^ (prefixWord ++ tailWord_6174548).sum := by decide
  have hdescent : baseEnd_6174548 < baseStart_6174548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6174548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
