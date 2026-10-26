import V185TrunkScan23Chunk0623

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3690294 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3690294 : Nat := 118140960795 + 3690294 * 2 ^ 59
def prefixEnd_3690294 : Nat := 4983230072969 + 3 ^ 40 * 3690294 * 2
def baseEnd_3690294 : Nat := 1894894578403089941453653

theorem tailTrace_3690294 : CollatzResearch.WordTrace tailWord_3690294 prefixEnd_3690294 1894894578403089941453653 := by
  unfold tailWord_3690294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8412254980793910305211371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89730719795135043255587957 8412254980793910305211371)
  ·
    refine ⟨12618382471190865457817057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8412254980793910305211371 12618382471190865457817057)
    ·
      refine ⟨9463786853393149093362793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12618382471190865457817057 9463786853393149093362793)
      ·
        refine ⟨7097840140044861820022095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9463786853393149093362793 7097840140044861820022095)
        ·
          refine ⟨10646760210067292730033143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097840140044861820022095 10646760210067292730033143)
          ·
            refine ⟨15970140315100939095049715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10646760210067292730033143 15970140315100939095049715)
            ·
              refine ⟨23955210472651408642574573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15970140315100939095049715 23955210472651408642574573)
              ·
                refine ⟨8983203927244278240965465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23955210472651408642574573 8983203927244278240965465)
                ·
                  refine ⟨6737402945433208680724099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8983203927244278240965465 6737402945433208680724099)
                  ·
                    refine ⟨10106104418149813021086149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6737402945433208680724099 10106104418149813021086149)
                    ·
                      refine ⟨1894894578403089941453653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10106104418149813021086149 1894894578403089941453653)
                      ·
                        rfl

theorem cell23_3690294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3690294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690294 prefixEnd_3690294 := by exact prefixLift 3690294
  have htrace : WordTrace (prefixWord ++ tailWord_3690294) baseStart_3690294 baseEnd_3690294 := by
    simpa [prefixWord, tailWord_3690294, baseEnd_3690294] using wordTrace_append hprefix tailTrace_3690294
  have hstable : (prefixWord ++ tailWord_3690294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690294).length < 2 ^ (prefixWord ++ tailWord_3690294).sum := by decide
  have hdescent : baseEnd_3690294 < baseStart_3690294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690321 : List Nat := [1, 2, 2, 1, 5, 1, 4, 2, 1, 4]
def baseStart_3690321 : Nat := 118140960795 + 3690321 * 2 ^ 59
def prefixEnd_3690321 : Nat := 4983230072969 + 3 ^ 40 * 3690321 * 2
def baseEnd_3690321 : Nat := 631636147460253778605343

theorem tailTrace_3690321 : CollatzResearch.WordTrace tailWord_3690321 prefixEnd_3690321 631636147460253778605343 := by
  unfold tailWord_3690321
  simp only [CollatzResearch.WordTrace]
  refine ⟨134597064463604748494614817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89731376309069832329743211 134597064463604748494614817)
  ·
    refine ⟨100947798347703561370961113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134597064463604748494614817 100947798347703561370961113)
    ·
      refine ⟨75710848760777671028220835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100947798347703561370961113 75710848760777671028220835)
      ·
        refine ⟨113566273141166506542331253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75710848760777671028220835 113566273141166506542331253)
        ·
          refine ⟨10646838106984359988343555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113566273141166506542331253 10646838106984359988343555)
          ·
            refine ⟨15970257160476539982515333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10646838106984359988343555 15970257160476539982515333)
            ·
              refine ⟨2994423217589351246721625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15970257160476539982515333 2994423217589351246721625)
              ·
                refine ⟨2245817413192013435041219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2994423217589351246721625 2245817413192013435041219)
                ·
                  refine ⟨3368726119788020152561829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245817413192013435041219 3368726119788020152561829)
                  ·
                    refine ⟨631636147460253778605343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368726119788020152561829 631636147460253778605343)
                    ·
                      rfl

theorem cell23_3690321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_3690321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690321 prefixEnd_3690321 := by exact prefixLift 3690321
  have htrace : WordTrace (prefixWord ++ tailWord_3690321) baseStart_3690321 baseEnd_3690321 := by
    simpa [prefixWord, tailWord_3690321, baseEnd_3690321] using wordTrace_append hprefix tailTrace_3690321
  have hstable : (prefixWord ++ tailWord_3690321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690321).length < 2 ^ (prefixWord ++ tailWord_3690321).sum := by decide
  have hdescent : baseEnd_3690321 < baseStart_3690321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690330 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_3690330 : Nat := 118140960795 + 3690330 * 2 ^ 59
def prefixEnd_3690330 : Nat := 4983230072969 + 3 ^ 40 * 3690330 * 2
def baseEnd_3690330 : Nat := 631637687902217266867829

theorem tailTrace_3690330 : CollatzResearch.WordTrace tailWord_3690330 prefixEnd_3690330 631637687902217266867829 := by
  unfold tailWord_3690330
  simp only [CollatzResearch.WordTrace]
  refine ⟨33649348180143035757923111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89731595147048095354461629 33649348180143035757923111)
  ·
    refine ⟨50474022270214553636884667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33649348180143035757923111 50474022270214553636884667)
    ·
      refine ⟨75711033405321830455327001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50474022270214553636884667 75711033405321830455327001)
      ·
        refine ⟨56783275053991372841495251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75711033405321830455327001 56783275053991372841495251)
        ·
          refine ⟨85174912580987059262242877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56783275053991372841495251 85174912580987059262242877)
          ·
            refine ⟨31940592217870147223341079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85174912580987059262242877 31940592217870147223341079)
            ·
              refine ⟨47910888326805220835011619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31940592217870147223341079 47910888326805220835011619)
              ·
                refine ⟨71866332490207831252517429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47910888326805220835011619 71866332490207831252517429)
                ·
                  refine ⟨6737468670956984179923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71866332490207831252517429 6737468670956984179923509)
                  ·
                    refine ⟨631637687902217266867829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6737468670956984179923509 631637687902217266867829)
                    ·
                      rfl

theorem cell23_3690330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_3690330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690330 prefixEnd_3690330 := by exact prefixLift 3690330
  have htrace : WordTrace (prefixWord ++ tailWord_3690330) baseStart_3690330 baseEnd_3690330 := by
    simpa [prefixWord, tailWord_3690330, baseEnd_3690330] using wordTrace_append hprefix tailTrace_3690330
  have hstable : (prefixWord ++ tailWord_3690330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690330).length < 2 ^ (prefixWord ++ tailWord_3690330).sum := by decide
  have hdescent : baseEnd_3690330 < baseStart_3690330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690337 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_3690337 : Nat := 118140960795 + 3690337 * 2 ^ 59
def prefixEnd_3690337 : Nat := 4983230072969 + 3 ^ 40 * 3690337 * 2
def baseEnd_3690337 : Nat := 1894916658071233273215955

theorem tailTrace_3690337 : CollatzResearch.WordTrace tailWord_3690337 prefixEnd_3690337 1894916658071233273215955 := by
  unfold tailWord_3690337
  simp only [CollatzResearch.WordTrace]
  refine ⟨134597648031546783227197265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89731765354364522151464843 134597648031546783227197265)
  ·
    refine ⟨100948236023660087420397949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134597648031546783227197265 100948236023660087420397949)
    ·
      refine ⟨37855588508872532782649231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100948236023660087420397949 37855588508872532782649231)
      ·
        refine ⟨56783382763308799173973847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37855588508872532782649231 56783382763308799173973847)
        ·
          refine ⟨85175074144963198760960771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56783382763308799173973847 85175074144963198760960771)
          ·
            refine ⟨127762611217444798141441157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85175074144963198760960771 127762611217444798141441157)
            ·
              refine ⟨23955489603270899651520217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127762611217444798141441157 23955489603270899651520217)
              ·
                refine ⟨17966617202453174738640163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23955489603270899651520217 17966617202453174738640163)
                ·
                  refine ⟨26949925803679762107960245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17966617202453174738640163 26949925803679762107960245)
                  ·
                    refine ⟨2526555544094977697621273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26949925803679762107960245 2526555544094977697621273)
                    ·
                      refine ⟨1894916658071233273215955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526555544094977697621273 1894916658071233273215955)
                      ·
                        rfl

theorem cell23_3690337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_3690337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690337 prefixEnd_3690337 := by exact prefixLift 3690337
  have htrace : WordTrace (prefixWord ++ tailWord_3690337) baseStart_3690337 baseEnd_3690337 := by
    simpa [prefixWord, tailWord_3690337, baseEnd_3690337] using wordTrace_append hprefix tailTrace_3690337
  have hstable : (prefixWord ++ tailWord_3690337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690337).length < 2 ^ (prefixWord ++ tailWord_3690337).sum := by decide
  have hdescent : baseEnd_3690337 < baseStart_3690337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690344 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3690344 : Nat := 118140960795 + 3690344 * 2 ^ 59
def prefixEnd_3690344 : Nat := 4983230072969 + 3 ^ 40 * 3690344 * 2
def baseEnd_3690344 : Nat := 1894920252435814745828423

theorem tailTrace_3690344 : CollatzResearch.WordTrace tailWord_3690344 prefixEnd_3690344 1894920252435814745828423 := by
  unfold tailWord_3690344
  simp only [CollatzResearch.WordTrace]
  refine ⟨67298951671260711711351043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89731935561680948948468057 67298951671260711711351043)
  ·
    refine ⟨100948427506891067567026565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67298951671260711711351043 100948427506891067567026565)
    ·
      refine ⟨18927830157542075168817481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100948427506891067567026565 18927830157542075168817481)
      ·
        refine ⟨14195872618156556376613111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18927830157542075168817481 14195872618156556376613111)
        ·
          refine ⟨21293808927234834564919667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195872618156556376613111 21293808927234834564919667)
          ·
            refine ⟨31940713390852251847379501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21293808927234834564919667 31940713390852251847379501)
            ·
              refine ⟨11977767521569594442767313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31940713390852251847379501 11977767521569594442767313)
              ·
                refine ⟨8983325641177195832075485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11977767521569594442767313 8983325641177195832075485)
                ·
                  refine ⟨3368747115441448437028307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8983325641177195832075485 3368747115441448437028307)
                  ·
                    refine ⟨5053120673162172655542461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3368747115441448437028307 5053120673162172655542461)
                    ·
                      refine ⟨1894920252435814745828423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053120673162172655542461 1894920252435814745828423)
                      ·
                        rfl

theorem cell23_3690344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3690344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690344 prefixEnd_3690344 := by exact prefixLift 3690344
  have htrace : WordTrace (prefixWord ++ tailWord_3690344) baseStart_3690344 baseEnd_3690344 := by
    simpa [prefixWord, tailWord_3690344, baseEnd_3690344] using wordTrace_append hprefix tailTrace_3690344
  have hstable : (prefixWord ++ tailWord_3690344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690344).length < 2 ^ (prefixWord ++ tailWord_3690344).sum := by decide
  have hdescent : baseEnd_3690344 < baseStart_3690344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690361 : List Nat := [1, 2, 1, 3, 2, 2, 4, 3, 1, 1, 3]
def baseStart_3690361 : Nat := 118140960795 + 3690361 * 2 ^ 59
def prefixEnd_3690361 : Nat := 4983230072969 + 3 ^ 40 * 3690361 * 2
def baseEnd_3690361 : Nat := 1894928981606941179315845

theorem tailTrace_3690361 : CollatzResearch.WordTrace tailWord_3690361 prefixEnd_3690361 1894928981606941179315845 := by
  unfold tailWord_3690361
  simp only [CollatzResearch.WordTrace]
  refine ⟨134598523383459835326070937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89732348922306556884047291 134598523383459835326070937)
  ·
    refine ⟨100948892537594876494553203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134598523383459835326070937 100948892537594876494553203)
    ·
      refine ⟨151423338806392314741829805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100948892537594876494553203 151423338806392314741829805)
      ·
        refine ⟨56783752052397118028186177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151423338806392314741829805 56783752052397118028186177)
        ·
          refine ⟨42587814039297838521139633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56783752052397118028186177 42587814039297838521139633)
          ·
            refine ⟨31940860529473378890854725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42587814039297838521139633 31940860529473378890854725)
            ·
              refine ⟨5988911349276258542035261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31940860529473378890854725 5988911349276258542035261)
              ·
                refine ⟨2245841755978596953263223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5988911349276258542035261 2245841755978596953263223)
                ·
                  refine ⟨3368762633967895429894835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245841755978596953263223 3368762633967895429894835)
                  ·
                    refine ⟨5053143950951843144842253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3368762633967895429894835 5053143950951843144842253)
                    ·
                      refine ⟨1894928981606941179315845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053143950951843144842253 1894928981606941179315845)
                      ·
                        rfl

theorem cell23_3690361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_3690361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690361 prefixEnd_3690361 := by exact prefixLift 3690361
  have htrace : WordTrace (prefixWord ++ tailWord_3690361) baseStart_3690361 baseEnd_3690361 := by
    simpa [prefixWord, tailWord_3690361, baseEnd_3690361] using wordTrace_append hprefix tailTrace_3690361
  have hstable : (prefixWord ++ tailWord_3690361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690361).length < 2 ^ (prefixWord ++ tailWord_3690361).sum := by decide
  have hdescent : baseEnd_3690361 < baseStart_3690361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690377 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 4, 4]
def baseStart_3690377 : Nat := 118140960795 + 3690377 * 2 ^ 59
def prefixEnd_3690377 : Nat := 4983230072969 + 3 ^ 40 * 3690377 * 2
def baseEnd_3690377 : Nat := 631645732432471038905257

theorem tailTrace_3690377 : CollatzResearch.WordTrace tailWord_3690377 prefixEnd_3690377 631645732432471038905257 := by
  unfold tailWord_3690377
  simp only [CollatzResearch.WordTrace]
  refine ⟨134599106951401870058653385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89732737967601246705768923 134599106951401870058653385)
  ·
    refine ⟨100949330213551402543990039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134599106951401870058653385 100949330213551402543990039)
    ·
      refine ⟨151423995320327103815985059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100949330213551402543990039 151423995320327103815985059)
      ·
        refine ⟨227135992980490655723977589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151423995320327103815985059 227135992980490655723977589)
        ·
          refine ⟨21293999341920998974122899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227135992980490655723977589 21293999341920998974122899)
          ·
            refine ⟨31940999012881498461184349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21293999341920998974122899 31940999012881498461184349)
            ·
              refine ⟨11977874629830561922944131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31940999012881498461184349 11977874629830561922944131)
              ·
                refine ⟨17966811944745842884416197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977874629830561922944131 17966811944745842884416197)
                ·
                  refine ⟨3368777239639845540828037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17966811944745842884416197 3368777239639845540828037)
                  ·
                    refine ⟨631645732432471038905257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368777239639845540828037 631645732432471038905257)
                    ·
                      rfl

theorem cell23_3690377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_3690377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690377 prefixEnd_3690377 := by exact prefixLift 3690377
  have htrace : WordTrace (prefixWord ++ tailWord_3690377) baseStart_3690377 baseEnd_3690377 := by
    simpa [prefixWord, tailWord_3690377, baseEnd_3690377] using wordTrace_append hprefix tailTrace_3690377
  have hstable : (prefixWord ++ tailWord_3690377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690377).length < 2 ^ (prefixWord ++ tailWord_3690377).sum := by decide
  have hdescent : baseEnd_3690377 < baseStart_3690377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690380 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_3690380 : Nat := 118140960795 + 3690380 * 2 ^ 59
def prefixEnd_3690380 : Nat := 4983230072969 + 3 ^ 40 * 3690380 * 2
def baseEnd_3690380 : Nat := 1894938737739376604978257

theorem tailTrace_3690380 : CollatzResearch.WordTrace tailWord_3690380 prefixEnd_3690380 1894938737739376604978257 := by
  unfold tailWord_3690380
  simp only [CollatzResearch.WordTrace]
  refine ⟨67299608185195500785506297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89732810913594001047341729 67299608185195500785506297)
  ·
    refine ⟨50474706138896625589129723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67299608185195500785506297 50474706138896625589129723)
    ·
      refine ⟨75712059208344938383694585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50474706138896625589129723 75712059208344938383694585)
      ·
        refine ⟨56784044406258703787770939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75712059208344938383694585 56784044406258703787770939)
        ·
          refine ⟨85176066609388055681656409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56784044406258703787770939 85176066609388055681656409)
          ·
            refine ⟨63882049957041041761242307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85176066609388055681656409 63882049957041041761242307)
            ·
              refine ⟨95823074935561562641863461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63882049957041041761242307 95823074935561562641863461)
              ·
                refine ⟨17966826550417792995349399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95823074935561562641863461 17966826550417792995349399)
                ·
                  refine ⟨26950239825626689493024099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17966826550417792995349399 26950239825626689493024099)
                  ·
                    refine ⟨40425359738440034239536149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26950239825626689493024099 40425359738440034239536149)
                    ·
                      refine ⟨1894938737739376604978257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40425359738440034239536149 1894938737739376604978257)
                      ·
                        rfl

theorem cell23_3690380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_3690380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690380 prefixEnd_3690380 := by exact prefixLift 3690380
  have htrace : WordTrace (prefixWord ++ tailWord_3690380) baseStart_3690380 baseEnd_3690380 := by
    simpa [prefixWord, tailWord_3690380, baseEnd_3690380] using wordTrace_append hprefix tailTrace_3690380
  have hstable : (prefixWord ++ tailWord_3690380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690380).length < 2 ^ (prefixWord ++ tailWord_3690380).sum := by decide
  have hdescent : baseEnd_3690380 < baseStart_3690380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690384 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 3, 2, 2]
def baseStart_3690384 : Nat := 118140960795 + 3690384 * 2 ^ 59
def prefixEnd_3690384 : Nat := 4983230072969 + 3 ^ 40 * 3690384 * 2
def baseEnd_3690384 : Nat := 1894940791661994589328239

theorem tailTrace_3690384 : CollatzResearch.WordTrace tailWord_3690384 prefixEnd_3690384 1894940791661994589328239 := by
  unfold tailWord_3690384
  simp only [CollatzResearch.WordTrace]
  refine ⟨67299681131188255127079103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89732908174917673502772137 67299681131188255127079103)
  ·
    refine ⟨100949521696782382690618655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67299681131188255127079103 100949521696782382690618655)
    ·
      refine ⟨151424282545173574035927983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100949521696782382690618655 151424282545173574035927983)
      ·
        refine ⟨227136423817760361053891975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151424282545173574035927983 227136423817760361053891975)
        ·
          refine ⟨340704635726640541580837963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227136423817760361053891975 340704635726640541580837963)
          ·
            refine ⟨511056953589960812371256945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340704635726640541580837963 511056953589960812371256945)
            ·
              refine ⟨383292715192470609278442709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511056953589960812371256945 383292715192470609278442709)
              ·
                refine ⟨8983423012323529904963501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 383292715192470609278442709 8983423012323529904963501)
                ·
                  refine ⟨3368783629621323714361313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8983423012323529904963501 3368783629621323714361313)
                  ·
                    refine ⟨2526587722215992785770985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368783629621323714361313 2526587722215992785770985)
                    ·
                      refine ⟨1894940791661994589328239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526587722215992785770985 1894940791661994589328239)
                      ·
                        rfl

theorem cell23_3690384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 2, 2].length) (baseStart_3690384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690384 prefixEnd_3690384 := by exact prefixLift 3690384
  have htrace : WordTrace (prefixWord ++ tailWord_3690384) baseStart_3690384 baseEnd_3690384 := by
    simpa [prefixWord, tailWord_3690384, baseEnd_3690384] using wordTrace_append hprefix tailTrace_3690384
  have hstable : (prefixWord ++ tailWord_3690384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690384).length < 2 ^ (prefixWord ++ tailWord_3690384).sum := by decide
  have hdescent : baseEnd_3690384 < baseStart_3690384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690394 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_3690394 : Nat := 118140960795 + 3690394 * 2 ^ 59
def prefixEnd_3690394 : Nat := 4983230072969 + 3 ^ 40 * 3690394 * 2
def baseEnd_3690394 : Nat := 631648642156179850067731

theorem tailTrace_3690394 : CollatzResearch.WordTrace tailWord_3690394 prefixEnd_3690394 631648642156179850067731 := by
  unfold tailWord_3690394
  simp only [CollatzResearch.WordTrace]
  refine ⟨33649931748085070490505559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89733151328226854641348157 33649931748085070490505559)
  ·
    refine ⟨50474897622127605735758339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33649931748085070490505559 50474897622127605735758339)
    ·
      refine ⟨75712346433191408603637509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50474897622127605735758339 75712346433191408603637509)
      ·
        refine ⟨14196064956223389113182033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75712346433191408603637509 14196064956223389113182033)
        ·
          refine ⟨10647048717167541834886525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14196064956223389113182033 10647048717167541834886525)
          ·
            refine ⟨3992643268937828188082447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10647048717167541834886525 3992643268937828188082447)
            ·
              refine ⟨5988964903406742282123671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992643268937828188082447 5988964903406742282123671)
              ·
                refine ⟨8983447355110113423185507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988964903406742282123671 8983447355110113423185507)
                ·
                  refine ⟨13475171032665170134778261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8983447355110113423185507 13475171032665170134778261)
                  ·
                    refine ⟨631648642156179850067731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13475171032665170134778261 631648642156179850067731)
                    ·
                      rfl

theorem cell23_3690394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_3690394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690394 prefixEnd_3690394 := by exact prefixLift 3690394
  have htrace : WordTrace (prefixWord ++ tailWord_3690394) baseStart_3690394 baseEnd_3690394 := by
    simpa [prefixWord, tailWord_3690394, baseEnd_3690394] using wordTrace_append hprefix tailTrace_3690394
  have hstable : (prefixWord ++ tailWord_3690394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690394).length < 2 ^ (prefixWord ++ tailWord_3690394).sum := by decide
  have hdescent : baseEnd_3690394 < baseStart_3690394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690397 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3690397 : Nat := 118140960795 + 3690397 * 2 ^ 59
def prefixEnd_3690397 : Nat := 4983230072969 + 3 ^ 40 * 3690397 * 2
def baseEnd_3690397 : Nat := 1894947466910503038465679

theorem tailTrace_3690397 : CollatzResearch.WordTrace tailWord_3690397 prefixEnd_3690397 1894947466910503038465679 := by
  unfold tailWord_3690397
  simp only [CollatzResearch.WordTrace]
  refine ⟨134599836411329413474381445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89733224274219608982920963 134599836411329413474381445)
  ·
    refine ⟨25237469327124265026446521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134599836411329413474381445 25237469327124265026446521)
    ·
      refine ⟨18928101995343198769834891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25237469327124265026446521 18928101995343198769834891)
      ·
        refine ⟨28392152993014798154752337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18928101995343198769834891 28392152993014798154752337)
        ·
          refine ⟨21294114744761098616064253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28392152993014798154752337 21294114744761098616064253)
          ·
            refine ⟨7985293029285411981024095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21294114744761098616064253 7985293029285411981024095)
            ·
              refine ⟨11977939543928117971536143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7985293029285411981024095 11977939543928117971536143)
              ·
                refine ⟨17966909315892176957304215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977939543928117971536143 17966909315892176957304215)
                ·
                  refine ⟨26950363973838265435956323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17966909315892176957304215 26950363973838265435956323)
                  ·
                    refine ⟨40425545960757398153934485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26950363973838265435956323 40425545960757398153934485)
                    ·
                      refine ⟨1894947466910503038465679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40425545960757398153934485 1894947466910503038465679)
                      ·
                        rfl

theorem cell23_3690397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3690397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690397 prefixEnd_3690397 := by exact prefixLift 3690397
  have htrace : WordTrace (prefixWord ++ tailWord_3690397) baseStart_3690397 baseEnd_3690397 := by
    simpa [prefixWord, tailWord_3690397, baseEnd_3690397] using wordTrace_append hprefix tailTrace_3690397
  have hstable : (prefixWord ++ tailWord_3690397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690397).length < 2 ^ (prefixWord ++ tailWord_3690397).sum := by decide
  have hdescent : baseEnd_3690397 < baseStart_3690397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690398 : List Nat := [4, 3, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3690398 : Nat := 118140960795 + 3690398 * 2 ^ 59
def prefixEnd_3690398 : Nat := 4983230072969 + 3 ^ 40 * 3690398 * 2
def baseEnd_3690398 : Nat := 631649326797052511517725

theorem tailTrace_3690398 : CollatzResearch.WordTrace tailWord_3690398 prefixEnd_3690398 631649326797052511517725 := by
  unfold tailWord_3690398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824984110540723830645981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89733248589550527096778565 16824984110540723830645981)
  ·
    refine ⟨6309369041452771436492243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16824984110540723830645981 6309369041452771436492243)
    ·
      refine ⟨9464053562179157154738365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309369041452771436492243 9464053562179157154738365)
      ·
        refine ⟨3549020085817183933026887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9464053562179157154738365 3549020085817183933026887)
        ·
          refine ⟨5323530128725775899540331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549020085817183933026887 5323530128725775899540331)
          ·
            refine ⟨7985295193088663849310497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323530128725775899540331 7985295193088663849310497)
            ·
              refine ⟨5988971394816497886982873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7985295193088663849310497 5988971394816497886982873)
              ·
                refine ⟨4491728546112373415237155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988971394816497886982873 4491728546112373415237155)
                ·
                  refine ⟨6737592819168560122855733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491728546112373415237155 6737592819168560122855733)
                  ·
                    refine ⟨631649326797052511517725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6737592819168560122855733 631649326797052511517725)
                    ·
                      rfl

theorem cell23_3690398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3690398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690398 prefixEnd_3690398 := by exact prefixLift 3690398
  have htrace : WordTrace (prefixWord ++ tailWord_3690398) baseStart_3690398 baseEnd_3690398 := by
    simpa [prefixWord, tailWord_3690398, baseEnd_3690398] using wordTrace_append hprefix tailTrace_3690398
  have hstable : (prefixWord ++ tailWord_3690398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690398).length < 2 ^ (prefixWord ++ tailWord_3690398).sum := by decide
  have hdescent : baseEnd_3690398 < baseStart_3690398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690401 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3690401 : Nat := 118140960795 + 3690401 * 2 ^ 59
def prefixEnd_3690401 : Nat := 4983230072969 + 3 ^ 40 * 3690401 * 2
def baseEnd_3690401 : Nat := 1894949520833121022815661

theorem tailTrace_3690401 : CollatzResearch.WordTrace tailWord_3690401 prefixEnd_3690401 1894949520833121022815661 := by
  unfold tailWord_3690401
  simp only [CollatzResearch.WordTrace]
  refine ⟨134599982303314922157527057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89733321535543281438351371 134599982303314922157527057)
  ·
    refine ⟨100949986727486191618145293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134599982303314922157527057 100949986727486191618145293)
    ·
      refine ⟨37856245022807321856804485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100949986727486191618145293 37856245022807321856804485)
      ·
        refine ⟨7098045941776372848150841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37856245022807321856804485 7098045941776372848150841)
        ·
          refine ⟨5323534456332279636113131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7098045941776372848150841 5323534456332279636113131)
          ·
            refine ⟨7985301684498419454169697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323534456332279636113131 7985301684498419454169697)
            ·
              refine ⟨5988976263373814590627273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7985301684498419454169697 5988976263373814590627273)
              ·
                refine ⟨4491732197530360942970455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988976263373814590627273 4491732197530360942970455)
                ·
                  refine ⟨6737598296295541414455683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491732197530360942970455 6737598296295541414455683)
                  ·
                    refine ⟨10106397444443312121683525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6737598296295541414455683 10106397444443312121683525)
                    ·
                      refine ⟨1894949520833121022815661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10106397444443312121683525 1894949520833121022815661)
                      ·
                        rfl

theorem cell23_3690401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3690401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690401 prefixEnd_3690401 := by exact prefixLift 3690401
  have htrace : WordTrace (prefixWord ++ tailWord_3690401) baseStart_3690401 baseEnd_3690401 := by
    simpa [prefixWord, tailWord_3690401, baseEnd_3690401] using wordTrace_append hprefix tailTrace_3690401
  have hstable : (prefixWord ++ tailWord_3690401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690401).length < 2 ^ (prefixWord ++ tailWord_3690401).sum := by decide
  have hdescent : baseEnd_3690401 < baseStart_3690401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690404 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_3690404 : Nat := 118140960795 + 3690404 * 2 ^ 59
def prefixEnd_3690404 : Nat := 4983230072969 + 3 ^ 40 * 3690404 * 2
def baseEnd_3690404 : Nat := 1894951061275084511078147

theorem tailTrace_3690404 : CollatzResearch.WordTrace tailWord_3690404 prefixEnd_3690404 1894951061275084511078147 := by
  unfold tailWord_3690404
  simp only [CollatzResearch.WordTrace]
  refine ⟨67300045861152026834943133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89733394481536035779924177 67300045861152026834943133)
  ·
    refine ⟨25237517197932010063103675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67300045861152026834943133 25237517197932010063103675)
    ·
      refine ⟨37856275796898015094655513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25237517197932010063103675 37856275796898015094655513)
      ·
        refine ⟨28392206847673511320991635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37856275796898015094655513 28392206847673511320991635)
        ·
          refine ⟨42588310271510266981487453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28392206847673511320991635 42588310271510266981487453)
          ·
            refine ⟨15970616351816350118057795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42588310271510266981487453 15970616351816350118057795)
            ·
              refine ⟨23955924527724525177086693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15970616351816350118057795 23955924527724525177086693)
              ·
                refine ⟨4491735848948348470703755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23955924527724525177086693 4491735848948348470703755)
                ·
                  refine ⟨6737603773422522706055633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491735848948348470703755 6737603773422522706055633)
                  ·
                    refine ⟨5053202830066892029541725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6737603773422522706055633 5053202830066892029541725)
                    ·
                      refine ⟨1894951061275084511078147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053202830066892029541725 1894951061275084511078147)
                      ·
                        rfl

theorem cell23_3690404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_3690404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690404 prefixEnd_3690404 := by exact prefixLift 3690404
  have htrace : WordTrace (prefixWord ++ tailWord_3690404) baseStart_3690404 baseEnd_3690404 := by
    simpa [prefixWord, tailWord_3690404, baseEnd_3690404] using wordTrace_append hprefix tailTrace_3690404
  have hstable : (prefixWord ++ tailWord_3690404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690404).length < 2 ^ (prefixWord ++ tailWord_3690404).sum := by decide
  have hdescent : baseEnd_3690404 < baseStart_3690404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690407 : List Nat := [1, 1, 6, 1, 2, 2, 1, 9]
def baseStart_3690407 : Nat := 118140960795 + 3690407 * 2 ^ 59
def prefixEnd_3690407 : Nat := 4983230072969 + 3 ^ 40 * 3690407 * 2
def baseEnd_3690407 : Nat := 70183429693223999975579

theorem tailTrace_3690407 : CollatzResearch.WordTrace tailWord_3690407 prefixEnd_3690407 70183429693223999975579 := by
  unfold tailWord_3690407
  simp only [CollatzResearch.WordTrace]
  refine ⟨134600201141293185182245475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89733467427528790121496983 134600201141293185182245475)
  ·
    refine ⟨201900301711939777773368213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134600201141293185182245475 201900301711939777773368213)
    ·
      refine ⟨9464076642747177083126635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201900301711939777773368213 9464076642747177083126635)
      ·
        refine ⟨14196114964120765624689953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9464076642747177083126635 14196114964120765624689953)
        ·
          refine ⟨10647086223090574218517465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14196114964120765624689953 10647086223090574218517465)
          ·
            refine ⟨7985314667317930663888099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10647086223090574218517465 7985314667317930663888099)
            ·
              refine ⟨11977972000976895995832149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7985314667317930663888099 11977972000976895995832149)
              ·
                refine ⟨70183429693223999975579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11977972000976895995832149 70183429693223999975579)
                ·
                  rfl

theorem cell23_3690407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 9].length) (baseStart_3690407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690407 prefixEnd_3690407 := by exact prefixLift 3690407
  have htrace : WordTrace (prefixWord ++ tailWord_3690407) baseStart_3690407 baseEnd_3690407 := by
    simpa [prefixWord, tailWord_3690407, baseEnd_3690407] using wordTrace_append hprefix tailTrace_3690407
  have hstable : (prefixWord ++ tailWord_3690407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690407).length < 2 ^ (prefixWord ++ tailWord_3690407).sum := by decide
  have hdescent : baseEnd_3690407 < baseStart_3690407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690491 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 2, 2, 2]
def baseStart_3690491 : Nat := 118140960795 + 3690491 * 2 ^ 59
def prefixEnd_3690491 : Nat := 4983230072969 + 3 ^ 40 * 3690491 * 2
def baseEnd_3690491 : Nat := 1894995734092025670690247

theorem tailTrace_3690491 : CollatzResearch.WordTrace tailWord_3690491 prefixEnd_3690491 1894995734092025670690247 := by
  unfold tailWord_3690491
  simp only [CollatzResearch.WordTrace]
  refine ⟨134603264872988867528303327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89735509915325911685535551 134603264872988867528303327)
  ·
    refine ⟨201904897309483301292454991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134603264872988867528303327 201904897309483301292454991)
    ·
      refine ⟨302857345964224951938682487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201904897309483301292454991 302857345964224951938682487)
      ·
        refine ⟨454286018946337427908023731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302857345964224951938682487 454286018946337427908023731)
        ·
          refine ⟨681429028419506141862035597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454286018946337427908023731 681429028419506141862035597)
          ·
            refine ⟨255535885657314803198263349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 681429028419506141862035597 255535885657314803198263349)
            ·
              refine ⟨23956489280373262799837189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255535885657314803198263349 23956489280373262799837189)
              ·
                refine ⟨4491841740069986774969473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23956489280373262799837189 4491841740069986774969473)
                ·
                  refine ⟨3368881305052490081227105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491841740069986774969473 3368881305052490081227105)
                  ·
                    refine ⟨2526660978789367560920329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368881305052490081227105 2526660978789367560920329)
                    ·
                      refine ⟨1894995734092025670690247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526660978789367560920329 1894995734092025670690247)
                      ·
                        rfl

theorem cell23_3690491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 2, 2].length) (baseStart_3690491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690491 prefixEnd_3690491 := by exact prefixLift 3690491
  have htrace : WordTrace (prefixWord ++ tailWord_3690491) baseStart_3690491 baseEnd_3690491 := by
    simpa [prefixWord, tailWord_3690491, baseEnd_3690491] using wordTrace_append hprefix tailTrace_3690491
  have hstable : (prefixWord ++ tailWord_3690491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690491).length < 2 ^ (prefixWord ++ tailWord_3690491).sum := by decide
  have hdescent : baseEnd_3690491 < baseStart_3690491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690497 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 7]
def baseStart_3690497 : Nat := 118140960795 + 3690497 * 2 ^ 59
def prefixEnd_3690497 : Nat := 4983230072969 + 3 ^ 40 * 3690497 * 2
def baseEnd_3690497 : Nat := 210555423886216960801691

theorem tailTrace_3690497 : CollatzResearch.WordTrace tailWord_3690497 prefixEnd_3690497 210555423886216960801691 := by
  unfold tailWord_3690497
  simp only [CollatzResearch.WordTrace]
  refine ⟨134603483710967130553021745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89735655807311420368681163 134603483710967130553021745)
  ·
    refine ⟨100952612783225347914766309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134603483710967130553021745 100952612783225347914766309)
    ·
      refine ⟨18928614896854752734018683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100952612783225347914766309 18928614896854752734018683)
      ·
        refine ⟨28392922345282129101028025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18928614896854752734018683 28392922345282129101028025)
        ·
          refine ⟨21294691758961596825771019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28392922345282129101028025 21294691758961596825771019)
          ·
            refine ⟨31942037638442395238656529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21294691758961596825771019 31942037638442395238656529)
            ·
              refine ⟨23956528228831796428992397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31942037638442395238656529 23956528228831796428992397)
              ·
                refine ⟨8983698085811923660872149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23956528228831796428992397 8983698085811923660872149)
                ·
                  refine ⟨210555423886216960801691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8983698085811923660872149 210555423886216960801691)
                  ·
                    rfl

theorem cell23_3690497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 7].length) (baseStart_3690497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690497 prefixEnd_3690497 := by exact prefixLift 3690497
  have htrace : WordTrace (prefixWord ++ tailWord_3690497) baseStart_3690497 baseEnd_3690497 := by
    simpa [prefixWord, tailWord_3690497, baseEnd_3690497] using wordTrace_append hprefix tailTrace_3690497
  have hstable : (prefixWord ++ tailWord_3690497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690497).length < 2 ^ (prefixWord ++ tailWord_3690497).sum := by decide
  have hdescent : baseEnd_3690497 < baseStart_3690497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690502 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3690502 : Nat := 118140960795 + 3690502 * 2 ^ 59
def prefixEnd_3690502 : Nat := 4983230072969 + 3 ^ 40 * 3690502 * 2
def baseEnd_3690502 : Nat := 1895001382379225127652697

theorem tailTrace_3690502 : CollatzResearch.WordTrace tailWord_3690502 prefixEnd_3690502 1895001382379225127652697 := by
  unfold tailWord_3690502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206364564873406762717305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89735777383966010937969173 4206364564873406762717305)
  ·
    refine ⟨3154773423655055072037979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4206364564873406762717305 3154773423655055072037979)
    ·
      refine ⟨4732160135482582608056969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154773423655055072037979 4732160135482582608056969)
      ·
        refine ⟨3549120101611936956042727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4732160135482582608056969 3549120101611936956042727)
        ·
          refine ⟨5323680152417905434064091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549120101611936956042727 5323680152417905434064091)
          ·
            refine ⟨7985520228626858151096137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5323680152417905434064091 7985520228626858151096137)
            ·
              refine ⟨5989140171470143613322103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7985520228626858151096137 5989140171470143613322103)
              ·
                refine ⟨8983710257205215419983155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989140171470143613322103 8983710257205215419983155)
                ·
                  refine ⟨13475565385807823129974733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8983710257205215419983155 13475565385807823129974733)
                  ·
                    refine ⟨5053337019677933673740525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13475565385807823129974733 5053337019677933673740525)
                    ·
                      refine ⟨1895001382379225127652697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053337019677933673740525 1895001382379225127652697)
                      ·
                        rfl

theorem cell23_3690502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3690502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690502 prefixEnd_3690502 := by exact prefixLift 3690502
  have htrace : WordTrace (prefixWord ++ tailWord_3690502) baseStart_3690502 baseEnd_3690502 := by
    simpa [prefixWord, tailWord_3690502, baseEnd_3690502] using wordTrace_append hprefix tailTrace_3690502
  have hstable : (prefixWord ++ tailWord_3690502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690502).length < 2 ^ (prefixWord ++ tailWord_3690502).sum := by decide
  have hdescent : baseEnd_3690502 < baseStart_3690502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690527 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 1, 7]
def baseStart_3690527 : Nat := 118140960795 + 3690527 * 2 ^ 59
def prefixEnd_3690527 : Nat := 4983230072969 + 3 ^ 40 * 3690527 * 2
def baseEnd_3690527 : Nat := 631671406465195843280027

theorem tailTrace_3690527 : CollatzResearch.WordTrace tailWord_3690527 prefixEnd_3690527 631671406465195843280027 := by
  unfold tailWord_3690527
  simp only [CollatzResearch.WordTrace]
  refine ⟨134604577900858445676613835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89736385267238963784409223 134604577900858445676613835)
  ·
    refine ⟨201906866851287668514920753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134604577900858445676613835 201906866851287668514920753)
    ·
      refine ⟨151430150138465751386190565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201906866851287668514920753 151430150138465751386190565)
      ·
        refine ⟨28393153150962328384910731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151430150138465751386190565 28393153150962328384910731)
        ·
          refine ⟨42589729726443492577366097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28393153150962328384910731 42589729726443492577366097)
          ·
            refine ⟨31942297294832619433024573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42589729726443492577366097 31942297294832619433024573)
            ·
              refine ⟨11978361485562232287384215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31942297294832619433024573 11978361485562232287384215)
              ·
                refine ⟨17967542228343348431076323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978361485562232287384215 17967542228343348431076323)
                ·
                  refine ⟨26951313342515022646614485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17967542228343348431076323 26951313342515022646614485)
                  ·
                    refine ⟨631671406465195843280027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26951313342515022646614485 631671406465195843280027)
                    ·
                      rfl

theorem cell23_3690527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_3690527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690527 prefixEnd_3690527 := by exact prefixLift 3690527
  have htrace : WordTrace (prefixWord ++ tailWord_3690527) baseStart_3690527 baseEnd_3690527 := by
    simpa [prefixWord, tailWord_3690527, baseEnd_3690527] using wordTrace_append hprefix tailTrace_3690527
  have hstable : (prefixWord ++ tailWord_3690527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690527).length < 2 ^ (prefixWord ++ tailWord_3690527).sum := by decide
  have hdescent : baseEnd_3690527 < baseStart_3690527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690577 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3690577 : Nat := 118140960795 + 3690577 * 2 ^ 59
def prefixEnd_3690577 : Nat := 4983230072969 + 3 ^ 40 * 3690577 * 2
def baseEnd_3690577 : Nat := 1895039893428312334214851

theorem tailTrace_3690577 : CollatzResearch.WordTrace tailWord_3690577 prefixEnd_3690577 1895039893428312334214851 := by
  unfold tailWord_3690577
  simp only [CollatzResearch.WordTrace]
  refine ⟨134606401550677304215933985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89737601033784869477289323 134606401550677304215933985)
  ·
    refine ⟨100954801163007978161950489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134606401550677304215933985 100954801163007978161950489)
    ·
      refine ⟨75716100872255983621462867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100954801163007978161950489 75716100872255983621462867)
      ·
        refine ⟨113574151308383975432194301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75716100872255983621462867 113574151308383975432194301)
        ·
          refine ⟨42590306740643990787072863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113574151308383975432194301 42590306740643990787072863)
          ·
            refine ⟨63885460110965986180609295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42590306740643990787072863 63885460110965986180609295)
            ·
              refine ⟨95828190166448979270913943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63885460110965986180609295 95828190166448979270913943)
              ·
                refine ⟨143742285249673468906370915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95828190166448979270913943 143742285249673468906370915)
                ·
                  refine ⟨215613427874510203359556373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143742285249673468906370915 215613427874510203359556373)
                  ·
                    refine ⟨10106879431617665782479205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215613427874510203359556373 10106879431617665782479205)
                    ·
                      refine ⟨1895039893428312334214851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10106879431617665782479205 1895039893428312334214851)
                      ·
                        rfl

theorem cell23_3690577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3690577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690577 prefixEnd_3690577 := by exact prefixLift 3690577
  have htrace : WordTrace (prefixWord ++ tailWord_3690577) baseStart_3690577 baseEnd_3690577 := by
    simpa [prefixWord, tailWord_3690577, baseEnd_3690577] using wordTrace_append hprefix tailTrace_3690577
  have hstable : (prefixWord ++ tailWord_3690577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690577).length < 2 ^ (prefixWord ++ tailWord_3690577).sum := by decide
  have hdescent : baseEnd_3690577 < baseStart_3690577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690584 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_3690584 : Nat := 118140960795 + 3690584 * 2 ^ 59
def prefixEnd_3690584 : Nat := 4983230072969 + 3 ^ 40 * 3690584 * 2
def baseEnd_3690584 : Nat := 1895043487792893806827319

theorem tailTrace_3690584 : CollatzResearch.WordTrace tailWord_3690584 prefixEnd_3690584 1895043487792893806827319 := by
  unfold tailWord_3690584
  simp only [CollatzResearch.WordTrace]
  refine ⟨67303328430825972205719403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89737771241101296274292537 67303328430825972205719403)
  ·
    refine ⟨100954992646238958308579105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67303328430825972205719403 100954992646238958308579105)
    ·
      refine ⟨75716244484679218731434329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100954992646238958308579105 75716244484679218731434329)
      ·
        refine ⟨56787183363509414048575747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75716244484679218731434329 56787183363509414048575747)
        ·
          refine ⟨85180775045264121072863621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56787183363509414048575747 85180775045264121072863621)
          ·
            refine ⟨15971395320987022701161929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85180775045264121072863621 15971395320987022701161929)
            ·
              refine ⟨11978546490740267025871447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15971395320987022701161929 11978546490740267025871447)
              ·
                refine ⟨17967819736110400538807171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11978546490740267025871447 17967819736110400538807171)
                ·
                  refine ⟨26951729604165600808210757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17967819736110400538807171 26951729604165600808210757)
                  ·
                    refine ⟨5053449300781050151539517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26951729604165600808210757 5053449300781050151539517)
                    ·
                      refine ⟨1895043487792893806827319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053449300781050151539517 1895043487792893806827319)
                      ·
                        rfl

theorem cell23_3690584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_3690584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690584 prefixEnd_3690584 := by exact prefixLift 3690584
  have htrace : WordTrace (prefixWord ++ tailWord_3690584) baseStart_3690584 baseEnd_3690584 := by
    simpa [prefixWord, tailWord_3690584, baseEnd_3690584] using wordTrace_append hprefix tailTrace_3690584
  have hstable : (prefixWord ++ tailWord_3690584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690584).length < 2 ^ (prefixWord ++ tailWord_3690584).sum := by decide
  have hdescent : baseEnd_3690584 < baseStart_3690584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690591 : List Nat := [1, 1, 2, 3, 1, 1, 2, 7, 1, 4]
def baseStart_3690591 : Nat := 118140960795 + 3690591 * 2 ^ 59
def prefixEnd_3690591 : Nat := 4983230072969 + 3 ^ 40 * 3690591 * 2
def baseEnd_3690591 : Nat := 631682360719158426479929

theorem tailTrace_3690591 : CollatzResearch.WordTrace tailWord_3690591 prefixEnd_3690591 631682360719158426479929 := by
  unfold tailWord_3690591
  simp only [CollatzResearch.WordTrace]
  refine ⟨134606912172626584606943627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89737941448417723071295751 134606912172626584606943627)
  ·
    refine ⟨201910368258939876910415441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134606912172626584606943627 201910368258939876910415441)
    ·
      refine ⟨151432776194204907682811581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201910368258939876910415441 151432776194204907682811581)
      ·
        refine ⟨56787291072826840381054343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151432776194204907682811581 56787291072826840381054343)
        ·
          refine ⟨85180936609240260571581515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56787291072826840381054343 85180936609240260571581515)
          ·
            refine ⟨127771404913860390857372273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85180936609240260571581515 127771404913860390857372273)
            ·
              refine ⟨95828553685395293143029205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127771404913860390857372273 95828553685395293143029205)
              ·
                refine ⟨2245981727001452183039747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95828553685395293143029205 2245981727001452183039747)
                ·
                  refine ⟨3368972590502178274559621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245981727001452183039747 3368972590502178274559621)
                  ·
                    refine ⟨631682360719158426479929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368972590502178274559621 631682360719158426479929)
                    ·
                      rfl

theorem cell23_3690591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 1, 4].length) (baseStart_3690591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690591 prefixEnd_3690591 := by exact prefixLift 3690591
  have htrace : WordTrace (prefixWord ++ tailWord_3690591) baseStart_3690591 baseEnd_3690591 := by
    simpa [prefixWord, tailWord_3690591, baseEnd_3690591] using wordTrace_append hprefix tailTrace_3690591
  have hstable : (prefixWord ++ tailWord_3690591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690591).length < 2 ^ (prefixWord ++ tailWord_3690591).sum := by decide
  have hdescent : baseEnd_3690591 < baseStart_3690591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690621 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 6]
def baseStart_3690621 : Nat := 118140960795 + 3690621 * 2 ^ 59
def prefixEnd_3690621 : Nat := 4983230072969 + 3 ^ 40 * 3690621 * 2
def baseEnd_3690621 : Nat := 210562498508567795784961

theorem tailTrace_3690621 : CollatzResearch.WordTrace tailWord_3690621 prefixEnd_3690621 210562498508567795784961 := by
  unfold tailWord_3690621
  simp only [CollatzResearch.WordTrace]
  refine ⟨134608006362517899730535717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89738670908345266487023811 134608006362517899730535717)
  ·
    refine ⟨25239001192972106199475447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134608006362517899730535717 25239001192972106199475447)
    ·
      refine ⟨37858501789458159299213171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25239001192972106199475447 37858501789458159299213171)
      ·
        refine ⟨56787752684187238948819757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37858501789458159299213171 56787752684187238948819757)
        ·
          refine ⟨21295407256570214605807409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56787752684187238948819757 21295407256570214605807409)
          ·
            refine ⟨15971555442427660954355557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21295407256570214605807409 15971555442427660954355557)
            ·
              refine ⟨2994666645455186428941667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15971555442427660954355557 2994666645455186428941667)
              ·
                refine ⟨4491999968182779643412501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994666645455186428941667 4491999968182779643412501)
                ·
                  refine ⟨210562498508567795784961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4491999968182779643412501 210562498508567795784961)
                  ·
                    rfl

theorem cell23_3690621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_3690621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690621 prefixEnd_3690621 := by exact prefixLift 3690621
  have htrace : WordTrace (prefixWord ++ tailWord_3690621) baseStart_3690621 baseEnd_3690621 := by
    simpa [prefixWord, tailWord_3690621, baseEnd_3690621] using wordTrace_append hprefix tailTrace_3690621
  have hstable : (prefixWord ++ tailWord_3690621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690621).length < 2 ^ (prefixWord ++ tailWord_3690621).sum := by decide
  have hdescent : baseEnd_3690621 < baseStart_3690621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690631 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_3690631 : Nat := 118140960795 + 3690631 * 2 ^ 59
def prefixEnd_3690631 : Nat := 4983230072969 + 3 ^ 40 * 3690631 * 2
def baseEnd_3690631 : Nat := 1895067621383655122939603

theorem tailTrace_3690631 : CollatzResearch.WordTrace tailWord_3690631 prefixEnd_3690631 1895067621383655122939603 := by
  unfold tailWord_3690631
  simp only [CollatzResearch.WordTrace]
  refine ⟨134608371092481671438399747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89738914061654447625599831 134608371092481671438399747)
  ·
    refine ⟨201912556638722507157599621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134608371092481671438399747 201912556638722507157599621)
    ·
      refine ⟨37858604369760470092049929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201912556638722507157599621 37858604369760470092049929)
      ·
        refine ⟨28393953277320352569037447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37858604369760470092049929 28393953277320352569037447)
        ·
          refine ⟨42590929915980528853556171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28393953277320352569037447 42590929915980528853556171)
          ·
            refine ⟨63886394873970793280334257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42590929915980528853556171 63886394873970793280334257)
            ·
              refine ⟨47914796155478094960250693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63886394873970793280334257 47914796155478094960250693)
              ·
                refine ⟨8984024279152142805047005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47914796155478094960250693 8984024279152142805047005)
                ·
                  refine ⟨3369009104682053551892627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8984024279152142805047005 3369009104682053551892627)
                  ·
                    refine ⟨5053513657023080327838941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369009104682053551892627 5053513657023080327838941)
                    ·
                      refine ⟨1895067621383655122939603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053513657023080327838941 1895067621383655122939603)
                      ·
                        rfl

theorem cell23_3690631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_3690631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690631 prefixEnd_3690631 := by exact prefixLift 3690631
  have htrace : WordTrace (prefixWord ++ tailWord_3690631) baseStart_3690631 baseEnd_3690631 := by
    simpa [prefixWord, tailWord_3690631, baseEnd_3690631] using wordTrace_append hprefix tailTrace_3690631
  have hstable : (prefixWord ++ tailWord_3690631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690631).length < 2 ^ (prefixWord ++ tailWord_3690631).sum := by decide
  have hdescent : baseEnd_3690631 < baseStart_3690631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690674 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_3690674 : Nat := 118140960795 + 3690674 * 2 ^ 59
def prefixEnd_3690674 : Nat := 4983230072969 + 3 ^ 40 * 3690674 * 2
def baseEnd_3690674 : Nat := 1895089701051798454701905

theorem tailTrace_3690674 : CollatzResearch.WordTrace tailWord_3690674 prefixEnd_3690674 1895089701051798454701905 := by
  unfold tailWord_3690674
  simp only [CollatzResearch.WordTrace]
  refine ⟨33652484857831472445553769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89739959620883926521476717 33652484857831472445553769)
  ·
    refine ⟨25239363643373604334165327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33652484857831472445553769 25239363643373604334165327)
    ·
      refine ⟨37859045465060406501247991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25239363643373604334165327 37859045465060406501247991)
      ·
        refine ⟨56788568197590609751871987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37859045465060406501247991 56788568197590609751871987)
        ·
          refine ⟨85182852296385914627807981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56788568197590609751871987 85182852296385914627807981)
          ·
            refine ⟨31943569611144717985427993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85182852296385914627807981 31943569611144717985427993)
            ·
              refine ⟨23957677208358538489070995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31943569611144717985427993 23957677208358538489070995)
              ·
                refine ⟨35936515812537807733606493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23957677208358538489070995 35936515812537807733606493)
                ·
                  refine ⟨13476193429701677900102435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35936515812537807733606493 13476193429701677900102435)
                  ·
                    refine ⟨20214290144552516850153653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13476193429701677900102435 20214290144552516850153653)
                    ·
                      refine ⟨1895089701051798454701905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20214290144552516850153653 1895089701051798454701905)
                      ·
                        rfl

theorem cell23_3690674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_3690674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690674 prefixEnd_3690674 := by exact prefixLift 3690674
  have htrace : WordTrace (prefixWord ++ tailWord_3690674) baseStart_3690674 baseEnd_3690674 := by
    simpa [prefixWord, tailWord_3690674, baseEnd_3690674] using wordTrace_append hprefix tailTrace_3690674
  have hstable : (prefixWord ++ tailWord_3690674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690674).length < 2 ^ (prefixWord ++ tailWord_3690674).sum := by decide
  have hdescent : baseEnd_3690674 < baseStart_3690674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690681 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 2, 4]
def baseStart_3690681 : Nat := 118140960795 + 3690681 * 2 ^ 59
def prefixEnd_3690681 : Nat := 4983230072969 + 3 ^ 40 * 3690681 * 2
def baseEnd_3690681 : Nat := 631697765138793309104791

theorem tailTrace_3690681 : CollatzResearch.WordTrace tailWord_3690681 prefixEnd_3690681 631697765138793309104791 := by
  unfold tailWord_3690681
  simp only [CollatzResearch.WordTrace]
  refine ⟨134610194742300529977719897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89740129828200353318479931 134610194742300529977719897)
  ·
    refine ⟨100957646056725397483289923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134610194742300529977719897 100957646056725397483289923)
    ·
      refine ⟨151436469085088096224934885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100957646056725397483289923 151436469085088096224934885)
      ·
        refine ⟨28394337953454018042175291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151436469085088096224934885 28394337953454018042175291)
        ·
          refine ⟨42591506930181027063262937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28394337953454018042175291 42591506930181027063262937)
          ·
            refine ⟨31943630197635770297447203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42591506930181027063262937 31943630197635770297447203)
            ·
              refine ⟨47915445296453655446170805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31943630197635770297447203 47915445296453655446170805)
              ·
                refine ⟨4492072996542530198078513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47915445296453655446170805 4492072996542530198078513)
                ·
                  refine ⟨3369054747406897648558885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4492072996542530198078513 3369054747406897648558885)
                  ·
                    refine ⟨631697765138793309104791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3369054747406897648558885 631697765138793309104791)
                    ·
                      rfl

theorem cell23_3690681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_3690681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690681 prefixEnd_3690681 := by exact prefixLift 3690681
  have htrace : WordTrace (prefixWord ++ tailWord_3690681) baseStart_3690681 baseEnd_3690681 := by
    simpa [prefixWord, tailWord_3690681, baseEnd_3690681] using wordTrace_append hprefix tailTrace_3690681
  have hstable : (prefixWord ++ tailWord_3690681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690681).length < 2 ^ (prefixWord ++ tailWord_3690681).sum := by decide
  have hdescent : baseEnd_3690681 < baseStart_3690681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690688 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 5, 2, 2]
def baseStart_3690688 : Nat := 118140960795 + 3690688 * 2 ^ 59
def prefixEnd_3690688 : Nat := 4983230072969 + 3 ^ 40 * 3690688 * 2
def baseEnd_3690688 : Nat := 1895096889780961399926841

theorem tailTrace_3690688 : CollatzResearch.WordTrace tailWord_3690688 prefixEnd_3690688 1895096889780961399926841 := by
  unfold tailWord_3690688
  simp only [CollatzResearch.WordTrace]
  refine ⟨67305225026637585086612359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89740300035516780115483145 67305225026637585086612359)
  ·
    refine ⟨100957837539956377629918539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67305225026637585086612359 100957837539956377629918539)
    ·
      refine ⟨151436756309934566444877809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100957837539956377629918539 151436756309934566444877809)
      ·
        refine ⟨113577567232450924833658357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151436756309934566444877809 113577567232450924833658357)
        ·
          refine ⟨10647896928042274203155471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113577567232450924833658357 10647896928042274203155471)
          ·
            refine ⟨15971845392063411304733207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10647896928042274203155471 15971845392063411304733207)
            ·
              refine ⟨23957768088095116957099811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15971845392063411304733207 23957768088095116957099811)
              ·
                refine ⟨35936652132142675435649717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23957768088095116957099811 35936652132142675435649717)
                ·
                  refine ⟨3369061137388375822092161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35936652132142675435649717 3369061137388375822092161)
                  ·
                    refine ⟨2526795853041281866569121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3369061137388375822092161 2526795853041281866569121)
                    ·
                      refine ⟨1895096889780961399926841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526795853041281866569121 1895096889780961399926841)
                      ·
                        rfl

theorem cell23_3690688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_3690688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690688 prefixEnd_3690688 := by exact prefixLift 3690688
  have htrace : WordTrace (prefixWord ++ tailWord_3690688) baseStart_3690688 baseEnd_3690688 := by
    simpa [prefixWord, tailWord_3690688, baseEnd_3690688] using wordTrace_append hprefix tailTrace_3690688
  have hstable : (prefixWord ++ tailWord_3690688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690688).length < 2 ^ (prefixWord ++ tailWord_3690688).sum := by decide
  have hdescent : baseEnd_3690688 < baseStart_3690688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690705 : List Nat := [1, 2, 2, 1, 2, 2, 3, 5, 1, 2, 2]
def baseStart_3690705 : Nat := 118140960795 + 3690705 * 2 ^ 59
def prefixEnd_3690705 : Nat := 4983230072969 + 3 ^ 40 * 3690705 * 2
def baseEnd_3690705 : Nat := 1895105618952087833414263

theorem tailTrace_3690705 : CollatzResearch.WordTrace tailWord_3690705 prefixEnd_3690705 1895105618952087833414263 := by
  unfold tailWord_3690705
  simp only [CollatzResearch.WordTrace]
  refine ⟨134611070094213582076593569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89740713396142388051062379 134611070094213582076593569)
  ·
    refine ⟨100958302570660186557445177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134611070094213582076593569 100958302570660186557445177)
    ·
      refine ⟨75718726927995139918083883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100958302570660186557445177 75718726927995139918083883)
      ·
        refine ⟨113578090391992709877125825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75718726927995139918083883 113578090391992709877125825)
        ·
          refine ⟨85183567793994532407844369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113578090391992709877125825 85183567793994532407844369)
          ·
            refine ⟨63887675845495899305883277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85183567793994532407844369 63887675845495899305883277)
            ·
              refine ⟨23957878442060962239706229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63887675845495899305883277 23957878442060962239706229)
              ·
                refine ⟨2246051103943215209972459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23957878442060962239706229 2246051103943215209972459)
                ·
                  refine ⟨3369076655914822814958689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246051103943215209972459 3369076655914822814958689)
                  ·
                    refine ⟨2526807491936117111219017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3369076655914822814958689 2526807491936117111219017)
                    ·
                      refine ⟨1895105618952087833414263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526807491936117111219017 1895105618952087833414263)
                      ·
                        rfl

theorem cell23_3690705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_3690705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690705 prefixEnd_3690705 := by exact prefixLift 3690705
  have htrace : WordTrace (prefixWord ++ tailWord_3690705) baseStart_3690705 baseEnd_3690705 := by
    simpa [prefixWord, tailWord_3690705, baseEnd_3690705] using wordTrace_append hprefix tailTrace_3690705
  have hstable : (prefixWord ++ tailWord_3690705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690705).length < 2 ^ (prefixWord ++ tailWord_3690705).sum := by decide
  have hdescent : baseEnd_3690705 < baseStart_3690705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690738 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3690738 : Nat := 118140960795 + 3690738 * 2 ^ 59
def prefixEnd_3690738 : Nat := 4983230072969 + 3 ^ 40 * 3690738 * 2
def baseEnd_3690738 : Nat := 1895122563813686204301611

theorem tailTrace_3690738 : CollatzResearch.WordTrace tailWord_3690738 prefixEnd_3690738 1895122563813686204301611 := by
  unfold tailWord_3690738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33653068425773507178136217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89741515802062685808363245 33653068425773507178136217)
  ·
    refine ⟨25239801319330130383602163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33653068425773507178136217 25239801319330130383602163)
    ·
      refine ⟨37859701978995195575403245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25239801319330130383602163 37859701978995195575403245)
      ·
        refine ⟨14197388242123198340776217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37859701978995195575403245 14197388242123198340776217)
        ·
          refine ⟨10648041181592398755582163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14197388242123198340776217 10648041181592398755582163)
          ·
            refine ⟨15972061772388598133373245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10648041181592398755582163 15972061772388598133373245)
            ·
              refine ⟨5989523164645724300014967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15972061772388598133373245 5989523164645724300014967)
              ·
                refine ⟨8984284746968586450022451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989523164645724300014967 8984284746968586450022451)
                ·
                  refine ⟨13476427120452879675033677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8984284746968586450022451 13476427120452879675033677)
                  ·
                    refine ⟨5053660170169829878137629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13476427120452879675033677 5053660170169829878137629)
                    ·
                      refine ⟨1895122563813686204301611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053660170169829878137629 1895122563813686204301611)
                      ·
                        rfl

theorem cell23_3690738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3690738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690738 prefixEnd_3690738 := by exact prefixLift 3690738
  have htrace : WordTrace (prefixWord ++ tailWord_3690738) baseStart_3690738 baseEnd_3690738 := by
    simpa [prefixWord, tailWord_3690738, baseEnd_3690738] using wordTrace_append hprefix tailTrace_3690738
  have hstable : (prefixWord ++ tailWord_3690738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690738).length < 2 ^ (prefixWord ++ tailWord_3690738).sum := by decide
  have hdescent : baseEnd_3690738 < baseStart_3690738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690744 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_3690744 : Nat := 118140960795 + 3690744 * 2 ^ 59
def prefixEnd_3690744 : Nat := 4983230072969 + 3 ^ 40 * 3690744 * 2
def baseEnd_3690744 : Nat := 1895125644697613180826583

theorem tailTrace_3690744 : CollatzResearch.WordTrace tailWord_3690744 prefixEnd_3690744 1895125644697613180826583 := by
  unfold tailWord_3690744
  simp only [CollatzResearch.WordTrace]
  refine ⟨67306246270536145868631643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89741661694048194491508857 67306246270536145868631643)
  ·
    refine ⟨100959369405804218802947465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67306246270536145868631643 100959369405804218802947465)
    ·
      refine ⟨75719527054353164102210599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100959369405804218802947465 75719527054353164102210599)
      ·
        refine ⟨113579290581529746153315899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75719527054353164102210599 113579290581529746153315899)
        ·
          refine ⟨170368935872294619229973849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113579290581529746153315899 170368935872294619229973849)
          ·
            refine ⟨127776701904220964422480387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170368935872294619229973849 127776701904220964422480387)
            ·
              refine ⟨191665052856331446633720581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127776701904220964422480387 191665052856331446633720581)
              ·
                refine ⟨35937197410562146243822609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191665052856331446633720581 35937197410562146243822609)
                ·
                  refine ⟨26952898057921609682866957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35937197410562146243822609 26952898057921609682866957)
                  ·
                    refine ⟨10107336771720603631075109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26952898057921609682866957 10107336771720603631075109)
                    ·
                      refine ⟨1895125644697613180826583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10107336771720603631075109 1895125644697613180826583)
                      ·
                        rfl

theorem cell23_3690744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_3690744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690744 prefixEnd_3690744 := by exact prefixLift 3690744
  have htrace : WordTrace (prefixWord ++ tailWord_3690744) baseStart_3690744 baseEnd_3690744 := by
    simpa [prefixWord, tailWord_3690744, baseEnd_3690744] using wordTrace_append hprefix tailTrace_3690744
  have hstable : (prefixWord ++ tailWord_3690744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690744).length < 2 ^ (prefixWord ++ tailWord_3690744).sum := by decide
  have hdescent : baseEnd_3690744 < baseStart_3690744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690756 : List Nat := [2, 3, 2, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3690756 : Nat := 118140960795 + 3690756 * 2 ^ 59
def prefixEnd_3690756 : Nat := 4983230072969 + 3 ^ 40 * 3690756 * 2
def baseEnd_3690756 : Nat := 1895131806465467133876529

theorem tailTrace_3690756 : CollatzResearch.WordTrace tailWord_3690756 prefixEnd_3690756 1895131806465467133876529 := by
  unfold tailWord_3690756
  simp only [CollatzResearch.WordTrace]
  refine ⟨67306465108514408893350061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89741953478019211857800081 67306465108514408893350061)
  ·
    refine ⟨25239924415692903335006273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67306465108514408893350061 25239924415692903335006273)
    ·
      refine ⟨18929943311769677501254705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25239924415692903335006273 18929943311769677501254705)
      ·
        refine ⟨14197457483827258125941029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18929943311769677501254705 14197457483827258125941029)
        ·
          refine ⟨2662023278217610898613943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14197457483827258125941029 2662023278217610898613943)
          ·
            refine ⟨3993034917326416347920915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662023278217610898613943 3993034917326416347920915)
            ·
              refine ⟨5989552375989624521881373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993034917326416347920915 5989552375989624521881373)
              ·
                refine ⟨2246082140996109195705515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5989552375989624521881373 2246082140996109195705515)
                ·
                  refine ⟨3369123211494163793558273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246082140996109195705515 3369123211494163793558273)
                  ·
                    refine ⟨2526842408620622845168705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3369123211494163793558273 2526842408620622845168705)
                    ·
                      refine ⟨1895131806465467133876529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526842408620622845168705 1895131806465467133876529)
                      ·
                        rfl

theorem cell23_3690756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3690756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690756 prefixEnd_3690756 := by exact prefixLift 3690756
  have htrace : WordTrace (prefixWord ++ tailWord_3690756) baseStart_3690756 baseEnd_3690756 := by
    simpa [prefixWord, tailWord_3690756, baseEnd_3690756] using wordTrace_append hprefix tailTrace_3690756
  have hstable : (prefixWord ++ tailWord_3690756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690756).length < 2 ^ (prefixWord ++ tailWord_3690756).sum := by decide
  have hdescent : baseEnd_3690756 < baseStart_3690756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690789 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 2, 1, 3]
def baseStart_3690789 : Nat := 118140960795 + 3690789 * 2 ^ 59
def prefixEnd_3690789 : Nat := 4983230072969 + 3 ^ 40 * 3690789 * 2
def baseEnd_3690789 : Nat := 1895148751327065504763877

theorem tailTrace_3690789 : CollatzResearch.WordTrace tailWord_3690789 prefixEnd_3690789 1895148751327065504763877 := by
  unfold tailWord_3690789
  simp only [CollatzResearch.WordTrace]
  refine ⟨134614133825909264422651421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89742755883939509615100947 134614133825909264422651421)
  ·
    refine ⟨50480300184715974158494283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134614133825909264422651421 50480300184715974158494283)
    ·
      refine ⟨75720450277073961237741425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50480300184715974158494283 75720450277073961237741425)
      ·
        refine ⟨56790337707805470928306069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75720450277073961237741425 56790337707805470928306069)
        ·
          refine ⟨2662047080053381449764347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56790337707805470928306069 2662047080053381449764347)
          ·
            refine ⟨3993070620080072174646521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662047080053381449764347 3993070620080072174646521)
            ·
              refine ⟨2994802965060054130984891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3993070620080072174646521 2994802965060054130984891)
              ·
                refine ⟨4492204447590081196477337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994802965060054130984891 4492204447590081196477337)
                ·
                  refine ⟨3369153335692560897358003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4492204447590081196477337 3369153335692560897358003)
                  ·
                    refine ⟨5053730003538841346037005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369153335692560897358003 5053730003538841346037005)
                    ·
                      refine ⟨1895148751327065504763877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053730003538841346037005 1895148751327065504763877)
                      ·
                        rfl

theorem cell23_3690789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_3690789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690789 prefixEnd_3690789 := by exact prefixLift 3690789
  have htrace : WordTrace (prefixWord ++ tailWord_3690789) baseStart_3690789 baseEnd_3690789 := by
    simpa [prefixWord, tailWord_3690789, baseEnd_3690789] using wordTrace_append hprefix tailTrace_3690789
  have hstable : (prefixWord ++ tailWord_3690789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690789).length < 2 ^ (prefixWord ++ tailWord_3690789).sum := by decide
  have hdescent : baseEnd_3690789 < baseStart_3690789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690851 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3690851 : Nat := 118140960795 + 3690851 * 2 ^ 59
def prefixEnd_3690851 : Nat := 4983230072969 + 3 ^ 40 * 3690851 * 2
def baseEnd_3690851 : Nat := 1895180587127644262188591

theorem tailTrace_3690851 : CollatzResearch.WordTrace tailWord_3690851 prefixEnd_3690851 1895180587127644262188591 := by
  unfold tailWord_3690851
  simp only [CollatzResearch.WordTrace]
  refine ⟨134616395151684649011408407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89744263434456432674272271 134616395151684649011408407)
  ·
    refine ⟨201924592727526973517112611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134616395151684649011408407 201924592727526973517112611)
    ·
      refine ⟨302886889091290460275668917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201924592727526973517112611 302886889091290460275668917)
      ·
        refine ⟨28395645852308480650843961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302886889091290460275668917 28395645852308480650843961)
        ·
          refine ⟨21296734389231360488132971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28395645852308480650843961 21296734389231360488132971)
          ·
            refine ⟨31945101583847040732199457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21296734389231360488132971 31945101583847040732199457)
            ·
              refine ⟨23958826187885280549149593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31945101583847040732199457 23958826187885280549149593)
              ·
                refine ⟨17969119640913960411862195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23958826187885280549149593 17969119640913960411862195)
                ·
                  refine ⟨26953679461370940617793293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17969119640913960411862195 26953679461370940617793293)
                  ·
                    refine ⟨10107629798014102731672485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26953679461370940617793293 10107629798014102731672485)
                    ·
                      refine ⟨1895180587127644262188591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10107629798014102731672485 1895180587127644262188591)
                      ·
                        rfl

theorem cell23_3690851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3690851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690851 prefixEnd_3690851 := by exact prefixLift 3690851
  have htrace : WordTrace (prefixWord ++ tailWord_3690851) baseStart_3690851 baseEnd_3690851 := by
    simpa [prefixWord, tailWord_3690851, baseEnd_3690851] using wordTrace_append hprefix tailTrace_3690851
  have hstable : (prefixWord ++ tailWord_3690851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690851).length < 2 ^ (prefixWord ++ tailWord_3690851).sum := by decide
  have hdescent : baseEnd_3690851 < baseStart_3690851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690888 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3690888 : Nat := 118140960795 + 3690888 * 2 ^ 59
def prefixEnd_3690888 : Nat := 4983230072969 + 3 ^ 40 * 3690888 * 2
def baseEnd_3690888 : Nat := 1895199585911860617425921

theorem tailTrace_3690888 : CollatzResearch.WordTrace tailWord_3690888 prefixEnd_3690888 1895199585911860617425921 := by
  unfold tailWord_3690888
  simp only [CollatzResearch.WordTrace]
  refine ⟨67308872326275302165252659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89745163101700402887003545 67308872326275302165252659)
  ·
    refine ⟨100963308489412953247878989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67308872326275302165252659 100963308489412953247878989)
    ·
      refine ⟨37861240683529857467954621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100963308489412953247878989 37861240683529857467954621)
      ·
        refine ⟨14197965256323696550482983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37861240683529857467954621 14197965256323696550482983)
        ·
          refine ⟨21296947884485544825724475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14197965256323696550482983 21296947884485544825724475)
          ·
            refine ⟨31945421826728317238586713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21296947884485544825724475 31945421826728317238586713)
            ·
              refine ⟨23959066370046237928940035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31945421826728317238586713 23959066370046237928940035)
              ·
                refine ⟨35938599555069356893410053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23959066370046237928940035 35938599555069356893410053)
                ·
                  refine ⟨6738487416575504417514385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35938599555069356893410053 6738487416575504417514385)
                  ·
                    refine ⟨5053865562431628313135789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6738487416575504417514385 5053865562431628313135789)
                    ·
                      refine ⟨1895199585911860617425921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053865562431628313135789 1895199585911860617425921)
                      ·
                        rfl

theorem cell23_3690888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3690888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690888 prefixEnd_3690888 := by exact prefixLift 3690888
  have htrace : WordTrace (prefixWord ++ tailWord_3690888) baseStart_3690888 baseEnd_3690888 := by
    simpa [prefixWord, tailWord_3690888, baseEnd_3690888] using wordTrace_append hprefix tailTrace_3690888
  have hstable : (prefixWord ++ tailWord_3690888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690888).length < 2 ^ (prefixWord ++ tailWord_3690888).sum := by decide
  have hdescent : baseEnd_3690888 < baseStart_3690888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690891 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 8]
def baseStart_3690891 : Nat := 118140960795 + 3690891 * 2 ^ 59
def prefixEnd_3690891 : Nat := 4983230072969 + 3 ^ 40 * 3690891 * 2
def baseEnd_3690891 : Nat := 210577902928202678409823

theorem tailTrace_3690891 : CollatzResearch.WordTrace tailWord_3690891 prefixEnd_3690891 210577902928202678409823 := by
  unfold tailWord_3690891
  simp only [CollatzResearch.WordTrace]
  refine ⟨134617854071539735842864527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89745236047693157228576351 134617854071539735842864527)
  ·
    refine ⟨201926781107309603764296791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134617854071539735842864527 201926781107309603764296791)
    ·
      refine ⟨302890171660964405646445187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201926781107309603764296791 302890171660964405646445187)
      ·
        refine ⟨454335257491446608469667781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302890171660964405646445187 454335257491446608469667781)
        ·
          refine ⟨85187860779646239088062709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454335257491446608469667781 85187860779646239088062709)
          ·
            refine ⟨7986361948091834914505879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85187860779646239088062709 7986361948091834914505879)
            ·
              refine ⟨11979542922137752371758819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7986361948091834914505879 11979542922137752371758819)
              ·
                refine ⟨17969314383206628557638229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11979542922137752371758819 17969314383206628557638229)
                ·
                  refine ⟨210577902928202678409823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17969314383206628557638229 210577902928202678409823)
                  ·
                    rfl

theorem cell23_3690891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 8].length) (baseStart_3690891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690891 prefixEnd_3690891 := by exact prefixLift 3690891
  have htrace : WordTrace (prefixWord ++ tailWord_3690891) baseStart_3690891 baseEnd_3690891 := by
    simpa [prefixWord, tailWord_3690891, baseEnd_3690891] using wordTrace_append hprefix tailTrace_3690891
  have hstable : (prefixWord ++ tailWord_3690891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690891).length < 2 ^ (prefixWord ++ tailWord_3690891).sum := by decide
  have hdescent : baseEnd_3690891 < baseStart_3690891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690911 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3690911 : Nat := 118140960795 + 3690911 * 2 ^ 59
def prefixEnd_3690911 : Nat := 4983230072969 + 3 ^ 40 * 3690911 * 2
def baseEnd_3690911 : Nat := 1895211395966914027438315

theorem tailTrace_3690911 : CollatzResearch.WordTrace tailWord_3690911 prefixEnd_3690911 1895211395966914027438315 := by
  unfold tailWord_3690911
  simp only [CollatzResearch.WordTrace]
  refine ⟨134618583531467279258592587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89745722354311519505728391 134618583531467279258592587)
  ·
    refine ⟨201927875297200918887888881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134618583531467279258592587 201927875297200918887888881)
    ·
      refine ⟨151445906472900689165916661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201927875297200918887888881 151445906472900689165916661)
      ·
        refine ⟨14198053731834439609304687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151445906472900689165916661 14198053731834439609304687)
        ·
          refine ⟨21297080597751659413957031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14198053731834439609304687 21297080597751659413957031)
          ·
            refine ⟨31945620896627489120935547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21297080597751659413957031 31945620896627489120935547)
            ·
              refine ⟨47918431344941233681403321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31945620896627489120935547 47918431344941233681403321)
              ·
                refine ⟨35938823508705925261052491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47918431344941233681403321 35938823508705925261052491)
                ·
                  refine ⟨53908235263058887891578737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35938823508705925261052491 53908235263058887891578737)
                  ·
                    refine ⟨40431176447294165918684053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53908235263058887891578737 40431176447294165918684053)
                    ·
                      refine ⟨1895211395966914027438315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40431176447294165918684053 1895211395966914027438315)
                      ·
                        rfl

theorem cell23_3690911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3690911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690911 prefixEnd_3690911 := by exact prefixLift 3690911
  have htrace : WordTrace (prefixWord ++ tailWord_3690911) baseStart_3690911 baseEnd_3690911 := by
    simpa [prefixWord, tailWord_3690911, baseEnd_3690911] using wordTrace_append hprefix tailTrace_3690911
  have hstable : (prefixWord ++ tailWord_3690911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690911).length < 2 ^ (prefixWord ++ tailWord_3690911).sum := by decide
  have hdescent : baseEnd_3690911 < baseStart_3690911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690921 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 3, 5]
def baseStart_3690921 : Nat := 118140960795 + 3690921 * 2 ^ 59
def prefixEnd_3690921 : Nat := 4983230072969 + 3 ^ 40 * 3690921 * 2
def baseEnd_3690921 : Nat := 631738843591152996104423

theorem tailTrace_3690921 : CollatzResearch.WordTrace tailWord_3690921 prefixEnd_3690921 631738843591152996104423 := by
  unfold tailWord_3690921
  simp only [CollatzResearch.WordTrace]
  refine ⟨134618948261431050966456617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89745965507620700644304411 134618948261431050966456617)
  ·
    refine ⟨100964211196073288224842463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134618948261431050966456617 100964211196073288224842463)
    ·
      refine ⟨151446316794109932337263695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100964211196073288224842463 151446316794109932337263695)
      ·
        refine ⟨227169475191164898505895543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151446316794109932337263695 227169475191164898505895543)
        ·
          refine ⟨340754212786747347758843315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227169475191164898505895543 340754212786747347758843315)
          ·
            refine ⟨511131319180121021638264973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340754212786747347758843315 511131319180121021638264973)
            ·
              refine ⟨191674244692545383114349365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511131319180121021638264973 191674244692545383114349365)
              ·
                refine ⟨17969460439926129666970253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191674244692545383114349365 17969460439926129666970253)
                ·
                  refine ⟨6738547664972298625113845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17969460439926129666970253 6738547664972298625113845)
                  ·
                    refine ⟨631738843591152996104423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6738547664972298625113845 631738843591152996104423)
                    ·
                      rfl

theorem cell23_3690921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_3690921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690921 prefixEnd_3690921 := by exact prefixLift 3690921
  have htrace : WordTrace (prefixWord ++ tailWord_3690921) baseStart_3690921 baseEnd_3690921 := by
    simpa [prefixWord, tailWord_3690921, baseEnd_3690921] using wordTrace_append hprefix tailTrace_3690921
  have hstable : (prefixWord ++ tailWord_3690921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690921).length < 2 ^ (prefixWord ++ tailWord_3690921).sum := by decide
  have hdescent : baseEnd_3690921 < baseStart_3690921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690952 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_3690952 : Nat := 118140960795 + 3690952 * 2 ^ 59
def prefixEnd_3690952 : Nat := 4983230072969 + 3 ^ 40 * 3690952 * 2
def baseEnd_3690952 : Nat := 1895232448673748367025627

theorem tailTrace_3690952 : CollatzResearch.WordTrace tailWord_3690952 prefixEnd_3690952 1895232448673748367025627 := by
  unfold tailWord_3690952
  simp only [CollatzResearch.WordTrace]
  refine ⟨67310039462159371630417555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89746719282879162173890073 67310039462159371630417555)
  ·
    refine ⟨100965059193239057445626333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67310039462159371630417555 100965059193239057445626333)
    ·
      refine ⟨37861897197464646542109875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100965059193239057445626333 37861897197464646542109875)
      ·
        refine ⟨56792845796196969813164813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37861897197464646542109875 56792845796196969813164813)
        ·
          refine ⟨21297317173573863679936805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56792845796196969813164813 21297317173573863679936805)
          ·
            refine ⟨3993246970045099439988151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21297317173573863679936805 3993246970045099439988151)
            ·
              refine ⟨5989870455067649159982227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993246970045099439988151 5989870455067649159982227)
              ·
                refine ⟨8984805682601473739973341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989870455067649159982227 8984805682601473739973341)
                ·
                  refine ⟨3369302130975552652490003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8984805682601473739973341 3369302130975552652490003)
                  ·
                    refine ⟨5053953196463328978735005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369302130975552652490003 5053953196463328978735005)
                    ·
                      refine ⟨1895232448673748367025627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5053953196463328978735005 1895232448673748367025627)
                      ·
                        rfl

theorem cell23_3690952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_3690952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690952 prefixEnd_3690952 := by exact prefixLift 3690952
  have htrace : WordTrace (prefixWord ++ tailWord_3690952) baseStart_3690952 baseEnd_3690952 := by
    simpa [prefixWord, tailWord_3690952, baseEnd_3690952] using wordTrace_append hprefix tailTrace_3690952
  have hstable : (prefixWord ++ tailWord_3690952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690952).length < 2 ^ (prefixWord ++ tailWord_3690952).sum := by decide
  have hdescent : baseEnd_3690952 < baseStart_3690952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690958 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3690958 : Nat := 118140960795 + 3690958 * 2 ^ 59
def prefixEnd_3690958 : Nat := 4983230072969 + 3 ^ 40 * 3690958 * 2
def baseEnd_3690958 : Nat := 1895235529557675343550599

theorem tailTrace_3690958 : CollatzResearch.WordTrace tailWord_3690958 prefixEnd_3690958 1895235529557675343550599 := by
  unfold tailWord_3690958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827537220287125785694191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89746865174864670857035685 16827537220287125785694191)
  ·
    refine ⟨25241305830430688678541287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16827537220287125785694191 25241305830430688678541287)
    ·
      refine ⟨37861958745646033017811931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25241305830430688678541287 37861958745646033017811931)
      ·
        refine ⟨56792938118469049526717897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37861958745646033017811931 56792938118469049526717897)
        ·
          refine ⟨42594703588851787145038423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56792938118469049526717897 42594703588851787145038423)
          ·
            refine ⟨63892055383277680717557635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42594703588851787145038423 63892055383277680717557635)
            ·
              refine ⟨95838083074916521076336453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63892055383277680717557635 95838083074916521076336453)
              ·
                refine ⟨17969640576546847701813085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95838083074916521076336453 17969640576546847701813085)
                ·
                  refine ⟨6738615216205067888179907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17969640576546847701813085 6738615216205067888179907)
                  ·
                    refine ⟨10107922824307601832269861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6738615216205067888179907 10107922824307601832269861)
                    ·
                      refine ⟨1895235529557675343550599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10107922824307601832269861 1895235529557675343550599)
                      ·
                        rfl

theorem cell23_3690958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3690958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690958 prefixEnd_3690958 := by exact prefixLift 3690958
  have htrace : WordTrace (prefixWord ++ tailWord_3690958) baseStart_3690958 baseEnd_3690958 := by
    simpa [prefixWord, tailWord_3690958, baseEnd_3690958] using wordTrace_append hprefix tailTrace_3690958
  have hstable : (prefixWord ++ tailWord_3690958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690958).length < 2 ^ (prefixWord ++ tailWord_3690958).sum := by decide
  have hdescent : baseEnd_3690958 < baseStart_3690958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690975 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 4]
def baseStart_3690975 : Nat := 118140960795 + 3690975 * 2 ^ 59
def prefixEnd_3690975 : Nat := 4983230072969 + 3 ^ 40 * 3690975 * 2
def baseEnd_3690975 : Nat := 1895244258728801777038021

theorem tailTrace_3690975 : CollatzResearch.WordTrace tailWord_3690975 prefixEnd_3690975 1895244258728801777038021 := by
  unfold tailWord_3690975
  simp only [CollatzResearch.WordTrace]
  refine ⟨134620917803235418188922379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89747278535490278792614919 134620917803235418188922379)
  ·
    refine ⟨201931376704853127283383569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134620917803235418188922379 201931376704853127283383569)
    ·
      refine ⟨151448532528639845462537677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201931376704853127283383569 151448532528639845462537677)
      ·
        refine ⟨56793199698239942048451629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151448532528639845462537677 56793199698239942048451629)
        ·
          refine ⟨21297449886839978268169361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56793199698239942048451629 21297449886839978268169361)
          ·
            refine ⟨15973087415129983701127021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21297449886839978268169361 15973087415129983701127021)
            ·
              refine ⟨5989907780673743887922633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15973087415129983701127021 5989907780673743887922633)
              ·
                refine ⟨4492430835505307915941975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5989907780673743887922633 4492430835505307915941975)
                ·
                  refine ⟨6738646253257961873912963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492430835505307915941975 6738646253257961873912963)
                  ·
                    refine ⟨10107969379886942810869445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6738646253257961873912963 10107969379886942810869445)
                    ·
                      refine ⟨1895244258728801777038021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10107969379886942810869445 1895244258728801777038021)
                      ·
                        rfl

theorem cell23_3690975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_3690975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690975 prefixEnd_3690975 := by exact prefixLift 3690975
  have htrace : WordTrace (prefixWord ++ tailWord_3690975) baseStart_3690975 baseEnd_3690975 := by
    simpa [prefixWord, tailWord_3690975, baseEnd_3690975] using wordTrace_append hprefix tailTrace_3690975
  have hstable : (prefixWord ++ tailWord_3690975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690975).length < 2 ^ (prefixWord ++ tailWord_3690975).sum := by decide
  have hdescent : baseEnd_3690975 < baseStart_3690975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690988 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_3690988 : Nat := 118140960795 + 3690988 * 2 ^ 59
def prefixEnd_3690988 : Nat := 4983230072969 + 3 ^ 40 * 3690988 * 2
def baseEnd_3690988 : Nat := 1895250933977310226175461

theorem tailTrace_3690988 : CollatzResearch.WordTrace tailWord_3690988 prefixEnd_3690988 1895250933977310226175461 := by
  unfold tailWord_3690988
  simp only [CollatzResearch.WordTrace]
  refine ⟨67310695976094160704572809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89747594634792214272763745 67310695976094160704572809)
  ·
    refine ⟨50483021982070620528429607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67310695976094160704572809 50483021982070620528429607)
    ·
      refine ⟨75724532973105930792644411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50483021982070620528429607 75724532973105930792644411)
      ·
        refine ⟨113586799459658896188966617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75724532973105930792644411 113586799459658896188966617)
        ·
          refine ⟨85190099594744172141724963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113586799459658896188966617 85190099594744172141724963)
          ·
            refine ⟨127785149392116258212587445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85190099594744172141724963 127785149392116258212587445)
            ·
              refine ⟨11979857755510899207430073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127785149392116258212587445 11979857755510899207430073)
              ·
                refine ⟨8984893316633174405572555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11979857755510899207430073 8984893316633174405572555)
                ·
                  refine ⟨13477339974949761608358833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8984893316633174405572555 13477339974949761608358833)
                  ·
                    refine ⟨10108004981212321206269125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13477339974949761608358833 10108004981212321206269125)
                    ·
                      refine ⟨1895250933977310226175461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10108004981212321206269125 1895250933977310226175461)
                      ·
                        rfl

theorem cell23_3690988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_3690988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690988 prefixEnd_3690988 := by exact prefixLift 3690988
  have htrace : WordTrace (prefixWord ++ tailWord_3690988) baseStart_3690988 baseEnd_3690988 := by
    simpa [prefixWord, tailWord_3690988, baseEnd_3690988] using wordTrace_append hprefix tailTrace_3690988
  have hstable : (prefixWord ++ tailWord_3690988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690988).length < 2 ^ (prefixWord ++ tailWord_3690988).sum := by decide
  have hdescent : baseEnd_3690988 < baseStart_3690988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691011 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 9]
def baseStart_3691011 : Nat := 118140960795 + 3691011 * 2 ^ 59
def prefixEnd_3691011 : Nat := 4983230072969 + 3 ^ 40 * 3691011 * 2
def baseEnd_3691011 : Nat := 631754248010787878729285

theorem tailTrace_3691011 : CollatzResearch.WordTrace tailWord_3691011 prefixEnd_3691011 631754248010787878729285 := by
  unfold tailWord_3691011
  simp only [CollatzResearch.WordTrace]
  refine ⟨134622230831104996337232887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89748153887403330891488591 134622230831104996337232887)
  ·
    refine ⟨201933346246657494505849331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134622230831104996337232887 201933346246657494505849331)
    ·
      refine ⟨302900019369986241758773997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201933346246657494505849331 302900019369986241758773997)
      ·
        refine ⟨113587507263744840659540249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302900019369986241758773997 113587507263744840659540249)
        ·
          refine ⟨85190630447808630494655187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113587507263744840659540249 85190630447808630494655187)
          ·
            refine ⟨127785945671712945741982781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85190630447808630494655187 127785945671712945741982781)
            ·
              refine ⟨47919729626892354653243543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127785945671712945741982781 47919729626892354653243543)
              ·
                refine ⟨71879594440338531979865315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47919729626892354653243543 71879594440338531979865315)
                ·
                  refine ⟨107819391660507797969797973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71879594440338531979865315 107819391660507797969797973)
                  ·
                    refine ⟨631754248010787878729285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 107819391660507797969797973 631754248010787878729285)
                    ·
                      rfl

theorem cell23_3691011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 9].length) (baseStart_3691011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691011 prefixEnd_3691011 := by exact prefixLift 3691011
  have htrace : WordTrace (prefixWord ++ tailWord_3691011) baseStart_3691011 baseEnd_3691011 := by
    simpa [prefixWord, tailWord_3691011, baseEnd_3691011] using wordTrace_append hprefix tailTrace_3691011
  have hstable : (prefixWord ++ tailWord_3691011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691011).length < 2 ^ (prefixWord ++ tailWord_3691011).sum := by decide
  have hdescent : baseEnd_3691011 < baseStart_3691011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691015 : List Nat := [1, 1, 4, 3, 3, 2, 1, 8]
def baseStart_3691015 : Nat := 118140960795 + 3691015 * 2 ^ 59
def prefixEnd_3691015 : Nat := 4983230072969 + 3 ^ 40 * 3691015 * 2
def baseEnd_3691015 : Nat := 70194992516851171131031

theorem tailTrace_3691015 : CollatzResearch.WordTrace tailWord_3691015 prefixEnd_3691015 70194992516851171131031 := by
  unfold tailWord_3691015
  simp only [CollatzResearch.WordTrace]
  refine ⟨134622376723090505020378499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89748251148727003346918999 134622376723090505020378499)
  ·
    refine ⟨201933565084635757530567749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134622376723090505020378499 201933565084635757530567749)
    ·
      refine ⟨37862543453369204536981453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201933565084635757530567749 37862543453369204536981453)
      ·
        refine ⟨14198453795013451701368045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37862543453369204536981453 14198453795013451701368045)
        ·
          refine ⟨5324420173130044388013017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14198453795013451701368045 5324420173130044388013017)
          ·
            refine ⟨3993315129847533291009763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5324420173130044388013017 3993315129847533291009763)
            ·
              refine ⟨5989972694771299936514645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993315129847533291009763 5989972694771299936514645)
              ·
                refine ⟨70194992516851171131031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5989972694771299936514645 70194992516851171131031)
                ·
                  rfl

theorem cell23_3691015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 8].length) (baseStart_3691015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691015 prefixEnd_3691015 := by exact prefixLift 3691015
  have htrace : WordTrace (prefixWord ++ tailWord_3691015) baseStart_3691015 baseEnd_3691015 := by
    simpa [prefixWord, tailWord_3691015, baseEnd_3691015] using wordTrace_append hprefix tailTrace_3691015
  have hstable : (prefixWord ++ tailWord_3691015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691015).length < 2 ^ (prefixWord ++ tailWord_3691015).sum := by decide
  have hdescent : baseEnd_3691015 < baseStart_3691015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691053 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3691053 : Nat := 118140960795 + 3691053 * 2 ^ 59
def prefixEnd_3691053 : Nat := 4983230072969 + 3 ^ 40 * 3691053 * 2
def baseEnd_3691053 : Nat := 631761436739950823954221

theorem tailTrace_3691053 : CollatzResearch.WordTrace tailWord_3691053 prefixEnd_3691053 631761436739950823954221 := by
  unfold tailWord_3691053
  simp only [CollatzResearch.WordTrace]
  refine ⟨134623762696952837510261813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89749175131301891673507875 134623762696952837510261813)
  ·
    refine ⟨12620977752839328516587045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134623762696952837510261813 12620977752839328516587045)
    ·
      refine ⟨2366433328657374096860071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12620977752839328516587045 2366433328657374096860071)
      ·
        refine ⟨3549649992986061145290107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366433328657374096860071 3549649992986061145290107)
        ·
          refine ⟨5324474989479091717935161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549649992986061145290107 5324474989479091717935161)
          ·
            refine ⟨3993356242109318788451371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5324474989479091717935161 3993356242109318788451371)
            ·
              refine ⟨5990034363163978182677057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993356242109318788451371 5990034363163978182677057)
              ·
                refine ⟨4492525772372983637007793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5990034363163978182677057 4492525772372983637007793)
                ·
                  refine ⟨3369394329279737727755845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4492525772372983637007793 3369394329279737727755845)
                  ·
                    refine ⟨631761436739950823954221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3369394329279737727755845 631761436739950823954221)
                    ·
                      rfl

theorem cell23_3691053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3691053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691053 prefixEnd_3691053 := by exact prefixLift 3691053
  have htrace : WordTrace (prefixWord ++ tailWord_3691053) baseStart_3691053 baseEnd_3691053 := by
    simpa [prefixWord, tailWord_3691053, baseEnd_3691053] using wordTrace_append hprefix tailTrace_3691053
  have hstable : (prefixWord ++ tailWord_3691053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691053).length < 2 ^ (prefixWord ++ tailWord_3691053).sum := by decide
  have hdescent : baseEnd_3691053 < baseStart_3691053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691058 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_3691058 : Nat := 118140960795 + 3691058 * 2 ^ 59
def prefixEnd_3691058 : Nat := 4983230072969 + 3 ^ 40 * 3691058 * 2
def baseEnd_3691058 : Nat := 631762292541041650766713

theorem tailTrace_3691058 : CollatzResearch.WordTrace tailWord_3691058 prefixEnd_3691058 631762292541041650766713 := by
  unfold tailWord_3691058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33655986265483680841048457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89749296707956482242795885 33655986265483680841048457)
  ·
    refine ⟨25241989699112760630786343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33655986265483680841048457 25241989699112760630786343)
    ·
      refine ⟨37862984548669140946179515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25241989699112760630786343 37862984548669140946179515)
      ·
        refine ⟨56794476823003711419269273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37862984548669140946179515 56794476823003711419269273)
        ·
          refine ⟨42595857617252783564451955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56794476823003711419269273 42595857617252783564451955)
          ·
            refine ⟨63893786425879175346677933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42595857617252783564451955 63893786425879175346677933)
            ·
              refine ⟨23960169909704690755004225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63893786425879175346677933 23960169909704690755004225)
              ·
                refine ⟨17970127432278518066253169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23960169909704690755004225 17970127432278518066253169)
                ·
                  refine ⟨13477595574208888549689877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17970127432278518066253169 13477595574208888549689877)
                  ·
                    refine ⟨631762292541041650766713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13477595574208888549689877 631762292541041650766713)
                    ·
                      rfl

theorem cell23_3691058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_3691058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691058 prefixEnd_3691058 := by exact prefixLift 3691058
  have htrace : WordTrace (prefixWord ++ tailWord_3691058) baseStart_3691058 baseEnd_3691058 := by
    simpa [prefixWord, tailWord_3691058, baseEnd_3691058] using wordTrace_append hprefix tailTrace_3691058
  have hstable : (prefixWord ++ tailWord_3691058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691058).length < 2 ^ (prefixWord ++ tailWord_3691058).sum := by decide
  have hdescent : baseEnd_3691058 < baseStart_3691058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691082 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_3691082 : Nat := 118140960795 + 3691082 * 2 ^ 59
def prefixEnd_3691082 : Nat := 4983230072969 + 3 ^ 40 * 3691082 * 2
def baseEnd_3691082 : Nat := 1895299201158832858400029

theorem tailTrace_3691082 : CollatzResearch.WordTrace tailWord_3691082 prefixEnd_3691082 1895299201158832858400029 := by
  unfold tailWord_3691082
  simp only [CollatzResearch.WordTrace]
  refine ⟨33656205103461943865766875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89749880275898516975378333 33656205103461943865766875)
  ·
    refine ⟨50484307655192915798650313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33656205103461943865766875 50484307655192915798650313)
    ·
      refine ⟨37863230741394686848987735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50484307655192915798650313 37863230741394686848987735)
      ·
        refine ⟨56794846112092030273481603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37863230741394686848987735 56794846112092030273481603)
        ·
          refine ⟨85192269168138045410222405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56794846112092030273481603 85192269168138045410222405)
          ·
            refine ⟨15973550469025883514416701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85192269168138045410222405 15973550469025883514416701)
            ·
              refine ⟨5990081425884706317906263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15973550469025883514416701 5990081425884706317906263)
              ·
                refine ⟨8985122138827059476859395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990081425884706317906263 8985122138827059476859395)
                ·
                  refine ⟨13477683208240589215289093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985122138827059476859395 13477683208240589215289093)
                  ·
                    refine ⟨2527065601545110477866705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13477683208240589215289093 2527065601545110477866705)
                    ·
                      refine ⟨1895299201158832858400029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527065601545110477866705 1895299201158832858400029)
                      ·
                        rfl

theorem cell23_3691082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_3691082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691082 prefixEnd_3691082 := by exact prefixLift 3691082
  have htrace : WordTrace (prefixWord ++ tailWord_3691082) baseStart_3691082 baseEnd_3691082 := by
    simpa [prefixWord, tailWord_3691082, baseEnd_3691082] using wordTrace_append hprefix tailTrace_3691082
  have hstable : (prefixWord ++ tailWord_3691082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691082).length < 2 ^ (prefixWord ++ tailWord_3691082).sum := by decide
  have hdescent : baseEnd_3691082 < baseStart_3691082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691122 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 7]
def baseStart_3691122 : Nat := 118140960795 + 3691122 * 2 ^ 59
def prefixEnd_3691122 : Nat := 4983230072969 + 3 ^ 40 * 3691122 * 2
def baseEnd_3691122 : Nat := 210591082265001411322205

theorem tailTrace_3691122 : CollatzResearch.WordTrace tailWord_3691122 prefixEnd_3691122 210591082265001411322205 := by
  unfold tailWord_3691122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33656569833425715573630905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89750852889135241529682413 33656569833425715573630905)
  ·
    refine ⟨25242427375069286680223179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33656569833425715573630905 25242427375069286680223179)
    ·
      refine ⟨37863641062603930020334769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25242427375069286680223179 37863641062603930020334769)
      ·
        refine ⟨28397730796952947515251077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37863641062603930020334769 28397730796952947515251077)
        ·
          refine ⟨5324574524428677659109577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28397730796952947515251077 5324574524428677659109577)
          ·
            refine ⟨3993430893321508244332183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5324574524428677659109577 3993430893321508244332183)
            ·
              refine ⟨5990146339982262366498275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993430893321508244332183 5990146339982262366498275)
              ·
                refine ⟨8985219509973393549747413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990146339982262366498275 8985219509973393549747413)
                ·
                  refine ⟨210591082265001411322205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8985219509973393549747413 210591082265001411322205)
                  ·
                    rfl

theorem cell23_3691122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_3691122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691122 prefixEnd_3691122 := by exact prefixLift 3691122
  have htrace : WordTrace (prefixWord ++ tailWord_3691122) baseStart_3691122 baseEnd_3691122 := by
    simpa [prefixWord, tailWord_3691122, baseEnd_3691122] using wordTrace_append hprefix tailTrace_3691122
  have hstable : (prefixWord ++ tailWord_3691122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691122).length < 2 ^ (prefixWord ++ tailWord_3691122).sum := by decide
  have hdescent : baseEnd_3691122 < baseStart_3691122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691128 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_3691128 : Nat := 118140960795 + 3691128 * 2 ^ 59
def prefixEnd_3691128 : Nat := 4983230072969 + 3 ^ 40 * 3691128 * 2
def baseEnd_3691128 : Nat := 1895322821268939678424817

theorem tailTrace_3691128 : CollatzResearch.WordTrace tailWord_3691128 prefixEnd_3691128 1895322821268939678424817 := by
  unfold tailWord_3691128
  simp only [CollatzResearch.WordTrace]
  refine ⟨67313249085840562659621019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89750998781120750212828025 67313249085840562659621019)
  ·
    refine ⟨100969873628760843989431529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67313249085840562659621019 100969873628760843989431529)
    ·
      refine ⟨75727405221570632992073647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100969873628760843989431529 75727405221570632992073647)
      ·
        refine ⟨113591107832355949488110471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75727405221570632992073647 113591107832355949488110471)
        ·
          refine ⟨170386661748533924232165707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113591107832355949488110471 170386661748533924232165707)
          ·
            refine ⟨255579992622800886348248561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170386661748533924232165707 255579992622800886348248561)
            ·
              refine ⟨191684994467100664761186421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255579992622800886348248561 191684994467100664761186421)
              ·
                refine ⟨17970468231290687321361227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191684994467100664761186421 17970468231290687321361227)
                ·
                  refine ⟨26955702346936030982041841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17970468231290687321361227 26955702346936030982041841)
                  ·
                    refine ⟨20216776760202023236531381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26955702346936030982041841 20216776760202023236531381)
                    ·
                      refine ⟨1895322821268939678424817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20216776760202023236531381 1895322821268939678424817)
                      ·
                        rfl

theorem cell23_3691128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_3691128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691128 prefixEnd_3691128 := by exact prefixLift 3691128
  have htrace : WordTrace (prefixWord ++ tailWord_3691128) baseStart_3691128 baseEnd_3691128 := by
    simpa [prefixWord, tailWord_3691128, baseEnd_3691128] using wordTrace_append hprefix tailTrace_3691128
  have hstable : (prefixWord ++ tailWord_3691128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691128).length < 2 ^ (prefixWord ++ tailWord_3691128).sum := by decide
  have hdescent : baseEnd_3691128 < baseStart_3691128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691133 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 2, 2, 2]
def baseStart_3691133 : Nat := 118140960795 + 3691133 * 2 ^ 59
def prefixEnd_3691133 : Nat := 4983230072969 + 3 ^ 40 * 3691133 * 2
def baseEnd_3691133 : Nat := 1895325388672212158862295

theorem tailTrace_3691133 : CollatzResearch.WordTrace tailWord_3691133 prefixEnd_3691133 1895325388672212158862295 := by
  unfold tailWord_3691133
  simp only [CollatzResearch.WordTrace]
  refine ⟨134626680536663011173174053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89751120357775340782116035 134626680536663011173174053)
  ·
    refine ⟨25242502600624314594970135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134626680536663011173174053 25242502600624314594970135)
    ·
      refine ⟨37863753900936471892455203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25242502600624314594970135 37863753900936471892455203)
      ·
        refine ⟨56795630851404707838682805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37863753900936471892455203 56795630851404707838682805)
        ·
          refine ⟨5324590392319191359876513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56795630851404707838682805 5324590392319191359876513)
          ·
            refine ⟨3993442794239393519907385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5324590392319191359876513 3993442794239393519907385)
            ·
              refine ⟨2995082095679545139930539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3993442794239393519907385 2995082095679545139930539)
              ·
                refine ⟨4492623143519317709895809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995082095679545139930539 4492623143519317709895809)
                ·
                  refine ⟨3369467357639488282421857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4492623143519317709895809 3369467357639488282421857)
                  ·
                    refine ⟨2527100518229616211816393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3369467357639488282421857 2527100518229616211816393)
                    ·
                      refine ⟨1895325388672212158862295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527100518229616211816393 1895325388672212158862295)
                      ·
                        rfl

theorem cell23_3691133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_3691133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691133 prefixEnd_3691133 := by exact prefixLift 3691133
  have htrace : WordTrace (prefixWord ++ tailWord_3691133) baseStart_3691133 baseEnd_3691133 := by
    simpa [prefixWord, tailWord_3691133, baseEnd_3691133] using wordTrace_append hprefix tailTrace_3691133
  have hstable : (prefixWord ++ tailWord_3691133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691133).length < 2 ^ (prefixWord ++ tailWord_3691133).sum := by decide
  have hdescent : baseEnd_3691133 < baseStart_3691133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691155 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 1, 6, 2]
def baseStart_3691155 : Nat := 118140960795 + 3691155 * 2 ^ 59
def prefixEnd_3691155 : Nat := 4983230072969 + 3 ^ 40 * 3691155 * 2
def baseEnd_3691155 : Nat := 1895336685246611072787193

theorem tailTrace_3691155 : CollatzResearch.WordTrace tailWord_3691155 prefixEnd_3691155 1895336685246611072787193 := by
  unfold tailWord_3691155
  simp only [CollatzResearch.WordTrace]
  refine ⟨134627482942583308930474919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89751655295055539286983279 134627482942583308930474919)
  ·
    refine ⟨201941224413874963395712379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134627482942583308930474919 201941224413874963395712379)
    ·
      refine ⟨302911836620812445093568569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201941224413874963395712379 302911836620812445093568569)
      ·
        refine ⟨227183877465609333820176427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302911836620812445093568569 227183877465609333820176427)
        ·
          refine ⟨340775816198414000730264641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227183877465609333820176427 340775816198414000730264641)
          ·
            refine ⟨255581862148810500547698481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340775816198414000730264641 255581862148810500547698481)
            ·
              refine ⟨191686396611607875410773861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255581862148810500547698481 191686396611607875410773861)
              ·
                refine ⟨35941199364676476639520099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191686396611607875410773861 35941199364676476639520099)
                ·
                  refine ⟨53911799047014714959280149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35941199364676476639520099 53911799047014714959280149)
                  ·
                    refine ⟨2527115580328814763716257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53911799047014714959280149 2527115580328814763716257)
                    ·
                      refine ⟨1895336685246611072787193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527115580328814763716257 1895336685246611072787193)
                      ·
                        rfl

theorem cell23_3691155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6, 2].length) (baseStart_3691155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691155 prefixEnd_3691155 := by exact prefixLift 3691155
  have htrace : WordTrace (prefixWord ++ tailWord_3691155) baseStart_3691155 baseEnd_3691155 := by
    simpa [prefixWord, tailWord_3691155, baseEnd_3691155] using wordTrace_append hprefix tailTrace_3691155
  have hstable : (prefixWord ++ tailWord_3691155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691155).length < 2 ^ (prefixWord ++ tailWord_3691155).sum := by decide
  have hdescent : baseEnd_3691155 < baseStart_3691155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691172 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_3691172 : Nat := 118140960795 + 3691172 * 2 ^ 59
def prefixEnd_3691172 : Nat := 4983230072969 + 3 ^ 40 * 3691172 * 2
def baseEnd_3691172 : Nat := 1895345414417737506274615

theorem tailTrace_3691172 : CollatzResearch.WordTrace tailWord_3691172 prefixEnd_3691172 1895345414417737506274615 := by
  unfold tailWord_3691172
  simp only [CollatzResearch.WordTrace]
  refine ⟨67314051491760860416921885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89752068655681147222562513 67314051491760860416921885)
  ·
    refine ⟨25242769309410322656345707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67314051491760860416921885 25242769309410322656345707)
    ·
      refine ⟨37864153964115483984518561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25242769309410322656345707 37864153964115483984518561)
      ·
        refine ⟨28398115473086612988388921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37864153964115483984518561 28398115473086612988388921)
        ·
          refine ⟨21298586604814959741291691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28398115473086612988388921 21298586604814959741291691)
          ·
            refine ⟨31947879907222439611937537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21298586604814959741291691 31947879907222439611937537)
            ·
              refine ⟨23960909930416829708953153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31947879907222439611937537 23960909930416829708953153)
              ·
                refine ⟨17970682447812622281714865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23960909930416829708953153 17970682447812622281714865)
                ·
                  refine ⟨13478011835859466711286149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17970682447812622281714865 13478011835859466711286149)
                  ·
                    refine ⟨2527127219223650008366153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13478011835859466711286149 2527127219223650008366153)
                    ·
                      refine ⟨1895345414417737506274615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527127219223650008366153 1895345414417737506274615)
                      ·
                        rfl

theorem cell23_3691172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_3691172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691172 prefixEnd_3691172 := by exact prefixLift 3691172
  have htrace : WordTrace (prefixWord ++ tailWord_3691172) baseStart_3691172 baseEnd_3691172 := by
    simpa [prefixWord, tailWord_3691172, baseEnd_3691172] using wordTrace_append hprefix tailTrace_3691172
  have hstable : (prefixWord ++ tailWord_3691172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691172).length < 2 ^ (prefixWord ++ tailWord_3691172).sum := by decide
  have hdescent : baseEnd_3691172 < baseStart_3691172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691189 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_3691189 : Nat := 118140960795 + 3691189 * 2 ^ 59
def prefixEnd_3691189 : Nat := 4983230072969 + 3 ^ 40 * 3691189 * 2
def baseEnd_3691189 : Nat := 1895354143588863939762037

theorem tailTrace_3691189 : CollatzResearch.WordTrace tailWord_3691189 prefixEnd_3691189 1895354143588863939762037 := by
  unfold tailWord_3691189
  simp only [CollatzResearch.WordTrace]
  refine ⟨134628723024460132737212621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89752482016306755158141747 134628723024460132737212621)
  ·
    refine ⟨50485771134172549776454733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134628723024460132737212621 50485771134172549776454733)
    ·
      refine ⟨18932164175314706166170525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50485771134172549776454733 18932164175314706166170525)
      ·
        refine ⟨7099561565743014812313947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18932164175314706166170525 7099561565743014812313947)
        ·
          refine ⟨10649342348614522218470921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099561565743014812313947 10649342348614522218470921)
          ·
            refine ⟨7987006761460891663853191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10649342348614522218470921 7987006761460891663853191)
            ·
              refine ⟨11980510142191337495779787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987006761460891663853191 11980510142191337495779787)
              ·
                refine ⟨17970765213287006243669681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11980510142191337495779787 17970765213287006243669681)
                ·
                  refine ⟨13478073909965254682752261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17970765213287006243669681 13478073909965254682752261)
                  ·
                    refine ⟨2527138858118485253016049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13478073909965254682752261 2527138858118485253016049)
                    ·
                      refine ⟨1895354143588863939762037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527138858118485253016049 1895354143588863939762037)
                      ·
                        rfl

theorem cell23_3691189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_3691189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691189 prefixEnd_3691189 := by exact prefixLift 3691189
  have htrace : WordTrace (prefixWord ++ tailWord_3691189) baseStart_3691189 baseEnd_3691189 := by
    simpa [prefixWord, tailWord_3691189, baseEnd_3691189] using wordTrace_append hprefix tailTrace_3691189
  have hstable : (prefixWord ++ tailWord_3691189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691189).length < 2 ^ (prefixWord ++ tailWord_3691189).sum := by decide
  have hdescent : baseEnd_3691189 < baseStart_3691189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691206 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3691206 : Nat := 118140960795 + 3691206 * 2 ^ 59
def prefixEnd_3691206 : Nat := 4983230072969 + 3 ^ 40 * 3691206 * 2
def baseEnd_3691206 : Nat := 1895362872759990373249459

theorem tailTrace_3691206 : CollatzResearch.WordTrace tailWord_3691206 prefixEnd_3691206 1895362872759990373249459 := by
  unfold tailWord_3691206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207166970793704520018171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89752895376932363093720981 4207166970793704520018171)
  ·
    refine ⟨6310750456190556780027257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4207166970793704520018171 6310750456190556780027257)
    ·
      refine ⟨4733062842142917585020443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6310750456190556780027257 4733062842142917585020443)
      ·
        refine ⟨7099594263214376377530665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733062842142917585020443 7099594263214376377530665)
        ·
          refine ⟨5324695697410782283147999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7099594263214376377530665 5324695697410782283147999)
          ·
            refine ⟨7987043546116173424721999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324695697410782283147999 7987043546116173424721999)
            ·
              refine ⟨11980565319174260137082999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987043546116173424721999 11980565319174260137082999)
              ·
                refine ⟨17970847978761390205624499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11980565319174260137082999 17970847978761390205624499)
                ·
                  refine ⟨26956271968142085308436749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17970847978761390205624499 26956271968142085308436749)
                  ·
                    refine ⟨10108601988053281990663781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26956271968142085308436749 10108601988053281990663781)
                    ·
                      refine ⟨1895362872759990373249459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10108601988053281990663781 1895362872759990373249459)
                      ·
                        rfl

theorem cell23_3691206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3691206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691206 prefixEnd_3691206 := by exact prefixLift 3691206
  have htrace : WordTrace (prefixWord ++ tailWord_3691206) baseStart_3691206 baseEnd_3691206 := by
    simpa [prefixWord, tailWord_3691206, baseEnd_3691206] using wordTrace_append hprefix tailTrace_3691206
  have hstable : (prefixWord ++ tailWord_3691206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691206).length < 2 ^ (prefixWord ++ tailWord_3691206).sum := by decide
  have hdescent : baseEnd_3691206 < baseStart_3691206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691232 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 4, 3, 2]
def baseStart_3691232 : Nat := 118140960795 + 3691232 * 2 ^ 59
def prefixEnd_3691232 : Nat := 4983230072969 + 3 ^ 40 * 3691232 * 2
def baseEnd_3691232 : Nat := 1895376223257007271524339

theorem tailTrace_3691232 : CollatzResearch.WordTrace tailWord_3691232 prefixEnd_3691232 1895376223257007271524339 := by
  unfold tailWord_3691232
  simp only [CollatzResearch.WordTrace]
  refine ⟨67315145681652175540513975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89753527575536234054018633 67315145681652175540513975)
  ·
    refine ⟨100972718522478263310770963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67315145681652175540513975 100972718522478263310770963)
    ·
      refine ⟨151459077783717394966156445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100972718522478263310770963 151459077783717394966156445)
      ·
        refine ⟨56797154168894023112308667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151459077783717394966156445 56797154168894023112308667)
        ·
          refine ⟨85195731253341034668463001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56797154168894023112308667 85195731253341034668463001)
          ·
            refine ⟨63896798440005776001347251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85195731253341034668463001 63896798440005776001347251)
            ·
              refine ⟨95845197660008664002020877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63896798440005776001347251 95845197660008664002020877)
              ·
                refine ⟨35941949122503249000757829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95845197660008664002020877 35941949122503249000757829)
                ·
                  refine ⟨6739115460469359187642093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35941949122503249000757829 6739115460469359187642093)
                  ·
                    refine ⟨2527168297676009695365785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6739115460469359187642093 2527168297676009695365785)
                    ·
                      refine ⟨1895376223257007271524339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527168297676009695365785 1895376223257007271524339)
                      ·
                        rfl

theorem cell23_3691232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_3691232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691232 prefixEnd_3691232 := by exact prefixLift 3691232
  have htrace : WordTrace (prefixWord ++ tailWord_3691232) baseStart_3691232 baseEnd_3691232 := by
    simpa [prefixWord, tailWord_3691232, baseEnd_3691232] using wordTrace_append hprefix tailTrace_3691232
  have hstable : (prefixWord ++ tailWord_3691232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691232).length < 2 ^ (prefixWord ++ tailWord_3691232).sum := by decide
  have hdescent : baseEnd_3691232 < baseStart_3691232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691265 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3691265 : Nat := 118140960795 + 3691265 * 2 ^ 59
def prefixEnd_3691265 : Nat := 4983230072969 + 3 ^ 40 * 3691265 * 2
def baseEnd_3691265 : Nat := 1895393168118605642411687

theorem tailTrace_3691265 : CollatzResearch.WordTrace tailWord_3691265 prefixEnd_3691265 1895393168118605642411687 := by
  unfold tailWord_3691265
  simp only [CollatzResearch.WordTrace]
  refine ⟨134631494972184797716979249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89754329981456531811319499 134631494972184797716979249)
  ·
    refine ⟨100973621229138598287734437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134631494972184797716979249 100973621229138598287734437)
    ·
      refine ⟨18932553980463487178950207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100973621229138598287734437 18932553980463487178950207)
      ·
        refine ⟨28398830970695230768425311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18932553980463487178950207 28398830970695230768425311)
        ·
          refine ⟨42598246456042846152637967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28398830970695230768425311 42598246456042846152637967)
          ·
            refine ⟨63897369684064269228956951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42598246456042846152637967 63897369684064269228956951)
            ·
              refine ⟨95846054526096403843435427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63897369684064269228956951 95846054526096403843435427)
              ·
                refine ⟨143769081789144605765153141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95846054526096403843435427 143769081789144605765153141)
                ·
                  refine ⟨13478351417732306790483107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143769081789144605765153141 13478351417732306790483107)
                  ·
                    refine ⟨20217527126598460185724661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13478351417732306790483107 20217527126598460185724661)
                    ·
                      refine ⟨1895393168118605642411687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20217527126598460185724661 1895393168118605642411687)
                      ·
                        rfl

theorem cell23_3691265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3691265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691265 prefixEnd_3691265 := by exact prefixLift 3691265
  have htrace : WordTrace (prefixWord ++ tailWord_3691265) baseStart_3691265 baseEnd_3691265 := by
    simpa [prefixWord, tailWord_3691265, baseEnd_3691265] using wordTrace_append hprefix tailTrace_3691265
  have hstable : (prefixWord ++ tailWord_3691265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691265).length < 2 ^ (prefixWord ++ tailWord_3691265).sum := by decide
  have hdescent : baseEnd_3691265 < baseStart_3691265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691272 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 4, 4]
def baseStart_3691272 : Nat := 118140960795 + 3691272 * 2 ^ 59
def prefixEnd_3691272 : Nat := 4983230072969 + 3 ^ 40 * 3691272 * 2
def baseEnd_3691272 : Nat := 631798920827729038341385

theorem tailTrace_3691272 : CollatzResearch.WordTrace tailWord_3691272 prefixEnd_3691272 631798920827729038341385 := by
  unfold tailWord_3691272
  simp only [CollatzResearch.WordTrace]
  refine ⟨67315875141579718956242035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89754500188772958608322713 67315875141579718956242035)
  ·
    refine ⟨100973812712369578434363053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67315875141579718956242035 100973812712369578434363053)
    ·
      refine ⟨37865179767138591912886145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100973812712369578434363053 37865179767138591912886145)
      ·
        refine ⟨28398884825353943934664609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37865179767138591912886145 28398884825353943934664609)
        ·
          refine ⟨21299163619015457950998457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28398884825353943934664609 21299163619015457950998457)
          ·
            refine ⟨15974372714261593463248843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21299163619015457950998457 15974372714261593463248843)
            ·
              refine ⟨23961559071392390194873265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15974372714261593463248843 23961559071392390194873265)
              ·
                refine ⟨17971169303544292646154949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23961559071392390194873265 17971169303544292646154949)
                ·
                  refine ⟨3369594244414554871154053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17971169303544292646154949 3369594244414554871154053)
                  ·
                    refine ⟨631798920827729038341385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3369594244414554871154053 631798920827729038341385)
                    ·
                      rfl

theorem cell23_3691272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_3691272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691272 prefixEnd_3691272 := by exact prefixLift 3691272
  have htrace : WordTrace (prefixWord ++ tailWord_3691272) baseStart_3691272 baseEnd_3691272 := by
    simpa [prefixWord, tailWord_3691272, baseEnd_3691272] using wordTrace_append hprefix tailTrace_3691272
  have hstable : (prefixWord ++ tailWord_3691272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691272).length < 2 ^ (prefixWord ++ tailWord_3691272).sum := by decide
  have hdescent : baseEnd_3691272 < baseStart_3691272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691275 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4]
def baseStart_3691275 : Nat := 118140960795 + 3691275 * 2 ^ 59
def prefixEnd_3691275 : Nat := 4983230072969 + 3 ^ 40 * 3691275 * 2
def baseEnd_3691275 : Nat := 1895398302925150603286641

theorem tailTrace_3691275 : CollatzResearch.WordTrace tailWord_3691275 prefixEnd_3691275 1895398302925150603286641 := by
  unfold tailWord_3691275
  simp only [CollatzResearch.WordTrace]
  refine ⟨134631859702148569424843279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89754573134765712949895519 134631859702148569424843279)
  ·
    refine ⟨201947789553222854137264919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134631859702148569424843279 201947789553222854137264919)
    ·
      refine ⟨302921684329834281205897379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201947789553222854137264919 302921684329834281205897379)
      ·
        refine ⟨454382526494751421808846069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302921684329834281205897379 454382526494751421808846069)
        ·
          refine ⟨42598361858882945794579319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 454382526494751421808846069 42598361858882945794579319)
          ·
            refine ⟨63897542788324418691868979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42598361858882945794579319 63897542788324418691868979)
            ·
              refine ⟨95846314182486628037803469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63897542788324418691868979 95846314182486628037803469)
              ·
                refine ⟨35942367818432485514176301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95846314182486628037803469 35942367818432485514176301)
                ·
                  refine ⟨13478387931912182067816113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35942367818432485514176301 13478387931912182067816113)
                  ·
                    refine ⟨10108790948934136550862085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13478387931912182067816113 10108790948934136550862085)
                    ·
                      refine ⟨1895398302925150603286641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10108790948934136550862085 1895398302925150603286641)
                      ·
                        rfl

theorem cell23_3691275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_3691275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691275 prefixEnd_3691275 := by exact prefixLift 3691275
  have htrace : WordTrace (prefixWord ++ tailWord_3691275) baseStart_3691275 baseEnd_3691275 := by
    simpa [prefixWord, tailWord_3691275, baseEnd_3691275] using wordTrace_append hprefix tailTrace_3691275
  have hstable : (prefixWord ++ tailWord_3691275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691275).length < 2 ^ (prefixWord ++ tailWord_3691275).sum := by decide
  have hdescent : baseEnd_3691275 < baseStart_3691275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691296 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 3, 2, 2]
def baseStart_3691296 : Nat := 118140960795 + 3691296 * 2 ^ 59
def prefixEnd_3691296 : Nat := 4983230072969 + 3 ^ 40 * 3691296 * 2
def baseEnd_3691296 : Nat := 1895409086018895021124045

theorem tailTrace_3691296 : CollatzResearch.WordTrace tailWord_3691296 prefixEnd_3691296 1895409086018895021124045 := by
  unfold tailWord_3691296
  simp only [CollatzResearch.WordTrace]
  refine ⟨67316312817536245005678871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89755083756714993340905161 67316312817536245005678871)
  ·
    refine ⟨100974469226304367508518307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67316312817536245005678871 100974469226304367508518307)
    ·
      refine ⟨151461703839456551262777461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100974469226304367508518307 151461703839456551262777461)
      ·
        refine ⟨14199534734949051680885387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151461703839456551262777461 14199534734949051680885387)
        ·
          refine ⟨21299302102423577521328081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14199534734949051680885387 21299302102423577521328081)
          ·
            refine ⟨15974476576817683140996061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21299302102423577521328081 15974476576817683140996061)
            ·
              refine ⟨5990428716306631177873523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15974476576817683140996061 5990428716306631177873523)
              ·
                refine ⟨8985643074459946766810285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990428716306631177873523 8985643074459946766810285)
                ·
                  refine ⟨3369616152922480037553857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8985643074459946766810285 3369616152922480037553857)
                  ·
                    refine ⟨2527212114691860028165393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3369616152922480037553857 2527212114691860028165393)
                    ·
                      refine ⟨1895409086018895021124045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527212114691860028165393 1895409086018895021124045)
                      ·
                        rfl

theorem cell23_3691296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_3691296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691296 prefixEnd_3691296 := by exact prefixLift 3691296
  have htrace : WordTrace (prefixWord ++ tailWord_3691296) baseStart_3691296 baseEnd_3691296 := by
    simpa [prefixWord, tailWord_3691296, baseEnd_3691296] using wordTrace_append hprefix tailTrace_3691296
  have hstable : (prefixWord ++ tailWord_3691296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691296).length < 2 ^ (prefixWord ++ tailWord_3691296).sum := by decide
  have hdescent : baseEnd_3691296 < baseStart_3691296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691316 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3691316 : Nat := 118140960795 + 3691316 * 2 ^ 59
def prefixEnd_3691316 : Nat := 4983230072969 + 3 ^ 40 * 3691316 * 2
def baseEnd_3691316 : Nat := 1895419355631984942873953

theorem tailTrace_3691316 : CollatzResearch.WordTrace tailWord_3691316 prefixEnd_3691316 1895419355631984942873953 := by
  unfold tailWord_3691316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67316677547500016713542901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89755570063333355618057201 67316677547500016713542901)
  ·
    refine ⟨6310938520078126566894647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67316677547500016713542901 6310938520078126566894647)
    ·
      refine ⟨9466407780117189850341971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6310938520078126566894647 9466407780117189850341971)
      ·
        refine ⟨14199611670175784775512957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9466407780117189850341971 14199611670175784775512957)
        ·
          refine ⟨5324854376315919290817359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14199611670175784775512957 5324854376315919290817359)
          ·
            refine ⟨7987281564473878936226039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324854376315919290817359 7987281564473878936226039)
            ·
              refine ⟨11980922346710818404339059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987281564473878936226039 11980922346710818404339059)
              ·
                refine ⟨17971383520066227606508589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11980922346710818404339059 17971383520066227606508589)
                ·
                  refine ⟨6739268820024835352440721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17971383520066227606508589 6739268820024835352440721)
                  ·
                    refine ⟨5054451615018626514330541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6739268820024835352440721 5054451615018626514330541)
                    ·
                      refine ⟨1895419355631984942873953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5054451615018626514330541 1895419355631984942873953)
                      ·
                        rfl

theorem cell23_3691316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3691316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691316 prefixEnd_3691316 := by exact prefixLift 3691316
  have htrace : WordTrace (prefixWord ++ tailWord_3691316) baseStart_3691316 baseEnd_3691316 := by
    simpa [prefixWord, tailWord_3691316, baseEnd_3691316] using wordTrace_append hprefix tailTrace_3691316
  have hstable : (prefixWord ++ tailWord_3691316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691316).length < 2 ^ (prefixWord ++ tailWord_3691316).sum := by decide
  have hdescent : baseEnd_3691316 < baseStart_3691316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691346 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3691346 : Nat := 118140960795 + 3691346 * 2 ^ 59
def prefixEnd_3691346 : Nat := 4983230072969 + 3 ^ 40 * 3691346 * 2
def baseEnd_3691346 : Nat := 1895434760051619825498815

theorem tailTrace_3691346 : CollatzResearch.WordTrace tailWord_3691346 prefixEnd_3691346 1895434760051619825498815 := by
  unfold tailWord_3691346
  simp only [CollatzResearch.WordTrace]
  refine ⟨33658612321222837137669473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89756299523260899033785261 33658612321222837137669473)
  ·
    refine ⟨25243959240917127853252105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33658612321222837137669473 25243959240917127853252105)
    ·
      refine ⟨18932969430687845889939079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25243959240917127853252105 18932969430687845889939079)
      ·
        refine ⟨28399454146031768834908619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18932969430687845889939079 28399454146031768834908619)
        ·
          refine ⟨42599181219047653252362929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28399454146031768834908619 42599181219047653252362929)
          ·
            refine ⟨31949385914285739939272197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42599181219047653252362929 31949385914285739939272197)
            ·
              refine ⟨5990509858928576238613537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31949385914285739939272197 5990509858928576238613537)
              ·
                refine ⟨4492882394196432178960153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5990509858928576238613537 4492882394196432178960153)
                ·
                  refine ⟨3369661795647324134220115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4492882394196432178960153 3369661795647324134220115)
                  ·
                    refine ⟨5054492693470986201330173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369661795647324134220115 5054492693470986201330173)
                    ·
                      refine ⟨1895434760051619825498815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5054492693470986201330173 1895434760051619825498815)
                      ·
                        rfl

theorem cell23_3691346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3691346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691346 prefixEnd_3691346 := by exact prefixLift 3691346
  have htrace : WordTrace (prefixWord ++ tailWord_3691346) baseStart_3691346 baseEnd_3691346 := by
    simpa [prefixWord, tailWord_3691346, baseEnd_3691346] using wordTrace_append hprefix tailTrace_3691346
  have hstable : (prefixWord ++ tailWord_3691346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691346).length < 2 ^ (prefixWord ++ tailWord_3691346).sum := by decide
  have hdescent : baseEnd_3691346 < baseStart_3691346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691356 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3691356 : Nat := 118140960795 + 3691356 * 2 ^ 59
def prefixEnd_3691356 : Nat := 4983230072969 + 3 ^ 40 * 3691356 * 2
def baseEnd_3691356 : Nat := 1895439894858164786373769

theorem tailTrace_3691356 : CollatzResearch.WordTrace tailWord_3691356 prefixEnd_3691356 1895439894858164786373769 := by
  unfold tailWord_3691356
  simp only [CollatzResearch.WordTrace]
  refine ⟨67317407007427560129270961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89756542676570080172361281 67317407007427560129270961)
  ·
    refine ⟨50488055255570670096953221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67317407007427560129270961 50488055255570670096953221)
    ·
      refine ⟨9466510360419500643178729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50488055255570670096953221 9466510360419500643178729)
      ·
        refine ⟨7099882770314625482384047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9466510360419500643178729 7099882770314625482384047)
        ·
          refine ⟨10649824155471938223576071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099882770314625482384047 10649824155471938223576071)
          ·
            refine ⟨15974736233207907335364107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10649824155471938223576071 15974736233207907335364107)
            ·
              refine ⟨23962104349811861003046161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15974736233207907335364107 23962104349811861003046161)
              ·
                refine ⟨17971578262358895752284621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23962104349811861003046161 17971578262358895752284621)
                ·
                  refine ⟨6739341848384585907106733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17971578262358895752284621 6739341848384585907106733)
                  ·
                    refine ⟨2527253193144219715165025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6739341848384585907106733 2527253193144219715165025)
                    ·
                      refine ⟨1895439894858164786373769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527253193144219715165025 1895439894858164786373769)
                      ·
                        rfl

theorem cell23_3691356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3691356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691356 prefixEnd_3691356 := by exact prefixLift 3691356
  have htrace : WordTrace (prefixWord ++ tailWord_3691356) baseStart_3691356 baseEnd_3691356 := by
    simpa [prefixWord, tailWord_3691356, baseEnd_3691356] using wordTrace_append hprefix tailTrace_3691356
  have hstable : (prefixWord ++ tailWord_3691356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691356).length < 2 ^ (prefixWord ++ tailWord_3691356).sum := by decide
  have hdescent : baseEnd_3691356 < baseStart_3691356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691369 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 8, 2, 2]
def baseStart_3691369 : Nat := 118140960795 + 3691369 * 2 ^ 59
def prefixEnd_3691369 : Nat := 4983230072969 + 3 ^ 40 * 3691369 * 2
def baseEnd_3691369 : Nat := 1895446570106673235511209

theorem tailTrace_3691369 : CollatzResearch.WordTrace tailWord_3691369 prefixEnd_3691369 1895446570106673235511209 := by
  unfold tailWord_3691369
  simp only [CollatzResearch.WordTrace]
  refine ⟨134635288163808023478765161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89756858775872015652510107 134635288163808023478765161)
  ·
    refine ⟨100976466122856017609073871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134635288163808023478765161 100976466122856017609073871)
    ·
      refine ⟨151464699184284026413610807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100976466122856017609073871 151464699184284026413610807)
      ·
        refine ⟨227197048776426039620416211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151464699184284026413610807 227197048776426039620416211)
        ·
          refine ⟨340795573164639059430624317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227197048776426039620416211 340795573164639059430624317)
          ·
            refine ⟨127798339936739647286484119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340795573164639059430624317 127798339936739647286484119)
            ·
              refine ⟨191697509905109470929726179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127798339936739647286484119 191697509905109470929726179)
              ·
                refine ⟨287546264857664206394589269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191697509905109470929726179 287546264857664206394589269)
                ·
                  refine ⟨3369682791300752418686593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 287546264857664206394589269 3369682791300752418686593)
                  ·
                    refine ⟨2527262093475564314014945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3369682791300752418686593 2527262093475564314014945)
                    ·
                      refine ⟨1895446570106673235511209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527262093475564314014945 1895446570106673235511209)
                      ·
                        rfl

theorem cell23_3691369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 2, 2].length) (baseStart_3691369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691369 prefixEnd_3691369 := by exact prefixLift 3691369
  have htrace : WordTrace (prefixWord ++ tailWord_3691369) baseStart_3691369 baseEnd_3691369 := by
    simpa [prefixWord, tailWord_3691369, baseEnd_3691369] using wordTrace_append hprefix tailTrace_3691369
  have hstable : (prefixWord ++ tailWord_3691369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691369).length < 2 ^ (prefixWord ++ tailWord_3691369).sum := by decide
  have hdescent : baseEnd_3691369 < baseStart_3691369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691372 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_3691372 : Nat := 118140960795 + 3691372 * 2 ^ 59
def prefixEnd_3691372 : Nat := 4983230072969 + 3 ^ 40 * 3691372 * 2
def baseEnd_3691372 : Nat := 1895448110548636723773695

theorem tailTrace_3691372 : CollatzResearch.WordTrace tailWord_3691372 prefixEnd_3691372 1895448110548636723773695 := by
  unfold tailWord_3691372
  simp only [CollatzResearch.WordTrace]
  refine ⟨67317698791398577495562185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89756931721864769994082913 67317698791398577495562185)
  ·
    refine ⟨50488274093548933121671639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67317698791398577495562185 50488274093548933121671639)
    ·
      refine ⟨75732411140323399682507459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50488274093548933121671639 75732411140323399682507459)
      ·
        refine ⟨113598616710485099523761189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75732411140323399682507459 113598616710485099523761189)
        ·
          refine ⟨21299740633215956160705223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113598616710485099523761189 21299740633215956160705223)
          ·
            refine ⟨31949610949823934241057835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21299740633215956160705223 31949610949823934241057835)
            ·
              refine ⟨47924416424735901361586753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31949610949823934241057835 47924416424735901361586753)
              ·
                refine ⟨35943312318551926021190065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47924416424735901361586753 35943312318551926021190065)
                ·
                  refine ⟨26957484238913944515892549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35943312318551926021190065 26957484238913944515892549)
                  ·
                    refine ⟨5054528294796364596729853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26957484238913944515892549 5054528294796364596729853)
                    ·
                      refine ⟨1895448110548636723773695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5054528294796364596729853 1895448110548636723773695)
                      ·
                        rfl

theorem cell23_3691372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_3691372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691372 prefixEnd_3691372 := by exact prefixLift 3691372
  have htrace : WordTrace (prefixWord ++ tailWord_3691372) baseStart_3691372 baseEnd_3691372 := by
    simpa [prefixWord, tailWord_3691372, baseEnd_3691372] using wordTrace_append hprefix tailTrace_3691372
  have hstable : (prefixWord ++ tailWord_3691372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691372).length < 2 ^ (prefixWord ++ tailWord_3691372).sum := by decide
  have hdescent : baseEnd_3691372 < baseStart_3691372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691390 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3691390 : Nat := 118140960795 + 3691390 * 2 ^ 59
def prefixEnd_3691390 : Nat := 4983230072969 + 3 ^ 40 * 3691390 * 2
def baseEnd_3691390 : Nat := 1895457353200417653348613

theorem tailTrace_3691390 : CollatzResearch.WordTrace tailWord_3691390 prefixEnd_3691390 1895457353200417653348613 := by
  unfold tailWord_3691390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16829506762091493008159953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89757369397821296043519749 16829506762091493008159953)
  ·
    refine ⟨12622130071568619756119965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16829506762091493008159953 12622130071568619756119965)
    ·
      refine ⟨4733298776838232408544987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12622130071568619756119965 4733298776838232408544987)
      ·
        refine ⟨7099948165257348612817481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733298776838232408544987 7099948165257348612817481)
        ·
          refine ⟨5324961123943011459613111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7099948165257348612817481 5324961123943011459613111)
          ·
            refine ⟨7987441685914517189419667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324961123943011459613111 7987441685914517189419667)
            ·
              refine ⟨11981162528871775784129501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987441685914517189419667 11981162528871775784129501)
              ·
                refine ⟨4492935948326915919048563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11981162528871775784129501 4492935948326915919048563)
                ·
                  refine ⟨6739403922490373878572845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492935948326915919048563 6739403922490373878572845)
                  ·
                    refine ⟨2527276470933890204464817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6739403922490373878572845 2527276470933890204464817)
                    ·
                      refine ⟨1895457353200417653348613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527276470933890204464817 1895457353200417653348613)
                      ·
                        rfl

theorem cell23_3691390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3691390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691390 prefixEnd_3691390 := by exact prefixLift 3691390
  have htrace : WordTrace (prefixWord ++ tailWord_3691390) baseStart_3691390 baseEnd_3691390 := by
    simpa [prefixWord, tailWord_3691390, baseEnd_3691390] using wordTrace_append hprefix tailTrace_3691390
  have hstable : (prefixWord ++ tailWord_3691390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691390).length < 2 ^ (prefixWord ++ tailWord_3691390).sum := by decide
  have hdescent : baseEnd_3691390 < baseStart_3691390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691420 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3691420 : Nat := 118140960795 + 3691420 * 2 ^ 59
def prefixEnd_3691420 : Nat := 4983230072969 + 3 ^ 40 * 3691420 * 2
def baseEnd_3691420 : Nat := 1895472757620052535973475

theorem tailTrace_3691420 : CollatzResearch.WordTrace tailWord_3691420 prefixEnd_3691420 1895472757620052535973475 := by
  unfold tailWord_3691420
  simp only [CollatzResearch.WordTrace]
  refine ⟨67318574143311629594435857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89758098857748839459247809 67318574143311629594435857)
  ·
    refine ⟨50488930607483722195826893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67318574143311629594435857 50488930607483722195826893)
    ·
      refine ⟨18933348977806395823435085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50488930607483722195826893 18933348977806395823435085)
      ·
        refine ⟨7100005866677398433788157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18933348977806395823435085 7100005866677398433788157)
        ·
          refine ⟨2662502200004024412670559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7100005866677398433788157 2662502200004024412670559)
          ·
            refine ⟨3993753300006036619005839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662502200004024412670559 3993753300006036619005839)
            ·
              refine ⟨5990629950009054928508759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993753300006036619005839 5990629950009054928508759)
              ·
                refine ⟨8985944925013582392763139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990629950009054928508759 8985944925013582392763139)
                ·
                  refine ⟨13478917387520373589144709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985944925013582392763139 13478917387520373589144709)
                  ·
                    refine ⟨2527297010160070047964633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13478917387520373589144709 2527297010160070047964633)
                    ·
                      refine ⟨1895472757620052535973475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527297010160070047964633 1895472757620052535973475)
                      ·
                        rfl

theorem cell23_3691420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3691420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691420 prefixEnd_3691420 := by exact prefixLift 3691420
  have htrace : WordTrace (prefixWord ++ tailWord_3691420) baseStart_3691420 baseEnd_3691420 := by
    simpa [prefixWord, tailWord_3691420, baseEnd_3691420] using wordTrace_append hprefix tailTrace_3691420
  have hstable : (prefixWord ++ tailWord_3691420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691420).length < 2 ^ (prefixWord ++ tailWord_3691420).sum := by decide
  have hdescent : baseEnd_3691420 < baseStart_3691420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691460 : List Nat := [2, 3, 3, 3, 1, 1, 3, 2, 5]
def baseStart_3691460 : Nat := 118140960795 + 3691460 * 2 ^ 59
def prefixEnd_3691460 : Nat := 4983230072969 + 3 ^ 40 * 3691460 * 2
def baseEnd_3691460 : Nat := 210610366316248042163699

theorem tailTrace_3691460 : CollatzResearch.WordTrace tailWord_3691460 prefixEnd_3691460 210610366316248042163699 := by
  unfold tailWord_3691460
  simp only [CollatzResearch.WordTrace]
  refine ⟨67319303603239173010163917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89759071470985564013551889 67319303603239173010163917)
  ·
    refine ⟨25244738851214689878811469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67319303603239173010163917 25244738851214689878811469)
    ·
      refine ⟨9466777069205508704554301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25244738851214689878811469 9466777069205508704554301)
      ·
        refine ⟨3550041400952065764207863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9466777069205508704554301 3550041400952065764207863)
        ·
          refine ⟨5325062101428098646311795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550041400952065764207863 5325062101428098646311795)
          ·
            refine ⟨7987593152142147969467693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325062101428098646311795 7987593152142147969467693)
            ·
              refine ⟨2995347432053305488550385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7987593152142147969467693 2995347432053305488550385)
              ·
                refine ⟨2246510574039979116412789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2995347432053305488550385 2246510574039979116412789)
                ·
                  refine ⟨210610366316248042163699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2246510574039979116412789 210610366316248042163699)
                  ·
                    rfl

theorem cell23_3691460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_3691460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691460 prefixEnd_3691460 := by exact prefixLift 3691460
  have htrace : WordTrace (prefixWord ++ tailWord_3691460) baseStart_3691460 baseEnd_3691460 := by
    simpa [prefixWord, tailWord_3691460, baseEnd_3691460] using wordTrace_append hprefix tailTrace_3691460
  have hstable : (prefixWord ++ tailWord_3691460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691460).length < 2 ^ (prefixWord ++ tailWord_3691460).sum := by decide
  have hdescent : baseEnd_3691460 < baseStart_3691460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691493 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3691493 : Nat := 118140960795 + 3691493 * 2 ^ 59
def prefixEnd_3691493 : Nat := 4983230072969 + 3 ^ 40 * 3691493 * 2
def baseEnd_3691493 : Nat := 1895510241707830750360639

theorem tailTrace_3691493 : CollatzResearch.WordTrace tailWord_3691493 prefixEnd_3691493 1895510241707830750360639 := by
  unfold tailWord_3691493
  simp only [CollatzResearch.WordTrace]
  refine ⟨134639810815358792656279133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89759873876905861770852755 134639810815358792656279133)
  ·
    refine ⟨50489929055759547246104675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134639810815358792656279133 50489929055759547246104675)
    ·
      refine ⟨75734893583639320869157013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50489929055759547246104675 75734893583639320869157013)
      ·
        refine ⟨3550073136733093165741735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75734893583639320869157013 3550073136733093165741735)
        ·
          refine ⟨5325109705099639748612603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550073136733093165741735 5325109705099639748612603)
          ·
            refine ⟨7987664557649459622918905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325109705099639748612603 7987664557649459622918905)
            ·
              refine ⟨5990748418237094717189179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7987664557649459622918905 5990748418237094717189179)
              ·
                refine ⟨8986122627355642075783769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990748418237094717189179 8986122627355642075783769)
                ·
                  refine ⟨6739591970516731556837827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8986122627355642075783769 6739591970516731556837827)
                  ·
                    refine ⟨10109387955775097335256741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6739591970516731556837827 10109387955775097335256741)
                    ·
                      refine ⟨1895510241707830750360639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10109387955775097335256741 1895510241707830750360639)
                      ·
                        rfl

theorem cell23_3691493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3691493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691493 prefixEnd_3691493 := by exact prefixLift 3691493
  have htrace : WordTrace (prefixWord ++ tailWord_3691493) baseStart_3691493 baseEnd_3691493 := by
    simpa [prefixWord, tailWord_3691493, baseEnd_3691493] using wordTrace_append hprefix tailTrace_3691493
  have hstable : (prefixWord ++ tailWord_3691493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691493).length < 2 ^ (prefixWord ++ tailWord_3691493).sum := by decide
  have hdescent : baseEnd_3691493 < baseStart_3691493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691519 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 5, 5, 2]
def baseStart_3691519 : Nat := 118140960795 + 3691519 * 2 ^ 59
def prefixEnd_3691519 : Nat := 4983230072969 + 3 ^ 40 * 3691519 * 2
def baseEnd_3691519 : Nat := 1895523592204847648635519

theorem tailTrace_3691519 : CollatzResearch.WordTrace tailWord_3691519 prefixEnd_3691519 1895523592204847648635519 := by
  unfold tailWord_3691519
  simp only [CollatzResearch.WordTrace]
  refine ⟨134640759113264599096725611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89760506075509732731150407 134640759113264599096725611)
  ·
    refine ⟨201961138669896898645088417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134640759113264599096725611 201961138669896898645088417)
    ·
      refine ⟨151470854002422673983816313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201961138669896898645088417 151470854002422673983816313)
      ·
        refine ⟨113603140501817005487862235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151470854002422673983816313 113603140501817005487862235)
        ·
          refine ⟨170404710752725508231793353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113603140501817005487862235 170404710752725508231793353)
          ·
            refine ⟨127803533064544131173845015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170404710752725508231793353 127803533064544131173845015)
            ·
              refine ⟨191705299596816196760767523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127803533064544131173845015 191705299596816196760767523)
              ·
                refine ⟨287557949395224295141151285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191705299596816196760767523 287557949395224295141151285)
                ·
                  refine ⟨26958557755802277669482933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287557949395224295141151285 26958557755802277669482933)
                  ·
                    refine ⟨2527364789606463531514025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26958557755802277669482933 2527364789606463531514025)
                    ·
                      refine ⟨1895523592204847648635519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527364789606463531514025 1895523592204847648635519)
                      ·
                        rfl

theorem cell23_3691519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_3691519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691519 prefixEnd_3691519 := by exact prefixLift 3691519
  have htrace : WordTrace (prefixWord ++ tailWord_3691519) baseStart_3691519 baseEnd_3691519 := by
    simpa [prefixWord, tailWord_3691519, baseEnd_3691519] using wordTrace_append hprefix tailTrace_3691519
  have hstable : (prefixWord ++ tailWord_3691519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691519).length < 2 ^ (prefixWord ++ tailWord_3691519).sum := by decide
  have hdescent : baseEnd_3691519 < baseStart_3691519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691543 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3691543 : Nat := 118140960795 + 3691543 * 2 ^ 59
def prefixEnd_3691543 : Nat := 4983230072969 + 3 ^ 40 * 3691543 * 2
def baseEnd_3691543 : Nat := 1895535915740555554735409

theorem tailTrace_3691543 : CollatzResearch.WordTrace tailWord_3691543 prefixEnd_3691543 1895535915740555554735409 := by
  unfold tailWord_3691543
  simp only [CollatzResearch.WordTrace]
  refine ⟨134641634465177651195599283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89761089643451767463732855 134641634465177651195599283)
  ·
    refine ⟨201962451697766476793398925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134641634465177651195599283 201962451697766476793398925)
    ·
      refine ⟨75735919386662428797524597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201962451697766476793398925 75735919386662428797524597)
      ·
        refine ⟨7100242442499602699767931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75735919386662428797524597 7100242442499602699767931)
        ·
          refine ⟨10650363663749404049651897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100242442499602699767931 10650363663749404049651897)
          ·
            refine ⟨7987772747812053037238923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10650363663749404049651897 7987772747812053037238923)
            ·
              refine ⟨11981659121718079555858385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987772747812053037238923 11981659121718079555858385)
              ·
                refine ⟨8986244341288559666893789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11981659121718079555858385 8986244341288559666893789)
                ·
                  refine ⟨3369841627983209875085171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8986244341288559666893789 3369841627983209875085171)
                  ·
                    refine ⟨5054762441974814812627757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369841627983209875085171 5054762441974814812627757)
                    ·
                      refine ⟨1895535915740555554735409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5054762441974814812627757 1895535915740555554735409)
                      ·
                        rfl

theorem cell23_3691543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3691543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691543 prefixEnd_3691543 := by exact prefixLift 3691543
  have htrace : WordTrace (prefixWord ++ tailWord_3691543) baseStart_3691543 baseEnd_3691543 := by
    simpa [prefixWord, tailWord_3691543, baseEnd_3691543] using wordTrace_append hprefix tailTrace_3691543
  have hstable : (prefixWord ++ tailWord_3691543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691543).length < 2 ^ (prefixWord ++ tailWord_3691543).sum := by decide
  have hdescent : baseEnd_3691543 < baseStart_3691543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691553 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_3691553 : Nat := 118140960795 + 3691553 * 2 ^ 59
def prefixEnd_3691553 : Nat := 4983230072969 + 3 ^ 40 * 3691553 * 2
def baseEnd_3691553 : Nat := 1895541050547100515610363

theorem tailTrace_3691553 : CollatzResearch.WordTrace tailWord_3691553 prefixEnd_3691553 1895541050547100515610363 := by
  unfold tailWord_3691553
  simp only [CollatzResearch.WordTrace]
  refine ⟨134641999195141422903463313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89761332796760948602308875 134641999195141422903463313)
  ·
    refine ⟨100981499396356067177597485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134641999195141422903463313 100981499396356067177597485)
    ·
      refine ⟨37868062273633525191599057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100981499396356067177597485 37868062273633525191599057)
      ·
        refine ⟨28401046705225143893699293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37868062273633525191599057 28401046705225143893699293)
        ·
          refine ⟨10650392514459428960137235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28401046705225143893699293 10650392514459428960137235)
          ·
            refine ⟨15975588771689143440205853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10650392514459428960137235 15975588771689143440205853)
            ·
              refine ⟨5990845789383428790077195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15975588771689143440205853 5990845789383428790077195)
              ·
                refine ⟨8986268684075143185115793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990845789383428790077195 8986268684075143185115793)
                ·
                  refine ⟨6739701513056357388836845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8986268684075143185115793 6739701513056357388836845)
                  ·
                    refine ⟨2527388067396134020813817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6739701513056357388836845 2527388067396134020813817)
                    ·
                      refine ⟨1895541050547100515610363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527388067396134020813817 1895541050547100515610363)
                      ·
                        rfl

theorem cell23_3691553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_3691553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691553 prefixEnd_3691553 := by exact prefixLift 3691553
  have htrace : WordTrace (prefixWord ++ tailWord_3691553) baseStart_3691553 baseEnd_3691553 := by
    simpa [prefixWord, tailWord_3691553, baseEnd_3691553] using wordTrace_append hprefix tailTrace_3691553
  have hstable : (prefixWord ++ tailWord_3691553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691553).length < 2 ^ (prefixWord ++ tailWord_3691553).sum := by decide
  have hdescent : baseEnd_3691553 < baseStart_3691553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691569 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3691569 : Nat := 118140960795 + 3691569 * 2 ^ 59
def prefixEnd_3691569 : Nat := 4983230072969 + 3 ^ 40 * 3691569 * 2
def baseEnd_3691569 : Nat := 1895549266237572453010289

theorem tailTrace_3691569 : CollatzResearch.WordTrace tailWord_3691569 prefixEnd_3691569 1895549266237572453010289 := by
  unfold tailWord_3691569
  simp only [CollatzResearch.WordTrace]
  refine ⟨134642582763083457636045761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89761721842055638424030507 134642582763083457636045761)
  ·
    refine ⟨100981937072312593227034321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134642582763083457636045761 100981937072312593227034321)
    ·
      refine ⟨75736452804234444920275741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100981937072312593227034321 75736452804234444920275741)
      ·
        refine ⟨28401169801587916845103403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75736452804234444920275741 28401169801587916845103403)
        ·
          refine ⟨42601754702381875267655105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28401169801587916845103403 42601754702381875267655105)
          ·
            refine ⟨31951316026786406450741329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42601754702381875267655105 31951316026786406450741329)
            ·
              refine ⟨23963487020089804838055997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31951316026786406450741329 23963487020089804838055997)
              ·
                refine ⟨8986307632533676814270999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23963487020089804838055997 8986307632533676814270999)
                ·
                  refine ⟨13479461448800515221406499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8986307632533676814270999 13479461448800515221406499)
                  ·
                    refine ⟨20219192173200772832109749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13479461448800515221406499 20219192173200772832109749)
                    ·
                      refine ⟨1895549266237572453010289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20219192173200772832109749 1895549266237572453010289)
                      ·
                        rfl

theorem cell23_3691569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3691569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691569 prefixEnd_3691569 := by exact prefixLift 3691569
  have htrace : WordTrace (prefixWord ++ tailWord_3691569) baseStart_3691569 baseEnd_3691569 := by
    simpa [prefixWord, tailWord_3691569, baseEnd_3691569] using wordTrace_append hprefix tailTrace_3691569
  have hstable : (prefixWord ++ tailWord_3691569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691569).length < 2 ^ (prefixWord ++ tailWord_3691569).sum := by decide
  have hdescent : baseEnd_3691569 < baseStart_3691569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691576 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 4, 4]
def baseStart_3691576 : Nat := 118140960795 + 3691576 * 2 ^ 59
def prefixEnd_3691576 : Nat := 4983230072969 + 3 ^ 40 * 3691576 * 2
def baseEnd_3691576 : Nat := 631850953534051308540919

theorem tailTrace_3691576 : CollatzResearch.WordTrace tailWord_3691576 prefixEnd_3691576 631850953534051308540919 := by
  unfold tailWord_3691576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67321419037029048915775291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89761892049372065221033721 67321419037029048915775291)
  ·
    refine ⟨100982128555543573373662937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67321419037029048915775291 100982128555543573373662937)
    ·
      refine ⟨75736596416657680030247203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100982128555543573373662937 75736596416657680030247203)
      ·
        refine ⟨113604894624986520045370805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75736596416657680030247203 113604894624986520045370805)
        ·
          refine ⟨10650458871092486254253513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113604894624986520045370805 10650458871092486254253513)
          ·
            refine ⟨7987844153319364690690135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10650458871092486254253513 7987844153319364690690135)
            ·
              refine ⟨11981766229979047036035203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7987844153319364690690135 11981766229979047036035203)
              ·
                refine ⟨17972649344968570554052805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11981766229979047036035203 17972649344968570554052805)
                ·
                  refine ⟨3369871752181606978884901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17972649344968570554052805 3369871752181606978884901)
                  ·
                    refine ⟨631850953534051308540919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3369871752181606978884901 631850953534051308540919)
                    ·
                      rfl

theorem cell23_3691576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_3691576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691576 prefixEnd_3691576 := by exact prefixLift 3691576
  have htrace : WordTrace (prefixWord ++ tailWord_3691576) baseStart_3691576 baseEnd_3691576 := by
    simpa [prefixWord, tailWord_3691576, baseEnd_3691576] using wordTrace_append hprefix tailTrace_3691576
  have hstable : (prefixWord ++ tailWord_3691576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691576).length < 2 ^ (prefixWord ++ tailWord_3691576).sum := by decide
  have hdescent : baseEnd_3691576 < baseStart_3691576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691616 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 6, 1, 3]
def baseStart_3691616 : Nat := 118140960795 + 3691616 * 2 ^ 59
def prefixEnd_3691616 : Nat := 4983230072969 + 3 ^ 40 * 3691616 * 2
def baseEnd_3691616 : Nat := 1895573399828333769122573

theorem tailTrace_3691616 : CollatzResearch.WordTrace tailWord_3691616 prefixEnd_3691616 1895573399828333769122573 := by
  unfold tailWord_3691616
  simp only [CollatzResearch.WordTrace]
  refine ⟨67322148496956592331503351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89762864662608789775337801 67322148496956592331503351)
  ·
    refine ⟨100983222745434888497255027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67322148496956592331503351 100983222745434888497255027)
    ·
      refine ⟨151474834118152332745882541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100983222745434888497255027 151474834118152332745882541)
      ·
        refine ⟨56803062794307124779705953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151474834118152332745882541 56803062794307124779705953)
        ·
          refine ⟨42602297095730343584779465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56803062794307124779705953 42602297095730343584779465)
          ·
            refine ⟨31951722821797757688584599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42602297095730343584779465 31951722821797757688584599)
            ·
              refine ⟨47927584232696636532876899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31951722821797757688584599 47927584232696636532876899)
              ·
                refine ⟨71891376349044954799315349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47927584232696636532876899 71891376349044954799315349)
                ·
                  refine ⟨3369908266361482256217907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71891376349044954799315349 3369908266361482256217907)
                  ·
                    refine ⟨5054862399542223384326861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3369908266361482256217907 5054862399542223384326861)
                    ·
                      refine ⟨1895573399828333769122573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5054862399542223384326861 1895573399828333769122573)
                      ·
                        rfl

theorem cell23_3691616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_3691616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691616 prefixEnd_3691616 := by exact prefixLift 3691616
  have htrace : WordTrace (prefixWord ++ tailWord_3691616) baseStart_3691616 baseEnd_3691616 := by
    simpa [prefixWord, tailWord_3691616, baseEnd_3691616] using wordTrace_append hprefix tailTrace_3691616
  have hstable : (prefixWord ++ tailWord_3691616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691616).length < 2 ^ (prefixWord ++ tailWord_3691616).sum := by decide
  have hdescent : baseEnd_3691616 < baseStart_3691616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691639 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_3691639 : Nat := 118140960795 + 3691639 * 2 ^ 59
def prefixEnd_3691639 : Nat := 4983230072969 + 3 ^ 40 * 3691639 * 2
def baseEnd_3691639 : Nat := 1895585209883387179134967

theorem tailTrace_3691639 : CollatzResearch.WordTrace tailWord_3691639 prefixEnd_3691639 1895585209883387179134967 := by
  unfold tailWord_3691639
  simp only [CollatzResearch.WordTrace]
  refine ⟨134645135872829859591093971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89763423915219906394062647 134645135872829859591093971)
  ·
    refine ⟨201967703809244789386640957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134645135872829859591093971 201967703809244789386640957)
    ·
      refine ⟨75737888928466796019990359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201967703809244789386640957 75737888928466796019990359)
      ·
        refine ⟨113606833392700194029985539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75737888928466796019990359 113606833392700194029985539)
        ·
          refine ⟨170410250089050291044978309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113606833392700194029985539 170410250089050291044978309)
          ·
            refine ⟨31951921891696929570933433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170410250089050291044978309 31951921891696929570933433)
            ·
              refine ⟨23963941418772697178200075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31951921891696929570933433 23963941418772697178200075)
              ·
                refine ⟨35945912128159045767300113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23963941418772697178200075 35945912128159045767300113)
                ·
                  refine ⟨26959434096119284325475085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35945912128159045767300113 26959434096119284325475085)
                  ·
                    refine ⟨10109787786044731622053157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26959434096119284325475085 10109787786044731622053157)
                    ·
                      refine ⟨1895585209883387179134967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10109787786044731622053157 1895585209883387179134967)
                      ·
                        rfl

theorem cell23_3691639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_3691639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691639 prefixEnd_3691639 := by exact prefixLift 3691639
  have htrace : WordTrace (prefixWord ++ tailWord_3691639) baseStart_3691639 baseEnd_3691639 := by
    simpa [prefixWord, tailWord_3691639, baseEnd_3691639] using wordTrace_append hprefix tailTrace_3691639
  have hstable : (prefixWord ++ tailWord_3691639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691639).length < 2 ^ (prefixWord ++ tailWord_3691639).sum := by decide
  have hdescent : baseEnd_3691639 < baseStart_3691639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691669 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3691669 : Nat := 118140960795 + 3691669 * 2 ^ 59
def prefixEnd_3691669 : Nat := 4983230072969 + 3 ^ 40 * 3691669 * 2
def baseEnd_3691669 : Nat := 1895600614303022061759829

theorem tailTrace_3691669 : CollatzResearch.WordTrace tailWord_3691669 prefixEnd_3691669 1895600614303022061759829 := by
  unfold tailWord_3691669
  simp only [CollatzResearch.WordTrace]
  refine ⟨134646230062721174714686061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89764153375147449809790707 134646230062721174714686061)
  ·
    refine ⟨50492336273520440518007273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134646230062721174714686061 50492336273520440518007273)
    ·
      refine ⟨37869252205140330388505455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50492336273520440518007273 37869252205140330388505455)
      ·
        refine ⟨56803878307710495582758183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37869252205140330388505455 56803878307710495582758183)
        ·
          refine ⟨85205817461565743374137275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56803878307710495582758183 85205817461565743374137275)
          ·
            refine ⟨127808726192348615061205913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85205817461565743374137275 127808726192348615061205913)
            ·
              refine ⟨95856544644261461295904435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127808726192348615061205913 95856544644261461295904435)
              ·
                refine ⟨143784816966392191943856653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95856544644261461295904435 143784816966392191943856653)
                ·
                  refine ⟨53919306362397071978946245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143784816966392191943856653 53919306362397071978946245)
                  ·
                    refine ⟨10109869942949450996052421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53919306362397071978946245 10109869942949450996052421)
                    ·
                      refine ⟨1895600614303022061759829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10109869942949450996052421 1895600614303022061759829)
                      ·
                        rfl

theorem cell23_3691669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3691669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691669 prefixEnd_3691669 := by exact prefixLift 3691669
  have htrace : WordTrace (prefixWord ++ tailWord_3691669) baseStart_3691669 baseEnd_3691669 := by
    simpa [prefixWord, tailWord_3691669, baseEnd_3691669] using wordTrace_append hprefix tailTrace_3691669
  have hstable : (prefixWord ++ tailWord_3691669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691669).length < 2 ^ (prefixWord ++ tailWord_3691669).sum := by decide
  have hdescent : baseEnd_3691669 < baseStart_3691669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691676 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3691676 : Nat := 118140960795 + 3691676 * 2 ^ 59
def prefixEnd_3691676 : Nat := 4983230072969 + 3 ^ 40 * 3691676 * 2
def baseEnd_3691676 : Nat := 1895604208667603534372297

theorem tailTrace_3691676 : CollatzResearch.WordTrace tailWord_3691676 prefixEnd_3691676 1895604208667603534372297 := by
  unfold tailWord_3691676
  simp only [CollatzResearch.WordTrace]
  refine ⟨67323242686847907455095441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89764323582463876606793921 67323242686847907455095441)
  ·
    refine ⟨50492432015135930591321581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67323242686847907455095441 50492432015135930591321581)
    ·
      refine ⟨18934662005675973971745593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50492432015135930591321581 18934662005675973971745593)
      ·
        refine ⟨14200996504256980478809195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18934662005675973971745593 14200996504256980478809195)
        ·
          refine ⟨21301494756385470718213793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14200996504256980478809195 21301494756385470718213793)
          ·
            refine ⟨15976121067289103038660345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21301494756385470718213793 15976121067289103038660345)
            ·
              refine ⟨11982090800466827278995259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15976121067289103038660345 11982090800466827278995259)
              ·
                refine ⟨17973136200700240918492889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11982090800466827278995259 17973136200700240918492889)
                ·
                  refine ⟨13479852150525180688869667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17973136200700240918492889 13479852150525180688869667)
                  ·
                    refine ⟨20219778225787771033304501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13479852150525180688869667 20219778225787771033304501)
                    ·
                      refine ⟨1895604208667603534372297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20219778225787771033304501 1895604208667603534372297)
                      ·
                        rfl

theorem cell23_3691676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3691676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691676 prefixEnd_3691676 := by exact prefixLift 3691676
  have htrace : WordTrace (prefixWord ++ tailWord_3691676) baseStart_3691676 baseEnd_3691676 := by
    simpa [prefixWord, tailWord_3691676, baseEnd_3691676] using wordTrace_append hprefix tailTrace_3691676
  have hstable : (prefixWord ++ tailWord_3691676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691676).length < 2 ^ (prefixWord ++ tailWord_3691676).sum := by decide
  have hdescent : baseEnd_3691676 < baseStart_3691676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691696 : List Nat := [2, 1, 1, 1, 2, 1, 2, 8, 5]
def baseStart_3691696 : Nat := 118140960795 + 3691696 * 2 ^ 59
def prefixEnd_3691696 : Nat := 4983230072969 + 3 ^ 40 * 3691696 * 2
def baseEnd_3691696 : Nat := 210623830920077050680245

theorem tailTrace_3691696 : CollatzResearch.WordTrace tailWord_3691696 prefixEnd_3691696 210623830920077050680245 := by
  unfold tailWord_3691696
  simp only [CollatzResearch.WordTrace]
  refine ⟨67323607416811679162959471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89764809889082238883945961 67323607416811679162959471)
  ·
    refine ⟨100985411125217518744439207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67323607416811679162959471 100985411125217518744439207)
    ·
      refine ⟨151478116687826278116658811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100985411125217518744439207 151478116687826278116658811)
      ·
        refine ⟨227217175031739417174988217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151478116687826278116658811 227217175031739417174988217)
        ·
          refine ⟨170412881273804562881241163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227217175031739417174988217 170412881273804562881241163)
          ·
            refine ⟨255619321910706844321861745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170412881273804562881241163 255619321910706844321861745)
            ·
              refine ⟨191714491433030133241396309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255619321910706844321861745 191714491433030133241396309)
              ·
                refine ⟨2246654196480821873922613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 191714491433030133241396309 2246654196480821873922613)
                ·
                  refine ⟨210623830920077050680245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2246654196480821873922613 210623830920077050680245)
                  ·
                    rfl

theorem cell23_3691696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 5].length) (baseStart_3691696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691696 prefixEnd_3691696 := by exact prefixLift 3691696
  have htrace : WordTrace (prefixWord ++ tailWord_3691696) baseStart_3691696 baseEnd_3691696 := by
    simpa [prefixWord, tailWord_3691696, baseEnd_3691696] using wordTrace_append hprefix tailTrace_3691696
  have hstable : (prefixWord ++ tailWord_3691696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691696).length < 2 ^ (prefixWord ++ tailWord_3691696).sum := by decide
  have hdescent : baseEnd_3691696 < baseStart_3691696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691713 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 7]
def baseStart_3691713 : Nat := 118140960795 + 3691713 * 2 ^ 59
def prefixEnd_3691713 : Nat := 4983230072969 + 3 ^ 40 * 3691713 * 2
def baseEnd_3691713 : Nat := 210624800827979987734403

theorem tailTrace_3691713 : CollatzResearch.WordTrace tailWord_3691713 prefixEnd_3691713 210624800827979987734403 := by
  unfold tailWord_3691713
  simp only [CollatzResearch.WordTrace]
  refine ⟨134647834874561770229287793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89765223249707846819525195 134647834874561770229287793)
  ·
    refine ⟨100985876155921327671965845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134647834874561770229287793 100985876155921327671965845)
    ·
      refine ⟨4733712944808812234623399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100985876155921327671965845 4733712944808812234623399)
      ·
        refine ⟨7100569417213218351935099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733712944808812234623399 7100569417213218351935099)
        ·
          refine ⟨10650854125819827527902649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7100569417213218351935099 10650854125819827527902649)
          ·
            refine ⟨7988140594364870645926987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10650854125819827527902649 7988140594364870645926987)
            ·
              refine ⟨11982210891547305968890481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988140594364870645926987 11982210891547305968890481)
              ·
                refine ⟨8986658168660479476667861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11982210891547305968890481 8986658168660479476667861)
                ·
                  refine ⟨210624800827979987734403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8986658168660479476667861 210624800827979987734403)
                  ·
                    rfl

theorem cell23_3691713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 7].length) (baseStart_3691713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691713 prefixEnd_3691713 := by exact prefixLift 3691713
  have htrace : WordTrace (prefixWord ++ tailWord_3691713) baseStart_3691713 baseEnd_3691713 := by
    simpa [prefixWord, tailWord_3691713, baseEnd_3691713] using wordTrace_append hprefix tailTrace_3691713
  have hstable : (prefixWord ++ tailWord_3691713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691713).length < 2 ^ (prefixWord ++ tailWord_3691713).sum := by decide
  have hdescent : baseEnd_3691713 < baseStart_3691713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691719 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3691719 : Nat := 118140960795 + 3691719 * 2 ^ 59
def prefixEnd_3691719 : Nat := 4983230072969 + 3 ^ 40 * 3691719 * 2
def baseEnd_3691719 : Nat := 1895626288335746866134599

theorem tailTrace_3691719 : CollatzResearch.WordTrace tailWord_3691719 prefixEnd_3691719 1895626288335746866134599 := by
  unfold tailWord_3691719
  simp only [CollatzResearch.WordTrace]
  refine ⟨134648053712540033254006211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89765369141693355502670807 134648053712540033254006211)
  ·
    refine ⟨201972080568810049881009317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134648053712540033254006211 201972080568810049881009317)
    ·
      refine ⟨37869765106651884352689247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201972080568810049881009317 37869765106651884352689247)
      ·
        refine ⟨56804647659977826529033871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37869765106651884352689247 56804647659977826529033871)
        ·
          refine ⟨85206971489966739793550807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56804647659977826529033871 85206971489966739793550807)
          ·
            refine ⟨127810457234950109690326211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85206971489966739793550807 127810457234950109690326211)
            ·
              refine ⟨191715685852425164535489317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127810457234950109690326211 191715685852425164535489317)
              ·
                refine ⟨35946691097329718350404247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191715685852425164535489317 35946691097329718350404247)
                ·
                  refine ⟨53920036645994577525606371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35946691097329718350404247 53920036645994577525606371)
                  ·
                    refine ⟨80880054968991866288409557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53920036645994577525606371 80880054968991866288409557)
                    ·
                      refine ⟨1895626288335746866134599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80880054968991866288409557 1895626288335746866134599)
                      ·
                        rfl

theorem cell23_3691719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3691719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691719 prefixEnd_3691719 := by exact prefixLift 3691719
  have htrace : WordTrace (prefixWord ++ tailWord_3691719) baseStart_3691719 baseEnd_3691719 := by
    simpa [prefixWord, tailWord_3691719, baseEnd_3691719] using wordTrace_append hprefix tailTrace_3691719
  have hstable : (prefixWord ++ tailWord_3691719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691719).length < 2 ^ (prefixWord ++ tailWord_3691719).sum := by decide
  have hdescent : baseEnd_3691719 < baseStart_3691719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691741 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3691741 : Nat := 118140960795 + 3691741 * 2 ^ 59
def prefixEnd_3691741 : Nat := 4983230072969 + 3 ^ 40 * 3691741 * 2
def baseEnd_3691741 : Nat := 1895637584910145780059499

theorem tailTrace_3691741 : CollatzResearch.WordTrace tailWord_3691741 prefixEnd_3691741 1895637584910145780059499 := by
  unfold tailWord_3691741
  simp only [CollatzResearch.WordTrace]
  refine ⟨134648856118460331011307077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89765904078973554007538051 134648856118460331011307077)
  ·
    refine ⟨25246660522211312064620077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134648856118460331011307077 25246660522211312064620077)
    ·
      refine ⟨9467497695829242024232529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25246660522211312064620077 9467497695829242024232529)
      ·
        refine ⟨7100623271871931518174397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467497695829242024232529 7100623271871931518174397)
        ·
          refine ⟨2662733726951974319315399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7100623271871931518174397 2662733726951974319315399)
          ·
            refine ⟨3994100590427961478973099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662733726951974319315399 3994100590427961478973099)
            ·
              refine ⟨5991150885641942218459649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994100590427961478973099 5991150885641942218459649)
              ·
                refine ⟨4493363164231456663844737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5991150885641942218459649 4493363164231456663844737)
                ·
                  refine ⟨3370022373173592497883553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493363164231456663844737 3370022373173592497883553)
                  ·
                    refine ⟨2527516779880194373412665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3370022373173592497883553 2527516779880194373412665)
                    ·
                      refine ⟨1895637584910145780059499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527516779880194373412665 1895637584910145780059499)
                      ·
                        rfl

theorem cell23_3691741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3691741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691741 prefixEnd_3691741 := by exact prefixLift 3691741
  have htrace : WordTrace (prefixWord ++ tailWord_3691741) baseStart_3691741 baseEnd_3691741 := by
    simpa [prefixWord, tailWord_3691741, baseEnd_3691741] using wordTrace_append hprefix tailTrace_3691741
  have hstable : (prefixWord ++ tailWord_3691741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691741).length < 2 ^ (prefixWord ++ tailWord_3691741).sum := by decide
  have hdescent : baseEnd_3691741 < baseStart_3691741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691763 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 2, 4, 2]
def baseStart_3691763 : Nat := 118140960795 + 3691763 * 2 ^ 59
def prefixEnd_3691763 : Nat := 4983230072969 + 3 ^ 40 * 3691763 * 2
def baseEnd_3691763 : Nat := 1895648881484544693984397

theorem tailTrace_3691763 : CollatzResearch.WordTrace tailWord_3691763 prefixEnd_3691763 1895648881484544693984397 := by
  unfold tailWord_3691763
  simp only [CollatzResearch.WordTrace]
  refine ⟨134649658524380628768607943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89766439016253752512405295 134649658524380628768607943)
  ·
    refine ⟨201974487786570943152911915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134649658524380628768607943 201974487786570943152911915)
    ·
      refine ⟨302961731679856414729367873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201974487786570943152911915 302961731679856414729367873)
      ·
        refine ⟨227221298759892311047025905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302961731679856414729367873 227221298759892311047025905)
        ·
          refine ⟨170415974069919233285269429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227221298759892311047025905 170415974069919233285269429)
          ·
            refine ⟨15976497569054928120494009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170415974069919233285269429 15976497569054928120494009)
            ·
              refine ⟨11982373176791196090370507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15976497569054928120494009 11982373176791196090370507)
              ·
                refine ⟨17973559765186794135555761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11982373176791196090370507 17973559765186794135555761)
                ·
                  refine ⟨13480169823890095601666821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17973559765186794135555761 13480169823890095601666821)
                  ·
                    refine ⟨2527531841979392925312529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13480169823890095601666821 2527531841979392925312529)
                    ·
                      refine ⟨1895648881484544693984397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527531841979392925312529 1895648881484544693984397)
                      ·
                        rfl

theorem cell23_3691763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4, 2].length) (baseStart_3691763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691763 prefixEnd_3691763 := by exact prefixLift 3691763
  have htrace : WordTrace (prefixWord ++ tailWord_3691763) baseStart_3691763 baseEnd_3691763 := by
    simpa [prefixWord, tailWord_3691763, baseEnd_3691763] using wordTrace_append hprefix tailTrace_3691763
  have hstable : (prefixWord ++ tailWord_3691763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691763).length < 2 ^ (prefixWord ++ tailWord_3691763).sum := by decide
  have hdescent : baseEnd_3691763 < baseStart_3691763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691807 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 3, 4]
def baseStart_3691807 : Nat := 118140960795 + 3691807 * 2 ^ 59
def prefixEnd_3691807 : Nat := 4983230072969 + 3 ^ 40 * 3691807 * 2
def baseEnd_3691807 : Nat := 631890491544447507278065

theorem tailTrace_3691807 : CollatzResearch.WordTrace tailWord_3691807 prefixEnd_3691807 631890491544447507278065 := by
  unfold tailWord_3691807
  simp only [CollatzResearch.WordTrace]
  refine ⟨134651263336221224283209675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89767508890814149522139783 134651263336221224283209675)
  ·
    refine ⟨201976895004331836424814513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134651263336221224283209675 201976895004331836424814513)
    ·
      refine ⟨151482671253248877318610885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201976895004331836424814513 151482671253248877318610885)
      ·
        refine ⟨28403000859984164497239541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151482671253248877318610885 28403000859984164497239541)
        ·
          refine ⟨2662781330623515421616207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28403000859984164497239541 2662781330623515421616207)
          ·
            refine ⟨3994171995935273132424311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662781330623515421616207 3994171995935273132424311)
            ·
              refine ⟨5991257993902909698636467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994171995935273132424311 5991257993902909698636467)
              ·
                refine ⟨8986886990854364547954701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991257993902909698636467 8986886990854364547954701)
                ·
                  refine ⟨3370082621570386705483013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8986886990854364547954701 3370082621570386705483013)
                  ·
                    refine ⟨631890491544447507278065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370082621570386705483013 631890491544447507278065)
                    ·
                      rfl

theorem cell23_3691807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 4].length) (baseStart_3691807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691807 prefixEnd_3691807 := by exact prefixLift 3691807
  have htrace : WordTrace (prefixWord ++ tailWord_3691807) baseStart_3691807 baseEnd_3691807 := by
    simpa [prefixWord, tailWord_3691807, baseEnd_3691807] using wordTrace_append hprefix tailTrace_3691807
  have hstable : (prefixWord ++ tailWord_3691807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691807).length < 2 ^ (prefixWord ++ tailWord_3691807).sum := by decide
  have hdescent : baseEnd_3691807 < baseStart_3691807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691823 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 6, 3, 2]
def baseStart_3691823 : Nat := 118140960795 + 3691823 * 2 ^ 59
def prefixEnd_3691823 : Nat := 4983230072969 + 3 ^ 40 * 3691823 * 2
def baseEnd_3691823 : Nat := 1895679690323814459234121

theorem tailTrace_3691823 : CollatzResearch.WordTrace tailWord_3691823 prefixEnd_3691823 1895679690323814459234121 := by
  unfold tailWord_3691823
  simp only [CollatzResearch.WordTrace]
  refine ⟨134651846904163259015792123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89767897936108839343861415 134651846904163259015792123)
  ·
    refine ⟨201977770356244888523688185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134651846904163259015792123 201977770356244888523688185)
    ·
      refine ⟨151483327767183666392766139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201977770356244888523688185 151483327767183666392766139)
      ·
        refine ⟨227224991650775499589149209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151483327767183666392766139 227224991650775499589149209)
        ·
          refine ⟨170418743738081624691861907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227224991650775499589149209 170418743738081624691861907)
          ·
            refine ⟨255628115607122437037792861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170418743738081624691861907 255628115607122437037792861)
            ·
              refine ⟨95860543352670913889172323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255628115607122437037792861 95860543352670913889172323)
              ·
                refine ⟨143790815029006370833758485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95860543352670913889172323 143790815029006370833758485)
                ·
                  refine ⟨6740194454484673632832429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143790815029006370833758485 6740194454484673632832429)
                  ·
                    refine ⟨2527572920431752612312161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6740194454484673632832429 2527572920431752612312161)
                    ·
                      refine ⟨1895679690323814459234121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527572920431752612312161 1895679690323814459234121)
                      ·
                        rfl

theorem cell23_3691823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3, 2].length) (baseStart_3691823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691823 prefixEnd_3691823 := by exact prefixLift 3691823
  have htrace : WordTrace (prefixWord ++ tailWord_3691823) baseStart_3691823 baseEnd_3691823 := by
    simpa [prefixWord, tailWord_3691823, baseEnd_3691823] using wordTrace_append hprefix tailTrace_3691823
  have hstable : (prefixWord ++ tailWord_3691823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691823).length < 2 ^ (prefixWord ++ tailWord_3691823).sum := by decide
  have hdescent : baseEnd_3691823 < baseStart_3691823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691840 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 2, 3, 2]
def baseStart_3691840 : Nat := 118140960795 + 3691840 * 2 ^ 59
def prefixEnd_3691840 : Nat := 4983230072969 + 3 ^ 40 * 3691840 * 2
def baseEnd_3691840 : Nat := 1895688419494940892721543

theorem tailTrace_3691840 : CollatzResearch.WordTrace tailWord_3691840 prefixEnd_3691840 1895688419494940892721543 := by
  unfold tailWord_3691840
  simp only [CollatzResearch.WordTrace]
  refine ⟨67326233472550835459580487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89768311296734447279440649 67326233472550835459580487)
  ·
    refine ⟨100989350208826253189370731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67326233472550835459580487 100989350208826253189370731)
    ·
      refine ⟨151484025313239379784056097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100989350208826253189370731 151484025313239379784056097)
      ·
        refine ⟨113613018984929534838042073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151484025313239379784056097 113613018984929534838042073)
        ·
          refine ⟨85209764238697151128531555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113613018984929534838042073 85209764238697151128531555)
          ·
            refine ⟨127814646358045726692797333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85209764238697151128531555 127814646358045726692797333)
            ·
              refine ⟨5991311548033393438724875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127814646358045726692797333 5991311548033393438724875)
              ·
                refine ⟨8986967322050090158087313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991311548033393438724875 8986967322050090158087313)
                ·
                  refine ⟨6740225491537567618565485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8986967322050090158087313 6740225491537567618565485)
                  ·
                    refine ⟨2527584559326587856962057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6740225491537567618565485 2527584559326587856962057)
                    ·
                      refine ⟨1895688419494940892721543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527584559326587856962057 1895688419494940892721543)
                      ·
                        rfl

theorem cell23_3691840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_3691840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691840 prefixEnd_3691840 := by exact prefixLift 3691840
  have htrace : WordTrace (prefixWord ++ tailWord_3691840) baseStart_3691840 baseEnd_3691840 := by
    simpa [prefixWord, tailWord_3691840, baseEnd_3691840] using wordTrace_append hprefix tailTrace_3691840
  have hstable : (prefixWord ++ tailWord_3691840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691840).length < 2 ^ (prefixWord ++ tailWord_3691840).sum := by decide
  have hdescent : baseEnd_3691840 < baseStart_3691840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691866 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_3691866 : Nat := 118140960795 + 3691866 * 2 ^ 59
def prefixEnd_3691866 : Nat := 4983230072969 + 3 ^ 40 * 3691866 * 2
def baseEnd_3691866 : Nat := 1895701769991957790996423

theorem tailTrace_3691866 : CollatzResearch.WordTrace tailWord_3691866 prefixEnd_3691866 1895701769991957790996423 := by
  unfold tailWord_3691866
  simp only [CollatzResearch.WordTrace]
  refine ⟨33663353810751869339901863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89768943495338318239738301 33663353810751869339901863)
  ·
    refine ⟨50495030716127804009852795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33663353810751869339901863 50495030716127804009852795)
    ·
      refine ⟨75742546074191706014779193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50495030716127804009852795 75742546074191706014779193)
      ·
        refine ⟨56806909555643779511084395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75742546074191706014779193 56806909555643779511084395)
        ·
          refine ⟨85210364333465669266626593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56806909555643779511084395 85210364333465669266626593)
          ·
            refine ⟨63907773250099251949969945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85210364333465669266626593 63907773250099251949969945)
            ·
              refine ⟨47930829937574438962477459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63907773250099251949969945 47930829937574438962477459)
              ·
                refine ⟨71896244906361658443716189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47930829937574438962477459 71896244906361658443716189)
                ·
                  refine ⟨26961091839885621916393571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71896244906361658443716189 26961091839885621916393571)
                  ·
                    refine ⟨40441637759828432874590357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26961091839885621916393571 40441637759828432874590357)
                    ·
                      refine ⟨1895701769991957790996423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40441637759828432874590357 1895701769991957790996423)
                      ·
                        rfl

theorem cell23_3691866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_3691866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691866 prefixEnd_3691866 := by exact prefixLift 3691866
  have htrace : WordTrace (prefixWord ++ tailWord_3691866) baseStart_3691866 baseEnd_3691866 := by
    simpa [prefixWord, tailWord_3691866, baseEnd_3691866] using wordTrace_append hprefix tailTrace_3691866
  have hstable : (prefixWord ++ tailWord_3691866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691866).length < 2 ^ (prefixWord ++ tailWord_3691866).sum := by decide
  have hdescent : baseEnd_3691866 < baseStart_3691866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691880 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 1, 6]
def baseStart_3691880 : Nat := 118140960795 + 3691880 * 2 ^ 59
def prefixEnd_3691880 : Nat := 4983230072969 + 3 ^ 40 * 3691880 * 2
def baseEnd_3691880 : Nat := 631902986240373578740453

theorem tailTrace_3691880 : CollatzResearch.WordTrace tailWord_3691880 prefixEnd_3691880 631902986240373578740453 := by
  unfold tailWord_3691880
  simp only [CollatzResearch.WordTrace]
  refine ⟨67326962932478378875308547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89769283909971171833744729 67326962932478378875308547)
  ·
    refine ⟨100990444398717568312962821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67326962932478378875308547 100990444398717568312962821)
    ·
      refine ⟨18935708324759544058680529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100990444398717568312962821 18935708324759544058680529)
      ·
        refine ⟨14201781243569658044010397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18935708324759544058680529 14201781243569658044010397)
        ·
          refine ⟨5325667966338621766503899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14201781243569658044010397 5325667966338621766503899)
          ·
            refine ⟨7988501949507932649755849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325667966338621766503899 7988501949507932649755849)
            ·
              refine ⟨5991376462130949487316887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7988501949507932649755849 5991376462130949487316887)
              ·
                refine ⟨8987064693196424230975331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991376462130949487316887 8987064693196424230975331)
                ·
                  refine ⟨13480597039794636346462997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987064693196424230975331 13480597039794636346462997)
                  ·
                    refine ⟨631902986240373578740453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13480597039794636346462997 631902986240373578740453)
                    ·
                      rfl

theorem cell23_3691880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_3691880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691880 prefixEnd_3691880 := by exact prefixLift 3691880
  have htrace : WordTrace (prefixWord ++ tailWord_3691880) baseStart_3691880 baseEnd_3691880 := by
    simpa [prefixWord, tailWord_3691880, baseEnd_3691880] using wordTrace_append hprefix tailTrace_3691880
  have hstable : (prefixWord ++ tailWord_3691880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691880).length < 2 ^ (prefixWord ++ tailWord_3691880).sum := by decide
  have hdescent : baseEnd_3691880 < baseStart_3691880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691890 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_3691890 : Nat := 118140960795 + 3691890 * 2 ^ 59
def prefixEnd_3691890 : Nat := 4983230072969 + 3 ^ 40 * 3691890 * 2
def baseEnd_3691890 : Nat := 1895714093527665697096313

theorem tailTrace_3691890 : CollatzResearch.WordTrace tailWord_3691890 prefixEnd_3691890 1895714093527665697096313 := by
  unfold tailWord_3691890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33663572648730132364620281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89769527063280352972320749 33663572648730132364620281)
  ·
    refine ⟨25247679486547599273465211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33663572648730132364620281 25247679486547599273465211)
    ·
      refine ⟨37871519229821398910197817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25247679486547599273465211 37871519229821398910197817)
      ·
        refine ⟨28403639422366049182648363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37871519229821398910197817 28403639422366049182648363)
        ·
          refine ⟨42605459133549073773972545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28403639422366049182648363 42605459133549073773972545)
          ·
            refine ⟨31954094350161805330479409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42605459133549073773972545 31954094350161805330479409)
            ·
              refine ⟨23965570762621353997859557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31954094350161805330479409 23965570762621353997859557)
              ·
                refine ⟨4493544517991503874598667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23965570762621353997859557 4493544517991503874598667)
                ·
                  refine ⟨6740316776987255811898001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493544517991503874598667 6740316776987255811898001)
                  ·
                    refine ⟨5055237582740441858923501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740316776987255811898001 5055237582740441858923501)
                    ·
                      refine ⟨1895714093527665697096313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5055237582740441858923501 1895714093527665697096313)
                      ·
                        rfl

theorem cell23_3691890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_3691890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691890 prefixEnd_3691890 := by exact prefixLift 3691890
  have htrace : WordTrace (prefixWord ++ tailWord_3691890) baseStart_3691890 baseEnd_3691890 := by
    simpa [prefixWord, tailWord_3691890, baseEnd_3691890] using wordTrace_append hprefix tailTrace_3691890
  have hstable : (prefixWord ++ tailWord_3691890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691890).length < 2 ^ (prefixWord ++ tailWord_3691890).sum := by decide
  have hdescent : baseEnd_3691890 < baseStart_3691890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691907 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 1, 2, 3]
def baseStart_3691907 : Nat := 118140960795 + 3691907 * 2 ^ 59
def prefixEnd_3691907 : Nat := 4983230072969 + 3 ^ 40 * 3691907 * 2
def baseEnd_3691907 : Nat := 1895722822698792130583735

theorem tailTrace_3691907 : CollatzResearch.WordTrace tailWord_3691907 prefixEnd_3691907 1895722822698792130583735 := by
  unfold tailWord_3691907
  simp only [CollatzResearch.WordTrace]
  refine ⟨134654910635858941361849975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89769940423905960907899983 134654910635858941361849975)
  ·
    refine ⟨201982365953788412042774963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134654910635858941361849975 201982365953788412042774963)
    ·
      refine ⟨302973548930682618064162445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201982365953788412042774963 302973548930682618064162445)
      ·
        refine ⟨113615080849005981774060917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302973548930682618064162445 113615080849005981774060917)
        ·
          refine ⟨10651413829594310791318211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113615080849005981774060917 10651413829594310791318211)
          ·
            refine ⟨15977120744391466186977317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651413829594310791318211 15977120744391466186977317)
            ·
              refine ⟨2995710139573399910058247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15977120744391466186977317 2995710139573399910058247)
              ·
                refine ⟨4493565209360099865087371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995710139573399910058247 4493565209360099865087371)
                ·
                  refine ⟨6740347814040149797631057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493565209360099865087371 6740347814040149797631057)
                  ·
                    refine ⟨5055260860530112348223293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740347814040149797631057 5055260860530112348223293)
                    ·
                      refine ⟨1895722822698792130583735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5055260860530112348223293 1895722822698792130583735)
                      ·
                        rfl

theorem cell23_3691907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_3691907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691907 prefixEnd_3691907 := by exact prefixLift 3691907
  have htrace : WordTrace (prefixWord ++ tailWord_3691907) baseStart_3691907 baseEnd_3691907 := by
    simpa [prefixWord, tailWord_3691907, baseEnd_3691907] using wordTrace_append hprefix tailTrace_3691907
  have hstable : (prefixWord ++ tailWord_3691907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691907).length < 2 ^ (prefixWord ++ tailWord_3691907).sum := by decide
  have hdescent : baseEnd_3691907 < baseStart_3691907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691934 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3691934 : Nat := 118140960795 + 3691934 * 2 ^ 59
def prefixEnd_3691934 : Nat := 4983230072969 + 3 ^ 40 * 3691934 * 2
def baseEnd_3691934 : Nat := 1895736686676463524946111

theorem tailTrace_3691934 : CollatzResearch.WordTrace tailWord_3691934 prefixEnd_3691934 1895736686676463524946111 := by
  unfold tailWord_3691934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831986925845140621635357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89770596937840749982055237 16831986925845140621635357)
  ·
    refine ⟨6311995097191927733113259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16831986925845140621635357 6311995097191927733113259)
    ·
      refine ⟨9467992645787891599669889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6311995097191927733113259 9467992645787891599669889)
      ·
        refine ⟨7100994484340918699752417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467992645787891599669889 7100994484340918699752417)
        ·
          refine ⟨5325745863255689024814313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7100994484340918699752417 5325745863255689024814313)
          ·
            refine ⟨3994309397441766768610735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325745863255689024814313 3994309397441766768610735)
            ·
              refine ⟨5991464096162650152916103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994309397441766768610735 5991464096162650152916103)
              ·
                refine ⟨8987196144243975229374155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991464096162650152916103 8987196144243975229374155)
                ·
                  refine ⟨13480794216365962844061233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987196144243975229374155 13480794216365962844061233)
                  ·
                    refine ⟨10110595662274472133045925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13480794216365962844061233 10110595662274472133045925)
                    ·
                      refine ⟨1895736686676463524946111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10110595662274472133045925 1895736686676463524946111)
                      ·
                        rfl

theorem cell23_3691934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3691934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691934 prefixEnd_3691934 := by exact prefixLift 3691934
  have htrace : WordTrace (prefixWord ++ tailWord_3691934) baseStart_3691934 baseEnd_3691934 := by
    simpa [prefixWord, tailWord_3691934, baseEnd_3691934] using wordTrace_append hprefix tailTrace_3691934
  have hstable : (prefixWord ++ tailWord_3691934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691934).length < 2 ^ (prefixWord ++ tailWord_3691934).sum := by decide
  have hdescent : baseEnd_3691934 < baseStart_3691934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691944 : List Nat := [2, 1, 6, 1, 3, 1, 2, 7]
def baseStart_3691944 : Nat := 118140960795 + 3691944 * 2 ^ 59
def prefixEnd_3691944 : Nat := 4983230072969 + 3 ^ 40 * 3691944 * 2
def baseEnd_3691944 : Nat := 70212660054926240215595

theorem tailTrace_3691944 : CollatzResearch.WordTrace tailWord_3691944 prefixEnd_3691944 70212660054926240215595 := by
  unfold tailWord_3691944
  simp only [CollatzResearch.WordTrace]
  refine ⟨67328130068362448340473443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89770840091149931120631257 67328130068362448340473443)
  ·
    refine ⟨100992195102543672510710165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67328130068362448340473443 100992195102543672510710165)
    ·
      refine ⟨4734009145431734648939539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100992195102543672510710165 4734009145431734648939539)
      ·
        refine ⟨7101013718147601973409309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734009145431734648939539 7101013718147601973409309)
        ·
          refine ⟨2662880144305350740028491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7101013718147601973409309 2662880144305350740028491)
          ·
            refine ⟨3994320216458026110042737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662880144305350740028491 3994320216458026110042737)
            ·
              refine ⟨2995740162343519582532053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3994320216458026110042737 2995740162343519582532053)
              ·
                refine ⟨70212660054926240215595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2995740162343519582532053 70212660054926240215595)
                ·
                  rfl

theorem cell23_3691944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 7].length) (baseStart_3691944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691944 prefixEnd_3691944 := by exact prefixLift 3691944
  have htrace : WordTrace (prefixWord ++ tailWord_3691944) baseStart_3691944 baseEnd_3691944 := by
    simpa [prefixWord, tailWord_3691944, baseEnd_3691944] using wordTrace_append hprefix tailTrace_3691944
  have hstable : (prefixWord ++ tailWord_3691944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691944).length < 2 ^ (prefixWord ++ tailWord_3691944).sum := by decide
  have hdescent : baseEnd_3691944 < baseStart_3691944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691960 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 1, 4, 2]
def baseStart_3691960 : Nat := 118140960795 + 3691960 * 2 ^ 59
def prefixEnd_3691960 : Nat := 4983230072969 + 3 ^ 40 * 3691960 * 2
def baseEnd_3691960 : Nat := 1895750037173480423220991

theorem tailTrace_3691960 : CollatzResearch.WordTrace tailWord_3691960 prefixEnd_3691960 1895750037173480423220991 := by
  unfold tailWord_3691960
  simp only [CollatzResearch.WordTrace]
  refine ⟨67328421852333465706764667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89771229136444620942352889 67328421852333465706764667)
  ·
    refine ⟨100992632778500198560147001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67328421852333465706764667 100992632778500198560147001)
    ·
      refine ⟨75744474583875148920110251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100992632778500198560147001 75744474583875148920110251)
      ·
        refine ⟨113616711875812723380165377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75744474583875148920110251 113616711875812723380165377)
        ·
          refine ⟨85212533906859542535124033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113616711875812723380165377 85212533906859542535124033)
          ·
            refine ⟨63909400430144656901343025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85212533906859542535124033 63909400430144656901343025)
            ·
              refine ⟨47932050322608492676007269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63909400430144656901343025 47932050322608492676007269)
              ·
                refine ⟨8987259435489092376751363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47932050322608492676007269 8987259435489092376751363)
                ·
                  refine ⟨13480889153233638565127045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987259435489092376751363 13480889153233638565127045)
                  ·
                    refine ⟨2527666716231307230961321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13480889153233638565127045 2527666716231307230961321)
                    ·
                      refine ⟨1895750037173480423220991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527666716231307230961321 1895750037173480423220991)
                      ·
                        rfl

theorem cell23_3691960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_3691960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691960 prefixEnd_3691960 := by exact prefixLift 3691960
  have htrace : WordTrace (prefixWord ++ tailWord_3691960) baseStart_3691960 baseEnd_3691960 := by
    simpa [prefixWord, tailWord_3691960, baseEnd_3691960] using wordTrace_append hprefix tailTrace_3691960
  have hstable : (prefixWord ++ tailWord_3691960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691960).length < 2 ^ (prefixWord ++ tailWord_3691960).sum := by decide
  have hdescent : baseEnd_3691960 < baseStart_3691960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691977 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 2, 2, 2]
def baseStart_3691977 : Nat := 118140960795 + 3691977 * 2 ^ 59
def prefixEnd_3691977 : Nat := 4983230072969 + 3 ^ 40 * 3691977 * 2
def baseEnd_3691977 : Nat := 1895758766344606856708413

theorem tailTrace_3691977 : CollatzResearch.WordTrace tailWord_3691977 prefixEnd_3691977 1895758766344606856708413 := by
  unfold tailWord_3691977
  simp only [CollatzResearch.WordTrace]
  refine ⟨134657463745605343316898185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89771642497070228877932123 134657463745605343316898185)
  ·
    refine ⟨100993097809204007487673639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134657463745605343316898185 100993097809204007487673639)
    ·
      refine ⟨151489646713806011231510459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100993097809204007487673639 151489646713806011231510459)
      ·
        refine ⟨227234470070709016847265689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151489646713806011231510459 227234470070709016847265689)
        ·
          refine ⟨170425852553031762635449267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227234470070709016847265689 170425852553031762635449267)
          ·
            refine ⟨255638778829547643953173901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170425852553031762635449267 255638778829547643953173901)
            ·
              refine ⟨95864542061080366482440213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255638778829547643953173901 95864542061080366482440213)
              ·
                refine ⟨4493650409113142178864385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95864542061080366482440213 4493650409113142178864385)
                ·
                  refine ⟨3370237806834856634148289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493650409113142178864385 3370237806834856634148289)
                  ·
                    refine ⟨2527678355126142475611217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3370237806834856634148289 2527678355126142475611217)
                    ·
                      refine ⟨1895758766344606856708413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527678355126142475611217 1895758766344606856708413)
                      ·
                        rfl

theorem cell23_3691977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 2, 2].length) (baseStart_3691977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691977 prefixEnd_3691977 := by exact prefixLift 3691977
  have htrace : WordTrace (prefixWord ++ tailWord_3691977) baseStart_3691977 baseEnd_3691977 := by
    simpa [prefixWord, tailWord_3691977, baseEnd_3691977] using wordTrace_append hprefix tailTrace_3691977
  have hstable : (prefixWord ++ tailWord_3691977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691977).length < 2 ^ (prefixWord ++ tailWord_3691977).sum := by decide
  have hdescent : baseEnd_3691977 < baseStart_3691977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691983 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 7]
def baseStart_3691983 : Nat := 118140960795 + 3691983 * 2 ^ 59
def prefixEnd_3691983 : Nat := 4983230072969 + 3 ^ 40 * 3691983 * 2
def baseEnd_3691983 : Nat := 210640205247614870359265

theorem tailTrace_3691983 : CollatzResearch.WordTrace tailWord_3691983 prefixEnd_3691983 210640205247614870359265 := by
  unfold tailWord_3691983
  simp only [CollatzResearch.WordTrace]
  refine ⟨134657682583583606341616603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89771788389055737561077735 134657682583583606341616603)
  ·
    refine ⟨201986523875375409512424905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134657682583583606341616603 201986523875375409512424905)
    ·
      refine ⟨151489892906531557134318679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201986523875375409512424905 151489892906531557134318679)
      ·
        refine ⟨227234839359797335701478019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151489892906531557134318679 227234839359797335701478019)
        ·
          refine ⟨340852259039696003552217029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227234839359797335701478019 340852259039696003552217029)
          ·
            refine ⟨63909798569943000666040693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340852259039696003552217029 63909798569943000666040693)
            ·
              refine ⟨5991543615932156312441315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63909798569943000666040693 5991543615932156312441315)
              ·
                refine ⟨8987315423898234468661973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5991543615932156312441315 8987315423898234468661973)
                ·
                  refine ⟨210640205247614870359265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8987315423898234468661973 210640205247614870359265)
                  ·
                    rfl

theorem cell23_3691983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 7].length) (baseStart_3691983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691983 prefixEnd_3691983 := by exact prefixLift 3691983
  have htrace : WordTrace (prefixWord ++ tailWord_3691983) baseStart_3691983 baseEnd_3691983 := by
    simpa [prefixWord, tailWord_3691983, baseEnd_3691983] using wordTrace_append hprefix tailTrace_3691983
  have hstable : (prefixWord ++ tailWord_3691983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691983).length < 2 ^ (prefixWord ++ tailWord_3691983).sum := by decide
  have hdescent : baseEnd_3691983 < baseStart_3691983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691988 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_3691988 : Nat := 118140960795 + 3691988 * 2 ^ 59
def prefixEnd_3691988 : Nat := 4983230072969 + 3 ^ 40 * 3691988 * 2
def baseEnd_3691988 : Nat := 1895764414631806313670863

theorem tailTrace_3691988 : CollatzResearch.WordTrace tailWord_3691988 prefixEnd_3691988 1895764414631806313670863 := by
  unfold tailWord_3691988
  simp only [CollatzResearch.WordTrace]
  refine ⟨67328932474282746097774309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89771909965710328130365745 67328932474282746097774309)
  ·
    refine ⟨12624174838928014893332683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67328932474282746097774309 12624174838928014893332683)
    ·
      refine ⟨18936262258392022339999025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12624174838928014893332683 18936262258392022339999025)
      ·
        refine ⟨14202196693794016754999269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18936262258392022339999025 14202196693794016754999269)
        ·
          refine ⟨2662911880086378141562363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14202196693794016754999269 2662911880086378141562363)
          ·
            refine ⟨3994367820129567212343545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662911880086378141562363 3994367820129567212343545)
            ·
              refine ⟨2995775865097175409257659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3994367820129567212343545 2995775865097175409257659)
              ·
                refine ⟨4493663797645763113886489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995775865097175409257659 4493663797645763113886489)
                ·
                  refine ⟨3370247848234322335414867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493663797645763113886489 3370247848234322335414867)
                  ·
                    refine ⟨5055371772351483503122301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3370247848234322335414867 5055371772351483503122301)
                    ·
                      refine ⟨1895764414631806313670863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5055371772351483503122301 1895764414631806313670863)
                      ·
                        rfl

theorem cell23_3691988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_3691988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691988 prefixEnd_3691988 := by exact prefixLift 3691988
  have htrace : WordTrace (prefixWord ++ tailWord_3691988) baseStart_3691988 baseEnd_3691988 := by
    simpa [prefixWord, tailWord_3691988, baseEnd_3691988] using wordTrace_append hprefix tailTrace_3691988
  have hstable : (prefixWord ++ tailWord_3691988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691988).length < 2 ^ (prefixWord ++ tailWord_3691988).sum := by decide
  have hdescent : baseEnd_3691988 < baseStart_3691988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691994 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2]
def baseStart_3691994 : Nat := 118140960795 + 3691994 * 2 ^ 59
def prefixEnd_3691994 : Nat := 4983230072969 + 3 ^ 40 * 3691994 * 2
def baseEnd_3691994 : Nat := 1895767495515733290195835

theorem tailTrace_3691994 : CollatzResearch.WordTrace tailWord_3691994 prefixEnd_3691994 1895767495515733290195835 := by
  unfold tailWord_3691994
  simp only [CollatzResearch.WordTrace]
  refine ⟨33664520946635938805066759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89772055857695836813511357 33664520946635938805066759)
  ·
    refine ⟨50496781419953908207600139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33664520946635938805066759 50496781419953908207600139)
    ·
      refine ⟨75745172129930862311400209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50496781419953908207600139 75745172129930862311400209)
      ·
        refine ⟨56808879097448146733550157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75745172129930862311400209 56808879097448146733550157)
        ·
          refine ⟨21303329661543055025081309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56808879097448146733550157 21303329661543055025081309)
          ·
            refine ⟨7988748623078645634405491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21303329661543055025081309 7988748623078645634405491)
            ·
              refine ⟨11983122934617968451608237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988748623078645634405491 11983122934617968451608237)
              ·
                refine ⟨4493671100481738169353089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11983122934617968451608237 4493671100481738169353089)
                ·
                  refine ⟨3370253325361303627014817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493671100481738169353089 3370253325361303627014817)
                  ·
                    refine ⟨2527689994020977720261113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3370253325361303627014817 2527689994020977720261113)
                    ·
                      refine ⟨1895767495515733290195835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527689994020977720261113 1895767495515733290195835)
                      ·
                        rfl

theorem cell23_3691994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_3691994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3691994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3691994 prefixEnd_3691994 := by exact prefixLift 3691994
  have htrace : WordTrace (prefixWord ++ tailWord_3691994) baseStart_3691994 baseEnd_3691994 := by
    simpa [prefixWord, tailWord_3691994, baseEnd_3691994] using wordTrace_append hprefix tailTrace_3691994
  have hstable : (prefixWord ++ tailWord_3691994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691994).length < 2 ^ (prefixWord ++ tailWord_3691994).sum := by decide
  have hdescent : baseEnd_3691994 < baseStart_3691994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692034 : List Nat := [3, 4, 1, 2, 1, 2, 1, 4, 5]
def baseStart_3692034 : Nat := 118140960795 + 3692034 * 2 ^ 59
def prefixEnd_3692034 : Nat := 4983230072969 + 3 ^ 40 * 3692034 * 2
def baseEnd_3692034 : Nat := 210643114971323681521739

theorem tailTrace_3692034 : CollatzResearch.WordTrace tailWord_3692034 prefixEnd_3692034 210643114971323681521739 := by
  unfold tailWord_3692034
  simp only [CollatzResearch.WordTrace]
  refine ⟨33664885676599710512930789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89773028470932561367815437 33664885676599710512930789)
  ·
    refine ⟨6312166064362445721174523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33664885676599710512930789 6312166064362445721174523)
    ·
      refine ⟨9468249096543668581761785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6312166064362445721174523 9468249096543668581761785)
      ·
        refine ⟨7101186822407751436321339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9468249096543668581761785 7101186822407751436321339)
        ·
          refine ⟨10651780233611627154482009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101186822407751436321339 10651780233611627154482009)
          ·
            refine ⟨7988835175208720365861507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10651780233611627154482009 7988835175208720365861507)
            ·
              refine ⟨11983252762813080548792261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988835175208720365861507 11983252762813080548792261)
              ·
                refine ⟨2246859893027452602898549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11983252762813080548792261 2246859893027452602898549)
                ·
                  refine ⟨210643114971323681521739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2246859893027452602898549 210643114971323681521739)
                  ·
                    rfl

theorem cell23_3692034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_3692034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692034 prefixEnd_3692034 := by exact prefixLift 3692034
  have htrace : WordTrace (prefixWord ++ tailWord_3692034) baseStart_3692034 baseEnd_3692034 := by
    simpa [prefixWord, tailWord_3692034, baseEnd_3692034] using wordTrace_append hprefix tailTrace_3692034
  have hstable : (prefixWord ++ tailWord_3692034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692034).length < 2 ^ (prefixWord ++ tailWord_3692034).sum := by decide
  have hdescent : baseEnd_3692034 < baseStart_3692034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692140 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_3692140 : Nat := 118140960795 + 3692140 * 2 ^ 59
def prefixEnd_3692140 : Nat := 4983230072969 + 3 ^ 40 * 3692140 * 2
def baseEnd_3692140 : Nat := 1895842463691289718970163

theorem tailTrace_3692140 : CollatzResearch.WordTrace tailWord_3692140 prefixEnd_3692140 1895842463691289718970163 := by
  unfold tailWord_3692140
  simp only [CollatzResearch.WordTrace]
  refine ⟨67331704422007411077540937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89775605896009881436721249 67331704422007411077540937)
  ·
    refine ⟨50498778316505558308155703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67331704422007411077540937 50498778316505558308155703)
    ·
      refine ⟨75748167474758337462233555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50498778316505558308155703 75748167474758337462233555)
      ·
        refine ⟨113622251212137506193350333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75748167474758337462233555 113622251212137506193350333)
        ·
          refine ⟨42608344204551564822506375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113622251212137506193350333 42608344204551564822506375)
          ·
            refine ⟨63912516306827347233759563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42608344204551564822506375 63912516306827347233759563)
            ·
              refine ⟨95868774460241020850639345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63912516306827347233759563 95868774460241020850639345)
              ·
                refine ⟨71901580845180765637979509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95868774460241020850639345 71901580845180765637979509)
                ·
                  refine ⟨6740773204235696778560579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71901580845180765637979509 6740773204235696778560579)
                  ·
                    refine ⟨10111159806353545167840869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6740773204235696778560579 10111159806353545167840869)
                    ·
                      refine ⟨1895842463691289718970163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10111159806353545167840869 1895842463691289718970163)
                      ·
                        rfl

theorem cell23_3692140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_3692140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692140 prefixEnd_3692140 := by exact prefixLift 3692140
  have htrace : WordTrace (prefixWord ++ tailWord_3692140) baseStart_3692140 baseEnd_3692140 := by
    simpa [prefixWord, tailWord_3692140, baseEnd_3692140] using wordTrace_append hprefix tailTrace_3692140
  have hstable : (prefixWord ++ tailWord_3692140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692140).length < 2 ^ (prefixWord ++ tailWord_3692140).sum := by decide
  have hdescent : baseEnd_3692140 < baseStart_3692140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692144 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 2, 3, 2]
def baseStart_3692144 : Nat := 118140960795 + 3692144 * 2 ^ 59
def prefixEnd_3692144 : Nat := 4983230072969 + 3 ^ 40 * 3692144 * 2
def baseEnd_3692144 : Nat := 1895844517613907703320145

theorem tailTrace_3692144 : CollatzResearch.WordTrace tailWord_3692144 prefixEnd_3692144 1895844517613907703320145 := by
  unfold tailWord_3692144
  simp only [CollatzResearch.WordTrace]
  refine ⟨67331777368000165419113743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89775703157333553892151657 67331777368000165419113743)
  ·
    refine ⟨100997666052000248128670615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67331777368000165419113743 100997666052000248128670615)
    ·
      refine ⟨151496499078000372193005923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100997666052000248128670615 151496499078000372193005923)
      ·
        refine ⟨227244748617000558289508885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151496499078000372193005923 227244748617000558289508885)
        ·
          refine ⟨10652097591421901169820729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227244748617000558289508885 10652097591421901169820729)
          ·
            refine ⟨7989073193566425877365547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10652097591421901169820729 7989073193566425877365547)
            ·
              refine ⟨11983609790349638816048321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989073193566425877365547 11983609790349638816048321)
              ·
                refine ⟨8987707342762229112036241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11983609790349638816048321 8987707342762229112036241)
                ·
                  refine ⟨6740780507071671834027181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8987707342762229112036241 6740780507071671834027181)
                  ·
                    refine ⟨2527792690151876937760193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6740780507071671834027181 2527792690151876937760193)
                    ·
                      refine ⟨1895844517613907703320145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527792690151876937760193 1895844517613907703320145)
                      ·
                        rfl

theorem cell23_3692144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 3, 2].length) (baseStart_3692144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692144 prefixEnd_3692144 := by exact prefixLift 3692144
  have htrace : WordTrace (prefixWord ++ tailWord_3692144) baseStart_3692144 baseEnd_3692144 := by
    simpa [prefixWord, tailWord_3692144, baseEnd_3692144] using wordTrace_append hprefix tailTrace_3692144
  have hstable : (prefixWord ++ tailWord_3692144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692144).length < 2 ^ (prefixWord ++ tailWord_3692144).sum := by decide
  have hdescent : baseEnd_3692144 < baseStart_3692144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692160 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_3692160 : Nat := 118140960795 + 3692160 * 2 ^ 59
def prefixEnd_3692160 : Nat := 4983230072969 + 3 ^ 40 * 3692160 * 2
def baseEnd_3692160 : Nat := 1895852733304379640720071

theorem tailTrace_3692160 : CollatzResearch.WordTrace tailWord_3692160 prefixEnd_3692160 1895852733304379640720071 := by
  unfold tailWord_3692160
  simp only [CollatzResearch.WordTrace]
  refine ⟨67332069151971182785404967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89776092202628243713873289 67332069151971182785404967)
  ·
    refine ⟨100998103727956774178107451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67332069151971182785404967 100998103727956774178107451)
    ·
      refine ⟨151497155591935161267161177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100998103727956774178107451 151497155591935161267161177)
      ·
        refine ⟨113622866693951370950370883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151497155591935161267161177 113622866693951370950370883)
        ·
          refine ⟨170434300040927056425556325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113622866693951370950370883 170434300040927056425556325)
          ·
            refine ⟨31956431257673823079791811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170434300040927056425556325 31956431257673823079791811)
            ·
              refine ⟨47934646886510734619687717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31956431257673823079791811 47934646886510734619687717)
              ·
                refine ⟨8987746291220762741191447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47934646886510734619687717 8987746291220762741191447)
                ·
                  refine ⟨13481619436831144111787171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8987746291220762741191447 13481619436831144111787171)
                  ·
                    refine ⟨20222429155246716167680757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13481619436831144111787171 20222429155246716167680757)
                    ·
                      refine ⟨1895852733304379640720071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20222429155246716167680757 1895852733304379640720071)
                      ·
                        rfl

theorem cell23_3692160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_3692160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692160 prefixEnd_3692160 := by exact prefixLift 3692160
  have htrace : WordTrace (prefixWord ++ tailWord_3692160) baseStart_3692160 baseEnd_3692160 := by
    simpa [prefixWord, tailWord_3692160, baseEnd_3692160] using wordTrace_append hprefix tailTrace_3692160
  have hstable : (prefixWord ++ tailWord_3692160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692160).length < 2 ^ (prefixWord ++ tailWord_3692160).sum := by decide
  have hdescent : baseEnd_3692160 < baseStart_3692160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692174 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3692174 : Nat := 118140960795 + 3692174 * 2 ^ 59
def prefixEnd_3692174 : Nat := 4983230072969 + 3 ^ 40 * 3692174 * 2
def baseEnd_3692174 : Nat := 1895859922033542585945007

theorem tailTrace_3692174 : CollatzResearch.WordTrace tailWord_3692174 prefixEnd_3692174 1895859922033542585945007 := by
  unfold tailWord_3692174
  simp only [CollatzResearch.WordTrace]
  refine ⟨16833081115736455745227447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89776432617261097307879717 16833081115736455745227447)
  ·
    refine ⟨25249621673604683617841171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16833081115736455745227447 25249621673604683617841171)
    ·
      refine ⟨37874432510407025426761757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25249621673604683617841171 37874432510407025426761757)
      ·
        refine ⟨14202912191402634535035659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37874432510407025426761757 14202912191402634535035659)
        ·
          refine ⟨21304368287103951802553489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14202912191402634535035659 21304368287103951802553489)
          ·
            refine ⟨15978276215327963851915117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21304368287103951802553489 15978276215327963851915117)
            ·
              refine ⟨5991853580747986444468169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15978276215327963851915117 5991853580747986444468169)
              ·
                refine ⟨4493890185560989833351127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5991853580747986444468169 4493890185560989833351127)
                ·
                  refine ⟨6740835278341484750026691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493890185560989833351127 6740835278341484750026691)
                  ·
                    refine ⟨10111252917512227125040037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6740835278341484750026691 10111252917512227125040037)
                    ·
                      refine ⟨1895859922033542585945007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10111252917512227125040037 1895859922033542585945007)
                      ·
                        rfl

theorem cell23_3692174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3692174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692174 prefixEnd_3692174 := by exact prefixLift 3692174
  have htrace : WordTrace (prefixWord ++ tailWord_3692174) baseStart_3692174 baseEnd_3692174 := by
    simpa [prefixWord, tailWord_3692174, baseEnd_3692174] using wordTrace_append hprefix tailTrace_3692174
  have hstable : (prefixWord ++ tailWord_3692174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692174).length < 2 ^ (prefixWord ++ tailWord_3692174).sum := by decide
  have hdescent : baseEnd_3692174 < baseStart_3692174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692177 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_3692177 : Nat := 118140960795 + 3692177 * 2 ^ 59
def prefixEnd_3692177 : Nat := 4983230072969 + 3 ^ 40 * 3692177 * 2
def baseEnd_3692177 : Nat := 1895861462475506074207493

theorem tailTrace_3692177 : CollatzResearch.WordTrace tailWord_3692177 prefixEnd_3692177 1895861462475506074207493 := by
  unfold tailWord_3692177
  simp only [CollatzResearch.WordTrace]
  refine ⟨134664758344880777474178785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89776505563253851649452523 134664758344880777474178785)
  ·
    refine ⟨100998568758660583105634089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134664758344880777474178785 100998568758660583105634089)
    ·
      refine ⟨75748926568995437329225567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100998568758660583105634089 75748926568995437329225567)
      ·
        refine ⟨113623389853493155993838351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75748926568995437329225567 113623389853493155993838351)
        ·
          refine ⟨170435084780239733990757527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113623389853493155993838351 170435084780239733990757527)
          ·
            refine ⟨255652627170359600986136291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170435084780239733990757527 255652627170359600986136291)
            ·
              refine ⟨383478940755539401479204437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255652627170359600986136291 383478940755539401479204437)
              ·
                refine ⟨4493893836978977361084427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 383478940755539401479204437 4493893836978977361084427)
                ·
                  refine ⟨6740840755468466041626641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493893836978977361084427 6740840755468466041626641)
                  ·
                    refine ⟨5055630566601349531219981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6740840755468466041626641 5055630566601349531219981)
                    ·
                      refine ⟨1895861462475506074207493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5055630566601349531219981 1895861462475506074207493)
                      ·
                        rfl

theorem cell23_3692177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_3692177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692177 prefixEnd_3692177 := by exact prefixLift 3692177
  have htrace : WordTrace (prefixWord ++ tailWord_3692177) baseStart_3692177 baseEnd_3692177 := by
    simpa [prefixWord, tailWord_3692177, baseEnd_3692177] using wordTrace_append hprefix tailTrace_3692177
  have hstable : (prefixWord ++ tailWord_3692177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692177).length < 2 ^ (prefixWord ++ tailWord_3692177).sum := by decide
  have hdescent : baseEnd_3692177 < baseStart_3692177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692208 : List Nat := [2, 1, 1, 1, 2, 1, 8, 2, 1, 2, 2]
def baseStart_3692208 : Nat := 118140960795 + 3692208 * 2 ^ 59
def prefixEnd_3692208 : Nat := 4983230072969 + 3 ^ 40 * 3692208 * 2
def baseEnd_3692208 : Nat := 1895877380375795452919851

theorem tailTrace_3692208 : CollatzResearch.WordTrace tailWord_3692208 prefixEnd_3692208 1895877380375795452919851 := by
  unfold tailWord_3692208
  simp only [CollatzResearch.WordTrace]
  refine ⟨67332944503884234884278639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89777259338512313179038185 67332944503884234884278639)
  ·
    refine ⟨100999416755826352326417959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67332944503884234884278639 100999416755826352326417959)
    ·
      refine ⟨151499125133739528489626939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100999416755826352326417959 151499125133739528489626939)
      ·
        refine ⟨227248687700609292734440409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151499125133739528489626939 227248687700609292734440409)
        ·
          refine ⟨170436515775456969550830307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227248687700609292734440409 170436515775456969550830307)
          ·
            refine ⟨255654773663185454326245461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170436515775456969550830307 255654773663185454326245461)
            ·
              refine ⟨2995954378865454542885689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 255654773663185454326245461 2995954378865454542885689)
              ·
                refine ⟨2246965784149090907164267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2995954378865454542885689 2246965784149090907164267)
                ·
                  refine ⟨3370448676223636360746401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246965784149090907164267 3370448676223636360746401)
                  ·
                    refine ⟨2527836507167727270559801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3370448676223636360746401 2527836507167727270559801)
                    ·
                      refine ⟨1895877380375795452919851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2527836507167727270559801 1895877380375795452919851)
                      ·
                        rfl

theorem cell23_3692208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 2, 2].length) (baseStart_3692208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692208 prefixEnd_3692208 := by exact prefixLift 3692208
  have htrace : WordTrace (prefixWord ++ tailWord_3692208) baseStart_3692208 baseEnd_3692208 := by
    simpa [prefixWord, tailWord_3692208, baseEnd_3692208] using wordTrace_append hprefix tailTrace_3692208
  have hstable : (prefixWord ++ tailWord_3692208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692208).length < 2 ^ (prefixWord ++ tailWord_3692208).sum := by decide
  have hdescent : baseEnd_3692208 < baseStart_3692208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692210 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_3692210 : Nat := 118140960795 + 3692210 * 2 ^ 59
def prefixEnd_3692210 : Nat := 4983230072969 + 3 ^ 40 * 3692210 * 2
def baseEnd_3692210 : Nat := 631959469112368148364947

theorem tailTrace_3692210 : CollatzResearch.WordTrace tailWord_3692210 prefixEnd_3692210 631959469112368148364947 := by
  unfold tailWord_3692210
  simp only [CollatzResearch.WordTrace]
  refine ⟨33666490488440306027532521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89777307969174149406753389 33666490488440306027532521)
  ·
    refine ⟨25249867866330229520649391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33666490488440306027532521 25249867866330229520649391)
    ·
      refine ⟨37874801799495344280974087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25249867866330229520649391 37874801799495344280974087)
      ·
        refine ⟨56812202699243016421461131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37874801799495344280974087 56812202699243016421461131)
        ·
          refine ⟨85218304048864524632191697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56812202699243016421461131 85218304048864524632191697)
          ·
            refine ⟨63913728036648393474143773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85218304048864524632191697 63913728036648393474143773)
            ·
              refine ⟨23967648013743147552803915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63913728036648393474143773 23967648013743147552803915)
              ·
                refine ⟨35951472020614721329205873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23967648013743147552803915 35951472020614721329205873)
                ·
                  refine ⟨26963604015461040996904405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35951472020614721329205873 26963604015461040996904405)
                  ·
                    refine ⟨631959469112368148364947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26963604015461040996904405 631959469112368148364947)
                    ·
                      rfl

theorem cell23_3692210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_3692210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692210 prefixEnd_3692210 := by exact prefixLift 3692210
  have htrace : WordTrace (prefixWord ++ tailWord_3692210) baseStart_3692210 baseEnd_3692210 := by
    simpa [prefixWord, tailWord_3692210, baseEnd_3692210] using wordTrace_append hprefix tailTrace_3692210
  have hstable : (prefixWord ++ tailWord_3692210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692210).length < 2 ^ (prefixWord ++ tailWord_3692210).sum := by decide
  have hdescent : baseEnd_3692210 < baseStart_3692210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692214 : List Nat := [5, 1, 3, 1, 1, 1, 3, 8]
def baseStart_3692214 : Nat := 118140960795 + 3692214 * 2 ^ 59
def prefixEnd_3692214 : Nat := 4983230072969 + 3 ^ 40 * 3692214 * 2
def baseEnd_3692214 : Nat := 70217794861471201090549

theorem tailTrace_3692214 : CollatzResearch.WordTrace tailWord_3692214 prefixEnd_3692214 70217794861471201090549 := by
  unfold tailWord_3692214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416631740359170799579731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89777405230497821862183797 8416631740359170799579731)
  ·
    refine ⟨12624947610538756199369597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8416631740359170799579731 12624947610538756199369597)
    ·
      refine ⟨4734355353952033574763599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12624947610538756199369597 4734355353952033574763599)
      ·
        refine ⟨7101533030928050362145399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734355353952033574763599 7101533030928050362145399)
        ·
          refine ⟨10652299546392075543218099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101533030928050362145399 10652299546392075543218099)
          ·
            refine ⟨15978449319588113314827149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10652299546392075543218099 15978449319588113314827149)
            ·
              refine ⟨5991918494845542493060181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15978449319588113314827149 5991918494845542493060181)
              ·
                refine ⟨70217794861471201090549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5991918494845542493060181 70217794861471201090549)
                ·
                  rfl

theorem cell23_3692214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_3692214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692214 prefixEnd_3692214 := by exact prefixLift 3692214
  have htrace : WordTrace (prefixWord ++ tailWord_3692214) baseStart_3692214 baseEnd_3692214 := by
    simpa [prefixWord, tailWord_3692214, baseEnd_3692214] using wordTrace_append hprefix tailTrace_3692214
  have hstable : (prefixWord ++ tailWord_3692214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692214).length < 2 ^ (prefixWord ++ tailWord_3692214).sum := by decide
  have hdescent : baseEnd_3692214 < baseStart_3692214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692224 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 2, 1, 3]
def baseStart_3692224 : Nat := 118140960795 + 3692224 * 2 ^ 59
def prefixEnd_3692224 : Nat := 4983230072969 + 3 ^ 40 * 3692224 * 2
def baseEnd_3692224 : Nat := 1895885596066267390319777

theorem tailTrace_3692224 : CollatzResearch.WordTrace tailWord_3692224 prefixEnd_3692224 1895885596066267390319777 := by
  unfold tailWord_3692224
  simp only [CollatzResearch.WordTrace]
  refine ⟨67333236287855252250569863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89777648383807003000759817 67333236287855252250569863)
  ·
    refine ⟨100999854431782878375854795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67333236287855252250569863 100999854431782878375854795)
    ·
      refine ⟨151499781647674317563782193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100999854431782878375854795 151499781647674317563782193)
      ·
        refine ⟨113624836235755738172836645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151499781647674317563782193 113624836235755738172836645)
        ·
          refine ⟨21304656794204200907406871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113624836235755738172836645 21304656794204200907406871)
          ·
            refine ⟨31956985191306301361110307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21304656794204200907406871 31956985191306301361110307)
            ·
              refine ⟨47935477786959452041665461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31956985191306301361110307 47935477786959452041665461)
              ·
                refine ⟨4493951042527448628906137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47935477786959452041665461 4493951042527448628906137)
                ·
                  refine ⟨3370463281895586471679603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493951042527448628906137 3370463281895586471679603)
                  ·
                    refine ⟨5055694922843379707519405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3370463281895586471679603 5055694922843379707519405)
                    ·
                      refine ⟨1895885596066267390319777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5055694922843379707519405 1895885596066267390319777)
                      ·
                        rfl

theorem cell23_3692224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_3692224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692224 prefixEnd_3692224 := by exact prefixLift 3692224
  have htrace : WordTrace (prefixWord ++ tailWord_3692224) baseStart_3692224 baseEnd_3692224 := by
    simpa [prefixWord, tailWord_3692224, baseEnd_3692224] using wordTrace_append hprefix tailTrace_3692224
  have hstable : (prefixWord ++ tailWord_3692224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692224).length < 2 ^ (prefixWord ++ tailWord_3692224).sum := by decide
  have hdescent : baseEnd_3692224 < baseStart_3692224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692321 : List Nat := [1, 2, 3, 2, 1, 4, 3, 2, 5]
def baseStart_3692321 : Nat := 118140960795 + 3692321 * 2 ^ 59
def prefixEnd_3692321 : Nat := 4983230072969 + 3 ^ 40 * 3692321 * 2
def baseEnd_3692321 : Nat := 210659489298861501200759

theorem tailTrace_3692321 : CollatzResearch.WordTrace tailWord_3692321 prefixEnd_3692321 210659489298861501200759 := by
  unfold tailWord_3692321
  simp only [CollatzResearch.WordTrace]
  refine ⟨134670010456359090067420817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89780006970906060044947211 134670010456359090067420817)
  ·
    refine ⟨101002507842269317550565613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134670010456359090067420817 101002507842269317550565613)
    ·
      refine ⟨37875940440850994081462105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101002507842269317550565613 37875940440850994081462105)
      ·
        refine ⟨28406955330638245561096579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37875940440850994081462105 28406955330638245561096579)
        ·
          refine ⟨42610432995957368341644869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28406955330638245561096579 42610432995957368341644869)
          ·
            refine ⟨7989456186742006564058413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42610432995957368341644869 7989456186742006564058413)
            ·
              refine ⟨2996046070028252461521905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7989456186742006564058413 2996046070028252461521905)
              ·
                refine ⟨2247034552521189346141429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2996046070028252461521905 2247034552521189346141429)
                ·
                  refine ⟨210659489298861501200759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2247034552521189346141429 210659489298861501200759)
                  ·
                    rfl

theorem cell23_3692321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 5].length) (baseStart_3692321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692321 prefixEnd_3692321 := by exact prefixLift 3692321
  have htrace : WordTrace (prefixWord ++ tailWord_3692321) baseStart_3692321 baseEnd_3692321 := by
    simpa [prefixWord, tailWord_3692321, baseEnd_3692321] using wordTrace_append hprefix tailTrace_3692321
  have hstable : (prefixWord ++ tailWord_3692321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692321).length < 2 ^ (prefixWord ++ tailWord_3692321).sum := by decide
  have hdescent : baseEnd_3692321 < baseStart_3692321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692467 : List Nat := [1, 1, 1, 2, 3, 1, 5, 9]
def baseStart_3692467 : Nat := 118140960795 + 3692467 * 2 ^ 59
def prefixEnd_3692467 : Nat := 4983230072969 + 3 ^ 40 * 3692467 * 2
def baseEnd_3692467 : Nat := 70222606365381849614117

theorem tailTrace_3692467 : CollatzResearch.WordTrace tailWord_3692467 prefixEnd_3692467 70222606365381849614117 := by
  unfold tailWord_3692467
  simp only [CollatzResearch.WordTrace]
  refine ⟨134675335513830157002235655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89783557009220104668157103 134675335513830157002235655)
  ·
    refine ⟨202013003270745235503353483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134675335513830157002235655 202013003270745235503353483)
    ·
      refine ⟨303019504906117853255030225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202013003270745235503353483 303019504906117853255030225)
      ·
        refine ⟨227264628679588389941272669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303019504906117853255030225 227264628679588389941272669)
        ·
          refine ⟨85224235754845646227977251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227264628679588389941272669 85224235754845646227977251)
          ·
            refine ⟨127836353632268469341965877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85224235754845646227977251 127836353632268469341965877)
            ·
              refine ⟨11984658153025169000809301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127836353632268469341965877 11984658153025169000809301)
              ·
                refine ⟨70222606365381849614117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11984658153025169000809301 70222606365381849614117)
                ·
                  rfl

theorem cell23_3692467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 9].length) (baseStart_3692467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692467 prefixEnd_3692467 := by exact prefixLift 3692467
  have htrace : WordTrace (prefixWord ++ tailWord_3692467) baseStart_3692467 baseEnd_3692467 := by
    simpa [prefixWord, tailWord_3692467, baseEnd_3692467] using wordTrace_append hprefix tailTrace_3692467
  have hstable : (prefixWord ++ tailWord_3692467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692467).length < 2 ^ (prefixWord ++ tailWord_3692467).sum := by decide
  have hdescent : baseEnd_3692467 < baseStart_3692467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692505 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 2, 4]
def baseStart_3692505 : Nat := 118140960795 + 3692505 * 2 ^ 59
def prefixEnd_3692505 : Nat := 4983230072969 + 3 ^ 40 * 3692505 * 2
def baseEnd_3692505 : Nat := 632009961376726930301995

theorem tailTrace_3692505 : CollatzResearch.WordTrace tailWord_3692505 prefixEnd_3692505 632009961376726930301995 := by
  unfold tailWord_3692505
  simp only [CollatzResearch.WordTrace]
  refine ⟨134676721487692489492118969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89784480991794992994745979 134676721487692489492118969)
  ·
    refine ⟨101007541115769367119089227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134676721487692489492118969 101007541115769367119089227)
    ·
      refine ⟨151511311673654050678633841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101007541115769367119089227 151511311673654050678633841)
      ·
        refine ⟨113633483755240538008975381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151511311673654050678633841 113633483755240538008975381)
        ·
          refine ⟨5326569551026900219170721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113633483755240538008975381 5326569551026900219170721)
          ·
            refine ⟨3994927163270175164378041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5326569551026900219170721 3994927163270175164378041)
            ·
              refine ⟨2996195372452631373283531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3994927163270175164378041 2996195372452631373283531)
              ·
                refine ⟨4494293058678947059925297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996195372452631373283531 4494293058678947059925297)
                ·
                  refine ⟨3370719794009210294943973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4494293058678947059925297 3370719794009210294943973)
                  ·
                    refine ⟨632009961376726930301995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370719794009210294943973 632009961376726930301995)
                    ·
                      rfl

theorem cell23_3692505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 4].length) (baseStart_3692505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692505 prefixEnd_3692505 := by exact prefixLift 3692505
  have htrace : WordTrace (prefixWord ++ tailWord_3692505) baseStart_3692505 baseEnd_3692505 := by
    simpa [prefixWord, tailWord_3692505, baseEnd_3692505] using wordTrace_append hprefix tailTrace_3692505
  have hstable : (prefixWord ++ tailWord_3692505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692505).length < 2 ^ (prefixWord ++ tailWord_3692505).sum := by decide
  have hdescent : baseEnd_3692505 < baseStart_3692505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692568 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 1, 4, 2]
def baseStart_3692568 : Nat := 118140960795 + 3692568 * 2 ^ 59
def prefixEnd_3692568 : Nat := 4983230072969 + 3 ^ 40 * 3692568 * 2
def baseEnd_3692568 : Nat := 1896062233411414044418195

theorem tailTrace_3692568 : CollatzResearch.WordTrace tailWord_3692568 prefixEnd_3692568 1896062233411414044418195 := by
  unfold tailWord_3692568
  simp only [CollatzResearch.WordTrace]
  refine ⟨67339509643232125625831179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89786012857642834167774905 67339509643232125625831179)
  ·
    refine ⟨101009264464848188438746769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67339509643232125625831179 101009264464848188438746769)
    ·
      refine ⟨75756948348636141329060077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101009264464848188438746769 75756948348636141329060077)
      ·
        refine ⟨28408855630738552998397529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75756948348636141329060077 28408855630738552998397529)
        ·
          refine ⟨21306641723053914748798147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28408855630738552998397529 21306641723053914748798147)
          ·
            refine ⟨31959962584580872123197221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21306641723053914748798147 31959962584580872123197221)
            ·
              refine ⟨5992492984608913523099479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31959962584580872123197221 5992492984608913523099479)
              ·
                refine ⟨8988739476913370284649219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992492984608913523099479 8988739476913370284649219)
                ·
                  refine ⟨13483109215370055426973829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8988739476913370284649219 13483109215370055426973829)
                  ·
                    refine ⟨2528082977881885392557593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13483109215370055426973829 2528082977881885392557593)
                    ·
                      refine ⟨1896062233411414044418195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528082977881885392557593 1896062233411414044418195)
                      ·
                        rfl

theorem cell23_3692568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_3692568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692568 prefixEnd_3692568 := by exact prefixLift 3692568
  have htrace : WordTrace (prefixWord ++ tailWord_3692568) baseStart_3692568 baseEnd_3692568 := by
    simpa [prefixWord, tailWord_3692568, baseEnd_3692568] using wordTrace_append hprefix tailTrace_3692568
  have hstable : (prefixWord ++ tailWord_3692568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692568).length < 2 ^ (prefixWord ++ tailWord_3692568).sum := by decide
  have hdescent : baseEnd_3692568 < baseStart_3692568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692611 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 2, 5, 2]
def baseStart_3692611 : Nat := 118140960795 + 3692611 * 2 ^ 59
def prefixEnd_3692611 : Nat := 4983230072969 + 3 ^ 40 * 3692611 * 2
def baseEnd_3692611 : Nat := 1896084313079557376180497

theorem tailTrace_3692611 : CollatzResearch.WordTrace tailWord_3692611 prefixEnd_3692611 1896084313079557376180497 := by
  unfold tailWord_3692611
  simp only [CollatzResearch.WordTrace]
  refine ⟨134680587625308469595477687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89787058416872313063651791 134680587625308469595477687)
  ·
    refine ⟨202020881437962704393216531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134680587625308469595477687 202020881437962704393216531)
    ·
      refine ⟨303031322156944056589824797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202020881437962704393216531 303031322156944056589824797)
      ·
        refine ⟨113636745808854021221184299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303031322156944056589824797 113636745808854021221184299)
        ·
          refine ⟨170455118713281031831776449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113636745808854021221184299 170455118713281031831776449)
          ·
            refine ⟨127841339034960773873832337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170455118713281031831776449 127841339034960773873832337)
            ·
              refine ⟨95881004276220580405374253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127841339034960773873832337 95881004276220580405374253)
              ·
                refine ⟨35955376603582717652015345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95881004276220580405374253 35955376603582717652015345)
                ·
                  refine ⟨26966532452687038239011509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35955376603582717652015345 26966532452687038239011509)
                  ·
                    refine ⟨2528112417439409834907329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26966532452687038239011509 2528112417439409834907329)
                    ·
                      refine ⟨1896084313079557376180497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528112417439409834907329 1896084313079557376180497)
                      ·
                        rfl

theorem cell23_3692611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_3692611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692611 prefixEnd_3692611 := by exact prefixLift 3692611
  have htrace : WordTrace (prefixWord ++ tailWord_3692611) baseStart_3692611 baseEnd_3692611 := by
    simpa [prefixWord, tailWord_3692611, baseEnd_3692611] using wordTrace_append hprefix tailTrace_3692611
  have hstable : (prefixWord ++ tailWord_3692611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692611).length < 2 ^ (prefixWord ++ tailWord_3692611).sum := by decide
  have hdescent : baseEnd_3692611 < baseStart_3692611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692621 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3692621 : Nat := 118140960795 + 3692621 * 2 ^ 59
def prefixEnd_3692621 : Nat := 4983230072969 + 3 ^ 40 * 3692621 * 2
def baseEnd_3692621 : Nat := 632029815962034112351817

theorem tailTrace_3692621 : CollatzResearch.WordTrace tailWord_3692621 prefixEnd_3692621 632029815962034112351817 := by
  unfold tailWord_3692621
  simp only [CollatzResearch.WordTrace]
  refine ⟨134680952355272241303341717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89787301570181494202227811 134680952355272241303341717)
  ·
    refine ⟨6313169641653386311094143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134680952355272241303341717 6313169641653386311094143)
    ·
      refine ⟨9469754462480079466641215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6313169641653386311094143 9469754462480079466641215)
      ·
        refine ⟨14204631693720119199961823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9469754462480079466641215 14204631693720119199961823)
        ·
          refine ⟨21306947540580178799942735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14204631693720119199961823 21306947540580178799942735)
          ·
            refine ⟨31960421310870268199914103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21306947540580178799942735 31960421310870268199914103)
            ·
              refine ⟨47940631966305402299871155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31960421310870268199914103 47940631966305402299871155)
              ·
                refine ⟨71910947949458103449806733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47940631966305402299871155 71910947949458103449806733)
                ·
                  refine ⟨26966605481046788793677525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71910947949458103449806733 26966605481046788793677525)
                  ·
                    refine ⟨632029815962034112351817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26966605481046788793677525 632029815962034112351817)
                    ·
                      rfl

theorem cell23_3692621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3692621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692621 prefixEnd_3692621 := by exact prefixLift 3692621
  have htrace : WordTrace (prefixWord ++ tailWord_3692621) baseStart_3692621 baseEnd_3692621 := by
    simpa [prefixWord, tailWord_3692621, baseEnd_3692621] using wordTrace_append hprefix tailTrace_3692621
  have hstable : (prefixWord ++ tailWord_3692621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692621).length < 2 ^ (prefixWord ++ tailWord_3692621).sum := by decide
  have hdescent : baseEnd_3692621 < baseStart_3692621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692634 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_3692634 : Nat := 118140960795 + 3692634 * 2 ^ 59
def prefixEnd_3692634 : Nat := 4983230072969 + 3 ^ 40 * 3692634 * 2
def baseEnd_3692634 : Nat := 632032041044870262064297

theorem tailTrace_3692634 : CollatzResearch.WordTrace tailWord_3692634 prefixEnd_3692634 632032041044870262064297 := by
  unfold tailWord_3692634
  simp only [CollatzResearch.WordTrace]
  refine ⟨33670356626056286130891239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89787617669483429682376637 33670356626056286130891239)
  ·
    refine ⟨50505534939084429196336859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33670356626056286130891239 50505534939084429196336859)
    ·
      refine ⟨75758302408626643794505289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50505534939084429196336859 75758302408626643794505289)
      ·
        refine ⟨56818726806469982845878967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75758302408626643794505289 56818726806469982845878967)
        ·
          refine ⟨85228090209704974268818451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56818726806469982845878967 85228090209704974268818451)
          ·
            refine ⟨127842135314557461403227677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85228090209704974268818451 127842135314557461403227677)
            ·
              refine ⟨47940800742959048026210379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127842135314557461403227677 47940800742959048026210379)
              ·
                refine ⟨71911201114438572039315569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47940800742959048026210379 71911201114438572039315569)
                ·
                  refine ⟨53933400835828929029486677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71911201114438572039315569 53933400835828929029486677)
                  ·
                    refine ⟨632032041044870262064297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53933400835828929029486677 632032041044870262064297)
                    ·
                      rfl

theorem cell23_3692634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_3692634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692634 prefixEnd_3692634 := by exact prefixLift 3692634
  have htrace : WordTrace (prefixWord ++ tailWord_3692634) baseStart_3692634 baseEnd_3692634 := by
    simpa [prefixWord, tailWord_3692634, baseEnd_3692634] using wordTrace_append hprefix tailTrace_3692634
  have hstable : (prefixWord ++ tailWord_3692634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692634).length < 2 ^ (prefixWord ++ tailWord_3692634).sum := by decide
  have hdescent : baseEnd_3692634 < baseStart_3692634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692641 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3692641 : Nat := 118140960795 + 3692641 * 2 ^ 59
def prefixEnd_3692641 : Nat := 4983230072969 + 3 ^ 40 * 3692641 * 2
def baseEnd_3692641 : Nat := 1896099717499192258805359

theorem tailTrace_3692641 : CollatzResearch.WordTrace tailWord_3692641 prefixEnd_3692641 1896099717499192258805359 := by
  unfold tailWord_3692641
  simp only [CollatzResearch.WordTrace]
  refine ⟨134681681815199784719069777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89787787876799856479379851 134681681815199784719069777)
  ·
    refine ⟨101011261361399838539302333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134681681815199784719069777 101011261361399838539302333)
    ·
      refine ⟨37879223010524939452238375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101011261361399838539302333 37879223010524939452238375)
      ·
        refine ⟨56818834515787409178357563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37879223010524939452238375 56818834515787409178357563)
        ·
          refine ⟨85228251773681113767536345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56818834515787409178357563 85228251773681113767536345)
          ·
            refine ⟨63921188830260835325652259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85228251773681113767536345 63921188830260835325652259)
            ·
              refine ⟨95881783245391252988478389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63921188830260835325652259 95881783245391252988478389)
              ·
                refine ⟨8988917179255429967669849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95881783245391252988478389 8988917179255429967669849)
                ·
                  refine ⟨6741687884441572475752387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8988917179255429967669849 6741687884441572475752387)
                  ·
                    refine ⟨10112531826662358713628581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6741687884441572475752387 10112531826662358713628581)
                    ·
                      refine ⟨1896099717499192258805359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10112531826662358713628581 1896099717499192258805359)
                      ·
                        rfl

theorem cell23_3692641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3692641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692641 prefixEnd_3692641 := by exact prefixLift 3692641
  have htrace : WordTrace (prefixWord ++ tailWord_3692641) baseStart_3692641 baseEnd_3692641 := by
    simpa [prefixWord, tailWord_3692641, baseEnd_3692641] using wordTrace_append hprefix tailTrace_3692641
  have hstable : (prefixWord ++ tailWord_3692641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692641).length < 2 ^ (prefixWord ++ tailWord_3692641).sum := by decide
  have hdescent : baseEnd_3692641 < baseStart_3692641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692642 : List Nat := [3, 3, 2, 2, 2, 2, 1, 3, 5]
def baseStart_3692642 : Nat := 118140960795 + 3692642 * 2 ^ 59
def prefixEnd_3692642 : Nat := 4983230072969 + 3 ^ 40 * 3692642 * 2
def baseEnd_3692642 : Nat := 210677803442205194988095

theorem tailTrace_3692642 : CollatzResearch.WordTrace tailWord_3692642 prefixEnd_3692642 210677803442205194988095 := by
  unfold tailWord_3692642
  simp only [CollatzResearch.WordTrace]
  refine ⟨33670429572049040472464045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89787812192130774593237453 33670429572049040472464045)
  ·
    refine ⟨12626411089518390177174017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33670429572049040472464045 12626411089518390177174017)
    ·
      refine ⟨9469808317138792632880513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12626411089518390177174017 9469808317138792632880513)
      ·
        refine ⟨7102356237854094474660385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9469808317138792632880513 7102356237854094474660385)
        ·
          refine ⟨5326767178390570855995289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7102356237854094474660385 5326767178390570855995289)
          ·
            refine ⟨3995075383792928141996467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5326767178390570855995289 3995075383792928141996467)
            ·
              refine ⟨5992613075689392212994701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995075383792928141996467 5992613075689392212994701)
              ·
                refine ⟨2247229903383522079873013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5992613075689392212994701 2247229903383522079873013)
                ·
                  refine ⟨210677803442205194988095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2247229903383522079873013 210677803442205194988095)
                  ·
                    rfl

theorem cell23_3692642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_3692642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692642 prefixEnd_3692642 := by exact prefixLift 3692642
  have htrace : WordTrace (prefixWord ++ tailWord_3692642) baseStart_3692642 baseEnd_3692642 := by
    simpa [prefixWord, tailWord_3692642, baseEnd_3692642] using wordTrace_append hprefix tailTrace_3692642
  have hstable : (prefixWord ++ tailWord_3692642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692642).length < 2 ^ (prefixWord ++ tailWord_3692642).sum := by decide
  have hdescent : baseEnd_3692642 < baseStart_3692642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692658 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3692658 : Nat := 118140960795 + 3692658 * 2 ^ 59
def prefixEnd_3692658 : Nat := 4983230072969 + 3 ^ 40 * 3692658 * 2
def baseEnd_3692658 : Nat := 1896108446670318692292781

theorem tailTrace_3692658 : CollatzResearch.WordTrace tailWord_3692658 prefixEnd_3692658 1896108446670318692292781 := by
  unfold tailWord_3692658
  simp only [CollatzResearch.WordTrace]
  refine ⟨33670575464034549155609657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89788201237425464414959085 33670575464034549155609657)
  ·
    refine ⟨25252931598025911866707243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33670575464034549155609657 25252931598025911866707243)
    ·
      refine ⟨37879397397038867800060865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25252931598025911866707243 37879397397038867800060865)
      ·
        refine ⟨28409548047779150850045649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37879397397038867800060865 28409548047779150850045649)
        ·
          refine ⟨21307161035834363137534237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28409548047779150850045649 21307161035834363137534237)
          ·
            refine ⟨7990185388437886176575339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21307161035834363137534237 7990185388437886176575339)
            ·
              refine ⟨11985278082656829264863009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990185388437886176575339 11985278082656829264863009)
              ·
                refine ⟨8988958561992621948647257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11985278082656829264863009 8988958561992621948647257)
                ·
                  refine ⟨6741718921494466461485443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8988958561992621948647257 6741718921494466461485443)
                  ·
                    refine ⟨10112578382241699692228165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6741718921494466461485443 10112578382241699692228165)
                    ·
                      refine ⟨1896108446670318692292781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10112578382241699692228165 1896108446670318692292781)
                      ·
                        rfl

theorem cell23_3692658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3692658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692658 prefixEnd_3692658 := by exact prefixLift 3692658
  have htrace : WordTrace (prefixWord ++ tailWord_3692658) baseStart_3692658 baseEnd_3692658 := by
    simpa [prefixWord, tailWord_3692658, baseEnd_3692658] using wordTrace_append hprefix tailTrace_3692658
  have hstable : (prefixWord ++ tailWord_3692658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692658).length < 2 ^ (prefixWord ++ tailWord_3692658).sum := by decide
  have hdescent : baseEnd_3692658 < baseStart_3692658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692668 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_3692668 : Nat := 118140960795 + 3692668 * 2 ^ 59
def prefixEnd_3692668 : Nat := 4983230072969 + 3 ^ 40 * 3692668 * 2
def baseEnd_3692668 : Nat := 632037860492287884389245

theorem tailTrace_3692668 : CollatzResearch.WordTrace tailWord_3692668 prefixEnd_3692668 632037860492287884389245 := by
  unfold tailWord_3692668
  simp only [CollatzResearch.WordTrace]
  refine ⟨67341333293050984165151329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89788444390734645553535105 67341333293050984165151329)
  ·
    refine ⟨50505999969788238123863497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67341333293050984165151329 50505999969788238123863497)
    ·
      refine ⟨37879499977341178592897623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50505999969788238123863497 37879499977341178592897623)
      ·
        refine ⟨56819249966011767889346435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37879499977341178592897623 56819249966011767889346435)
        ·
          refine ⟨85228874949017651834019653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56819249966011767889346435 85228874949017651834019653)
          ·
            refine ⟨15980414052940809718878685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85228874949017651834019653 15980414052940809718878685)
            ·
              refine ⟨5992655269852803644579507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15980414052940809718878685 5992655269852803644579507)
              ·
                refine ⟨8988982904779205466869261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992655269852803644579507 8988982904779205466869261)
                ·
                  refine ⟨3370868589292202050075973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8988982904779205466869261 3370868589292202050075973)
                  ·
                    refine ⟨632037860492287884389245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370868589292202050075973 632037860492287884389245)
                    ·
                      rfl

theorem cell23_3692668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_3692668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692668 prefixEnd_3692668 := by exact prefixLift 3692668
  have htrace : WordTrace (prefixWord ++ tailWord_3692668) baseStart_3692668 baseEnd_3692668 := by
    simpa [prefixWord, tailWord_3692668, baseEnd_3692668] using wordTrace_append hprefix tailTrace_3692668
  have hstable : (prefixWord ++ tailWord_3692668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692668).length < 2 ^ (prefixWord ++ tailWord_3692668).sum := by decide
  have hdescent : baseEnd_3692668 < baseStart_3692668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692681 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 6]
def baseStart_3692681 : Nat := 118140960795 + 3692681 * 2 ^ 59
def prefixEnd_3692681 : Nat := 4983230072969 + 3 ^ 40 * 3692681 * 2
def baseEnd_3692681 : Nat := 210680028525041344700575

theorem tailTrace_3692681 : CollatzResearch.WordTrace tailWord_3692681 prefixEnd_3692681 210680028525041344700575 := by
  unfold tailWord_3692681
  simp only [CollatzResearch.WordTrace]
  refine ⟨134683140735054871550525897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89788760490036581033683931 134683140735054871550525897)
  ·
    refine ⟨101012355551291153662894423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134683140735054871550525897 101012355551291153662894423)
    ·
      refine ⟨151518533326936730494341635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101012355551291153662894423 151518533326936730494341635)
      ·
        refine ⟨227277799990405095741512453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151518533326936730494341635 227277799990405095741512453)
        ·
          refine ⟨42614587498200955451533585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227277799990405095741512453 42614587498200955451533585)
          ·
            refine ⟨31960940623650716588650189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42614587498200955451533585 31960940623650716588650189)
            ·
              refine ⟨11985352733869018720743821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31960940623650716588650189 11985352733869018720743821)
              ·
                refine ⟨4494507275200882020278933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11985352733869018720743821 4494507275200882020278933)
                ·
                  refine ⟨210680028525041344700575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4494507275200882020278933 210680028525041344700575)
                  ·
                    rfl

theorem cell23_3692681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 6].length) (baseStart_3692681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692681 prefixEnd_3692681 := by exact prefixLift 3692681
  have htrace : WordTrace (prefixWord ++ tailWord_3692681) baseStart_3692681 baseEnd_3692681 := by
    simpa [prefixWord, tailWord_3692681, baseEnd_3692681] using wordTrace_append hprefix tailTrace_3692681
  have hstable : (prefixWord ++ tailWord_3692681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692681).length < 2 ^ (prefixWord ++ tailWord_3692681).sum := by decide
  have hdescent : baseEnd_3692681 < baseStart_3692681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692692 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3692692 : Nat := 118140960795 + 3692692 * 2 ^ 59
def prefixEnd_3692692 : Nat := 4983230072969 + 3 ^ 40 * 3692692 * 2
def baseEnd_3692692 : Nat := 1896125905012571559267625

theorem tailTrace_3692692 : CollatzResearch.WordTrace tailWord_3692692 prefixEnd_3692692 1896125905012571559267625 := by
  unfold tailWord_3692692
  simp only [CollatzResearch.WordTrace]
  refine ⟨67341770969007510214588165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89789027958676680286117553 67341770969007510214588165)
  ·
    refine ⟨12626582056688908165235281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67341770969007510214588165 12626582056688908165235281)
    ·
      refine ⟨9469936542516681123926461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12626582056688908165235281 9469936542516681123926461)
      ·
        refine ⟨3551226203443755421472423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9469936542516681123926461 3551226203443755421472423)
        ·
          refine ⟨5326839305165633132208635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551226203443755421472423 5326839305165633132208635)
          ·
            refine ⟨7990258957748449698312953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326839305165633132208635 7990258957748449698312953)
            ·
              refine ⟨5992694218311337273734715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990258957748449698312953 5992694218311337273734715)
              ·
                refine ⟨8989041327467005910602073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992694218311337273734715 8989041327467005910602073)
                ·
                  refine ⟨6741780995600254432951555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8989041327467005910602073 6741780995600254432951555)
                  ·
                    refine ⟨10112671493400381649427333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6741780995600254432951555 10112671493400381649427333)
                    ·
                      refine ⟨1896125905012571559267625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10112671493400381649427333 1896125905012571559267625)
                      ·
                        rfl

theorem cell23_3692692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3692692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692692 prefixEnd_3692692 := by exact prefixLift 3692692
  have htrace : WordTrace (prefixWord ++ tailWord_3692692) baseStart_3692692 baseEnd_3692692 := by
    simpa [prefixWord, tailWord_3692692, baseEnd_3692692] using wordTrace_append hprefix tailTrace_3692692
  have hstable : (prefixWord ++ tailWord_3692692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692692).length < 2 ^ (prefixWord ++ tailWord_3692692).sum := by decide
  have hdescent : baseEnd_3692692 < baseStart_3692692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692695 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_3692695 : Nat := 118140960795 + 3692695 * 2 ^ 59
def prefixEnd_3692695 : Nat := 4983230072969 + 3 ^ 40 * 3692695 * 2
def baseEnd_3692695 : Nat := 1896127445454535047530111

theorem tailTrace_3692695 : CollatzResearch.WordTrace tailWord_3692695 prefixEnd_3692695 1896127445454535047530111 := by
  unfold tailWord_3692695
  simp only [CollatzResearch.WordTrace]
  refine ⟨134683651357004151941535539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89789100904669434627690359 134683651357004151941535539)
  ·
    refine ⟨202025477035506227912303309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134683651357004151941535539 202025477035506227912303309)
    ·
      refine ⟨75759553888314835467113741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202025477035506227912303309 75759553888314835467113741)
      ·
        refine ⟨28409832708118063300167653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75759553888314835467113741 28409832708118063300167653)
        ·
          refine ⟨5326843632772136868781435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28409832708118063300167653 5326843632772136868781435)
          ·
            refine ⟨7990265449158205303172153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326843632772136868781435 7990265449158205303172153)
            ·
              refine ⟨5992699086868653977379115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990265449158205303172153 5992699086868653977379115)
              ·
                refine ⟨8989048630302980966068673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992699086868653977379115 8989048630302980966068673)
                ·
                  refine ⟨6741786472727235724551505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8989048630302980966068673 6741786472727235724551505)
                  ·
                    refine ⟨5056339854545426793413629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6741786472727235724551505 5056339854545426793413629)
                    ·
                      refine ⟨1896127445454535047530111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5056339854545426793413629 1896127445454535047530111)
                      ·
                        rfl

theorem cell23_3692695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_3692695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692695 prefixEnd_3692695 := by exact prefixLift 3692695
  have htrace : WordTrace (prefixWord ++ tailWord_3692695) baseStart_3692695 baseEnd_3692695 := by
    simpa [prefixWord, tailWord_3692695, baseEnd_3692695] using wordTrace_append hprefix tailTrace_3692695
  have hstable : (prefixWord ++ tailWord_3692695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692695).length < 2 ^ (prefixWord ++ tailWord_3692695).sum := by decide
  have hdescent : baseEnd_3692695 < baseStart_3692695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692731 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 4]
def baseStart_3692731 : Nat := 118140960795 + 3692731 * 2 ^ 59
def prefixEnd_3692731 : Nat := 4983230072969 + 3 ^ 40 * 3692731 * 2
def baseEnd_3692731 : Nat := 1896145930758096906679945

theorem tailTrace_3692731 : CollatzResearch.WordTrace tailWord_3692731 prefixEnd_3692731 1896145930758096906679945 := by
  unfold tailWord_3692731
  simp only [CollatzResearch.WordTrace]
  refine ⟨134684964384873730089846047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89789976256582486726564031 134684964384873730089846047)
  ·
    refine ⟨202027446577310595134769071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134684964384873730089846047 202027446577310595134769071)
    ·
      refine ⟨303041169865965892702153607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202027446577310595134769071 303041169865965892702153607)
      ·
        refine ⟨454561754798948839053230411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303041169865965892702153607 454561754798948839053230411)
        ·
          refine ⟨681842632198423258579845617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454561754798948839053230411 681842632198423258579845617)
          ·
            refine ⟨511381974148817443934884213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681842632198423258579845617 511381974148817443934884213)
            ·
              refine ⟨47942060076451635368895395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 511381974148817443934884213 47942060076451635368895395)
              ·
                refine ⟨71913090114677453053343093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47942060076451635368895395 71913090114677453053343093)
                ·
                  refine ⟨6741852198251011223750915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71913090114677453053343093 6741852198251011223750915)
                  ·
                    refine ⟨10112778297376516835626373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6741852198251011223750915 10112778297376516835626373)
                    ·
                      refine ⟨1896145930758096906679945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10112778297376516835626373 1896145930758096906679945)
                      ·
                        rfl

theorem cell23_3692731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 4].length) (baseStart_3692731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692731 prefixEnd_3692731 := by exact prefixLift 3692731
  have htrace : WordTrace (prefixWord ++ tailWord_3692731) baseStart_3692731 baseEnd_3692731 := by
    simpa [prefixWord, tailWord_3692731, baseEnd_3692731] using wordTrace_append hprefix tailTrace_3692731
  have hstable : (prefixWord ++ tailWord_3692731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692731).length < 2 ^ (prefixWord ++ tailWord_3692731).sum := by decide
  have hdescent : baseEnd_3692731 < baseStart_3692731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692741 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 1, 6]
def baseStart_3692741 : Nat := 118140960795 + 3692741 * 2 ^ 59
def prefixEnd_3692741 : Nat := 4983230072969 + 3 ^ 40 * 3692741 * 2
def baseEnd_3692741 : Nat := 632050355188213955851633

theorem tailTrace_3692741 : CollatzResearch.WordTrace tailWord_3692741 prefixEnd_3692741 632050355188213955851633 := by
  unfold tailWord_3692741
  simp only [CollatzResearch.WordTrace]
  refine ⟨134685329114837501797710077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89790219409891667865140051 134685329114837501797710077)
  ·
    refine ⟨50506998418064063174141279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134685329114837501797710077 50506998418064063174141279)
    ·
      refine ⟨75760497627096094761211919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50506998418064063174141279 75760497627096094761211919)
      ·
        refine ⟨113640746440644142141817879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75760497627096094761211919 113640746440644142141817879)
        ·
          refine ⟨170461119660966213212726819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113640746440644142141817879 170461119660966213212726819)
          ·
            refine ⟨255691679491449319819090229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170461119660966213212726819 255691679491449319819090229)
            ·
              refine ⟨23971094952323373733039709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255691679491449319819090229 23971094952323373733039709)
              ·
                refine ⟨8989160607121265149889891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23971094952323373733039709 8989160607121265149889891)
                ·
                  refine ⟨13483740910681897724834837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8989160607121265149889891 13483740910681897724834837)
                  ·
                    refine ⟨632050355188213955851633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13483740910681897724834837 632050355188213955851633)
                    ·
                      rfl

theorem cell23_3692741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_3692741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692741 prefixEnd_3692741 := by exact prefixLift 3692741
  have htrace : WordTrace (prefixWord ++ tailWord_3692741) baseStart_3692741 baseEnd_3692741 := by
    simpa [prefixWord, tailWord_3692741, baseEnd_3692741] using wordTrace_append hprefix tailTrace_3692741
  have hstable : (prefixWord ++ tailWord_3692741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692741).length < 2 ^ (prefixWord ++ tailWord_3692741).sum := by decide
  have hdescent : baseEnd_3692741 < baseStart_3692741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692775 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 4, 4]
def baseStart_3692775 : Nat := 118140960795 + 3692775 * 2 ^ 59
def prefixEnd_3692775 : Nat := 4983230072969 + 3 ^ 40 * 3692775 * 2
def baseEnd_3692775 : Nat := 632056174635631578176581

theorem tailTrace_3692775 : CollatzResearch.WordTrace tailWord_3692775 prefixEnd_3692775 632056174635631578176581 := by
  unfold tailWord_3692775
  simp only [CollatzResearch.WordTrace]
  refine ⟨134686569196714325604447779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89791046131142883736298519 134686569196714325604447779)
  ·
    refine ⟨202029853795071488406671669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134686569196714325604447779 202029853795071488406671669)
    ·
      refine ⟨18940298793287952038125469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202029853795071488406671669 18940298793287952038125469)
      ·
        refine ⟨7102612047482982014297051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18940298793287952038125469 7102612047482982014297051)
        ·
          refine ⟨10653918071224473021445577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7102612047482982014297051 10653918071224473021445577)
          ·
            refine ⟨7990438553418354766084183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10653918071224473021445577 7990438553418354766084183)
            ·
              refine ⟨11985657830127532149126275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990438553418354766084183 11985657830127532149126275)
              ·
                refine ⟨17978486745191298223689413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985657830127532149126275 17978486745191298223689413)
                ·
                  refine ⟨3370966264723368416941765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17978486745191298223689413 3370966264723368416941765)
                  ·
                    refine ⟨632056174635631578176581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3370966264723368416941765 632056174635631578176581)
                    ·
                      rfl

theorem cell23_3692775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_3692775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692775 prefixEnd_3692775 := by exact prefixLift 3692775
  have htrace : WordTrace (prefixWord ++ tailWord_3692775) baseStart_3692775 baseEnd_3692775 := by
    simpa [prefixWord, tailWord_3692775, baseEnd_3692775] using wordTrace_append hprefix tailTrace_3692775
  have hstable : (prefixWord ++ tailWord_3692775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692775).length < 2 ^ (prefixWord ++ tailWord_3692775).sum := by decide
  have hdescent : baseEnd_3692775 < baseStart_3692775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692802 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_3692802 : Nat := 118140960795 + 3692802 * 2 ^ 59
def prefixEnd_3692802 : Nat := 4983230072969 + 3 ^ 40 * 3692802 * 2
def baseEnd_3692802 : Nat := 1896182387884566128892119

theorem tailTrace_3692802 : CollatzResearch.WordTrace tailWord_3692802 prefixEnd_3692802 1896182387884566128892119 := by
  unfold tailWord_3692802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33671888491904127303920165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89791702645077672810453773 33671888491904127303920165)
  ·
    refine ⟨6313479092232023869485031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33671888491904127303920165 6313479092232023869485031)
    ·
      refine ⟨9470218638348035804227547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6313479092232023869485031 9470218638348035804227547)
      ·
        refine ⟨14205327957522053706341321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9470218638348035804227547 14205327957522053706341321)
        ·
          refine ⟨10653995968141540279755991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14205327957522053706341321 10653995968141540279755991)
          ·
            refine ⟨15980993952212310419633987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10653995968141540279755991 15980993952212310419633987)
            ·
              refine ⟨23971490928318465629450981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15980993952212310419633987 23971490928318465629450981)
              ·
                refine ⟨4494654549059712305522059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23971490928318465629450981 4494654549059712305522059)
                ·
                  refine ⟨6741981823589568458283089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4494654549059712305522059 6741981823589568458283089)
                  ·
                    refine ⟨5056486367692176343712317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6741981823589568458283089 5056486367692176343712317)
                    ·
                      refine ⟨1896182387884566128892119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5056486367692176343712317 1896182387884566128892119)
                      ·
                        rfl

theorem cell23_3692802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_3692802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692802 prefixEnd_3692802 := by exact prefixLift 3692802
  have htrace : WordTrace (prefixWord ++ tailWord_3692802) baseStart_3692802 baseEnd_3692802 := by
    simpa [prefixWord, tailWord_3692802, baseEnd_3692802] using wordTrace_append hprefix tailTrace_3692802
  have hstable : (prefixWord ++ tailWord_3692802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692802).length < 2 ^ (prefixWord ++ tailWord_3692802).sum := by decide
  have hdescent : baseEnd_3692802 < baseStart_3692802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692811 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5]
def baseStart_3692811 : Nat := 118140960795 + 3692811 * 2 ^ 59
def prefixEnd_3692811 : Nat := 4983230072969 + 3 ^ 40 * 3692811 * 2
def baseEnd_3692811 : Nat := 1896187009210456593679577

theorem tailTrace_3692811 : CollatzResearch.WordTrace tailWord_3692811 prefixEnd_3692811 1896187009210456593679577 := by
  unfold tailWord_3692811
  simp only [CollatzResearch.WordTrace]
  refine ⟨134687882224583903752758287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89791921483055935835172191 134687882224583903752758287)
  ·
    refine ⟨202031823336875855629137431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134687882224583903752758287 202031823336875855629137431)
    ·
      refine ⟨303047735005313783443706147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202031823336875855629137431 303047735005313783443706147)
      ·
        refine ⟨454571602507970675165559221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303047735005313783443706147 454571602507970675165559221)
        ·
          refine ⟨42616087735122250796771177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 454571602507970675165559221 42616087735122250796771177)
          ·
            refine ⟨31962065801341688097578383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42616087735122250796771177 31962065801341688097578383)
            ·
              refine ⟨47943098702012532146367575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31962065801341688097578383 47943098702012532146367575)
              ·
                refine ⟨71914648053018798219551363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47943098702012532146367575 71914648053018798219551363)
                ·
                  refine ⟨107871972079528197329327045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71914648053018798219551363 107871972079528197329327045)
                  ·
                    refine ⟨20225994764911536999248821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107871972079528197329327045 20225994764911536999248821)
                    ·
                      refine ⟨1896187009210456593679577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20225994764911536999248821 1896187009210456593679577)
                      ·
                        rfl

theorem cell23_3692811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_3692811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692811 prefixEnd_3692811 := by exact prefixLift 3692811
  have htrace : WordTrace (prefixWord ++ tailWord_3692811) baseStart_3692811 baseEnd_3692811 := by
    simpa [prefixWord, tailWord_3692811, baseEnd_3692811] using wordTrace_append hprefix tailTrace_3692811
  have hstable : (prefixWord ++ tailWord_3692811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692811).length < 2 ^ (prefixWord ++ tailWord_3692811).sum := by decide
  have hdescent : baseEnd_3692811 < baseStart_3692811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692858 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_3692858 : Nat := 118140960795 + 3692858 * 2 ^ 59
def prefixEnd_3692858 : Nat := 4983230072969 + 3 ^ 40 * 3692858 * 2
def baseEnd_3692858 : Nat := 1896211142801217909791861

theorem tailTrace_3692858 : CollatzResearch.WordTrace tailWord_3692858 prefixEnd_3692858 1896211142801217909791861 := by
  unfold tailWord_3692858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33672399113853407694929807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89793064303609087186479485 33672399113853407694929807)
  ·
    refine ⟨50508598670780111542394711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33672399113853407694929807 50508598670780111542394711)
    ·
      refine ⟨75762898006170167313592067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50508598670780111542394711 75762898006170167313592067)
      ·
        refine ⟨113644347009255250970388101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75762898006170167313592067 113644347009255250970388101)
        ·
          refine ⟨21308315064235359556947769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113644347009255250970388101 21308315064235359556947769)
          ·
            refine ⟨15981236298176519667710827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21308315064235359556947769 15981236298176519667710827)
            ·
              refine ⟨23971854447264779501566241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15981236298176519667710827 23971854447264779501566241)
              ·
                refine ⟨17978890835448584626174681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23971854447264779501566241 17978890835448584626174681)
                ·
                  refine ⟨13484168126586438469631011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17978890835448584626174681 13484168126586438469631011)
                  ·
                    refine ⟨20226252189879657704446517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13484168126586438469631011 20226252189879657704446517)
                    ·
                      refine ⟨1896211142801217909791861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20226252189879657704446517 1896211142801217909791861)
                      ·
                        rfl

theorem cell23_3692858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_3692858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692858 prefixEnd_3692858 := by exact prefixLift 3692858
  have htrace : WordTrace (prefixWord ++ tailWord_3692858) baseStart_3692858 baseEnd_3692858 := by
    simpa [prefixWord, tailWord_3692858, baseEnd_3692858] using wordTrace_append hprefix tailTrace_3692858
  have hstable : (prefixWord ++ tailWord_3692858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692858).length < 2 ^ (prefixWord ++ tailWord_3692858).sum := by decide
  have hdescent : baseEnd_3692858 < baseStart_3692858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692925 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_3692925 : Nat := 118140960795 + 3692925 * 2 ^ 59
def prefixEnd_3692925 : Nat := 4983230072969 + 3 ^ 40 * 3692925 * 2
def baseEnd_3692925 : Nat := 632081848668356382551351

theorem tailTrace_3692925 : CollatzResearch.WordTrace tailWord_3692925 prefixEnd_3692925 632081848668356382551351 := by
  unfold tailWord_3692925
  simp only [CollatzResearch.WordTrace]
  refine ⟨134692040146170901222408229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89794693430780600814938819 134692040146170901222408229)
  ·
    refine ⟨25254757527407043979201543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134692040146170901222408229 25254757527407043979201543)
    ·
      refine ⟨37882136291110565968802315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25254757527407043979201543 37882136291110565968802315)
      ·
        refine ⟨56823204436665848953203473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37882136291110565968802315 56823204436665848953203473)
        ·
          refine ⟨42617403327499386714902605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56823204436665848953203473 42617403327499386714902605)
          ·
            refine ⟨15981526247812270018088477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42617403327499386714902605 15981526247812270018088477)
            ·
              refine ⟨5993072342929601256783179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15981526247812270018088477 5993072342929601256783179)
              ·
                refine ⟨8989608514394401885174769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5993072342929601256783179 8989608514394401885174769)
                ·
                  refine ⟨6742206385795801413881077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8989608514394401885174769 6742206385795801413881077)
                  ·
                    refine ⟨632081848668356382551351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6742206385795801413881077 632081848668356382551351)
                    ·
                      rfl

theorem cell23_3692925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_3692925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692925 prefixEnd_3692925 := by exact prefixLift 3692925
  have htrace : WordTrace (prefixWord ++ tailWord_3692925) baseStart_3692925 baseEnd_3692925 := by
    simpa [prefixWord, tailWord_3692925, baseEnd_3692925] using wordTrace_append hprefix tailTrace_3692925
  have hstable : (prefixWord ++ tailWord_3692925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692925).length < 2 ^ (prefixWord ++ tailWord_3692925).sum := by decide
  have hdescent : baseEnd_3692925 < baseStart_3692925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692962 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_3692962 : Nat := 118140960795 + 3692962 * 2 ^ 59
def prefixEnd_3692962 : Nat := 4983230072969 + 3 ^ 40 * 3692962 * 2
def baseEnd_3692962 : Nat := 1896264544789285502891383

theorem tailTrace_3692962 : CollatzResearch.WordTrace tailWord_3692962 prefixEnd_3692962 1896264544789285502891383 := by
  unfold tailWord_3692962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33673347411759214135376285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89795593098024571027670093 33673347411759214135376285)
  ·
    refine ⟨12627505279409705300766107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33673347411759214135376285 12627505279409705300766107)
    ·
      refine ⟨18941257919114557951149161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12627505279409705300766107 18941257919114557951149161)
      ·
        refine ⟨14205943439335918463361871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18941257919114557951149161 14205943439335918463361871)
        ·
          refine ⟨21308915159003877695042807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14205943439335918463361871 21308915159003877695042807)
          ·
            refine ⟨31963372738505816542564211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21308915159003877695042807 31963372738505816542564211)
            ·
              refine ⟨47945059107758724813846317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31963372738505816542564211 47945059107758724813846317)
              ·
                refine ⟨17979397165409521805192369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47945059107758724813846317 17979397165409521805192369)
                ·
                  refine ⟨13484547874057141353894277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17979397165409521805192369 13484547874057141353894277)
                  ·
                    refine ⟨2528352726385714003855177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13484547874057141353894277 2528352726385714003855177)
                    ·
                      refine ⟨1896264544789285502891383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528352726385714003855177 1896264544789285502891383)
                      ·
                        rfl

theorem cell23_3692962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_3692962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692962 prefixEnd_3692962 := by exact prefixLift 3692962
  have htrace : WordTrace (prefixWord ++ tailWord_3692962) baseStart_3692962 baseEnd_3692962 := by
    simpa [prefixWord, tailWord_3692962, baseEnd_3692962] using wordTrace_append hprefix tailTrace_3692962
  have hstable : (prefixWord ++ tailWord_3692962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692962).length < 2 ^ (prefixWord ++ tailWord_3692962).sum := by decide
  have hdescent : baseEnd_3692962 < baseStart_3692962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692989 : List Nat := [1, 4, 1, 2, 2, 2, 3, 3, 1, 4]
def baseStart_3692989 : Nat := 118140960795 + 3692989 * 2 ^ 59
def prefixEnd_3692989 : Nat := 4983230072969 + 3 ^ 40 * 3692989 * 2
def baseEnd_3692989 : Nat := 632092802922318965751253

theorem tailTrace_3692989 : CollatzResearch.WordTrace tailWord_3692989 prefixEnd_3692989 632092802922318965751253 := by
  unfold tailWord_3692989
  simp only [CollatzResearch.WordTrace]
  refine ⟨134694374417939040152738021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89796249611959360101825347 134694374417939040152738021)
  ·
    refine ⟨25255195203363570028638379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134694374417939040152738021 25255195203363570028638379)
    ·
      refine ⟨37882792805045355042957569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25255195203363570028638379 37882792805045355042957569)
      ·
        refine ⟨28412094603784016282218177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37882792805045355042957569 28412094603784016282218177)
        ·
          refine ⟨21309070952838012211663633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28412094603784016282218177 21309070952838012211663633)
          ·
            refine ⟨15981803214628509158747725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21309070952838012211663633 15981803214628509158747725)
            ·
              refine ⟨5993176205485690934530397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15981803214628509158747725 5993176205485690934530397)
              ·
                refine ⟨2247441077057134100448899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5993176205485690934530397 2247441077057134100448899)
                ·
                  refine ⟨3371161615585701150673349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247441077057134100448899 3371161615585701150673349)
                  ·
                    refine ⟨632092802922318965751253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371161615585701150673349 632092802922318965751253)
                    ·
                      rfl

theorem cell23_3692989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_3692989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3692989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3692989 prefixEnd_3692989 := by exact prefixLift 3692989
  have htrace : WordTrace (prefixWord ++ tailWord_3692989) baseStart_3692989 baseEnd_3692989 := by
    simpa [prefixWord, tailWord_3692989, baseEnd_3692989] using wordTrace_append hprefix tailTrace_3692989
  have hstable : (prefixWord ++ tailWord_3692989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692989).length < 2 ^ (prefixWord ++ tailWord_3692989).sum := by decide
  have hdescent : baseEnd_3692989 < baseStart_3692989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693032 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 1, 5]
def baseStart_3693032 : Nat := 118140960795 + 3693032 * 2 ^ 59
def prefixEnd_3693032 : Nat := 4983230072969 + 3 ^ 40 * 3693032 * 2
def baseEnd_3693032 : Nat := 632100162811700076338687

theorem tailTrace_3693032 : CollatzResearch.WordTrace tailWord_3693032 prefixEnd_3693032 632100162811700076338687 := by
  unfold tailWord_3693032
  simp only [CollatzResearch.WordTrace]
  refine ⟨67347971378391629248276675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89797295171188838997702233 67347971378391629248276675)
  ·
    refine ⟨101021957067587443872415013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67347971378391629248276675 101021957067587443872415013)
    ·
      refine ⟨18941616950172645726077815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101021957067587443872415013 18941616950172645726077815)
      ·
        refine ⟨28412425425258968589116723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18941616950172645726077815 28412425425258968589116723)
        ·
          refine ⟨42618638137888452883675085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28412425425258968589116723 42618638137888452883675085)
          ·
            refine ⟨15981989301708169831378157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42618638137888452883675085 15981989301708169831378157)
            ·
              refine ⟨5993245988140563686766809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15981989301708169831378157 5993245988140563686766809)
              ·
                refine ⟨4494934491105422765075107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5993245988140563686766809 4494934491105422765075107)
                ·
                  refine ⟨6742401736658134147612661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4494934491105422765075107 6742401736658134147612661)
                  ·
                    refine ⟨632100162811700076338687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6742401736658134147612661 632100162811700076338687)
                    ·
                      rfl

theorem cell23_3693032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_3693032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693032 prefixEnd_3693032 := by exact prefixLift 3693032
  have htrace : WordTrace (prefixWord ++ tailWord_3693032) baseStart_3693032 baseEnd_3693032 := by
    simpa [prefixWord, tailWord_3693032, baseEnd_3693032] using wordTrace_append hprefix tailTrace_3693032
  have hstable : (prefixWord ++ tailWord_3693032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693032).length < 2 ^ (prefixWord ++ tailWord_3693032).sum := by decide
  have hdescent : baseEnd_3693032 < baseStart_3693032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693035 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 4]
def baseStart_3693035 : Nat := 118140960795 + 3693035 * 2 ^ 59
def prefixEnd_3693035 : Nat := 4983230072969 + 3 ^ 40 * 3693035 * 2
def baseEnd_3693035 : Nat := 1896302028877063717278547

theorem tailTrace_3693035 : CollatzResearch.WordTrace tailWord_3693035 prefixEnd_3693035 1896302028877063717278547 := by
  unfold tailWord_3693035
  simp only [CollatzResearch.WordTrace]
  refine ⟨134696052175772390008912559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89797368117181593339275039 134696052175772390008912559)
  ·
    refine ⟨202044078263658585013368839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134696052175772390008912559 202044078263658585013368839)
    ·
      refine ⟨303066117395487877520053259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202044078263658585013368839 303066117395487877520053259)
      ·
        refine ⟨454599176093231816280079889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303066117395487877520053259 454599176093231816280079889)
        ·
          refine ⟨340949382069923862210059917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454599176093231816280079889 340949382069923862210059917)
          ·
            refine ⟨127856018276221448328772469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340949382069923862210059917 127856018276221448328772469)
            ·
              refine ⟨11986501713395760780822419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127856018276221448328772469 11986501713395760780822419)
              ·
                refine ⟨17979752570093641171233629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986501713395760780822419 17979752570093641171233629)
                ·
                  refine ⟨6742407213785115439212611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17979752570093641171233629 6742407213785115439212611)
                  ·
                    refine ⟨10113610820677673158818917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6742407213785115439212611 10113610820677673158818917)
                    ·
                      refine ⟨1896302028877063717278547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10113610820677673158818917 1896302028877063717278547)
                      ·
                        rfl

theorem cell23_3693035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 4].length) (baseStart_3693035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693035 prefixEnd_3693035 := by exact prefixLift 3693035
  have htrace : WordTrace (prefixWord ++ tailWord_3693035) baseStart_3693035 baseEnd_3693035 := by
    simpa [prefixWord, tailWord_3693035, baseEnd_3693035] using wordTrace_append hprefix tailTrace_3693035
  have hstable : (prefixWord ++ tailWord_3693035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693035).length < 2 ^ (prefixWord ++ tailWord_3693035).sum := by decide
  have hdescent : baseEnd_3693035 < baseStart_3693035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693046 : List Nat := [5, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_3693046 : Nat := 118140960795 + 3693046 * 2 ^ 59
def prefixEnd_3693046 : Nat := 4983230072969 + 3 ^ 40 * 3693046 * 2
def baseEnd_3693046 : Nat := 1896307677164263174240997

theorem tailTrace_3693046 : CollatzResearch.WordTrace tailWord_3693046 prefixEnd_3693046 1896307677164263174240997 := by
  unfold tailWord_3693046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8418528336170783680472687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89797635585821692591708661 8418528336170783680472687)
  ·
    refine ⟨12627792504256175520709031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8418528336170783680472687 12627792504256175520709031)
    ·
      refine ⟨18941688756384263281063547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12627792504256175520709031 18941688756384263281063547)
      ·
        refine ⟨28412533134576394921595321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18941688756384263281063547 28412533134576394921595321)
        ·
          refine ⟨21309399850932296191196491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28412533134576394921595321 21309399850932296191196491)
          ·
            refine ⟨31964099776398444286794737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21309399850932296191196491 31964099776398444286794737)
            ·
              refine ⟨23973074832298833215096053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31964099776398444286794737 23973074832298833215096053)
              ·
                refine ⟨2247475765528015613915255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23973074832298833215096053 2247475765528015613915255)
                ·
                  refine ⟨3371213648292023420872883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247475765528015613915255 3371213648292023420872883)
                  ·
                    refine ⟨5056820472438035131309325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3371213648292023420872883 5056820472438035131309325)
                    ·
                      refine ⟨1896307677164263174240997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5056820472438035131309325 1896307677164263174240997)
                      ·
                        rfl

theorem cell23_3693046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_3693046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693046 prefixEnd_3693046 := by exact prefixLift 3693046
  have htrace : WordTrace (prefixWord ++ tailWord_3693046) baseStart_3693046 baseEnd_3693046 := by
    simpa [prefixWord, tailWord_3693046, baseEnd_3693046] using wordTrace_append hprefix tailTrace_3693046
  have hstable : (prefixWord ++ tailWord_3693046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693046).length < 2 ^ (prefixWord ++ tailWord_3693046).sum := by decide
  have hdescent : baseEnd_3693046 < baseStart_3693046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693079 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 1, 6]
def baseStart_3693079 : Nat := 118140960795 + 3693079 * 2 ^ 59
def prefixEnd_3693079 : Nat := 4983230072969 + 3 ^ 40 * 3693079 * 2
def baseEnd_3693079 : Nat := 632108207341953848376115

theorem tailTrace_3693079 : CollatzResearch.WordTrace tailWord_3693079 prefixEnd_3693079 632108207341953848376115 := by
  unfold tailWord_3693079
  simp only [CollatzResearch.WordTrace]
  refine ⟨134697656987612985523514291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89798437991741990349009527 134697656987612985523514291)
  ·
    refine ⟨202046485481419478285271437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134697656987612985523514291 202046485481419478285271437)
    ·
      refine ⟨75767432055532304356976789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202046485481419478285271437 75767432055532304356976789)
      ·
        refine ⟨3551598377603076766733287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75767432055532304356976789 3551598377603076766733287)
        ·
          refine ⟨5327397566404615150099931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551598377603076766733287 5327397566404615150099931)
          ·
            refine ⟨7991096349606922725149897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5327397566404615150099931 7991096349606922725149897)
            ·
              refine ⟨5993322262205192043862423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7991096349606922725149897 5993322262205192043862423)
              ·
                refine ⟨8989983393307788065793635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5993322262205192043862423 8989983393307788065793635)
                ·
                  refine ⟨13484975089961682098690453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8989983393307788065793635 13484975089961682098690453)
                  ·
                    refine ⟨632108207341953848376115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13484975089961682098690453 632108207341953848376115)
                    ·
                      rfl

theorem cell23_3693079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_3693079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693079 prefixEnd_3693079 := by exact prefixLift 3693079
  have htrace : WordTrace (prefixWord ++ tailWord_3693079) baseStart_3693079 baseEnd_3693079 := by
    simpa [prefixWord, tailWord_3693079, baseEnd_3693079] using wordTrace_append hprefix tailTrace_3693079
  have hstable : (prefixWord ++ tailWord_3693079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693079).length < 2 ^ (prefixWord ++ tailWord_3693079).sum := by decide
  have hdescent : baseEnd_3693079 < baseStart_3693079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693135 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 2, 6]
def baseStart_3693135 : Nat := 118140960795 + 3693135 * 2 ^ 59
def prefixEnd_3693135 : Nat := 4983230072969 + 3 ^ 40 * 3693135 * 2
def baseEnd_3693135 : Nat := 632117792314171108676029

theorem tailTrace_3693135 : CollatzResearch.WordTrace tailWord_3693135 prefixEnd_3693135 632117792314171108676029 := by
  unfold tailWord_3693135
  simp only [CollatzResearch.WordTrace]
  refine ⟨134699699475410107087552859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89799799650273404725035239 134699699475410107087552859)
  ·
    refine ⟨202049549213115160631329289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134699699475410107087552859 202049549213115160631329289)
    ·
      refine ⟨151537161909836370473496967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202049549213115160631329289 151537161909836370473496967)
      ·
        refine ⟨227305742864754555710245451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151537161909836370473496967 227305742864754555710245451)
        ·
          refine ⟨340958614297131833565368177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227305742864754555710245451 340958614297131833565368177)
          ·
            refine ⟨255718960722848875174026133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340958614297131833565368177 255718960722848875174026133)
            ·
              refine ⟨11986826283883541023782475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255718960722848875174026133 11986826283883541023782475)
              ·
                refine ⟨17980239425825311535673713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986826283883541023782475 17980239425825311535673713)
                ·
                  refine ⟨13485179569368983651755285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17980239425825311535673713 13485179569368983651755285)
                  ·
                    refine ⟨632117792314171108676029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13485179569368983651755285 632117792314171108676029)
                    ·
                      rfl

theorem cell23_3693135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_3693135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693135 prefixEnd_3693135 := by exact prefixLift 3693135
  have htrace : WordTrace (prefixWord ++ tailWord_3693135) baseStart_3693135 baseEnd_3693135 := by
    simpa [prefixWord, tailWord_3693135, baseEnd_3693135] using wordTrace_append hprefix tailTrace_3693135
  have hstable : (prefixWord ++ tailWord_3693135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693135).length < 2 ^ (prefixWord ++ tailWord_3693135).sum := by decide
  have hdescent : baseEnd_3693135 < baseStart_3693135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693154 : List Nat := [3, 3, 2, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3693154 : Nat := 118140960795 + 3693154 * 2 ^ 59
def prefixEnd_3693154 : Nat := 4983230072969 + 3 ^ 40 * 3693154 * 2
def baseEnd_3693154 : Nat := 1896363133074948751690501

theorem tailTrace_3693154 : CollatzResearch.WordTrace tailWord_3693154 prefixEnd_3693154 1896363133074948751690501 := by
  unfold tailWord_3693154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33675098115585318333123629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89800261641560848888329677 33675098115585318333123629)
  ·
    refine ⟨12628161793344494374921361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33675098115585318333123629 12628161793344494374921361)
    ·
      refine ⟨9471121345008370781191021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12628161793344494374921361 9471121345008370781191021)
      ·
        refine ⟨3551670504378139042946633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9471121345008370781191021 3551670504378139042946633)
        ·
          refine ⟨2663752878283604282209975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3551670504378139042946633 2663752878283604282209975)
          ·
            refine ⟨3995629317425406423314963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663752878283604282209975 3995629317425406423314963)
            ·
              refine ⟨5993443976138109634972445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995629317425406423314963 5993443976138109634972445)
              ·
                refine ⟨2247541491051791113114667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5993443976138109634972445 2247541491051791113114667)
                ·
                  refine ⟨3371312236577686669672001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247541491051791113114667 3371312236577686669672001)
                  ·
                    refine ⟨2528484177433265002254001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3371312236577686669672001 2528484177433265002254001)
                    ·
                      refine ⟨1896363133074948751690501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528484177433265002254001 1896363133074948751690501)
                      ·
                        rfl

theorem cell23_3693154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3693154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693154 prefixEnd_3693154 := by exact prefixLift 3693154
  have htrace : WordTrace (prefixWord ++ tailWord_3693154) baseStart_3693154 baseEnd_3693154 := by
    simpa [prefixWord, tailWord_3693154, baseEnd_3693154] using wordTrace_append hprefix tailTrace_3693154
  have hstable : (prefixWord ++ tailWord_3693154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693154).length < 2 ^ (prefixWord ++ tailWord_3693154).sum := by decide
  have hdescent : baseEnd_3693154 < baseStart_3693154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693162 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3693162 : Nat := 118140960795 + 3693162 * 2 ^ 59
def prefixEnd_3693162 : Nat := 4983230072969 + 3 ^ 40 * 3693162 * 2
def baseEnd_3693162 : Nat := 1896367240920184720390463

theorem tailTrace_3693162 : CollatzResearch.WordTrace tailWord_3693162 prefixEnd_3693162 1896367240920184720390463 := by
  unfold tailWord_3693162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33675171061578072674696435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89800456164208193799190493 33675171061578072674696435)
  ·
    refine ⟨50512756592367109012044653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33675171061578072674696435 50512756592367109012044653)
    ·
      refine ⟨18942283722137665879516745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50512756592367109012044653 18942283722137665879516745)
      ·
        refine ⟨14206712791603249409637559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18942283722137665879516745 14206712791603249409637559)
        ·
          refine ⟨21310069187404874114456339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14206712791603249409637559 21310069187404874114456339)
          ·
            refine ⟨31965103781107311171684509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21310069187404874114456339 31965103781107311171684509)
            ·
              refine ⟨11986913917915241689381691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31965103781107311171684509 11986913917915241689381691)
              ·
                refine ⟨17980370876872862534072537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986913917915241689381691 17980370876872862534072537)
                ·
                  refine ⟨13485278157654646900554403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17980370876872862534072537 13485278157654646900554403)
                  ·
                    refine ⟨20227917236481970350831605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13485278157654646900554403 20227917236481970350831605)
                    ·
                      refine ⟨1896367240920184720390463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20227917236481970350831605 1896367240920184720390463)
                      ·
                        rfl

theorem cell23_3693162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3693162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693162 prefixEnd_3693162 := by exact prefixLift 3693162
  have htrace : WordTrace (prefixWord ++ tailWord_3693162) baseStart_3693162 baseEnd_3693162 := by
    simpa [prefixWord, tailWord_3693162, baseEnd_3693162] using wordTrace_append hprefix tailTrace_3693162
  have hstable : (prefixWord ++ tailWord_3693162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693162).length < 2 ^ (prefixWord ++ tailWord_3693162).sum := by decide
  have hdescent : baseEnd_3693162 < baseStart_3693162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693195 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 1, 7]
def baseStart_3693195 : Nat := 118140960795 + 3693195 * 2 ^ 59
def prefixEnd_3693195 : Nat := 4983230072969 + 3 ^ 40 * 3693195 * 2
def baseEnd_3693195 : Nat := 632128061927261030425937

theorem tailTrace_3693195 : CollatzResearch.WordTrace tailWord_3693195 prefixEnd_3693195 632128061927261030425937 := by
  unfold tailWord_3693195
  simp only [CollatzResearch.WordTrace]
  refine ⟨134701887855192737334737039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89801258570128491556491359 134701887855192737334737039)
  ·
    refine ⟨202052831782789106002105559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134701887855192737334737039 202052831782789106002105559)
    ·
      refine ⟨303079247674183659003158339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202052831782789106002105559 303079247674183659003158339)
      ·
        refine ⟨454618871511275488504737509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303079247674183659003158339 454618871511275488504737509)
        ·
          refine ⟨85241038408364154094638283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454618871511275488504737509 85241038408364154094638283)
          ·
            refine ⟨127861557612546231141957425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85241038408364154094638283 127861557612546231141957425)
            ·
              refine ⟨95896168209409673356468069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127861557612546231141957425 95896168209409673356468069)
              ·
                refine ⟨17980531539264313754337763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95896168209409673356468069 17980531539264313754337763)
                ·
                  refine ⟨26970797308896470631506645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17980531539264313754337763 26970797308896470631506645)
                  ·
                    refine ⟨632128061927261030425937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26970797308896470631506645 632128061927261030425937)
                    ·
                      rfl

theorem cell23_3693195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 7].length) (baseStart_3693195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693195 prefixEnd_3693195 := by exact prefixLift 3693195
  have htrace : WordTrace (prefixWord ++ tailWord_3693195) baseStart_3693195 baseEnd_3693195 := by
    simpa [prefixWord, tailWord_3693195, baseEnd_3693195] using wordTrace_append hprefix tailTrace_3693195
  have hstable : (prefixWord ++ tailWord_3693195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693195).length < 2 ^ (prefixWord ++ tailWord_3693195).sum := by decide
  have hdescent : baseEnd_3693195 < baseStart_3693195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693229 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3693229 : Nat := 118140960795 + 3693229 * 2 ^ 59
def prefixEnd_3693229 : Nat := 4983230072969 + 3 ^ 40 * 3693229 * 2
def baseEnd_3693229 : Nat := 632133881374678652750885

theorem tailTrace_3693229 : CollatzResearch.WordTrace tailWord_3693229 prefixEnd_3693229 632133881374678652750885 := by
  unfold tailWord_3693229
  simp only [CollatzResearch.WordTrace]
  refine ⟨134703127937069561141474741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89802085291379707427649827 134703127937069561141474741)
  ·
    refine ⟨12628418244100271357013257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134703127937069561141474741 12628418244100271357013257)
    ·
      refine ⟨9471313683075203517759943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12628418244100271357013257 9471313683075203517759943)
      ·
        refine ⟨14206970524612805276639915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9471313683075203517759943 14206970524612805276639915)
        ·
          refine ⟨21310455786919207914959873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14206970524612805276639915 21310455786919207914959873)
          ·
            refine ⟨15982841840189405936219905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21310455786919207914959873 15982841840189405936219905)
            ·
              refine ⟨11987131380142054452164929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15982841840189405936219905 11987131380142054452164929)
              ·
                refine ⟨8990348535106540839123697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11987131380142054452164929 8990348535106540839123697)
                ·
                  refine ⟨6742761401329905629342773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990348535106540839123697 6742761401329905629342773)
                  ·
                    refine ⟨632133881374678652750885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6742761401329905629342773 632133881374678652750885)
                    ·
                      rfl

theorem cell23_3693229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3693229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693229 prefixEnd_3693229 := by exact prefixLift 3693229
  have htrace : WordTrace (prefixWord ++ tailWord_3693229) baseStart_3693229 baseEnd_3693229 := by
    simpa [prefixWord, tailWord_3693229, baseEnd_3693229] using wordTrace_append hprefix tailTrace_3693229
  have hstable : (prefixWord ++ tailWord_3693229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693229).length < 2 ^ (prefixWord ++ tailWord_3693229).sum := by decide
  have hdescent : baseEnd_3693229 < baseStart_3693229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693309 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_3693309 : Nat := 118140960795 + 3693309 * 2 ^ 59
def prefixEnd_3693309 : Nat := 4983230072969 + 3 ^ 40 * 3693309 * 2
def baseEnd_3693309 : Nat := 1896442722576395645252287

theorem tailTrace_3693309 : CollatzResearch.WordTrace tailWord_3693309 prefixEnd_3693309 1896442722576395645252287 := by
  unfold tailWord_3693309
  simp only [CollatzResearch.WordTrace]
  refine ⟨134706045776779734804386981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89804030517853156536257987 134706045776779734804386981)
  ·
    refine ⟨25257383583146200275822559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134706045776779734804386981 25257383583146200275822559)
    ·
      refine ⟨37886075374719300413733839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25257383583146200275822559 37886075374719300413733839)
      ·
        refine ⟨56829113062078950620600759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37886075374719300413733839 56829113062078950620600759)
        ·
          refine ⟨85243669593118425930901139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56829113062078950620600759 85243669593118425930901139)
          ·
            refine ⟨127865504389677638896351709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85243669593118425930901139 127865504389677638896351709)
            ·
              refine ⟨47949564146129114586131891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127865504389677638896351709 47949564146129114586131891)
              ·
                refine ⟨71924346219193671879197837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47949564146129114586131891 71924346219193671879197837)
                ·
                  refine ⟨26971629832197626954699189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71924346219193671879197837 26971629832197626954699189)
                  ·
                    refine ⟨2528590296768527527003049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26971629832197626954699189 2528590296768527527003049)
                    ·
                      refine ⟨1896442722576395645252287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528590296768527527003049 1896442722576395645252287)
                      ·
                        rfl

theorem cell23_3693309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_3693309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693309 prefixEnd_3693309 := by exact prefixLift 3693309
  have htrace : WordTrace (prefixWord ++ tailWord_3693309) baseStart_3693309 baseEnd_3693309 := by
    simpa [prefixWord, tailWord_3693309, baseEnd_3693309] using wordTrace_append hprefix tailTrace_3693309
  have hstable : (prefixWord ++ tailWord_3693309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693309).length < 2 ^ (prefixWord ++ tailWord_3693309).sum := by decide
  have hdescent : baseEnd_3693309 < baseStart_3693309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693316 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3693316 : Nat := 118140960795 + 3693316 * 2 ^ 59
def prefixEnd_3693316 : Nat := 4983230072969 + 3 ^ 40 * 3693316 * 2
def baseEnd_3693316 : Nat := 1896446316940977117864755

theorem tailTrace_3693316 : CollatzResearch.WordTrace tailWord_3693316 prefixEnd_3693316 1896446316940977117864755 := by
  unfold tailWord_3693316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67353150543877187499945901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89804200725169583333261201 67353150543877187499945901)
  ·
    refine ⟨25257431453953945312479713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67353150543877187499945901 25257431453953945312479713)
    ·
      refine ⟨18943073590465458984359785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25257431453953945312479713 18943073590465458984359785)
      ·
        refine ⟨14207305192849094238269839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18943073590465458984359785 14207305192849094238269839)
        ·
          refine ⟨21310957789273641357404759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14207305192849094238269839 21310957789273641357404759)
          ·
            refine ⟨31966436683910462036107139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21310957789273641357404759 31966436683910462036107139)
            ·
              refine ⟨47949655025865693054160709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31966436683910462036107139 47949655025865693054160709)
              ·
                refine ⟨8990560317349817447655133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47949655025865693054160709 8990560317349817447655133)
                ·
                  refine ⟨3371460119006181542870675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8990560317349817447655133 3371460119006181542870675)
                  ·
                    refine ⟨5057190178509272314306013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3371460119006181542870675 5057190178509272314306013)
                    ·
                      refine ⟨1896446316940977117864755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5057190178509272314306013 1896446316940977117864755)
                      ·
                        rfl

theorem cell23_3693316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3693316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693316 prefixEnd_3693316 := by exact prefixLift 3693316
  have htrace : WordTrace (prefixWord ++ tailWord_3693316) baseStart_3693316 baseEnd_3693316 := by
    simpa [prefixWord, tailWord_3693316, baseEnd_3693316] using wordTrace_append hprefix tailTrace_3693316
  have hstable : (prefixWord ++ tailWord_3693316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693316).length < 2 ^ (prefixWord ++ tailWord_3693316).sum := by decide
  have hdescent : baseEnd_3693316 < baseStart_3693316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693326 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_3693326 : Nat := 118140960795 + 3693326 * 2 ^ 59
def prefixEnd_3693326 : Nat := 4983230072969 + 3 ^ 40 * 3693326 * 2
def baseEnd_3693326 : Nat := 1896451451747522078739709

theorem tailTrace_3693326 : CollatzResearch.WordTrace tailWord_3693326 prefixEnd_3693326 1896451451747522078739709 := by
  unfold tailWord_3693326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16838333227214768338469479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89804443878478764471837221 16838333227214768338469479)
  ·
    refine ⟨25257499840822152507704219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16838333227214768338469479 25257499840822152507704219)
    ·
      refine ⟨37886249761233228761556329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25257499840822152507704219 37886249761233228761556329)
      ·
        refine ⟨28414687320924921571167247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37886249761233228761556329 28414687320924921571167247)
        ·
          refine ⟨42622030981387382356750871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28414687320924921571167247 42622030981387382356750871)
          ·
            refine ⟨63933046472081073535126307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42622030981387382356750871 63933046472081073535126307)
            ·
              refine ⟨95899569708121610302689461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63933046472081073535126307 95899569708121610302689461)
              ·
                refine ⟨8990584660136400965877137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95899569708121610302689461 8990584660136400965877137)
                ·
                  refine ⟨6742938495102300724407853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8990584660136400965877137 6742938495102300724407853)
                  ·
                    refine ⟨2528601935663362771652945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6742938495102300724407853 2528601935663362771652945)
                    ·
                      refine ⟨1896451451747522078739709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528601935663362771652945 1896451451747522078739709)
                      ·
                        rfl

theorem cell23_3693326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_3693326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693326 prefixEnd_3693326 := by exact prefixLift 3693326
  have htrace : WordTrace (prefixWord ++ tailWord_3693326) baseStart_3693326 baseEnd_3693326 := by
    simpa [prefixWord, tailWord_3693326, baseEnd_3693326] using wordTrace_append hprefix tailTrace_3693326
  have hstable : (prefixWord ++ tailWord_3693326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693326).length < 2 ^ (prefixWord ++ tailWord_3693326).sum := by decide
  have hdescent : baseEnd_3693326 < baseStart_3693326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693349 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_3693349 : Nat := 118140960795 + 3693349 * 2 ^ 59
def prefixEnd_3693349 : Nat := 4983230072969 + 3 ^ 40 * 3693349 * 2
def baseEnd_3693349 : Nat := 632154420600858496250701

theorem tailTrace_3693349 : CollatzResearch.WordTrace tailWord_3693349 prefixEnd_3693349 632154420600858496250701 := by
  unfold tailWord_3693349
  simp only [CollatzResearch.WordTrace]
  refine ⟨134707504696634821635843101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89805003131089881090562067 134707504696634821635843101)
  ·
    refine ⟨50515314261238058113441163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134707504696634821635843101 50515314261238058113441163)
    ·
      refine ⟨75772971391857087170161745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50515314261238058113441163 75772971391857087170161745)
      ·
        refine ⟨56829728543892815377621309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75772971391857087170161745 56829728543892815377621309)
        ·
          refine ⟨21311148203959805766607991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56829728543892815377621309 21311148203959805766607991)
          ·
            refine ⟨31966722305939708649911987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21311148203959805766607991 31966722305939708649911987)
            ·
              refine ⟨47950083458909562974867981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31966722305939708649911987 47950083458909562974867981)
              ·
                refine ⟨17981281297091086115575493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47950083458909562974867981 17981281297091086115575493)
                ·
                  refine ⟨3371490243204578646670405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17981281297091086115575493 3371490243204578646670405)
                  ·
                    refine ⟨632154420600858496250701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371490243204578646670405 632154420600858496250701)
                    ·
                      rfl

theorem cell23_3693349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_3693349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693349 prefixEnd_3693349 := by exact prefixLift 3693349
  have htrace : WordTrace (prefixWord ++ tailWord_3693349) baseStart_3693349 baseEnd_3693349 := by
    simpa [prefixWord, tailWord_3693349, baseEnd_3693349] using wordTrace_append hprefix tailTrace_3693349
  have hstable : (prefixWord ++ tailWord_3693349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693349).length < 2 ^ (prefixWord ++ tailWord_3693349).sum := by decide
  have hdescent : baseEnd_3693349 < baseStart_3693349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693357 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3693357 : Nat := 118140960795 + 3693357 * 2 ^ 59
def prefixEnd_3693357 : Nat := 4983230072969 + 3 ^ 40 * 3693357 * 2
def baseEnd_3693357 : Nat := 210718596627534606383563

theorem tailTrace_3693357 : CollatzResearch.WordTrace tailWord_3693357 prefixEnd_3693357 210718596627534606383563 := by
  unfold tailWord_3693357
  simp only [CollatzResearch.WordTrace]
  refine ⟨134707796480605839002134325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89805197653737226001422883 134707796480605839002134325)
  ·
    refine ⟨12628855920056797406450093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134707796480605839002134325 12628855920056797406450093)
    ·
      refine ⟨4735820970021299027418785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12628855920056797406450093 4735820970021299027418785)
      ·
        refine ⟨3551865727515974270564089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4735820970021299027418785 3551865727515974270564089)
        ·
          refine ⟨2663899295636980702923067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3551865727515974270564089 2663899295636980702923067)
          ·
            refine ⟨3995848943455471054384601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663899295636980702923067 3995848943455471054384601)
            ·
              refine ⟨2996886707591603290788451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3995848943455471054384601 2996886707591603290788451)
              ·
                refine ⟨4495330061387404936182677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2996886707591603290788451 4495330061387404936182677)
                ·
                  refine ⟨210718596627534606383563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4495330061387404936182677 210718596627534606383563)
                  ·
                    rfl

theorem cell23_3693357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3693357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693357 prefixEnd_3693357 := by exact prefixLift 3693357
  have htrace : WordTrace (prefixWord ++ tailWord_3693357) baseStart_3693357 baseEnd_3693357 := by
    simpa [prefixWord, tailWord_3693357, baseEnd_3693357] using wordTrace_append hprefix tailTrace_3693357
  have hstable : (prefixWord ++ tailWord_3693357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693357).length < 2 ^ (prefixWord ++ tailWord_3693357).sum := by decide
  have hdescent : baseEnd_3693357 < baseStart_3693357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693393 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 1, 1, 5]
def baseStart_3693393 : Nat := 118140960795 + 3693393 * 2 ^ 59
def prefixEnd_3693393 : Nat := 4983230072969 + 3 ^ 40 * 3693393 * 2
def baseEnd_3693393 : Nat := 1896485854951373316601901

theorem tailTrace_3693393 : CollatzResearch.WordTrace tailWord_3693393 prefixEnd_3693393 1896485854951373316601901 := by
  unfold tailWord_3693393
  simp only [CollatzResearch.WordTrace]
  refine ⟨134709109508475417150444833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89806073005650278100296555 134709109508475417150444833)
  ·
    refine ⟨101031832131356562862833625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134709109508475417150444833 101031832131356562862833625)
    ·
      refine ⟨75773874098517422147125219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101031832131356562862833625 75773874098517422147125219)
      ·
        refine ⟨113660811147776133220687829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75773874098517422147125219 113660811147776133220687829)
        ·
          refine ⟨2663925261276003122359871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113660811147776133220687829 2663925261276003122359871)
          ·
            refine ⟨3995887891914004683539807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663925261276003122359871 3995887891914004683539807)
            ·
              refine ⟨5993831837871007025309711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995887891914004683539807 5993831837871007025309711)
              ·
                refine ⟨8990747756806510537964567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5993831837871007025309711 8990747756806510537964567)
                ·
                  refine ⟨13486121635209765806946851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8990747756806510537964567 13486121635209765806946851)
                  ·
                    refine ⟨20229182452814648710420277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13486121635209765806946851 20229182452814648710420277)
                    ·
                      refine ⟨1896485854951373316601901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20229182452814648710420277 1896485854951373316601901)
                      ·
                        rfl

theorem cell23_3693393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_3693393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693393 prefixEnd_3693393 := by exact prefixLift 3693393
  have htrace : WordTrace (prefixWord ++ tailWord_3693393) baseStart_3693393 baseEnd_3693393 := by
    simpa [prefixWord, tailWord_3693393, baseEnd_3693393] using wordTrace_append hprefix tailTrace_3693393
  have hstable : (prefixWord ++ tailWord_3693393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693393).length < 2 ^ (prefixWord ++ tailWord_3693393).sum := by decide
  have hdescent : baseEnd_3693393 < baseStart_3693393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693450 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_3693450 : Nat := 118140960795 + 3693450 * 2 ^ 59
def prefixEnd_3693450 : Nat := 4983230072969 + 3 ^ 40 * 3693450 * 2
def baseEnd_3693450 : Nat := 1896515123348679593589139

theorem tailTrace_3693450 : CollatzResearch.WordTrace tailWord_3693450 prefixEnd_3693450 1896515123348679593589139 := by
  unfold tailWord_3693450
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677797117317228971317451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89807458979512610590179869 33677797117317228971317451)
  ·
    refine ⟨50516695675975843456976177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33677797117317228971317451 50516695675975843456976177)
    ·
      refine ⟨37887521756981882592732133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50516695675975843456976177 37887521756981882592732133)
      ·
        refine ⟨7103910329434102986137275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37887521756981882592732133 7103910329434102986137275)
        ·
          refine ⟨10655865494151154479205913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7103910329434102986137275 10655865494151154479205913)
          ·
            refine ⟨7991899120613365859404435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10655865494151154479205913 7991899120613365859404435)
            ·
              refine ⟨11987848680920048789106653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7991899120613365859404435 11987848680920048789106653)
              ·
                refine ⟨4495443255345018295914995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11987848680920048789106653 4495443255345018295914995)
                ·
                  refine ⟨6743164883017527443872493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495443255345018295914995 6743164883017527443872493)
                  ·
                    refine ⟨2528686831131572791452185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6743164883017527443872493 2528686831131572791452185)
                    ·
                      refine ⟨1896515123348679593589139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528686831131572791452185 1896515123348679593589139)
                      ·
                        rfl

theorem cell23_3693450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_3693450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693450 prefixEnd_3693450 := by exact prefixLift 3693450
  have htrace : WordTrace (prefixWord ++ tailWord_3693450) baseStart_3693450 baseEnd_3693450 := by
    simpa [prefixWord, tailWord_3693450, baseEnd_3693450] using wordTrace_append hprefix tailTrace_3693450
  have hstable : (prefixWord ++ tailWord_3693450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693450).length < 2 ^ (prefixWord ++ tailWord_3693450).sum := by decide
  have hdescent : baseEnd_3693450 < baseStart_3693450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693463 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 4, 2, 2]
def baseStart_3693463 : Nat := 118140960795 + 3693463 * 2 ^ 59
def prefixEnd_3693463 : Nat := 4983230072969 + 3 ^ 40 * 3693463 * 2
def baseEnd_3693463 : Nat := 1896521798597188042726579

theorem tailTrace_3693463 : CollatzResearch.WordTrace tailWord_3693463 prefixEnd_3693463 1896521798597188042726579 := by
  unfold tailWord_3693463
  simp only [CollatzResearch.WordTrace]
  refine ⟨134711662618221819105493043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89807775078814546070328695 134711662618221819105493043)
  ·
    refine ⟨202067493927332728658239565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134711662618221819105493043 202067493927332728658239565)
    ·
      refine ⟨75775310222749773246839837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202067493927332728658239565 75775310222749773246839837)
      ·
        refine ⟨28415741333531164967564939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75775310222749773246839837 28415741333531164967564939)
        ·
          refine ⟨42623612000296747451347409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28415741333531164967564939 42623612000296747451347409)
          ·
            refine ⟨31967709000222560588510557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42623612000296747451347409 31967709000222560588510557)
            ·
              refine ⟨11987890875083460220691459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31967709000222560588510557 11987890875083460220691459)
              ·
                refine ⟨17981836312625190331037189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11987890875083460220691459 17981836312625190331037189)
                ·
                  refine ⟨3371594308617223187069473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17981836312625190331037189 3371594308617223187069473)
                  ·
                    refine ⟨2528695731462917390302105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3371594308617223187069473 2528695731462917390302105)
                    ·
                      refine ⟨1896521798597188042726579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528695731462917390302105 1896521798597188042726579)
                      ·
                        rfl

theorem cell23_3693463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_3693463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693463 prefixEnd_3693463 := by exact prefixLift 3693463
  have htrace : WordTrace (prefixWord ++ tailWord_3693463) baseStart_3693463 baseEnd_3693463 := by
    simpa [prefixWord, tailWord_3693463, baseEnd_3693463] using wordTrace_append hprefix tailTrace_3693463
  have hstable : (prefixWord ++ tailWord_3693463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693463).length < 2 ^ (prefixWord ++ tailWord_3693463).sum := by decide
  have hdescent : baseEnd_3693463 < baseStart_3693463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693516 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 2, 5]
def baseStart_3693516 : Nat := 118140960795 + 3693516 * 2 ^ 59
def prefixEnd_3693516 : Nat := 4983230072969 + 3 ^ 40 * 3693516 * 2
def baseEnd_3693516 : Nat := 632183004357292111787945

theorem tailTrace_3693516 : CollatzResearch.WordTrace tailWord_3693516 prefixEnd_3693516 632183004357292111787945 := by
  unfold tailWord_3693516
  simp only [CollatzResearch.WordTrace]
  refine ⟨67356797843514904578586201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89809063791353206104781601 67356797843514904578586201)
  ·
    refine ⟨50517598382636178433939651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67356797843514904578586201 50517598382636178433939651)
    ·
      refine ⟨75776397573954267650909477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50517598382636178433939651 75776397573954267650909477)
      ·
        refine ⟨14208074545116425184545527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75776397573954267650909477 14208074545116425184545527)
        ·
          refine ⟨21312111817674637776818291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14208074545116425184545527 21312111817674637776818291)
          ·
            refine ⟨31968167726511956665227437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21312111817674637776818291 31968167726511956665227437)
            ·
              refine ⟨11988062897441983749460289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31968167726511956665227437 11988062897441983749460289)
              ·
                refine ⟨8991047173081487812095217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11988062897441983749460289 8991047173081487812095217)
                ·
                  refine ⟨6743285379811115859071413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8991047173081487812095217 6743285379811115859071413)
                  ·
                    refine ⟨632183004357292111787945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6743285379811115859071413 632183004357292111787945)
                    ·
                      rfl

theorem cell23_3693516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_3693516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693516 prefixEnd_3693516 := by exact prefixLift 3693516
  have htrace : WordTrace (prefixWord ++ tailWord_3693516) baseStart_3693516 baseEnd_3693516 := by
    simpa [prefixWord, tailWord_3693516, baseEnd_3693516] using wordTrace_append hprefix tailTrace_3693516
  have hstable : (prefixWord ++ tailWord_3693516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693516).length < 2 ^ (prefixWord ++ tailWord_3693516).sum := by decide
  have hdescent : baseEnd_3693516 < baseStart_3693516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693553 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_3693553 : Nat := 118140960795 + 3693553 * 2 ^ 59
def prefixEnd_3693553 : Nat := 4983230072969 + 3 ^ 40 * 3693553 * 2
def baseEnd_3693553 : Nat := 1896568011856092690601165

theorem tailTrace_3693553 : CollatzResearch.WordTrace tailWord_3693553 prefixEnd_3693553 1896568011856092690601165 := by
  unfold tailWord_3693553
  simp only [CollatzResearch.WordTrace]
  refine ⟨134714945187895764476269313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89809963458597176317512875 134714945187895764476269313)
  ·
    refine ⟨101036208890921823357201985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134714945187895764476269313 101036208890921823357201985)
    ·
      refine ⟨75777156668191367517901489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101036208890921823357201985 75777156668191367517901489)
      ·
        refine ⟨56832867501143525638426117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75777156668191367517901489 56832867501143525638426117)
        ·
          refine ⟨10656162656464411057204897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56832867501143525638426117 10656162656464411057204897)
          ·
            refine ⟨7992121992348308292903673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10656162656464411057204897 7992121992348308292903673)
            ·
              refine ⟨5994091494261231219677755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7992121992348308292903673 5994091494261231219677755)
              ·
                refine ⟨8991137241391846829516633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994091494261231219677755 8991137241391846829516633)
                ·
                  refine ⟨6743352931043885122137475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8991137241391846829516633 6743352931043885122137475)
                  ·
                    refine ⟨10115029396565827683206213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6743352931043885122137475 10115029396565827683206213)
                    ·
                      refine ⟨1896568011856092690601165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10115029396565827683206213 1896568011856092690601165)
                      ·
                        rfl

theorem cell23_3693553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_3693553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693553 prefixEnd_3693553 := by exact prefixLift 3693553
  have htrace : WordTrace (prefixWord ++ tailWord_3693553) baseStart_3693553 baseEnd_3693553 := by
    simpa [prefixWord, tailWord_3693553, baseEnd_3693553] using wordTrace_append hprefix tailTrace_3693553
  have hstable : (prefixWord ++ tailWord_3693553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693553).length < 2 ^ (prefixWord ++ tailWord_3693553).sum := by decide
  have hdescent : baseEnd_3693553 < baseStart_3693553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693563 : List Nat := [1, 1, 1, 1, 1, 3, 3, 7, 1, 4]
def baseStart_3693563 : Nat := 118140960795 + 3693563 * 2 ^ 59
def prefixEnd_3693563 : Nat := 4983230072969 + 3 ^ 40 * 3693563 * 2
def baseEnd_3693563 : Nat := 632191048887545883825373

theorem tailTrace_3693563 : CollatzResearch.WordTrace tailWord_3693563 prefixEnd_3693563 632191048887545883825373 := by
  unfold tailWord_3693563
  simp only [CollatzResearch.WordTrace]
  refine ⟨134715309917859536184133343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89810206611906357456088895 134715309917859536184133343)
  ·
    refine ⟨202072964876789304276200015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134715309917859536184133343 202072964876789304276200015)
    ·
      refine ⟨303109447315183956414300023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202072964876789304276200015 303109447315183956414300023)
      ·
        refine ⟨454664170972775934621450035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303109447315183956414300023 454664170972775934621450035)
        ·
          refine ⟨681996256459163901932175053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454664170972775934621450035 681996256459163901932175053)
          ·
            refine ⟨255748596172186463224565645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 681996256459163901932175053 255748596172186463224565645)
            ·
              refine ⟨95905723564569923709212117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255748596172186463224565645 95905723564569923709212117)
              ·
                refine ⟨2247790396044607586934659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95905723564569923709212117 2247790396044607586934659)
                ·
                  refine ⟨3371685594066911380401989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247790396044607586934659 3371685594066911380401989)
                  ·
                    refine ⟨632191048887545883825373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371685594066911380401989 632191048887545883825373)
                    ·
                      rfl

theorem cell23_3693563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 4].length) (baseStart_3693563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693563 prefixEnd_3693563 := by exact prefixLift 3693563
  have htrace : WordTrace (prefixWord ++ tailWord_3693563) baseStart_3693563 baseEnd_3693563 := by
    simpa [prefixWord, tailWord_3693563, baseEnd_3693563] using wordTrace_append hprefix tailTrace_3693563
  have hstable : (prefixWord ++ tailWord_3693563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693563).length < 2 ^ (prefixWord ++ tailWord_3693563).sum := by decide
  have hdescent : baseEnd_3693563 < baseStart_3693563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693576 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 6]
def baseStart_3693576 : Nat := 118140960795 + 3693576 * 2 ^ 59
def prefixEnd_3693576 : Nat := 4983230072969 + 3 ^ 40 * 3693576 * 2
def baseEnd_3693576 : Nat := 210731091323460677845951

theorem tailTrace_3693576 : CollatzResearch.WordTrace tailWord_3693576 prefixEnd_3693576 210731091323460677845951 := by
  unfold tailWord_3693576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67357892033406219702178291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89810522711208292936237721 67357892033406219702178291)
  ·
    refine ⟨101036838050109329553267437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67357892033406219702178291 101036838050109329553267437)
    ·
      refine ⟨37888814268790998582475289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101036838050109329553267437 37888814268790998582475289)
      ·
        refine ⟨28416610701593248936856467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37888814268790998582475289 28416610701593248936856467)
        ·
          refine ⟨42624916052389873405284701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28416610701593248936856467 42624916052389873405284701)
          ·
            refine ⟨15984343519646202526981763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42624916052389873405284701 15984343519646202526981763)
            ·
              refine ⟨23976515279469303790472645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15984343519646202526981763 23976515279469303790472645)
              ·
                refine ⟨4495596614900494460713621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23976515279469303790472645 4495596614900494460713621)
                ·
                  refine ⟨210731091323460677845951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4495596614900494460713621 210731091323460677845951)
                  ·
                    rfl

theorem cell23_3693576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 6].length) (baseStart_3693576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693576 prefixEnd_3693576 := by exact prefixLift 3693576
  have htrace : WordTrace (prefixWord ++ tailWord_3693576) baseStart_3693576 baseEnd_3693576 := by
    simpa [prefixWord, tailWord_3693576, baseEnd_3693576] using wordTrace_append hprefix tailTrace_3693576
  have hstable : (prefixWord ++ tailWord_3693576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693576).length < 2 ^ (prefixWord ++ tailWord_3693576).sum := by decide
  have hdescent : baseEnd_3693576 < baseStart_3693576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693580 : List Nat := [2, 2, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_3693580 : Nat := 118140960795 + 3693580 * 2 ^ 59
def prefixEnd_3693580 : Nat := 4983230072969 + 3 ^ 40 * 3693580 * 2
def baseEnd_3693580 : Nat := 632193958611254694987847

theorem tailTrace_3693580 : CollatzResearch.WordTrace tailWord_3693580 prefixEnd_3693580 632193958611254694987847 := by
  unfold tailWord_3693580
  simp only [CollatzResearch.WordTrace]
  refine ⟨67357964979398974043751097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89810619972531965391668129 67357964979398974043751097)
  ·
    refine ⟨50518473734549230532813323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67357964979398974043751097 50518473734549230532813323)
    ·
      refine ⟨75777710601823845799219985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50518473734549230532813323 75777710601823845799219985)
      ·
        refine ⟨56833282951367884349414989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75777710601823845799219985 56833282951367884349414989)
        ·
          refine ⟨21312481106762956631030621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56833282951367884349414989 21312481106762956631030621)
          ·
            refine ⟨7992180415036108736636483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21312481106762956631030621 7992180415036108736636483)
            ·
              refine ⟨11988270622554163104954725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992180415036108736636483 11988270622554163104954725)
              ·
                refine ⟨2247800741728905582179011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11988270622554163104954725 2247800741728905582179011)
                ·
                  refine ⟨3371701112593358373268517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247800741728905582179011 3371701112593358373268517)
                  ·
                    refine ⟨632193958611254694987847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371701112593358373268517 632193958611254694987847)
                    ·
                      rfl

theorem cell23_3693580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_3693580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693580 prefixEnd_3693580 := by exact prefixLift 3693580
  have htrace : WordTrace (prefixWord ++ tailWord_3693580) baseStart_3693580 baseEnd_3693580 := by
    simpa [prefixWord, tailWord_3693580, baseEnd_3693580] using wordTrace_append hprefix tailTrace_3693580
  have hstable : (prefixWord ++ tailWord_3693580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693580).length < 2 ^ (prefixWord ++ tailWord_3693580).sum := by decide
  have hdescent : baseEnd_3693580 < baseStart_3693580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693603 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 3]
def baseStart_3693603 : Nat := 118140960795 + 3693603 * 2 ^ 59
def prefixEnd_3693603 : Nat := 4983230072969 + 3 ^ 40 * 3693603 * 2
def baseEnd_3693603 : Nat := 1896593685888817494975935

theorem tailTrace_3693603 : CollatzResearch.WordTrace tailWord_3693603 prefixEnd_3693603 1896593685888817494975935 := by
  unfold tailWord_3693603
  simp only [CollatzResearch.WordTrace]
  refine ⟨134716768837714623015589463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89811179225143082010392975 134716768837714623015589463)
  ·
    refine ⟨202075153256571934523384195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134716768837714623015589463 202075153256571934523384195)
    ·
      refine ⟨303112729884857901785076293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202075153256571934523384195 303112729884857901785076293)
      ·
        refine ⟨56833636853410856584701805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303112729884857901785076293 56833636853410856584701805)
        ·
          refine ⟨21312613820029071219263177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56833636853410856584701805 21312613820029071219263177)
          ·
            refine ⟨15984460365021803414447383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21312613820029071219263177 15984460365021803414447383)
            ·
              refine ⟨23976690547532705121671075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15984460365021803414447383 23976690547532705121671075)
              ·
                refine ⟨35965035821299057682506613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23976690547532705121671075 35965035821299057682506613)
                ·
                  refine ⟨3371722108246786657734995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35965035821299057682506613 3371722108246786657734995)
                  ·
                    refine ⟨5057583162370179986602493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3371722108246786657734995 5057583162370179986602493)
                    ·
                      refine ⟨1896593685888817494975935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5057583162370179986602493 1896593685888817494975935)
                      ·
                        rfl

theorem cell23_3693603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_3693603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693603 prefixEnd_3693603 := by exact prefixLift 3693603
  have htrace : WordTrace (prefixWord ++ tailWord_3693603) baseStart_3693603 baseEnd_3693603 := by
    simpa [prefixWord, tailWord_3693603, baseEnd_3693603] using wordTrace_append hprefix tailTrace_3693603
  have hstable : (prefixWord ++ tailWord_3693603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693603).length < 2 ^ (prefixWord ++ tailWord_3693603).sum := by decide
  have hdescent : baseEnd_3693603 < baseStart_3693603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693607 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3693607 : Nat := 118140960795 + 3693607 * 2 ^ 59
def prefixEnd_3693607 : Nat := 4983230072969 + 3 ^ 40 * 3693607 * 2
def baseEnd_3693607 : Nat := 1896595739811435479325917

theorem tailTrace_3693607 : CollatzResearch.WordTrace tailWord_3693607 prefixEnd_3693607 1896595739811435479325917 := by
  unfold tailWord_3693607
  simp only [CollatzResearch.WordTrace]
  refine ⟨134716914729700131698735075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89811276486466754465823383 134716914729700131698735075)
  ·
    refine ⟨202075372094550197548102613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134716914729700131698735075 202075372094550197548102613)
    ·
      refine ⟨4736141533466020255033655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 202075372094550197548102613 4736141533466020255033655)
      ·
        refine ⟨7104212300199030382550483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736141533466020255033655 7104212300199030382550483)
        ·
          refine ⟨10656318450298545573825725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104212300199030382550483 10656318450298545573825725)
          ·
            refine ⟨3996119418861954590184647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10656318450298545573825725 3996119418861954590184647)
            ·
              refine ⟨5994179128292931885276971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996119418861954590184647 5994179128292931885276971)
              ·
                refine ⟨8991268692439397827915457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994179128292931885276971 8991268692439397827915457)
                ·
                  refine ⟨6743451519329548370936593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8991268692439397827915457 6743451519329548370936593)
                  ·
                    refine ⟨5057588639497161278202445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6743451519329548370936593 5057588639497161278202445)
                    ·
                      refine ⟨1896595739811435479325917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5057588639497161278202445 1896595739811435479325917)
                      ·
                        rfl

theorem cell23_3693607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3693607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693607 prefixEnd_3693607 := by exact prefixLift 3693607
  have htrace : WordTrace (prefixWord ++ tailWord_3693607) baseStart_3693607 baseEnd_3693607 := by
    simpa [prefixWord, tailWord_3693607, baseEnd_3693607] using wordTrace_append hprefix tailTrace_3693607
  have hstable : (prefixWord ++ tailWord_3693607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693607).length < 2 ^ (prefixWord ++ tailWord_3693607).sum := by decide
  have hdescent : baseEnd_3693607 < baseStart_3693607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693656 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3693656 : Nat := 118140960795 + 3693656 * 2 ^ 59
def prefixEnd_3693656 : Nat := 4983230072969 + 3 ^ 40 * 3693656 * 2
def baseEnd_3693656 : Nat := 1896620900363505787613191

theorem tailTrace_3693656 : CollatzResearch.WordTrace tailWord_3693656 prefixEnd_3693656 1896620900363505787613191 := by
  unfold tailWord_3693656
  simp only [CollatzResearch.WordTrace]
  refine ⟨67359350953261306533634411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89812467937681742044845881 67359350953261306533634411)
  ·
    refine ⟨101039026429891959800451617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67359350953261306533634411 101039026429891959800451617)
    ·
      refine ⟨75779269822418969850338713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101039026429891959800451617 75779269822418969850338713)
      ·
        refine ⟨56834452366814227387754035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75779269822418969850338713 56834452366814227387754035)
        ·
          refine ⟨85251678550221341081631053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56834452366814227387754035 85251678550221341081631053)
          ·
            refine ⟨31969379456333002905611645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85251678550221341081631053 31969379456333002905611645)
            ·
              refine ⟨11988517296124876089604367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31969379456333002905611645 11988517296124876089604367)
              ·
                refine ⟨17982775944187314134406551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11988517296124876089604367 17982775944187314134406551)
                ·
                  refine ⟨26974163916280971201609827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17982775944187314134406551 26974163916280971201609827)
                  ·
                    refine ⟨40461245874421456802414741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26974163916280971201609827 40461245874421456802414741)
                    ·
                      refine ⟨1896620900363505787613191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40461245874421456802414741 1896620900363505787613191)
                      ·
                        rfl

theorem cell23_3693656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3693656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693656 prefixEnd_3693656 := by exact prefixLift 3693656
  have htrace : WordTrace (prefixWord ++ tailWord_3693656) baseStart_3693656 baseEnd_3693656 := by
    simpa [prefixWord, tailWord_3693656, baseEnd_3693656] using wordTrace_append hprefix tailTrace_3693656
  have hstable : (prefixWord ++ tailWord_3693656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693656).length < 2 ^ (prefixWord ++ tailWord_3693656).sum := by decide
  have hdescent : baseEnd_3693656 < baseStart_3693656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693660 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3693660 : Nat := 118140960795 + 3693660 * 2 ^ 59
def prefixEnd_3693660 : Nat := 4983230072969 + 3 ^ 40 * 3693660 * 2
def baseEnd_3693660 : Nat := 1896622954286123771963173

theorem tailTrace_3693660 : CollatzResearch.WordTrace tailWord_3693660 prefixEnd_3693660 1896622954286123771963173 := by
  unfold tailWord_3693660
  simp only [CollatzResearch.WordTrace]
  refine ⟨67359423899254060875207217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89812565199005414500276289 67359423899254060875207217)
  ·
    refine ⟨50519567924440545656405413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67359423899254060875207217 50519567924440545656405413)
    ·
      refine ⟨9472418985832602310576015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50519567924440545656405413 9472418985832602310576015)
      ·
        refine ⟨14208628478748903465864023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9472418985832602310576015 14208628478748903465864023)
        ·
          refine ⟨21312942718123355198796035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14208628478748903465864023 21312942718123355198796035)
          ·
            refine ⟨31969414077185032798194053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21312942718123355198796035 31969414077185032798194053)
            ·
              refine ⟨5994265139472193649661385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31969414077185032798194053 5994265139472193649661385)
              ·
                refine ⟨4495698854604145237246039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994265139472193649661385 4495698854604145237246039)
                ·
                  refine ⟨6743548281906217855869059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495698854604145237246039 6743548281906217855869059)
                  ·
                    refine ⟨10115322422859326783803589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6743548281906217855869059 10115322422859326783803589)
                    ·
                      refine ⟨1896622954286123771963173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10115322422859326783803589 1896622954286123771963173)
                      ·
                        rfl

theorem cell23_3693660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3693660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693660 prefixEnd_3693660 := by exact prefixLift 3693660
  have htrace : WordTrace (prefixWord ++ tailWord_3693660) baseStart_3693660 baseEnd_3693660 := by
    simpa [prefixWord, tailWord_3693660, baseEnd_3693660] using wordTrace_append hprefix tailTrace_3693660
  have hstable : (prefixWord ++ tailWord_3693660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693660).length < 2 ^ (prefixWord ++ tailWord_3693660).sum := by decide
  have hdescent : baseEnd_3693660 < baseStart_3693660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693703 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_3693703 : Nat := 118140960795 + 3693703 * 2 ^ 59
def prefixEnd_3693703 : Nat := 4983230072969 + 3 ^ 40 * 3693703 * 2
def baseEnd_3693703 : Nat := 1896645033954267103725475

theorem tailTrace_3693703 : CollatzResearch.WordTrace tailWord_3693703 prefixEnd_3693703 1896645033954267103725475 := by
  unfold tailWord_3693703
  simp only [CollatzResearch.WordTrace]
  refine ⟨134720416137352340094229763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89813610758234893396153175 134720416137352340094229763)
  ·
    refine ⟨202080624206028510141344645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134720416137352340094229763 202080624206028510141344645)
    ·
      refine ⟨37890117038630345651502121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202080624206028510141344645 37890117038630345651502121)
      ·
        refine ⟨28417587778972759238626591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37890117038630345651502121 28417587778972759238626591)
        ·
          refine ⟨42626381668459138857939887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28417587778972759238626591 42626381668459138857939887)
          ·
            refine ⟨63939572502688708286909831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42626381668459138857939887 63939572502688708286909831)
            ·
              refine ⟨95909358754033062430364747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63939572502688708286909831 95909358754033062430364747)
              ·
                refine ⟨143864038131049593645547121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95909358754033062430364747 143864038131049593645547121)
                ·
                  refine ⟨107898028598287195234160341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143864038131049593645547121 107898028598287195234160341)
                  ·
                    refine ⟨2528860045272356138300633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107898028598287195234160341 2528860045272356138300633)
                    ·
                      refine ⟨1896645033954267103725475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2528860045272356138300633 1896645033954267103725475)
                      ·
                        rfl

theorem cell23_3693703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_3693703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693703 prefixEnd_3693703 := by exact prefixLift 3693703
  have htrace : WordTrace (prefixWord ++ tailWord_3693703) baseStart_3693703 baseEnd_3693703 := by
    simpa [prefixWord, tailWord_3693703, baseEnd_3693703] using wordTrace_append hprefix tailTrace_3693703
  have hstable : (prefixWord ++ tailWord_3693703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693703).length < 2 ^ (prefixWord ++ tailWord_3693703).sum := by decide
  have hdescent : baseEnd_3693703 < baseStart_3693703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693704 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 2, 4]
def baseStart_3693704 : Nat := 118140960795 + 3693704 * 2 ^ 59
def prefixEnd_3693704 : Nat := 4983230072969 + 3 ^ 40 * 3693704 * 2
def baseEnd_3693704 : Nat := 632215182478307199937657

theorem tailTrace_3693704 : CollatzResearch.WordTrace tailWord_3693704 prefixEnd_3693704 632215182478307199937657 := by
  unfold tailWord_3693704
  simp only [CollatzResearch.WordTrace]
  refine ⟨67360226305174358632508083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89813635073565811510010777 67360226305174358632508083)
  ·
    refine ⟨101040339457761537948762125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67360226305174358632508083 101040339457761537948762125)
    ·
      refine ⟨37890127296660576730785797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101040339457761537948762125 37890127296660576730785797)
      ·
        refine ⟨7104398868123858137022337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37890127296660576730785797 7104398868123858137022337)
        ·
          refine ⟨5328299151092893602766753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7104398868123858137022337 5328299151092893602766753)
          ·
            refine ⟨3996224363319670202075065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5328299151092893602766753 3996224363319670202075065)
            ·
              refine ⟨2997168272489752651556299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996224363319670202075065 2997168272489752651556299)
              ·
                refine ⟨4495752408734628977334449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997168272489752651556299 4495752408734628977334449)
                ·
                  refine ⟨3371814306550971733000837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4495752408734628977334449 3371814306550971733000837)
                  ·
                    refine ⟨632215182478307199937657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3371814306550971733000837 632215182478307199937657)
                    ·
                      rfl

theorem cell23_3693704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_3693704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693704 prefixEnd_3693704 := by exact prefixLift 3693704
  have htrace : WordTrace (prefixWord ++ tailWord_3693704) baseStart_3693704 baseEnd_3693704 := by
    simpa [prefixWord, tailWord_3693704, baseEnd_3693704] using wordTrace_append hprefix tailTrace_3693704
  have hstable : (prefixWord ++ tailWord_3693704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693704).length < 2 ^ (prefixWord ++ tailWord_3693704).sum := by decide
  have hdescent : baseEnd_3693704 < baseStart_3693704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693753 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3693753 : Nat := 118140960795 + 3693753 * 2 ^ 59
def prefixEnd_3693753 : Nat := 4983230072969 + 3 ^ 40 * 3693753 * 2
def baseEnd_3693753 : Nat := 1896670707986991908100245

theorem tailTrace_3693753 : CollatzResearch.WordTrace tailWord_3693753 prefixEnd_3693753 1896670707986991908100245 := by
  unfold tailWord_3693753
  simp only [CollatzResearch.WordTrace]
  refine ⟨134722239787171198633549913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89814826524780799089033275 134722239787171198633549913)
  ·
    refine ⟨101041679840378398975162435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134722239787171198633549913 101041679840378398975162435)
    ·
      refine ⟨151562519760567598462743653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101041679840378398975162435 151562519760567598462743653)
      ·
        refine ⟨28417972455106424711764435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151562519760567598462743653 28417972455106424711764435)
        ·
          refine ⟨42626958682659637067646653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28417972455106424711764435 42626958682659637067646653)
          ·
            refine ⟨15985109505997363900367495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42626958682659637067646653 15985109505997363900367495)
            ·
              refine ⟨23977664258996045850551243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15985109505997363900367495 23977664258996045850551243)
              ·
                refine ⟨35966496388494068775826865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23977664258996045850551243 35966496388494068775826865)
                ·
                  refine ⟨26974872291370551581870149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35966496388494068775826865 26974872291370551581870149)
                  ·
                    refine ⟨5057788554631978421600653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26974872291370551581870149 5057788554631978421600653)
                    ·
                      refine ⟨1896670707986991908100245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5057788554631978421600653 1896670707986991908100245)
                      ·
                        rfl

theorem cell23_3693753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3693753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693753 prefixEnd_3693753 := by exact prefixLift 3693753
  have htrace : WordTrace (prefixWord ++ tailWord_3693753) baseStart_3693753 baseEnd_3693753 := by
    simpa [prefixWord, tailWord_3693753, baseEnd_3693753] using wordTrace_append hprefix tailTrace_3693753
  have hstable : (prefixWord ++ tailWord_3693753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693753).length < 2 ^ (prefixWord ++ tailWord_3693753).sum := by decide
  have hdescent : baseEnd_3693753 < baseStart_3693753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693823 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_3693823 : Nat := 118140960795 + 3693823 * 2 ^ 59
def prefixEnd_3693823 : Nat := 4983230072969 + 3 ^ 40 * 3693823 * 2
def baseEnd_3693823 : Nat := 1896706651632806634224923

theorem tailTrace_3693823 : CollatzResearch.WordTrace tailWord_3693823 prefixEnd_3693823 1896706651632806634224923 := by
  unfold tailWord_3693823
  simp only [CollatzResearch.WordTrace]
  refine ⟨134724792896917600588598123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89816528597945067059065415 134724792896917600588598123)
  ·
    refine ⟨202087189345376400882897185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134724792896917600588598123 202087189345376400882897185)
    ·
      refine ⟨151565392009032300662172889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202087189345376400882897185 151565392009032300662172889)
      ·
        refine ⟨113674044006774225496629667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151565392009032300662172889 113674044006774225496629667)
        ·
          refine ⟨170511066010161338244944501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113674044006774225496629667 170511066010161338244944501)
          ·
            refine ⟨15985412438452625460463547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170511066010161338244944501 15985412438452625460463547)
            ·
              refine ⟨23978118657678938190695321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15985412438452625460463547 23978118657678938190695321)
              ·
                refine ⟨17983588993259203643021491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23978118657678938190695321 17983588993259203643021491)
                ·
                  refine ⟨26975383489888805464532237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17983588993259203643021491 26975383489888805464532237)
                  ·
                    refine ⟨10115768808708302049199589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26975383489888805464532237 10115768808708302049199589)
                    ·
                      refine ⟨1896706651632806634224923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10115768808708302049199589 1896706651632806634224923)
                      ·
                        rfl

theorem cell23_3693823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_3693823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693823 prefixEnd_3693823 := by exact prefixLift 3693823
  have htrace : WordTrace (prefixWord ++ tailWord_3693823) baseStart_3693823 baseEnd_3693823 := by
    simpa [prefixWord, tailWord_3693823, baseEnd_3693823] using wordTrace_append hprefix tailTrace_3693823
  have hstable : (prefixWord ++ tailWord_3693823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693823).length < 2 ^ (prefixWord ++ tailWord_3693823).sum := by decide
  have hdescent : baseEnd_3693823 < baseStart_3693823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693854 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3693854 : Nat := 118140960795 + 3693854 * 2 ^ 59
def prefixEnd_3693854 : Nat := 4983230072969 + 3 ^ 40 * 3693854 * 2
def baseEnd_3693854 : Nat := 632240856511032004312427

theorem tailTrace_3693854 : CollatzResearch.WordTrace tailWord_3693854 prefixEnd_3693854 632240856511032004312427 := by
  unfold tailWord_3693854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16840740444975661610372077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89817282373203528588651077 16840740444975661610372077)
  ·
    refine ⟨6315277666865873103889529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16840740444975661610372077 6315277666865873103889529)
    ·
      refine ⟨4736458250149404827917147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6315277666865873103889529 4736458250149404827917147)
      ·
        refine ⟨7104687375224107241875721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736458250149404827917147 7104687375224107241875721)
        ·
          refine ⟨5328515531418080431406791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7104687375224107241875721 5328515531418080431406791)
          ·
            refine ⟨7992773297127120647110187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328515531418080431406791 7992773297127120647110187)
            ·
              refine ⟨11989159945690680970665281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992773297127120647110187 11989159945690680970665281)
              ·
                refine ⟨8991869959268010727998961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11989159945690680970665281 8991869959268010727998961)
                ·
                  refine ⟨6743902469451008045999221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8991869959268010727998961 6743902469451008045999221)
                  ·
                    refine ⟨632240856511032004312427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6743902469451008045999221 632240856511032004312427)
                    ·
                      rfl

theorem cell23_3693854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3693854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693854 prefixEnd_3693854 := by exact prefixLift 3693854
  have htrace : WordTrace (prefixWord ++ tailWord_3693854) baseStart_3693854 baseEnd_3693854 := by
    simpa [prefixWord, tailWord_3693854, baseEnd_3693854] using wordTrace_append hprefix tailTrace_3693854
  have hstable : (prefixWord ++ tailWord_3693854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693854).length < 2 ^ (prefixWord ++ tailWord_3693854).sum := by decide
  have hdescent : baseEnd_3693854 < baseStart_3693854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693961 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 1, 5]
def baseStart_3693961 : Nat := 118140960795 + 3693961 * 2 ^ 59
def prefixEnd_3693961 : Nat := 4983230072969 + 3 ^ 40 * 3693961 * 2
def baseEnd_3693961 : Nat := 632259170654375698099763

theorem tailTrace_3693961 : CollatzResearch.WordTrace tailWord_3693961 prefixEnd_3693961 632259170654375698099763 := by
  unfold tailWord_3693961
  simp only [CollatzResearch.WordTrace]
  refine ⟨134729826170417650157121737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89819884113611766771414491 134729826170417650157121737)
  ·
    refine ⟨101047369627813237617841303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134729826170417650157121737 101047369627813237617841303)
    ·
      refine ⟨151571054441719856426761955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101047369627813237617841303 151571054441719856426761955)
      ·
        refine ⟨227356581662579784640142933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151571054441719856426761955 227356581662579784640142933)
        ·
          refine ⟨2664334941358356851251675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 227356581662579784640142933 2664334941358356851251675)
          ·
            refine ⟨3996502412037535276877513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664334941358356851251675 3996502412037535276877513)
            ·
              refine ⟨2997376809028151457658135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996502412037535276877513 2997376809028151457658135)
              ·
                refine ⟨4496065213542227186487203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997376809028151457658135 4496065213542227186487203)
                ·
                  refine ⟨6744097820313340779730805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496065213542227186487203 6744097820313340779730805)
                  ·
                    refine ⟨632259170654375698099763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6744097820313340779730805 632259170654375698099763)
                    ·
                      rfl

theorem cell23_3693961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 5].length) (baseStart_3693961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693961 prefixEnd_3693961 := by exact prefixLift 3693961
  have htrace : WordTrace (prefixWord ++ tailWord_3693961) baseStart_3693961 baseEnd_3693961 := by
    simpa [prefixWord, tailWord_3693961, baseEnd_3693961] using wordTrace_append hprefix tailTrace_3693961
  have hstable : (prefixWord ++ tailWord_3693961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693961).length < 2 ^ (prefixWord ++ tailWord_3693961).sum := by decide
  have hdescent : baseEnd_3693961 < baseStart_3693961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693981 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_3693981 : Nat := 118140960795 + 3693981 * 2 ^ 59
def prefixEnd_3693981 : Nat := 4983230072969 + 3 ^ 40 * 3693981 * 2
def baseEnd_3693981 : Nat := 1896787781576217016049197

theorem tailTrace_3693981 : CollatzResearch.WordTrace tailWord_3693981 prefixEnd_3693981 1896787781576217016049197 := by
  unfold tailWord_3693981
  simp only [CollatzResearch.WordTrace]
  refine ⟨134730555630345193572849797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89820370420230129048566531 134730555630345193572849797)
  ·
    refine ⟨25261979180689723794909337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134730555630345193572849797 25261979180689723794909337)
    ·
      refine ⟨18946484385517292846182003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25261979180689723794909337 18946484385517292846182003)
      ·
        refine ⟨28419726578275939269273005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18946484385517292846182003 28419726578275939269273005)
        ·
          refine ⟨10657397466853477225977377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28419726578275939269273005 10657397466853477225977377)
          ·
            refine ⟨7993048100140107919483033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10657397466853477225977377 7993048100140107919483033)
            ·
              refine ⟨5994786075105080939612275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7993048100140107919483033 5994786075105080939612275)
              ·
                refine ⟨8992179112657621409418413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994786075105080939612275 8992179112657621409418413)
                ·
                  refine ⟨3372067167246608028531905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8992179112657621409418413 3372067167246608028531905)
                  ·
                    refine ⟨2529050375434956021398929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3372067167246608028531905 2529050375434956021398929)
                    ·
                      refine ⟨1896787781576217016049197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529050375434956021398929 1896787781576217016049197)
                      ·
                        rfl

theorem cell23_3693981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_3693981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3693981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3693981 prefixEnd_3693981 := by exact prefixLift 3693981
  have htrace : WordTrace (prefixWord ++ tailWord_3693981) baseStart_3693981 baseEnd_3693981 := by
    simpa [prefixWord, tailWord_3693981, baseEnd_3693981] using wordTrace_append hprefix tailTrace_3693981
  have hstable : (prefixWord ++ tailWord_3693981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693981).length < 2 ^ (prefixWord ++ tailWord_3693981).sum := by decide
  have hdescent : baseEnd_3693981 < baseStart_3693981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694024 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_3694024 : Nat := 118140960795 + 3694024 * 2 ^ 59
def prefixEnd_3694024 : Nat := 4983230072969 + 3 ^ 40 * 3694024 * 2
def baseEnd_3694024 : Nat := 1896809861244360347811499

theorem tailTrace_3694024 : CollatzResearch.WordTrace tailWord_3694024 prefixEnd_3694024 1896809861244360347811499 := by
  unfold tailWord_3694024
  simp only [CollatzResearch.WordTrace]
  refine ⟨67366061984594705958332563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89821415979459607944443417 67366061984594705958332563)
  ·
    refine ⟨101049092976892058937498845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67366061984594705958332563 101049092976892058937498845)
    ·
      refine ⟨37893409866334522101562067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101049092976892058937498845 37893409866334522101562067)
      ·
        refine ⟨56840114799501783152343101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37893409866334522101562067 56840114799501783152343101)
        ·
          refine ⟨21315043049813168682128663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56840114799501783152343101 21315043049813168682128663)
          ·
            refine ⟨31972564574719753023192995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21315043049813168682128663 31972564574719753023192995)
            ·
              refine ⟨47958846862079629534789493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31972564574719753023192995 47958846862079629534789493)
              ·
                refine ⟨4496141893319965268886515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47958846862079629534789493 4496141893319965268886515)
                ·
                  refine ⟨6744212839979947903329773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496141893319965268886515 6744212839979947903329773)
                  ·
                    refine ⟨2529079814992480463748665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6744212839979947903329773 2529079814992480463748665)
                    ·
                      refine ⟨1896809861244360347811499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529079814992480463748665 1896809861244360347811499)
                      ·
                        rfl

theorem cell23_3694024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_3694024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694024 prefixEnd_3694024 := by exact prefixLift 3694024
  have htrace : WordTrace (prefixWord ++ tailWord_3694024) baseStart_3694024 baseEnd_3694024 := by
    simpa [prefixWord, tailWord_3694024, baseEnd_3694024] using wordTrace_append hprefix tailTrace_3694024
  have hstable : (prefixWord ++ tailWord_3694024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694024).length < 2 ^ (prefixWord ++ tailWord_3694024).sum := by decide
  have hdescent : baseEnd_3694024 < baseStart_3694024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694030 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_3694030 : Nat := 118140960795 + 3694030 * 2 ^ 59
def prefixEnd_3694030 : Nat := 4983230072969 + 3 ^ 40 * 3694030 * 2
def baseEnd_3694030 : Nat := 632270980709429108112157

theorem tailTrace_3694030 : CollatzResearch.WordTrace tailWord_3694030 prefixEnd_3694030 632270980709429108112157 := by
  unfold tailWord_3694030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16841542850895959367672943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89821561871445116627589029 16841542850895959367672943)
  ·
    refine ⟨25262314276343939051509415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16841542850895959367672943 25262314276343939051509415)
    ·
      refine ⟨37893471414515908577264123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25262314276343939051509415 37893471414515908577264123)
      ·
        refine ⟨56840207121773862865896185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37893471414515908577264123 56840207121773862865896185)
        ·
          refine ⟨42630155341330397149422139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56840207121773862865896185 42630155341330397149422139)
          ·
            refine ⟨63945233011995595724133209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42630155341330397149422139 63945233011995595724133209)
            ·
              refine ⟨47958924758996696793099907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63945233011995595724133209 47958924758996696793099907)
              ·
                refine ⟨71938387138495045189649861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47958924758996696793099907 71938387138495045189649861)
                ·
                  refine ⟨13488447588467820973059349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71938387138495045189649861 13488447588467820973059349)
                  ·
                    refine ⟨632270980709429108112157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13488447588467820973059349 632270980709429108112157)
                    ·
                      rfl

theorem cell23_3694030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_3694030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694030 prefixEnd_3694030 := by exact prefixLift 3694030
  have htrace : WordTrace (prefixWord ++ tailWord_3694030) baseStart_3694030 baseEnd_3694030 := by
    simpa [prefixWord, tailWord_3694030, baseEnd_3694030] using wordTrace_append hprefix tailTrace_3694030
  have hstable : (prefixWord ++ tailWord_3694030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694030).length < 2 ^ (prefixWord ++ tailWord_3694030).sum := by decide
  have hdescent : baseEnd_3694030 < baseStart_3694030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694058 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_3694058 : Nat := 118140960795 + 3694058 * 2 ^ 59
def prefixEnd_3694058 : Nat := 4983230072969 + 3 ^ 40 * 3694058 * 2
def baseEnd_3694058 : Nat := 1896827319586613214786343

theorem tailTrace_3694058 : CollatzResearch.WordTrace tailWord_3694058 prefixEnd_3694058 1896827319586613214786343 := by
  unfold tailWord_3694058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33683341012766558930850707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89822242700710823815601885 33683341012766558930850707)
  ·
    refine ⟨50525011519149838396276061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33683341012766558930850707 50525011519149838396276061)
    ·
      refine ⟨18946879319681189398603523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50525011519149838396276061 18946879319681189398603523)
      ·
        refine ⟨28420318979521784097905285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18946879319681189398603523 28420318979521784097905285)
        ·
          refine ⟨5328809808660334518357241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28420318979521784097905285 5328809808660334518357241)
          ·
            refine ⟨3996607356495250888767931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5328809808660334518357241 3996607356495250888767931)
            ·
              refine ⟨5994911034742876333151897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996607356495250888767931 5994911034742876333151897)
              ·
                refine ⟨4496183276057157249863923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994911034742876333151897 4496183276057157249863923)
                ·
                  refine ⟨6744274914085735874795885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496183276057157249863923 6744274914085735874795885)
                  ·
                    refine ⟨2529103092782150953048457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6744274914085735874795885 2529103092782150953048457)
                    ·
                      refine ⟨1896827319586613214786343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529103092782150953048457 1896827319586613214786343)
                      ·
                        rfl

theorem cell23_3694058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_3694058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694058 prefixEnd_3694058 := by exact prefixLift 3694058
  have htrace : WordTrace (prefixWord ++ tailWord_3694058) baseStart_3694058 baseEnd_3694058 := by
    simpa [prefixWord, tailWord_3694058, baseEnd_3694058] using wordTrace_append hprefix tailTrace_3694058
  have hstable : (prefixWord ++ tailWord_3694058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694058).length < 2 ^ (prefixWord ++ tailWord_3694058).sum := by decide
  have hdescent : baseEnd_3694058 < baseStart_3694058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694097 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 7, 2]
def baseStart_3694097 : Nat := 118140960795 + 3694097 * 2 ^ 59
def prefixEnd_3694097 : Nat := 4983230072969 + 3 ^ 40 * 3694097 * 2
def baseEnd_3694097 : Nat := 1896847345332138562198663

theorem tailTrace_3694097 : CollatzResearch.WordTrace tailWord_3694097 prefixEnd_3694097 1896847345332138562198663 := by
  unfold tailWord_3694097
  simp only [CollatzResearch.WordTrace]
  refine ⟨134734786497924945384072545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89823190998616630256048363 134734786497924945384072545)
  ·
    refine ⟨101051089873443709038054409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134734786497924945384072545 101051089873443709038054409)
    ·
      refine ⟨75788317405082781778540807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101051089873443709038054409 75788317405082781778540807)
      ·
        refine ⟨113682476107624172667811211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75788317405082781778540807 113682476107624172667811211)
        ·
          refine ⟨170523714161436259001716817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113682476107624172667811211 170523714161436259001716817)
          ·
            refine ⟨127892785621077194251287613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170523714161436259001716817 127892785621077194251287613)
            ·
              refine ⟨47959794607903947844232855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127892785621077194251287613 47959794607903947844232855)
              ·
                refine ⟨71939691911855921766349283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47959794607903947844232855 71939691911855921766349283)
                ·
                  refine ⟨107909537867783882649523925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71939691911855921766349283 107909537867783882649523925)
                  ·
                    refine ⟨2529129793776184749598217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107909537867783882649523925 2529129793776184749598217)
                    ·
                      refine ⟨1896847345332138562198663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529129793776184749598217 1896847345332138562198663)
                      ·
                        rfl

theorem cell23_3694097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_3694097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694097 prefixEnd_3694097 := by exact prefixLift 3694097
  have htrace : WordTrace (prefixWord ++ tailWord_3694097) baseStart_3694097 baseEnd_3694097 := by
    simpa [prefixWord, tailWord_3694097, baseEnd_3694097] using wordTrace_append hprefix tailTrace_3694097
  have hstable : (prefixWord ++ tailWord_3694097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694097).length < 2 ^ (prefixWord ++ tailWord_3694097).sum := by decide
  have hdescent : baseEnd_3694097 < baseStart_3694097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694104 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_3694104 : Nat := 118140960795 + 3694104 * 2 ^ 59
def prefixEnd_3694104 : Nat := 4983230072969 + 3 ^ 40 * 3694104 * 2
def baseEnd_3694104 : Nat := 1896850939696720034811131

theorem tailTrace_3694104 : CollatzResearch.WordTrace tailWord_3694104 prefixEnd_3694104 1896850939696720034811131 := by
  unfold tailWord_3694104
  simp only [CollatzResearch.WordTrace]
  refine ⟨67367520904449792789788683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89823361205933057053051577 67367520904449792789788683)
  ·
    refine ⟨101051281356674689184683025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67367520904449792789788683 101051281356674689184683025)
    ·
      refine ⟨75788461017506016888512269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101051281356674689184683025 75788461017506016888512269)
      ·
        refine ⟨28420672881564756333192101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75788461017506016888512269 28420672881564756333192101)
        ·
          refine ⟨5328876165293391812473519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28420672881564756333192101 5328876165293391812473519)
          ·
            refine ⟨7993314247940087718710279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328876165293391812473519 7993314247940087718710279)
            ·
              refine ⟨11989971371910131578065419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993314247940087718710279 11989971371910131578065419)
              ·
                refine ⟨17984957057865197367098129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11989971371910131578065419 17984957057865197367098129)
                ·
                  refine ⟨13488717793398898025323597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17984957057865197367098129 13488717793398898025323597)
                  ·
                    refine ⟨5058269172524586759496349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13488717793398898025323597 5058269172524586759496349)
                    ·
                      refine ⟨1896850939696720034811131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5058269172524586759496349 1896850939696720034811131)
                      ·
                        rfl

theorem cell23_3694104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_3694104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694104 prefixEnd_3694104 := by exact prefixLift 3694104
  have htrace : WordTrace (prefixWord ++ tailWord_3694104) baseStart_3694104 baseEnd_3694104 := by
    simpa [prefixWord, tailWord_3694104, baseEnd_3694104] using wordTrace_append hprefix tailTrace_3694104
  have hstable : (prefixWord ++ tailWord_3694104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694104).length < 2 ^ (prefixWord ++ tailWord_3694104).sum := by decide
  have hdescent : baseEnd_3694104 < baseStart_3694104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694154 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_3694154 : Nat := 118140960795 + 3694154 * 2 ^ 59
def prefixEnd_3694154 : Nat := 4983230072969 + 3 ^ 40 * 3694154 * 2
def baseEnd_3694154 : Nat := 632292204576481613061967

theorem tailTrace_3694154 : CollatzResearch.WordTrace tailWord_3694154 prefixEnd_3694154 632292204576481613061967 := by
  unfold tailWord_3694154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33684216364679611029724379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89824576972478962745931677 33684216364679611029724379)
  ·
    refine ⟨50526324547019416544586569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33684216364679611029724379 50526324547019416544586569)
    ·
      refine ⟨37894743410264562408439927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50526324547019416544586569 37894743410264562408439927)
      ·
        refine ⟨56842115115396843612659891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37894743410264562408439927 56842115115396843612659891)
        ·
          refine ⟨85263172673095265418989837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56842115115396843612659891 85263172673095265418989837)
          ·
            refine ⟨31973689752410724532121189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85263172673095265418989837 31973689752410724532121189)
            ·
              refine ⟨5995066828577010849772723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31973689752410724532121189 5995066828577010849772723)
              ·
                refine ⟨8992600242865516274659085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995066828577010849772723 8992600242865516274659085)
                ·
                  refine ⟨3372225091074568602997157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8992600242865516274659085 3372225091074568602997157)
                  ·
                    refine ⟨632292204576481613061967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3372225091074568602997157 632292204576481613061967)
                    ·
                      rfl

theorem cell23_3694154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_3694154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694154 prefixEnd_3694154 := by exact prefixLift 3694154
  have htrace : WordTrace (prefixWord ++ tailWord_3694154) baseStart_3694154 baseEnd_3694154 := by
    simpa [prefixWord, tailWord_3694154, baseEnd_3694154] using wordTrace_append hprefix tailTrace_3694154
  have hstable : (prefixWord ++ tailWord_3694154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694154).length < 2 ^ (prefixWord ++ tailWord_3694154).sum := by decide
  have hdescent : baseEnd_3694154 < baseStart_3694154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694177 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3694177 : Nat := 118140960795 + 3694177 * 2 ^ 59
def prefixEnd_3694177 : Nat := 4983230072969 + 3 ^ 40 * 3694177 * 2
def baseEnd_3694177 : Nat := 1896888423784498249198295

theorem tailTrace_3694177 : CollatzResearch.WordTrace tailWord_3694177 prefixEnd_3694177 1896888423784498249198295 := by
  unfold tailWord_3694177
  simp only [CollatzResearch.WordTrace]
  refine ⟨134737704337635119046984785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89825136225090079364656523 134737704337635119046984785)
  ·
    refine ⟨101053278253226339285238589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134737704337635119046984785 101053278253226339285238589)
    ·
      refine ⟨37894979344959877231964471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101053278253226339285238589 37894979344959877231964471)
      ·
        refine ⟨56842469017439815847946707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37894979344959877231964471 56842469017439815847946707)
        ·
          refine ⟨85263703526159723771920061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56842469017439815847946707 85263703526159723771920061)
          ·
            refine ⟨31973888822309896414470023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85263703526159723771920061 31973888822309896414470023)
            ·
              refine ⟨47960833233464844621705035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31973888822309896414470023 47960833233464844621705035)
              ·
                refine ⟨71941249850197266932557553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47960833233464844621705035 71941249850197266932557553)
                ·
                  refine ⟨53955937387647950199418165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71941249850197266932557553 53955937387647950199418165)
                  ·
                    refine ⟨5058369130091995331195453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53955937387647950199418165 5058369130091995331195453)
                    ·
                      refine ⟨1896888423784498249198295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5058369130091995331195453 1896888423784498249198295)
                      ·
                        rfl

theorem cell23_3694177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3694177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694177 prefixEnd_3694177 := by exact prefixLift 3694177
  have htrace : WordTrace (prefixWord ++ tailWord_3694177) baseStart_3694177 baseEnd_3694177 := by
    simpa [prefixWord, tailWord_3694177, baseEnd_3694177] using wordTrace_append hprefix tailTrace_3694177
  have hstable : (prefixWord ++ tailWord_3694177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694177).length < 2 ^ (prefixWord ++ tailWord_3694177).sum := by decide
  have hdescent : baseEnd_3694177 < baseStart_3694177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694231 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 1, 5]
def baseStart_3694231 : Nat := 118140960795 + 3694231 * 2 ^ 59
def prefixEnd_3694231 : Nat := 4983230072969 + 3 ^ 40 * 3694231 * 2
def baseEnd_3694231 : Nat := 632305383913280345974349

theorem tailTrace_3694231 : CollatzResearch.WordTrace tailWord_3694231 prefixEnd_3694231 632305383913280345974349 := by
  unfold tailWord_3694231
  simp only [CollatzResearch.WordTrace]
  refine ⟨134739673879439486269450547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89826449252959657512967031 134739673879439486269450547)
  ·
    refine ⟨202109510819159229404175821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134739673879439486269450547 202109510819159229404175821)
    ·
      refine ⟨75791066557184711026565933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202109510819159229404175821 75791066557184711026565933)
      ·
        refine ⟨28421649958944266634962225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75791066557184711026565933 28421649958944266634962225)
        ·
          refine ⟨21316237469208199976221669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28421649958944266634962225 21316237469208199976221669)
          ·
            refine ⟨3996794525476537495541563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21316237469208199976221669 3996794525476537495541563)
            ·
              refine ⟨5995191788214806243312345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996794525476537495541563 5995191788214806243312345)
              ·
                refine ⟨4496393841161104682484259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5995191788214806243312345 4496393841161104682484259)
                ·
                  refine ⟨6744590761741657023726389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496393841161104682484259 6744590761741657023726389)
                  ·
                    refine ⟨632305383913280345974349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6744590761741657023726389 632305383913280345974349)
                    ·
                      rfl

theorem cell23_3694231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_3694231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694231 prefixEnd_3694231 := by exact prefixLift 3694231
  have htrace : WordTrace (prefixWord ++ tailWord_3694231) baseStart_3694231 baseEnd_3694231 := by
    simpa [prefixWord, tailWord_3694231, baseEnd_3694231] using wordTrace_append hprefix tailTrace_3694231
  have hstable : (prefixWord ++ tailWord_3694231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694231).length < 2 ^ (prefixWord ++ tailWord_3694231).sum := by decide
  have hdescent : baseEnd_3694231 < baseStart_3694231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694238 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_3694238 : Nat := 118140960795 + 3694238 * 2 ^ 59
def prefixEnd_3694238 : Nat := 4983230072969 + 3 ^ 40 * 3694238 * 2
def baseEnd_3694238 : Nat := 1896919746104422510535515

theorem tailTrace_3694238 : CollatzResearch.WordTrace tailWord_3694238 prefixEnd_3694238 1896919746104422510535515 := by
  unfold tailWord_3694238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16842491148801765808119421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89826619460276084309970245 16842491148801765808119421)
  ·
    refine ⟨6315934180800662178044783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16842491148801765808119421 6315934180800662178044783)
    ·
      refine ⟨9473901271200993267067175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6315934180800662178044783 9473901271200993267067175)
      ·
        refine ⟨14210851906801489900600763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9473901271200993267067175 14210851906801489900600763)
        ·
          refine ⟨21316277860202234850901145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14210851906801489900600763 21316277860202234850901145)
          ·
            refine ⟨15987208395151676138175859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21316277860202234850901145 15987208395151676138175859)
            ·
              refine ⟨23980812592727514207263789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15987208395151676138175859 23980812592727514207263789)
              ·
                refine ⟨8992804722272817827723921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23980812592727514207263789 8992804722272817827723921)
                ·
                  refine ⟨6744603541704613370792941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8992804722272817827723921 6744603541704613370792941)
                  ·
                    refine ⟨2529226328139230014047353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6744603541704613370792941 2529226328139230014047353)
                    ·
                      refine ⟨1896919746104422510535515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529226328139230014047353 1896919746104422510535515)
                      ·
                        rfl

theorem cell23_3694238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_3694238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694238 prefixEnd_3694238 := by exact prefixLift 3694238
  have htrace : WordTrace (prefixWord ++ tailWord_3694238) baseStart_3694238 baseEnd_3694238 := by
    simpa [prefixWord, tailWord_3694238, baseEnd_3694238] using wordTrace_append hprefix tailTrace_3694238
  have hstable : (prefixWord ++ tailWord_3694238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694238).length < 2 ^ (prefixWord ++ tailWord_3694238).sum := by decide
  have hdescent : baseEnd_3694238 < baseStart_3694238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694244 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_3694244 : Nat := 118140960795 + 3694244 * 2 ^ 59
def prefixEnd_3694244 : Nat := 4983230072969 + 3 ^ 40 * 3694244 * 2
def baseEnd_3694244 : Nat := 632307608996116495686829

theorem tailTrace_3694244 : CollatzResearch.WordTrace tailWord_3694244 prefixEnd_3694244 632307608996116495686829 := by
  unfold tailWord_3694244
  simp only [CollatzResearch.WordTrace]
  refine ⟨67370074014196194744836893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89826765352261592993115857 67370074014196194744836893)
  ·
    refine ⟨25263777755323573029313835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67370074014196194744836893 25263777755323573029313835)
    ·
      refine ⟨37895666632985359543970753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25263777755323573029313835 37895666632985359543970753)
      ·
        refine ⟨28421749974739019657978065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37895666632985359543970753 28421749974739019657978065)
        ·
          refine ⟨21316312481054264743483549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28421749974739019657978065 21316312481054264743483549)
          ·
            refine ⟨7993617180395349278806331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21316312481054264743483549 7993617180395349278806331)
            ·
              refine ⟨11990425770593023918209497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993617180395349278806331 11990425770593023918209497)
              ·
                refine ⟨8992819327944767938657123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11990425770593023918209497 8992819327944767938657123)
                ·
                  refine ⟨13489228991917151907985685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8992819327944767938657123 13489228991917151907985685)
                  ·
                    refine ⟨632307608996116495686829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13489228991917151907985685 632307608996116495686829)
                    ·
                      rfl

theorem cell23_3694244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_3694244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694244 prefixEnd_3694244 := by exact prefixLift 3694244
  have htrace : WordTrace (prefixWord ++ tailWord_3694244) baseStart_3694244 baseEnd_3694244 := by
    simpa [prefixWord, tailWord_3694244, baseEnd_3694244] using wordTrace_append hprefix tailTrace_3694244
  have hstable : (prefixWord ++ tailWord_3694244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694244).length < 2 ^ (prefixWord ++ tailWord_3694244).sum := by decide
  have hdescent : baseEnd_3694244 < baseStart_3694244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694262 : List Nat := [5, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_3694262 : Nat := 118140960795 + 3694262 * 2 ^ 59
def prefixEnd_3694262 : Nat := 4983230072969 + 3 ^ 40 * 3694262 * 2
def baseEnd_3694262 : Nat := 1896932069640130416635405

theorem tailTrace_3694262 : CollatzResearch.WordTrace tailWord_3694262 prefixEnd_3694262 1896932069640130416635405 := by
  unfold tailWord_3694262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421300283895448660239315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89827203028218119042552693 8421300283895448660239315)
  ·
    refine ⟨12631950425843172990358973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421300283895448660239315 12631950425843172990358973)
    ·
      refine ⟨4736981409691189871384615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12631950425843172990358973 4736981409691189871384615)
      ·
        refine ⟨7105472114536784807076923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736981409691189871384615 7105472114536784807076923)
        ·
          refine ⟨10658208171805177210615385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105472114536784807076923 10658208171805177210615385)
          ·
            refine ⟨7993656128853882907961539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10658208171805177210615385 7993656128853882907961539)
            ·
              refine ⟨11990484193280824361942309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993656128853882907961539 11990484193280824361942309)
              ·
                refine ⟨2248215786240154567864183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11990484193280824361942309 2248215786240154567864183)
                ·
                  refine ⟨3372323679360231851796275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248215786240154567864183 3372323679360231851796275)
                  ·
                    refine ⟨5058485519040347777694413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372323679360231851796275 5058485519040347777694413)
                    ·
                      refine ⟨1896932069640130416635405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5058485519040347777694413 1896932069640130416635405)
                      ·
                        rfl

theorem cell23_3694262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_3694262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694262 prefixEnd_3694262 := by exact prefixLift 3694262
  have htrace : WordTrace (prefixWord ++ tailWord_3694262) baseStart_3694262 baseEnd_3694262 := by
    simpa [prefixWord, tailWord_3694262, baseEnd_3694262] using wordTrace_append hprefix tailTrace_3694262
  have hstable : (prefixWord ++ tailWord_3694262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694262).length < 2 ^ (prefixWord ++ tailWord_3694262).sum := by decide
  have hdescent : baseEnd_3694262 < baseStart_3694262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694278 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3694278 : Nat := 118140960795 + 3694278 * 2 ^ 59
def prefixEnd_3694278 : Nat := 4983230072969 + 3 ^ 40 * 3694278 * 2
def baseEnd_3694278 : Nat := 632313428443534118011777

theorem tailTrace_3694278 : CollatzResearch.WordTrace tailWord_3694278 prefixEnd_3694278 632313428443534118011777 := by
  unfold tailWord_3694278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210668378445912915512859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89827592073512808864274325 4210668378445912915512859)
  ·
    refine ⟨6316002567668869373269289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4210668378445912915512859 6316002567668869373269289)
    ·
      refine ⟨4737001925751652029951967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6316002567668869373269289 4737001925751652029951967)
      ·
        refine ⟨7105502888627478044927951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737001925751652029951967 7105502888627478044927951)
        ·
          refine ⟨10658254332941217067391927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105502888627478044927951 10658254332941217067391927)
          ·
            refine ⟨15987381499411825601087891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658254332941217067391927 15987381499411825601087891)
            ·
              refine ⟨23981072249117738401631837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15987381499411825601087891 23981072249117738401631837)
              ·
                refine ⟨8992902093419151900611939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23981072249117738401631837 8992902093419151900611939)
                ·
                  refine ⟨13489353140128727850917909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8992902093419151900611939 13489353140128727850917909)
                  ·
                    refine ⟨632313428443534118011777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13489353140128727850917909 632313428443534118011777)
                    ·
                      rfl

theorem cell23_3694278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3694278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694278 prefixEnd_3694278 := by exact prefixLift 3694278
  have htrace : WordTrace (prefixWord ++ tailWord_3694278) baseStart_3694278 baseEnd_3694278 := by
    simpa [prefixWord, tailWord_3694278, baseEnd_3694278] using wordTrace_append hprefix tailTrace_3694278
  have hstable : (prefixWord ++ tailWord_3694278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694278).length < 2 ^ (prefixWord ++ tailWord_3694278).sum := by decide
  have hdescent : baseEnd_3694278 < baseStart_3694278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694285 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3694285 : Nat := 118140960795 + 3694285 * 2 ^ 59
def prefixEnd_3694285 : Nat := 4983230072969 + 3 ^ 40 * 3694285 * 2
def baseEnd_3694285 : Nat := 1896943879695183826647799

theorem tailTrace_3694285 : CollatzResearch.WordTrace tailWord_3694285 prefixEnd_3694285 1896943879695183826647799 := by
  unfold tailWord_3694285
  simp only [CollatzResearch.WordTrace]
  refine ⟨134741643421243853491916309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89827762280829235661277539 134741643421243853491916309)
  ·
    refine ⟨6316014535370805632433577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134741643421243853491916309 6316014535370805632433577)
    ·
      refine ⟨4737010901528104224325183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6316014535370805632433577 4737010901528104224325183)
      ·
        refine ⟨7105516352292156336487775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737010901528104224325183 7105516352292156336487775)
        ·
          refine ⟨10658274528438234504731663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7105516352292156336487775 10658274528438234504731663)
          ·
            refine ⟨15987411792657351757097495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658274528438234504731663 15987411792657351757097495)
            ·
              refine ⟨23981117688986027635646243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15987411792657351757097495 23981117688986027635646243)
              ·
                refine ⟨35971676533479041453469365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23981117688986027635646243 35971676533479041453469365)
                ·
                  refine ⟨3372344675013660136262753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35971676533479041453469365 3372344675013660136262753)
                  ·
                    refine ⟨2529258506260245102197065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3372344675013660136262753 2529258506260245102197065)
                    ·
                      refine ⟨1896943879695183826647799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529258506260245102197065 1896943879695183826647799)
                      ·
                        rfl

theorem cell23_3694285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3694285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694285 prefixEnd_3694285 := by exact prefixLift 3694285
  have htrace : WordTrace (prefixWord ++ tailWord_3694285) baseStart_3694285 baseEnd_3694285 := by
    simpa [prefixWord, tailWord_3694285, baseEnd_3694285] using wordTrace_append hprefix tailTrace_3694285
  have hstable : (prefixWord ++ tailWord_3694285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694285).length < 2 ^ (prefixWord ++ tailWord_3694285).sum := by decide
  have hdescent : baseEnd_3694285 < baseStart_3694285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694305 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_3694305 : Nat := 118140960795 + 3694305 * 2 ^ 59
def prefixEnd_3694305 : Nat := 4983230072969 + 3 ^ 40 * 3694305 * 2
def baseEnd_3694305 : Nat := 1896954149308273748397707

theorem tailTrace_3694305 : CollatzResearch.WordTrace tailWord_3694305 prefixEnd_3694305 1896954149308273748397707 := by
  unfold tailWord_3694305
  simp only [CollatzResearch.WordTrace]
  refine ⟨134742372881171396907644369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89828248587447597938429579 134742372881171396907644369)
  ·
    refine ⟨101056779660878547680733277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134742372881171396907644369 101056779660878547680733277)
    ·
      refine ⟨37896292372829455380274979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101056779660878547680733277 37896292372829455380274979)
      ·
        refine ⟨56844438559244183070412469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37896292372829455380274979 56844438559244183070412469)
        ·
          refine ⟨5329166114929142162851169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56844438559244183070412469 5329166114929142162851169)
          ·
            refine ⟨3996874586196856622138377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5329166114929142162851169 3996874586196856622138377)
            ·
              refine ⟨2997655939647642466603783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996874586196856622138377 2997655939647642466603783)
              ·
                refine ⟨4496483909471463699905675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997655939647642466603783 4496483909471463699905675)
                ·
                  refine ⟨6744725864207195549858513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496483909471463699905675 6744725864207195549858513)
                  ·
                    refine ⟨5058544398155396662393885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6744725864207195549858513 5058544398155396662393885)
                    ·
                      refine ⟨1896954149308273748397707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5058544398155396662393885 1896954149308273748397707)
                      ·
                        rfl

theorem cell23_3694305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_3694305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694305 prefixEnd_3694305 := by exact prefixLift 3694305
  have htrace : WordTrace (prefixWord ++ tailWord_3694305) baseStart_3694305 baseEnd_3694305 := by
    simpa [prefixWord, tailWord_3694305, baseEnd_3694305] using wordTrace_append hprefix tailTrace_3694305
  have hstable : (prefixWord ++ tailWord_3694305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694305).length < 2 ^ (prefixWord ++ tailWord_3694305).sum := by decide
  have hdescent : baseEnd_3694305 < baseStart_3694305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694342 : List Nat := [6, 2, 2, 1, 1, 1, 1, 9]
def baseStart_3694342 : Nat := 118140960795 + 3694342 * 2 ^ 59
def prefixEnd_3694342 : Nat := 4983230072969 + 3 ^ 40 * 3694342 * 2
def baseEnd_3694342 : Nat := 70258264744166300134631

theorem tailTrace_3694342 : CollatzResearch.WordTrace tailWord_3694342 prefixEnd_3694342 70258264744166300134631 := by
  unfold tailWord_3694342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210741324438667257085665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89829148254691568151160853 4210741324438667257085665)
  ·
    refine ⟨3158055993329000442814249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4210741324438667257085665 3158055993329000442814249)
    ·
      refine ⟨2368541994996750332110687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3158055993329000442814249 2368541994996750332110687)
      ·
        refine ⟨3552812992495125498166031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368541994996750332110687 3552812992495125498166031)
        ·
          refine ⟨5329219488742688247249047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552812992495125498166031 5329219488742688247249047)
          ·
            refine ⟨7993829233114032370873571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329219488742688247249047 7993829233114032370873571)
            ·
              refine ⟨11990743849671048556310357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993829233114032370873571 11990743849671048556310357)
              ·
                refine ⟨70258264744166300134631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11990743849671048556310357 70258264744166300134631)
                ·
                  rfl

theorem cell23_3694342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_3694342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694342 prefixEnd_3694342 := by exact prefixLift 3694342
  have htrace : WordTrace (prefixWord ++ tailWord_3694342) baseStart_3694342 baseEnd_3694342 := by
    simpa [prefixWord, tailWord_3694342, baseEnd_3694342] using wordTrace_append hprefix tailTrace_3694342
  have hstable : (prefixWord ++ tailWord_3694342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694342).length < 2 ^ (prefixWord ++ tailWord_3694342).sum := by decide
  have hdescent : baseEnd_3694342 < baseStart_3694342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694344 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3694344 : Nat := 118140960795 + 3694344 * 2 ^ 59
def prefixEnd_3694344 : Nat := 4983230072969 + 3 ^ 40 * 3694344 * 2
def baseEnd_3694344 : Nat := 1896974175053799095810027

theorem tailTrace_3694344 : CollatzResearch.WordTrace tailWord_3694344 prefixEnd_3694344 1896974175053799095810027 := by
  unfold tailWord_3694344
  simp only [CollatzResearch.WordTrace]
  refine ⟨67371897664015053284157043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89829196885353404378876057 67371897664015053284157043)
  ·
    refine ⟨101057846496022579926235565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67371897664015053284157043 101057846496022579926235565)
    ·
      refine ⟨37896692436008467472338337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101057846496022579926235565 37896692436008467472338337)
      ·
        refine ⟨28422519327006350604253753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37896692436008467472338337 28422519327006350604253753)
        ·
          refine ⟨21316889495254762953190315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28422519327006350604253753 21316889495254762953190315)
          ·
            refine ⟨31975334242882144429785473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21316889495254762953190315 31975334242882144429785473)
            ·
              refine ⟨23981500682161608322339105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31975334242882144429785473 23981500682161608322339105)
              ·
                refine ⟨17986125511621206241754329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23981500682161608322339105 17986125511621206241754329)
                ·
                  refine ⟨13489594133715904681315747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17986125511621206241754329 13489594133715904681315747)
                  ·
                    refine ⟨20234391200573857021973621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13489594133715904681315747 20234391200573857021973621)
                    ·
                      refine ⟨1896974175053799095810027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20234391200573857021973621 1896974175053799095810027)
                      ·
                        rfl

theorem cell23_3694344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3694344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694344 prefixEnd_3694344 := by exact prefixLift 3694344
  have htrace : WordTrace (prefixWord ++ tailWord_3694344) baseStart_3694344 baseEnd_3694344 := by
    simpa [prefixWord, tailWord_3694344, baseEnd_3694344] using wordTrace_append hprefix tailTrace_3694344
  have hstable : (prefixWord ++ tailWord_3694344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694344).length < 2 ^ (prefixWord ++ tailWord_3694344).sum := by decide
  have hdescent : baseEnd_3694344 < baseStart_3694344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694392 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 2, 2, 2]
def baseStart_3694392 : Nat := 118140960795 + 3694392 * 2 ^ 59
def prefixEnd_3694392 : Nat := 4983230072969 + 3 ^ 40 * 3694392 * 2
def baseEnd_3694392 : Nat := 1896998822125214908009807

theorem tailTrace_3694392 : CollatzResearch.WordTrace tailWord_3694392 prefixEnd_3694392 1896998822125214908009807 := by
  unfold tailWord_3694392
  simp only [CollatzResearch.WordTrace]
  refine ⟨67372773015928105383030715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89830364021237473844040953 67372773015928105383030715)
  ·
    refine ⟨101059159523892158074546073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67372773015928105383030715 101059159523892158074546073)
    ·
      refine ⟨75794369642919118555909555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101059159523892158074546073 75794369642919118555909555)
      ·
        refine ⟨113691554464378677833864333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75794369642919118555909555 113691554464378677833864333)
        ·
          refine ⟨42634332924142004187699125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113691554464378677833864333 42634332924142004187699125)
          ·
            refine ⟨3996968711638312892596793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42634332924142004187699125 3996968711638312892596793)
            ·
              refine ⟨2997726533728734669447595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996968711638312892596793 2997726533728734669447595)
              ·
                refine ⟨4496589800593102004171393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997726533728734669447595 4496589800593102004171393)
                ·
                  refine ⟨3372442350444826503128545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4496589800593102004171393 3372442350444826503128545)
                  ·
                    refine ⟨2529331762833619877346409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3372442350444826503128545 2529331762833619877346409)
                    ·
                      refine ⟨1896998822125214908009807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529331762833619877346409 1896998822125214908009807)
                      ·
                        rfl

theorem cell23_3694392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_3694392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694392 prefixEnd_3694392 := by exact prefixLift 3694392
  have htrace : WordTrace (prefixWord ++ tailWord_3694392) baseStart_3694392 baseEnd_3694392 := by
    simpa [prefixWord, tailWord_3694392, baseEnd_3694392] using wordTrace_append hprefix tailTrace_3694392
  have hstable : (prefixWord ++ tailWord_3694392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694392).length < 2 ^ (prefixWord ++ tailWord_3694392).sum := by decide
  have hdescent : baseEnd_3694392 < baseStart_3694392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694431 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_3694431 : Nat := 118140960795 + 3694431 * 2 ^ 59
def prefixEnd_3694431 : Nat := 4983230072969 + 3 ^ 40 * 3694431 * 2
def baseEnd_3694431 : Nat := 1897018847870740255422127

theorem tailTrace_3694431 : CollatzResearch.WordTrace tailWord_3694431 prefixEnd_3694431 1897018847870740255422127 := by
  unfold tailWord_3694431
  simp only [CollatzResearch.WordTrace]
  refine ⟨134746968478714920426731147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89831312319143280284487431 134746968478714920426731147)
  ·
    refine ⟨202120452718072380640096721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134746968478714920426731147 202120452718072380640096721)
    ·
      refine ⟨151590339538554285480072541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202120452718072380640096721 151590339538554285480072541)
      ·
        refine ⟨56846377326957857055027203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151590339538554285480072541 56846377326957857055027203)
        ·
          refine ⟨85269565990436785582540805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56846377326957857055027203 85269565990436785582540805)
          ·
            refine ⟨15988043623206897296726401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85269565990436785582540805 15988043623206897296726401)
            ·
              refine ⟨11991032717405172972544801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15988043623206897296726401 11991032717405172972544801)
              ·
                refine ⟨8993274538053879729408601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11991032717405172972544801 8993274538053879729408601)
                ·
                  refine ⟨6744955903540409797056451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8993274538053879729408601 6744955903540409797056451)
                  ·
                    refine ⟨10117433855310614695584677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6744955903540409797056451 10117433855310614695584677)
                    ·
                      refine ⟨1897018847870740255422127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10117433855310614695584677 1897018847870740255422127)
                      ·
                        rfl

theorem cell23_3694431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_3694431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694431 prefixEnd_3694431 := by exact prefixLift 3694431
  have htrace : WordTrace (prefixWord ++ tailWord_3694431) baseStart_3694431 baseEnd_3694431 := by
    simpa [prefixWord, tailWord_3694431, baseEnd_3694431] using wordTrace_append hprefix tailTrace_3694431
  have hstable : (prefixWord ++ tailWord_3694431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694431).length < 2 ^ (prefixWord ++ tailWord_3694431).sum := by decide
  have hdescent : baseEnd_3694431 < baseStart_3694431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694468 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_3694468 : Nat := 118140960795 + 3694468 * 2 ^ 59
def prefixEnd_3694468 : Nat := 4983230072969 + 3 ^ 40 * 3694468 * 2
def baseEnd_3694468 : Nat := 1897037846654956610659457

theorem tailTrace_3694468 : CollatzResearch.WordTrace tailWord_3694468 prefixEnd_3694468 1897037846654956610659457 := by
  unfold tailWord_3694468
  simp only [CollatzResearch.WordTrace]
  refine ⟨67374158989790437872914029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89832211986387250497218705 67374158989790437872914029)
  ·
    refine ⟨25265309621171414202342761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67374158989790437872914029 25265309621171414202342761)
    ·
      refine ⟨18948982215878560651757071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25265309621171414202342761 18948982215878560651757071)
      ·
        refine ⟨28423473323817840977635607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18948982215878560651757071 28423473323817840977635607)
        ·
          refine ⟨42635209985726761466453411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28423473323817840977635607 42635209985726761466453411)
          ·
            refine ⟨63952814978590142199680117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42635209985726761466453411 63952814978590142199680117)
            ·
              refine ⟨5995576404242825831220011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63952814978590142199680117 5995576404242825831220011)
              ·
                refine ⟨8993364606364238746830017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5995576404242825831220011 8993364606364238746830017)
                ·
                  refine ⟨6745023454773179060122513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8993364606364238746830017 6745023454773179060122513)
                  ·
                    refine ⟨5058767591079884295091885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6745023454773179060122513 5058767591079884295091885)
                    ·
                      refine ⟨1897037846654956610659457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5058767591079884295091885 1897037846654956610659457)
                      ·
                        rfl

theorem cell23_3694468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_3694468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694468 prefixEnd_3694468 := by exact prefixLift 3694468
  have htrace : WordTrace (prefixWord ++ tailWord_3694468) baseStart_3694468 baseEnd_3694468 := by
    simpa [prefixWord, tailWord_3694468, baseEnd_3694468] using wordTrace_append hprefix tailTrace_3694468
  have hstable : (prefixWord ++ tailWord_3694468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694468).length < 2 ^ (prefixWord ++ tailWord_3694468).sum := by decide
  have hdescent : baseEnd_3694468 < baseStart_3694468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694488 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 8]
def baseStart_3694488 : Nat := 118140960795 + 3694488 * 2 ^ 59
def prefixEnd_3694488 : Nat := 4983230072969 + 3 ^ 40 * 3694488 * 2
def baseEnd_3694488 : Nat := 210783124029782948045485

theorem tailTrace_3694488 : CollatzResearch.WordTrace tailWord_3694488 prefixEnd_3694488 210783124029782948045485 := by
  unfold tailWord_3694488
  simp only [CollatzResearch.WordTrace]
  refine ⟨67374523719754209580778059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89832698293005612774370745 67374523719754209580778059)
  ·
    refine ⟨101061785579631314371167089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67374523719754209580778059 101061785579631314371167089)
    ·
      refine ⟨75796339184723485778375317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101061785579631314371167089 75796339184723485778375317)
      ·
        refine ⟨3552953399283913395861343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75796339184723485778375317 3552953399283913395861343)
        ·
          refine ⟨5329430098925870093792015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552953399283913395861343 5329430098925870093792015)
          ·
            refine ⟨7994145148388805140688023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329430098925870093792015 7994145148388805140688023)
            ·
              refine ⟨11991217722583207711032035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7994145148388805140688023 11991217722583207711032035)
              ·
                refine ⟨17986826583874811566548053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11991217722583207711032035 17986826583874811566548053)
                ·
                  refine ⟨210783124029782948045485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17986826583874811566548053 210783124029782948045485)
                  ·
                    rfl

theorem cell23_3694488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 8].length) (baseStart_3694488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694488 prefixEnd_3694488 := by exact prefixLift 3694488
  have htrace : WordTrace (prefixWord ++ tailWord_3694488) baseStart_3694488 baseEnd_3694488 := by
    simpa [prefixWord, tailWord_3694488, baseEnd_3694488] using wordTrace_append hprefix tailTrace_3694488
  have hstable : (prefixWord ++ tailWord_3694488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694488).length < 2 ^ (prefixWord ++ tailWord_3694488).sum := by decide
  have hdescent : baseEnd_3694488 < baseStart_3694488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694538 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_3694538 : Nat := 118140960795 + 3694538 * 2 ^ 59
def prefixEnd_3694538 : Nat := 4983230072969 + 3 ^ 40 * 3694538 * 2
def baseEnd_3694538 : Nat := 1897073790300771336784135

theorem tailTrace_3694538 : CollatzResearch.WordTrace tailWord_3694538 prefixEnd_3694538 1897073790300771336784135 := by
  unfold tailWord_3694538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33687717772331819425219067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89833914059551518467250845 33687717772331819425219067)
  ·
    refine ⟨50531576658497729137828601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33687717772331819425219067 50531576658497729137828601)
    ·
      refine ⟨37898682493873296853371451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50531576658497729137828601 37898682493873296853371451)
      ·
        refine ⟨56848023740809945280057177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37898682493873296853371451 56848023740809945280057177)
        ·
          refine ⟨42636017805607458960042883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56848023740809945280057177 42636017805607458960042883)
          ·
            refine ⟨63954026708411188440064325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42636017805607458960042883 63954026708411188440064325)
            ·
              refine ⟨11991380007827097832512061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63954026708411188440064325 11991380007827097832512061)
              ·
                refine ⟨4496767502935161687192023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11991380007827097832512061 4496767502935161687192023)
                ·
                  refine ⟨6745151254402742530788035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496767502935161687192023 6745151254402742530788035)
                  ·
                    refine ⟨10117726881604113796182053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6745151254402742530788035 10117726881604113796182053)
                    ·
                      refine ⟨1897073790300771336784135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10117726881604113796182053 1897073790300771336784135)
                      ·
                        rfl

theorem cell23_3694538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_3694538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694538 prefixEnd_3694538 := by exact prefixLift 3694538
  have htrace : WordTrace (prefixWord ++ tailWord_3694538) baseStart_3694538 baseEnd_3694538 := by
    simpa [prefixWord, tailWord_3694538, baseEnd_3694538] using wordTrace_append hprefix tailTrace_3694538
  have hstable : (prefixWord ++ tailWord_3694538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694538).length < 2 ^ (prefixWord ++ tailWord_3694538).sum := by decide
  have hdescent : baseEnd_3694538 < baseStart_3694538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694544 : List Nat := [2, 1, 1, 1, 1, 2, 15]
def baseStart_3694544 : Nat := 118140960795 + 3694544 * 2 ^ 59
def prefixEnd_3694544 : Nat := 4983230072969 + 3 ^ 40 * 3694544 * 2
def baseEnd_3694544 : Nat := 23420702113391337201347

theorem tailTrace_3694544 : CollatzResearch.WordTrace tailWord_3694544 prefixEnd_3694544 23420702113391337201347 := by
  unfold tailWord_3694544
  simp only [CollatzResearch.WordTrace]
  refine ⟨67375544963652770362797343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89834059951537027150396457 67375544963652770362797343)
  ·
    refine ⟨101063317445479155544196015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67375544963652770362797343 101063317445479155544196015)
    ·
      refine ⟨151594976168218733316294023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101063317445479155544196015 151594976168218733316294023)
      ·
        refine ⟨227392464252328099974441035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151594976168218733316294023 227392464252328099974441035)
        ·
          refine ⟨341088696378492149961661553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227392464252328099974441035 341088696378492149961661553)
          ·
            refine ⟨255816522283869112471246165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341088696378492149961661553 255816522283869112471246165)
            ·
              refine ⟨23420702113391337201347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 255816522283869112471246165 23420702113391337201347)
              ·
                rfl

theorem cell23_3694544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 15].length) (baseStart_3694544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694544 prefixEnd_3694544 := by exact prefixLift 3694544
  have htrace : WordTrace (prefixWord ++ tailWord_3694544) baseStart_3694544 baseEnd_3694544 := by
    simpa [prefixWord, tailWord_3694544, baseEnd_3694544] using wordTrace_append hprefix tailTrace_3694544
  have hstable : (prefixWord ++ tailWord_3694544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694544).length < 2 ^ (prefixWord ++ tailWord_3694544).sum := by decide
  have hdescent : baseEnd_3694544 < baseStart_3694544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694548 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_3694548 : Nat := 118140960795 + 3694548 * 2 ^ 59
def prefixEnd_3694548 : Nat := 4983230072969 + 3 ^ 40 * 3694548 * 2
def baseEnd_3694548 : Nat := 632359641702438765886363

theorem tailTrace_3694548 : CollatzResearch.WordTrace tailWord_3694548 prefixEnd_3694548 632359641702438765886363 := by
  unfold tailWord_3694548
  simp only [CollatzResearch.WordTrace]
  refine ⟨67375617909645524704370149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89834157212860699605826865 67375617909645524704370149)
  ·
    refine ⟨12632928358058535882069403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67375617909645524704370149 12632928358058535882069403)
    ·
      refine ⟨18949392537087803823104105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12632928358058535882069403 18949392537087803823104105)
      ·
        refine ⟨14212044402815852867328079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18949392537087803823104105 14212044402815852867328079)
        ·
          refine ⟨21318066604223779300992119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14212044402815852867328079 21318066604223779300992119)
          ·
            refine ⟨31977099906335668951488179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21318066604223779300992119 31977099906335668951488179)
            ·
              refine ⟨47965649859503503427232269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31977099906335668951488179 47965649859503503427232269)
              ·
                refine ⟨17987118697313813785212101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47965649859503503427232269 17987118697313813785212101)
                ·
                  refine ⟨3372584755746340084727269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17987118697313813785212101 3372584755746340084727269)
                  ·
                    refine ⟨632359641702438765886363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3372584755746340084727269 632359641702438765886363)
                    ·
                      rfl

theorem cell23_3694548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_3694548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694548 prefixEnd_3694548 := by exact prefixLift 3694548
  have htrace : WordTrace (prefixWord ++ tailWord_3694548) baseStart_3694548 baseEnd_3694548 := by
    simpa [prefixWord, tailWord_3694548, baseEnd_3694548] using wordTrace_append hprefix tailTrace_3694548
  have hstable : (prefixWord ++ tailWord_3694548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694548).length < 2 ^ (prefixWord ++ tailWord_3694548).sum := by decide
  have hdescent : baseEnd_3694548 < baseStart_3694548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694549 : List Nat := [1, 3, 2, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3694549 : Nat := 118140960795 + 3694549 * 2 ^ 59
def prefixEnd_3694549 : Nat := 4983230072969 + 3 ^ 40 * 3694549 * 2
def baseEnd_3694549 : Nat := 1897079438587970793746585

theorem tailTrace_3694549 : CollatzResearch.WordTrace tailWord_3694549 prefixEnd_3694549 1897079438587970793746585 := by
  unfold tailWord_3694549
  simp only [CollatzResearch.WordTrace]
  refine ⟨134751272292287426579526701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89834181528191617719684467 134751272292287426579526701)
  ·
    refine ⟨50531727109607784967322513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134751272292287426579526701 50531727109607784967322513)
    ·
      refine ⟨37898795332205838725491885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50531727109607784967322513 37898795332205838725491885)
      ·
        refine ⟨14212048249577189522059457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37898795332205838725491885 14212048249577189522059457)
        ·
          refine ⟨10659036187182892141544593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14212048249577189522059457 10659036187182892141544593)
          ·
            refine ⟨7994277140387169106158445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10659036187182892141544593 7994277140387169106158445)
            ·
              refine ⟨2997853927645188414809417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7994277140387169106158445 2997853927645188414809417)
              ·
                refine ⟨2248390445733891311107063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2997853927645188414809417 2248390445733891311107063)
                ·
                  refine ⟨3372585668600836966660595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248390445733891311107063 3372585668600836966660595)
                  ·
                    refine ⟨5058878502901255449990893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372585668600836966660595 5058878502901255449990893)
                    ·
                      refine ⟨1897079438587970793746585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5058878502901255449990893 1897079438587970793746585)
                      ·
                        rfl

theorem cell23_3694549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3694549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694549 prefixEnd_3694549 := by exact prefixLift 3694549
  have htrace : WordTrace (prefixWord ++ tailWord_3694549) baseStart_3694549 baseEnd_3694549 := by
    simpa [prefixWord, tailWord_3694549, baseEnd_3694549] using wordTrace_append hprefix tailTrace_3694549
  have hstable : (prefixWord ++ tailWord_3694549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694549).length < 2 ^ (prefixWord ++ tailWord_3694549).sum := by decide
  have hdescent : baseEnd_3694549 < baseStart_3694549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694556 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 6]
def baseStart_3694556 : Nat := 118140960795 + 3694556 * 2 ^ 59
def prefixEnd_3694556 : Nat := 4983230072969 + 3 ^ 40 * 3694556 * 2
def baseEnd_3694556 : Nat := 210787003661394696262117

theorem tailTrace_3694556 : CollatzResearch.WordTrace tailWord_3694556 prefixEnd_3694556 210787003661394696262117 := by
  unfold tailWord_3694556
  simp only [CollatzResearch.WordTrace]
  refine ⟨67375763801631033387515761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89834351735508044516687681 67375763801631033387515761)
  ·
    refine ⟨50531822851223275040636821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67375763801631033387515761 50531822851223275040636821)
    ·
      refine ⟨2368679196151091017529851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50531822851223275040636821 2368679196151091017529851)
      ·
        refine ⟨3553018794226636526294777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368679196151091017529851 3553018794226636526294777)
        ·
          refine ⟨2664764095669977394721083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3553018794226636526294777 2664764095669977394721083)
          ·
            refine ⟨3997146143504966092081625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664764095669977394721083 3997146143504966092081625)
            ·
              refine ⟨2997859607628724569061219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3997146143504966092081625 2997859607628724569061219)
              ·
                refine ⟨4496789411443086853591829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997859607628724569061219 4496789411443086853591829)
                ·
                  refine ⟨210787003661394696262117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4496789411443086853591829 210787003661394696262117)
                  ·
                    rfl

theorem cell23_3694556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_3694556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694556 prefixEnd_3694556 := by exact prefixLift 3694556
  have htrace : WordTrace (prefixWord ++ tailWord_3694556) baseStart_3694556 baseEnd_3694556 := by
    simpa [prefixWord, tailWord_3694556, baseEnd_3694556] using wordTrace_append hprefix tailTrace_3694556
  have hstable : (prefixWord ++ tailWord_3694556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694556).length < 2 ^ (prefixWord ++ tailWord_3694556).sum := by decide
  have hdescent : baseEnd_3694556 < baseStart_3694556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694571 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 3]
def baseStart_3694571 : Nat := 118140960795 + 3694571 * 2 ^ 59
def prefixEnd_3694571 : Nat := 4983230072969 + 3 ^ 40 * 3694571 * 2
def baseEnd_3694571 : Nat := 1897090735162369707671483

theorem tailTrace_3694571 : CollatzResearch.WordTrace tailWord_3694571 prefixEnd_3694571 1897090735162369707671483 := by
  unfold tailWord_3694571
  simp only [CollatzResearch.WordTrace]
  refine ⟨134752074698207724336827567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89834716465471816224551711 134752074698207724336827567)
  ·
    refine ⟨202128112047311586505241351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134752074698207724336827567 202128112047311586505241351)
    ·
      refine ⟨303192168070967379757862027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202128112047311586505241351 303192168070967379757862027)
      ·
        refine ⟨454788252106451069636793041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303192168070967379757862027 454788252106451069636793041)
        ·
          refine ⟨341091189079838302227594781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454788252106451069636793041 341091189079838302227594781)
          ·
            refine ⟨127909195904939363335348043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341091189079838302227594781 127909195904939363335348043)
            ·
              refine ⟨191863793857409045003022065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127909195904939363335348043 191863793857409045003022065)
              ·
                refine ⟨143897845393056783752266549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191863793857409045003022065 143897845393056783752266549)
                ·
                  refine ⟨13490423005599073476774989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143897845393056783752266549 13490423005599073476774989)
                  ·
                    refine ⟨5058908627099652553790621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13490423005599073476774989 5058908627099652553790621)
                    ·
                      refine ⟨1897090735162369707671483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5058908627099652553790621 1897090735162369707671483)
                      ·
                        rfl

theorem cell23_3694571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 3].length) (baseStart_3694571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694571 prefixEnd_3694571 := by exact prefixLift 3694571
  have htrace : WordTrace (prefixWord ++ tailWord_3694571) baseStart_3694571 baseEnd_3694571 := by
    simpa [prefixWord, tailWord_3694571, baseEnd_3694571] using wordTrace_append hprefix tailTrace_3694571
  have hstable : (prefixWord ++ tailWord_3694571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694571).length < 2 ^ (prefixWord ++ tailWord_3694571).sum := by decide
  have hdescent : baseEnd_3694571 < baseStart_3694571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694588 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_3694588 : Nat := 118140960795 + 3694588 * 2 ^ 59
def prefixEnd_3694588 : Nat := 4983230072969 + 3 ^ 40 * 3694588 * 2
def baseEnd_3694588 : Nat := 1897099464333496141158905

theorem tailTrace_3694588 : CollatzResearch.WordTrace tailWord_3694588 prefixEnd_3694588 1897099464333496141158905 := by
  unfold tailWord_3694588
  simp only [CollatzResearch.WordTrace]
  refine ⟨67376347369573068120098209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89835129826097424160130945 67376347369573068120098209)
  ·
    refine ⟨50532260527179801090073657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67376347369573068120098209 50532260527179801090073657)
    ·
      refine ⟨37899195395384850817555243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50532260527179801090073657 37899195395384850817555243)
      ·
        refine ⟨56848793093077276226332865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37899195395384850817555243 56848793093077276226332865)
        ·
          refine ⟨42636594819807957169749649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56848793093077276226332865 42636594819807957169749649)
          ·
            refine ⟨31977446114855967877312237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42636594819807957169749649 31977446114855967877312237)
            ·
              refine ⟨11991542293070987953992089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31977446114855967877312237 11991542293070987953992089)
              ·
                refine ⟨8993656719803240965494067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11991542293070987953992089 8993656719803240965494067)
                ·
                  refine ⟨13490485079704861448241101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8993656719803240965494067 13490485079704861448241101)
                  ·
                    refine ⟨5058931904889323043090413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13490485079704861448241101 5058931904889323043090413)
                    ·
                      refine ⟨1897099464333496141158905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5058931904889323043090413 1897099464333496141158905)
                      ·
                        rfl

theorem cell23_3694588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_3694588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694588 prefixEnd_3694588 := by exact prefixLift 3694588
  have htrace : WordTrace (prefixWord ++ tailWord_3694588) baseStart_3694588 baseEnd_3694588 := by
    simpa [prefixWord, tailWord_3694588, baseEnd_3694588] using wordTrace_append hprefix tailTrace_3694588
  have hstable : (prefixWord ++ tailWord_3694588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694588).length < 2 ^ (prefixWord ++ tailWord_3694588).sum := by decide
  have hdescent : baseEnd_3694588 < baseStart_3694588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694611 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4]
def baseStart_3694611 : Nat := 118140960795 + 3694611 * 2 ^ 59
def prefixEnd_3694611 : Nat := 4983230072969 + 3 ^ 40 * 3694611 * 2
def baseEnd_3694611 : Nat := 1897111274388549551171299

theorem tailTrace_3694611 : CollatzResearch.WordTrace tailWord_3694611 prefixEnd_3694611 1897111274388549551171299 := by
  unfold tailWord_3694611
  simp only [CollatzResearch.WordTrace]
  refine ⟨134753533618062811168283687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89835689078708540778855791 134753533618062811168283687)
  ·
    refine ⟨202130300427094216752425531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134753533618062811168283687 202130300427094216752425531)
    ·
      refine ⟨303195450640641325128638297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202130300427094216752425531 303195450640641325128638297)
      ·
        refine ⟨227396587980480993846478723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303195450640641325128638297 227396587980480993846478723)
        ·
          refine ⟨341094881970721490769718085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227396587980480993846478723 341094881970721490769718085)
          ·
            refine ⟨63955290369510279519322141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 341094881970721490769718085 63955290369510279519322141)
            ·
              refine ⟨23983233888566354819745803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63955290369510279519322141 23983233888566354819745803)
              ·
                refine ⟨35974850832849532229618705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23983233888566354819745803 35974850832849532229618705)
                ·
                  refine ⟨26981138124637149172214029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35974850832849532229618705 26981138124637149172214029)
                  ·
                    refine ⟨10117926796738930939580261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26981138124637149172214029 10117926796738930939580261)
                    ·
                      refine ⟨1897111274388549551171299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10117926796738930939580261 1897111274388549551171299)
                      ·
                        rfl

theorem cell23_3694611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_3694611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694611 prefixEnd_3694611 := by exact prefixLift 3694611
  have htrace : WordTrace (prefixWord ++ tailWord_3694611) baseStart_3694611 baseEnd_3694611 := by
    simpa [prefixWord, tailWord_3694611, baseEnd_3694611] using wordTrace_append hprefix tailTrace_3694611
  have hstable : (prefixWord ++ tailWord_3694611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694611).length < 2 ^ (prefixWord ++ tailWord_3694611).sum := by decide
  have hdescent : baseEnd_3694611 < baseStart_3694611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694612 : List Nat := [2, 4, 3, 2, 1, 2, 1, 8]
def baseStart_3694612 : Nat := 118140960795 + 3694612 * 2 ^ 59
def prefixEnd_3694612 : Nat := 4983230072969 + 3 ^ 40 * 3694612 * 2
def baseEnd_3694612 : Nat := 70263399550711261009585

theorem tailTrace_3694612 : CollatzResearch.WordTrace tailWord_3694612 prefixEnd_3694612 70263399550711261009585 := by
  unfold tailWord_3694612
  simp only [CollatzResearch.WordTrace]
  refine ⟨67376785045529594169535045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89835713394039458892713393 67376785045529594169535045)
  ·
    refine ⟨12633147196036798906787821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67376785045529594169535045 12633147196036798906787821)
    ·
      refine ⟨4737430198513799590045433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12633147196036798906787821 4737430198513799590045433)
      ·
        refine ⟨3553072648885349692534075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4737430198513799590045433 3553072648885349692534075)
        ·
          refine ⟨5329608973328024538801113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553072648885349692534075 5329608973328024538801113)
          ·
            refine ⟨3997206729996018404100835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5329608973328024538801113 3997206729996018404100835)
            ·
              refine ⟨5995810094994027606151253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997206729996018404100835 5995810094994027606151253)
              ·
                refine ⟨70263399550711261009585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5995810094994027606151253 70263399550711261009585)
                ·
                  rfl

theorem cell23_3694612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 8].length) (baseStart_3694612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694612 prefixEnd_3694612 := by exact prefixLift 3694612
  have htrace : WordTrace (prefixWord ++ tailWord_3694612) baseStart_3694612 baseEnd_3694612 := by
    simpa [prefixWord, tailWord_3694612, baseEnd_3694612] using wordTrace_append hprefix tailTrace_3694612
  have hstable : (prefixWord ++ tailWord_3694612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694612).length < 2 ^ (prefixWord ++ tailWord_3694612).sum := by decide
  have hdescent : baseEnd_3694612 < baseStart_3694612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694645 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_3694645 : Nat := 118140960795 + 3694645 * 2 ^ 59
def prefixEnd_3694645 : Nat := 4983230072969 + 3 ^ 40 * 3694645 * 2
def baseEnd_3694645 : Nat := 1897128732730802418146143

theorem tailTrace_3694645 : CollatzResearch.WordTrace tailWord_3694645 prefixEnd_3694645 1897128732730802418146143 := by
  unfold tailWord_3694645
  simp only [CollatzResearch.WordTrace]
  refine ⟨134754773699939634975021389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89836515799959756650014259 134754773699939634975021389)
  ·
    refine ⟨50533040137477363115633021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134754773699939634975021389 50533040137477363115633021)
    ·
      refine ⟨18949890051554011168362383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50533040137477363115633021 18949890051554011168362383)
      ·
        refine ⟨28424835077331016752543575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18949890051554011168362383 28424835077331016752543575)
        ·
          refine ⟨42637252615996525128815363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28424835077331016752543575 42637252615996525128815363)
          ·
            refine ⟨63955878923994787693223045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42637252615996525128815363 63955878923994787693223045)
            ·
              refine ⟨11991727298249022692479321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63955878923994787693223045 11991727298249022692479321)
              ·
                refine ⟨8993795473686767019359491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11991727298249022692479321 8993795473686767019359491)
                ·
                  refine ⟨13490693210530150529039237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8993795473686767019359491 13490693210530150529039237)
                  ·
                    refine ⟨2529504976974403224194857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13490693210530150529039237 2529504976974403224194857)
                    ·
                      refine ⟨1897128732730802418146143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529504976974403224194857 1897128732730802418146143)
                      ·
                        rfl

theorem cell23_3694645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_3694645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694645 prefixEnd_3694645 := by exact prefixLift 3694645
  have htrace : WordTrace (prefixWord ++ tailWord_3694645) baseStart_3694645 baseEnd_3694645 := by
    simpa [prefixWord, tailWord_3694645, baseEnd_3694645] using wordTrace_append hprefix tailTrace_3694645
  have hstable : (prefixWord ++ tailWord_3694645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694645).length < 2 ^ (prefixWord ++ tailWord_3694645).sum := by decide
  have hdescent : baseEnd_3694645 < baseStart_3694645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694681 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 3, 7]
def baseStart_3694681 : Nat := 118140960795 + 3694681 * 2 ^ 59
def prefixEnd_3694681 : Nat := 4983230072969 + 3 ^ 40 * 3694681 * 2
def baseEnd_3694681 : Nat := 632382406011454759098659

theorem tailTrace_3694681 : CollatzResearch.WordTrace tailWord_3694681 prefixEnd_3694681 632382406011454759098659 := by
  unfold tailWord_3694681
  simp only [CollatzResearch.WordTrace]
  refine ⟨134756086727809213123331897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89837391151872808748887931 134756086727809213123331897)
  ·
    refine ⟨101067065045856909842498923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134756086727809213123331897 101067065045856909842498923)
    ·
      refine ⟨151600597568785364763748385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101067065045856909842498923 151600597568785364763748385)
      ·
        refine ⟨113700448176589023572811289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151600597568785364763748385 113700448176589023572811289)
        ·
          refine ⟨85275336132441767679608467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113700448176589023572811289 85275336132441767679608467)
          ·
            refine ⟨127913004198662651519412701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85275336132441767679608467 127913004198662651519412701)
            ·
              refine ⟨47967376574498494319779763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127913004198662651519412701 47967376574498494319779763)
              ·
                refine ⟨71951064861747741479669645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47967376574498494319779763 71951064861747741479669645)
                ·
                  refine ⟨26981649323155403054876117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71951064861747741479669645 26981649323155403054876117)
                  ·
                    refine ⟨632382406011454759098659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26981649323155403054876117 632382406011454759098659)
                    ·
                      rfl

theorem cell23_3694681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_3694681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694681 prefixEnd_3694681 := by exact prefixLift 3694681
  have htrace : WordTrace (prefixWord ++ tailWord_3694681) baseStart_3694681 baseEnd_3694681 := by
    simpa [prefixWord, tailWord_3694681, baseEnd_3694681] using wordTrace_append hprefix tailTrace_3694681
  have hstable : (prefixWord ++ tailWord_3694681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694681).length < 2 ^ (prefixWord ++ tailWord_3694681).sum := by decide
  have hdescent : baseEnd_3694681 < baseStart_3694681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694685 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 7]
def baseStart_3694685 : Nat := 118140960795 + 3694685 * 2 ^ 59
def prefixEnd_3694685 : Nat := 4983230072969 + 3 ^ 40 * 3694685 * 2
def baseEnd_3694685 : Nat := 210794363550775806849551

theorem tailTrace_3694685 : CollatzResearch.WordTrace tailWord_3694685 prefixEnd_3694685 210794363550775806849551 := by
  unfold tailWord_3694685
  simp only [CollatzResearch.WordTrace]
  refine ⟨134756232619794721806477509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89837488413196481204318339 134756232619794721806477509)
  ·
    refine ⟨25266793616211510338714533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134756232619794721806477509 25266793616211510338714533)
    ·
      refine ⟨4737523803039658188508975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25266793616211510338714533 4737523803039658188508975)
      ·
        refine ⟨7106285704559487282763463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737523803039658188508975 7106285704559487282763463)
        ·
          refine ⟨10659428556839230924145195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106285704559487282763463 10659428556839230924145195)
          ·
            refine ⟨15989142835258846386217793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10659428556839230924145195 15989142835258846386217793)
            ·
              refine ⟨11991857126444134789663345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15989142835258846386217793 11991857126444134789663345)
              ·
                refine ⟨8993892844833101092247509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11991857126444134789663345 8993892844833101092247509)
                ·
                  refine ⟨210794363550775806849551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8993892844833101092247509 210794363550775806849551)
                  ·
                    rfl

theorem cell23_3694685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_3694685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694685 prefixEnd_3694685 := by exact prefixLift 3694685
  have htrace : WordTrace (prefixWord ++ tailWord_3694685) baseStart_3694685 baseEnd_3694685 := by
    simpa [prefixWord, tailWord_3694685, baseEnd_3694685] using wordTrace_append hprefix tailTrace_3694685
  have hstable : (prefixWord ++ tailWord_3694685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694685).length < 2 ^ (prefixWord ++ tailWord_3694685).sum := by decide
  have hdescent : baseEnd_3694685 < baseStart_3694685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694775 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 6]
def baseStart_3694775 : Nat := 118140960795 + 3694775 * 2 ^ 59
def prefixEnd_3694775 : Nat := 4983230072969 + 3 ^ 40 * 3694775 * 2
def baseEnd_3694775 : Nat := 210799498357320767724505

theorem tailTrace_3694775 : CollatzResearch.WordTrace tailWord_3694775 prefixEnd_3694775 210799498357320767724505 := by
  unfold tailWord_3694775
  simp only [CollatzResearch.WordTrace]
  refine ⟨134759515189468667177253779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89839676792979111451502519 134759515189468667177253779)
  ·
    refine ⟨202139272784203000765880669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134759515189468667177253779 202139272784203000765880669)
    ·
      refine ⟨75802227294076125287205251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202139272784203000765880669 75802227294076125287205251)
      ·
        refine ⟨113703340941114187930807877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75802227294076125287205251 113703340941114187930807877)
        ·
          refine ⟨21319376426458910237026477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113703340941114187930807877 21319376426458910237026477)
          ·
            refine ⟨7994766159922091338884929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21319376426458910237026477 7994766159922091338884929)
            ·
              refine ⟨5996074619941568504163697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7994766159922091338884929 5996074619941568504163697)
              ·
                refine ⟨4497055964956176378122773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996074619941568504163697 4497055964956176378122773)
                ·
                  refine ⟨210799498357320767724505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4497055964956176378122773 210799498357320767724505)
                  ·
                    rfl

theorem cell23_3694775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 6].length) (baseStart_3694775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694775 prefixEnd_3694775 := by exact prefixLift 3694775
  have htrace : WordTrace (prefixWord ++ tailWord_3694775) baseStart_3694775 baseEnd_3694775 := by
    simpa [prefixWord, tailWord_3694775, baseEnd_3694775] using wordTrace_append hprefix tailTrace_3694775
  have hstable : (prefixWord ++ tailWord_3694775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694775).length < 2 ^ (prefixWord ++ tailWord_3694775).sum := by decide
  have hdescent : baseEnd_3694775 < baseStart_3694775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694786 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_3694786 : Nat := 118140960795 + 3694786 * 2 ^ 59
def prefixEnd_3694786 : Nat := 4983230072969 + 3 ^ 40 * 3694786 * 2
def baseEnd_3694786 : Nat := 1897201133503086366482995

theorem tailTrace_3694786 : CollatzResearch.WordTrace tailWord_3694786 prefixEnd_3694786 1897201133503086366482995 := by
  unfold tailWord_3694786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33689979098107204013976053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89839944261619210703936141 33689979098107204013976053)
  ·
    refine ⟨3158435540447550376310255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33689979098107204013976053 3158435540447550376310255)
    ·
      refine ⟨4737653310671325564465383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3158435540447550376310255 4737653310671325564465383)
      ·
        refine ⟨7106479966006988346698075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4737653310671325564465383 7106479966006988346698075)
        ·
          refine ⟨10659719949010482520047113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106479966006988346698075 10659719949010482520047113)
          ·
            refine ⟨7994789961757861890035335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10659719949010482520047113 7994789961757861890035335)
            ·
              refine ⟨11992184942636792835053003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7994789961757861890035335 11992184942636792835053003)
              ·
                refine ⟨17988277413955189252579505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992184942636792835053003 17988277413955189252579505)
                ·
                  refine ⟨13491208060466391939434629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17988277413955189252579505 13491208060466391939434629)
                  ·
                    refine ⟨2529601511337448488643993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13491208060466391939434629 2529601511337448488643993)
                    ·
                      refine ⟨1897201133503086366482995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529601511337448488643993 1897201133503086366482995)
                      ·
                        rfl

theorem cell23_3694786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_3694786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694786 prefixEnd_3694786 := by exact prefixLift 3694786
  have htrace : WordTrace (prefixWord ++ tailWord_3694786) baseStart_3694786 baseEnd_3694786 := by
    simpa [prefixWord, tailWord_3694786, baseEnd_3694786] using wordTrace_append hprefix tailTrace_3694786
  have hstable : (prefixWord ++ tailWord_3694786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694786).length < 2 ^ (prefixWord ++ tailWord_3694786).sum := by decide
  have hdescent : baseEnd_3694786 < baseStart_3694786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694795 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 1, 5, 2]
def baseStart_3694795 : Nat := 118140960795 + 3694795 * 2 ^ 59
def prefixEnd_3694795 : Nat := 4983230072969 + 3 ^ 40 * 3694795 * 2
def baseEnd_3694795 : Nat := 1897205754828976831270453

theorem tailTrace_3694795 : CollatzResearch.WordTrace tailWord_3694795 prefixEnd_3694795 1897205754828976831270453 := by
  unfold tailWord_3694795
  simp only [CollatzResearch.WordTrace]
  refine ⟨134760244649396210592981839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89840163099597473728654559 134760244649396210592981839)
  ·
    refine ⟨202140366974094315889472759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134760244649396210592981839 202140366974094315889472759)
    ·
      refine ⟨303210550461141473834209139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202140366974094315889472759 303210550461141473834209139)
      ·
        refine ⟨454815825691712210751313709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303210550461141473834209139 454815825691712210751313709)
        ·
          refine ⟨170555934634392079031742641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454815825691712210751313709 170555934634392079031742641)
          ·
            refine ⟨127916950975794059273806981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170555934634392079031742641 127916950975794059273806981)
            ·
              refine ⟨23984428307961386113838809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127916950975794059273806981 23984428307961386113838809)
              ·
                refine ⟨17988321230971039585379107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23984428307961386113838809 17988321230971039585379107)
                ·
                  refine ⟨26982481846456559378068661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17988321230971039585379107 26982481846456559378068661)
                  ·
                    refine ⟨2529607673105302441693937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26982481846456559378068661 2529607673105302441693937)
                    ·
                      refine ⟨1897205754828976831270453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529607673105302441693937 1897205754828976831270453)
                      ·
                        rfl

theorem cell23_3694795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 5, 2].length) (baseStart_3694795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694795 prefixEnd_3694795 := by exact prefixLift 3694795
  have htrace : WordTrace (prefixWord ++ tailWord_3694795) baseStart_3694795 baseEnd_3694795 := by
    simpa [prefixWord, tailWord_3694795, baseEnd_3694795] using wordTrace_append hprefix tailTrace_3694795
  have hstable : (prefixWord ++ tailWord_3694795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694795).length < 2 ^ (prefixWord ++ tailWord_3694795).sum := by decide
  have hdescent : baseEnd_3694795 < baseStart_3694795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694802 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_3694802 : Nat := 118140960795 + 3694802 * 2 ^ 59
def prefixEnd_3694802 : Nat := 4983230072969 + 3 ^ 40 * 3694802 * 2
def baseEnd_3694802 : Nat := 1897209349193558303882921

theorem tailTrace_3694802 : CollatzResearch.WordTrace tailWord_3694802 prefixEnd_3694802 1897209349193558303882921 := by
  unfold tailWord_3694802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33690124990092712697121665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89840333306913900525657773 33690124990092712697121665)
  ·
    refine ⟨25267593742569534522841249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33690124990092712697121665 25267593742569534522841249)
    ·
      refine ⟨18950695306927150892130937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25267593742569534522841249 18950695306927150892130937)
      ·
        refine ⟨14213021480195363169098203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18950695306927150892130937 14213021480195363169098203)
        ·
          refine ⟨21319532220293044753647305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14213021480195363169098203 21319532220293044753647305)
          ·
            refine ⟨15989649165219783565235479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21319532220293044753647305 15989649165219783565235479)
            ·
              refine ⟨23984473747829675347853219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15989649165219783565235479 23984473747829675347853219)
              ·
                refine ⟨35976710621744513021779829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23984473747829675347853219 35976710621744513021779829)
                ·
                  refine ⟨3372816620788548095791859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35976710621744513021779829 3372816620788548095791859)
                  ·
                    refine ⟨5059224931182822143687789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372816620788548095791859 5059224931182822143687789)
                    ·
                      refine ⟨1897209349193558303882921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059224931182822143687789 1897209349193558303882921)
                      ·
                        rfl

theorem cell23_3694802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_3694802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694802 prefixEnd_3694802 := by exact prefixLift 3694802
  have htrace : WordTrace (prefixWord ++ tailWord_3694802) baseStart_3694802 baseEnd_3694802 := by
    simpa [prefixWord, tailWord_3694802, baseEnd_3694802] using wordTrace_append hprefix tailTrace_3694802
  have hstable : (prefixWord ++ tailWord_3694802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694802).length < 2 ^ (prefixWord ++ tailWord_3694802).sum := by decide
  have hdescent : baseEnd_3694802 < baseStart_3694802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694806 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3694806 : Nat := 118140960795 + 3694806 * 2 ^ 59
def prefixEnd_3694806 : Nat := 4983230072969 + 3 ^ 40 * 3694806 * 2
def baseEnd_3694806 : Nat := 1897211403116176288232903

theorem tailTrace_3694806 : CollatzResearch.WordTrace tailWord_3694806 prefixEnd_3694806 1897211403116176288232903 := by
  unfold tailWord_3694806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422540365772272466977017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89840430568237572981088181 8422540365772272466977017)
  ·
    refine ⟨6316905274329204350232763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8422540365772272466977017 6316905274329204350232763)
    ·
      refine ⟨9475357911493806525349145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6316905274329204350232763 9475357911493806525349145)
      ·
        refine ⟨7106518433620354894011859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9475357911493806525349145 7106518433620354894011859)
        ·
          refine ⟨10659777650430532341017789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106518433620354894011859 10659777650430532341017789)
          ·
            refine ⟨3997416618911449627881671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10659777650430532341017789 3997416618911449627881671)
            ·
              refine ⟨5996124928367174441822507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997416618911449627881671 5996124928367174441822507)
              ·
                refine ⟨8994187392550761662733761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996124928367174441822507 8994187392550761662733761)
                ·
                  refine ⟨6745640544413071247050321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8994187392550761662733761 6745640544413071247050321)
                  ·
                    refine ⟨5059230408309803435287741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6745640544413071247050321 5059230408309803435287741)
                    ·
                      refine ⟨1897211403116176288232903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059230408309803435287741 1897211403116176288232903)
                      ·
                        rfl

theorem cell23_3694806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3694806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694806 prefixEnd_3694806 := by exact prefixLift 3694806
  have htrace : WordTrace (prefixWord ++ tailWord_3694806) baseStart_3694806 baseEnd_3694806 := by
    simpa [prefixWord, tailWord_3694806, baseEnd_3694806] using wordTrace_append hprefix tailTrace_3694806
  have hstable : (prefixWord ++ tailWord_3694806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694806).length < 2 ^ (prefixWord ++ tailWord_3694806).sum := by decide
  have hdescent : baseEnd_3694806 < baseStart_3694806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694825 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 4]
def baseStart_3694825 : Nat := 118140960795 + 3694825 * 2 ^ 59
def prefixEnd_3694825 : Nat := 4983230072969 + 3 ^ 40 * 3694825 * 2
def baseEnd_3694825 : Nat := 1897221159248611713895315

theorem tailTrace_3694825 : CollatzResearch.WordTrace tailWord_3694825 prefixEnd_3694825 1897221159248611713895315 := by
  unfold tailWord_3694825
  simp only [CollatzResearch.WordTrace]
  refine ⟨134761338839287525716573929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89840892559525017144382619 134761338839287525716573929)
  ·
    refine ⟨101071004129465644287430447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134761338839287525716573929 101071004129465644287430447)
    ·
      refine ⟨151606506194198466431145671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101071004129465644287430447 151606506194198466431145671)
      ·
        refine ⟨227409759291297699646718507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151606506194198466431145671 227409759291297699646718507)
        ·
          refine ⟨341114638936946549470077761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227409759291297699646718507 341114638936946549470077761)
          ·
            refine ⟨255835979202709912102558321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341114638936946549470077761 255835979202709912102558321)
            ·
              refine ⟨191876984402032434076918741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255835979202709912102558321 191876984402032434076918741)
              ·
                refine ⟨4497116821922635173677783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191876984402032434076918741 4497116821922635173677783)
                ·
                  refine ⟨6745675232883952760516675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497116821922635173677783 6745675232883952760516675)
                  ·
                    refine ⟨10118512849325929140775013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6745675232883952760516675 10118512849325929140775013)
                    ·
                      refine ⟨1897221159248611713895315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10118512849325929140775013 1897221159248611713895315)
                      ·
                        rfl

theorem cell23_3694825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_3694825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694825 prefixEnd_3694825 := by exact prefixLift 3694825
  have htrace : WordTrace (prefixWord ++ tailWord_3694825) baseStart_3694825 baseEnd_3694825 := by
    simpa [prefixWord, tailWord_3694825, baseEnd_3694825] using wordTrace_append hprefix tailTrace_3694825
  have hstable : (prefixWord ++ tailWord_3694825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694825).length < 2 ^ (prefixWord ++ tailWord_3694825).sum := by decide
  have hdescent : baseEnd_3694825 < baseStart_3694825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694835 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 4, 4]
def baseStart_3694835 : Nat := 118140960795 + 3694835 * 2 ^ 59
def prefixEnd_3694835 : Nat := 4983230072969 + 3 ^ 40 * 3694835 * 2
def baseEnd_3694835 : Nat := 632408764685052224923423

theorem tailTrace_3694835 : CollatzResearch.WordTrace tailWord_3694835 prefixEnd_3694835 632408764685052224923423 := by
  unfold tailWord_3694835
  simp only [CollatzResearch.WordTrace]
  refine ⟨134761703569251297424437959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89841135712834198282958639 134761703569251297424437959)
  ·
    refine ⟨202142555353876946136656939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134761703569251297424437959 202142555353876946136656939)
    ·
      refine ⟨303213833030815419204985409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202142555353876946136656939 303213833030815419204985409)
      ·
        refine ⟨227410374773111564403739057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303213833030815419204985409 227410374773111564403739057)
        ·
          refine ⟨170557781079833673302804293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227410374773111564403739057 170557781079833673302804293)
          ·
            refine ⟨31979583952468813744275805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170557781079833673302804293 31979583952468813744275805)
            ·
              refine ⟨11992343982175805154103427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31979583952468813744275805 11992343982175805154103427)
              ·
                refine ⟨17988515973263707731155141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992343982175805154103427 17988515973263707731155141)
                ·
                  refine ⟨3372846744986945199591589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17988515973263707731155141 3372846744986945199591589)
                  ·
                    refine ⟨632408764685052224923423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3372846744986945199591589 632408764685052224923423)
                    ·
                      rfl

theorem cell23_3694835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 4].length) (baseStart_3694835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694835 prefixEnd_3694835 := by exact prefixLift 3694835
  have htrace : WordTrace (prefixWord ++ tailWord_3694835) baseStart_3694835 baseEnd_3694835 := by
    simpa [prefixWord, tailWord_3694835, baseEnd_3694835] using wordTrace_append hprefix tailTrace_3694835
  have hstable : (prefixWord ++ tailWord_3694835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694835).length < 2 ^ (prefixWord ++ tailWord_3694835).sum := by decide
  have hdescent : baseEnd_3694835 < baseStart_3694835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694845 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_3694845 : Nat := 118140960795 + 3694845 * 2 ^ 59
def prefixEnd_3694845 : Nat := 4983230072969 + 3 ^ 40 * 3694845 * 2
def baseEnd_3694845 : Nat := 1897231428861701635645223

theorem tailTrace_3694845 : CollatzResearch.WordTrace tailWord_3694845 prefixEnd_3694845 1897231428861701635645223 := by
  unfold tailWord_3694845
  simp only [CollatzResearch.WordTrace]
  refine ⟨134762068299215069132301989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89841378866143379421534659 134762068299215069132301989)
  ·
    refine ⟨25267887806102825462306623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134762068299215069132301989 25267887806102825462306623)
    ·
      refine ⟨37901831709154238193459935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25267887806102825462306623 37901831709154238193459935)
      ·
        refine ⟨56852747563731357290189903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37901831709154238193459935 56852747563731357290189903)
        ·
          refine ⟨85279121345597035935284855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56852747563731357290189903 85279121345597035935284855)
          ·
            refine ⟨127918682018395553902927283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85279121345597035935284855 127918682018395553902927283)
            ·
              refine ⟨191878023027593330854390925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127918682018395553902927283 191878023027593330854390925)
              ·
                refine ⟨71954258635347499070396597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191878023027593330854390925 71954258635347499070396597)
                ·
                  refine ⟨6745711747063828037849681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71954258635347499070396597 6745711747063828037849681)
                  ·
                    refine ⟨5059283810297871028387261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6745711747063828037849681 5059283810297871028387261)
                    ·
                      refine ⟨1897231428861701635645223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059283810297871028387261 1897231428861701635645223)
                      ·
                        rfl

theorem cell23_3694845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_3694845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694845 prefixEnd_3694845 := by exact prefixLift 3694845
  have htrace : WordTrace (prefixWord ++ tailWord_3694845) baseStart_3694845 baseEnd_3694845 := by
    simpa [prefixWord, tailWord_3694845, baseEnd_3694845] using wordTrace_append hprefix tailTrace_3694845
  have hstable : (prefixWord ++ tailWord_3694845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694845).length < 2 ^ (prefixWord ++ tailWord_3694845).sum := by decide
  have hdescent : baseEnd_3694845 < baseStart_3694845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694865 : List Nat := [1, 2, 2, 1, 1, 5, 4, 7]
def baseStart_3694865 : Nat := 118140960795 + 3694865 * 2 ^ 59
def prefixEnd_3694865 : Nat := 4983230072969 + 3 ^ 40 * 3694865 * 2
def baseEnd_3694865 : Nat := 70268211054621909533153

theorem tailTrace_3694865 : CollatzResearch.WordTrace tailWord_3694865 prefixEnd_3694865 70268211054621909533153 := by
  unfold tailWord_3694865
  simp only [CollatzResearch.WordTrace]
  refine ⟨134762797759142612548030049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89841865172761741698686699 134762797759142612548030049)
  ·
    refine ⟨101072098319356959411022537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134762797759142612548030049 101072098319356959411022537)
    ·
      refine ⟨75804073739517719558266903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101072098319356959411022537 75804073739517719558266903)
      ·
        refine ⟨113706110609276579337400355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75804073739517719558266903 113706110609276579337400355)
        ·
          refine ⟨170559165913914869006100533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113706110609276579337400355 170559165913914869006100533)
          ·
            refine ⟨15989921804429518969321925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170559165913914869006100533 15989921804429518969321925)
            ·
              refine ⟨2998110338330534806747861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15989921804429518969321925 2998110338330534806747861)
              ·
                refine ⟨70268211054621909533153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2998110338330534806747861 70268211054621909533153)
                ·
                  rfl

theorem cell23_3694865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 7].length) (baseStart_3694865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694865 prefixEnd_3694865 := by exact prefixLift 3694865
  have htrace : WordTrace (prefixWord ++ tailWord_3694865) baseStart_3694865 baseEnd_3694865 := by
    simpa [prefixWord, tailWord_3694865, baseEnd_3694865] using wordTrace_append hprefix tailTrace_3694865
  have hstable : (prefixWord ++ tailWord_3694865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694865).length < 2 ^ (prefixWord ++ tailWord_3694865).sum := by decide
  have hdescent : baseEnd_3694865 < baseStart_3694865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694875 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 3]
def baseStart_3694875 : Nat := 118140960795 + 3694875 * 2 ^ 59
def prefixEnd_3694875 : Nat := 4983230072969 + 3 ^ 40 * 3694875 * 2
def baseEnd_3694875 : Nat := 1897246833281336518270085

theorem tailTrace_3694875 : CollatzResearch.WordTrace tailWord_3694875 prefixEnd_3694875 1897246833281336518270085 := by
  unfold tailWord_3694875
  simp only [CollatzResearch.WordTrace]
  refine ⟨134763162489106384255894079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89842108326070922837262719 134763162489106384255894079)
  ·
    refine ⟨202144743733659576383841119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134763162489106384255894079 202144743733659576383841119)
    ·
      refine ⟨303217115600489364575761679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202144743733659576383841119 303217115600489364575761679)
      ·
        refine ⟨454825673400734046863642519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303217115600489364575761679 454825673400734046863642519)
        ·
          refine ⟨682238510101101070295463779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454825673400734046863642519 682238510101101070295463779)
          ·
            refine ⟨1023357765151651605443195669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682238510101101070295463779 1023357765151651605443195669)
            ·
              refine ⟨47969895241483669005149797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1023357765151651605443195669 47969895241483669005149797)
              ·
                refine ⟨8994355357778187938465587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47969895241483669005149797 8994355357778187938465587)
                ·
                  refine ⟨13491533036667281907698381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8994355357778187938465587 13491533036667281907698381)
                  ·
                    refine ⟨5059324888750230715386893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13491533036667281907698381 5059324888750230715386893)
                    ·
                      refine ⟨1897246833281336518270085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059324888750230715386893 1897246833281336518270085)
                      ·
                        rfl

theorem cell23_3694875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 3].length) (baseStart_3694875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694875 prefixEnd_3694875 := by exact prefixLift 3694875
  have htrace : WordTrace (prefixWord ++ tailWord_3694875) baseStart_3694875 baseEnd_3694875 := by
    simpa [prefixWord, tailWord_3694875, baseEnd_3694875] using wordTrace_append hprefix tailTrace_3694875
  have hstable : (prefixWord ++ tailWord_3694875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694875).length < 2 ^ (prefixWord ++ tailWord_3694875).sum := by decide
  have hdescent : baseEnd_3694875 < baseStart_3694875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694887 : List Nat := [1, 1, 8, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3694887 : Nat := 118140960795 + 3694887 * 2 ^ 59
def prefixEnd_3694887 : Nat := 4983230072969 + 3 ^ 40 * 3694887 * 2
def baseEnd_3694887 : Nat := 1897252995049190471320031

theorem tailTrace_3694887 : CollatzResearch.WordTrace tailWord_3694887 prefixEnd_3694887 1897252995049190471320031 := by
  unfold tailWord_3694887
  simp only [CollatzResearch.WordTrace]
  refine ⟨134763600165062910305330915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89842400110041940203553943 134763600165062910305330915)
  ·
    refine ⟨202145400247594365457996373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134763600165062910305330915 202145400247594365457996373)
    ·
      refine ⟨2368891409151496470210895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 202145400247594365457996373 2368891409151496470210895)
      ·
        refine ⟨3553337113727244705316343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368891409151496470210895 3553337113727244705316343)
        ·
          refine ⟨5330005670590867057974515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553337113727244705316343 5330005670590867057974515)
          ·
            refine ⟨7995008505886300586961773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330005670590867057974515 7995008505886300586961773)
            ·
              refine ⟨2998128189707362720110665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7995008505886300586961773 2998128189707362720110665)
              ·
                refine ⟨2248596142280522040082999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998128189707362720110665 2248596142280522040082999)
                ·
                  refine ⟨3372894213420783060124499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248596142280522040082999 3372894213420783060124499)
                  ·
                    refine ⟨5059341320131174590186749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372894213420783060124499 5059341320131174590186749)
                    ·
                      refine ⟨1897252995049190471320031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059341320131174590186749 1897252995049190471320031)
                      ·
                        rfl

theorem cell23_3694887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3694887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694887 prefixEnd_3694887 := by exact prefixLift 3694887
  have htrace : WordTrace (prefixWord ++ tailWord_3694887) baseStart_3694887 baseEnd_3694887 := by
    simpa [prefixWord, tailWord_3694887, baseEnd_3694887] using wordTrace_append hprefix tailTrace_3694887
  have hstable : (prefixWord ++ tailWord_3694887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694887).length < 2 ^ (prefixWord ++ tailWord_3694887).sum := by decide
  have hdescent : baseEnd_3694887 < baseStart_3694887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694892 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_3694892 : Nat := 118140960795 + 3694892 * 2 ^ 59
def prefixEnd_3694892 : Nat := 4983230072969 + 3 ^ 40 * 3694892 * 2
def baseEnd_3694892 : Nat := 1897255562452462951757507

theorem tailTrace_3694892 : CollatzResearch.WordTrace tailWord_3694892 prefixEnd_3694892 1897255562452462951757507 := by
  unfold tailWord_3694892
  simp only [CollatzResearch.WordTrace]
  refine ⟨67381891265022398079631465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89842521686696530772841953 67381891265022398079631465)
  ·
    refine ⟨50536418448766798559723599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67381891265022398079631465 50536418448766798559723599)
    ·
      refine ⟨75804627673150197839585399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50536418448766798559723599 75804627673150197839585399)
      ·
        refine ⟨113706941509725296759378099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75804627673150197839585399 113706941509725296759378099)
        ·
          refine ⟨170560412264587945139067149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113706941509725296759378099 170560412264587945139067149)
          ·
            refine ⟨63960154599220479427150181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170560412264587945139067149 63960154599220479427150181)
            ·
              refine ⟨11992528987353839892590659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63960154599220479427150181 11992528987353839892590659)
              ·
                refine ⟨17988793481030759838885989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992528987353839892590659 17988793481030759838885989)
                ·
                  refine ⟨3372898777693267469791123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17988793481030759838885989 3372898777693267469791123)
                  ·
                    refine ⟨5059348166539901204686685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3372898777693267469791123 5059348166539901204686685)
                    ·
                      refine ⟨1897255562452462951757507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059348166539901204686685 1897255562452462951757507)
                      ·
                        rfl

theorem cell23_3694892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_3694892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694892 prefixEnd_3694892 := by exact prefixLift 3694892
  have htrace : WordTrace (prefixWord ++ tailWord_3694892) baseStart_3694892 baseEnd_3694892 := by
    simpa [prefixWord, tailWord_3694892, baseEnd_3694892] using wordTrace_append hprefix tailTrace_3694892
  have hstable : (prefixWord ++ tailWord_3694892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694892).length < 2 ^ (prefixWord ++ tailWord_3694892).sum := by decide
  have hdescent : baseEnd_3694892 < baseStart_3694892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694913 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3694913 : Nat := 118140960795 + 3694913 * 2 ^ 59
def prefixEnd_3694913 : Nat := 4983230072969 + 3 ^ 40 * 3694913 * 2
def baseEnd_3694913 : Nat := 1897266345546207369594911

theorem tailTrace_3694913 : CollatzResearch.WordTrace tailWord_3694913 prefixEnd_3694913 1897266345546207369594911 := by
  unfold tailWord_3694913
  simp only [CollatzResearch.WordTrace]
  refine ⟨134764548462968716745777393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89843032308645811163851595 134764548462968716745777393)
  ·
    refine ⟨101073411347226537559333045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134764548462968716745777393 101073411347226537559333045)
    ·
      refine ⟨9475632313802487896187473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101073411347226537559333045 9475632313802487896187473)
      ·
        refine ⟨7106724235351865922140605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9475632313802487896187473 7106724235351865922140605)
        ·
          refine ⟨2665021588256949720802727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7106724235351865922140605 2665021588256949720802727)
          ·
            refine ⟨3997532382385424581204091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665021588256949720802727 3997532382385424581204091)
            ·
              refine ⟨5996298573578136871806137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997532382385424581204091 5996298573578136871806137)
              ·
                refine ⟨4497223930183602653854603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996298573578136871806137 4497223930183602653854603)
                ·
                  refine ⟨6745835895275403980781905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497223930183602653854603 6745835895275403980781905)
                  ·
                    refine ⟨5059376921456552985586429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6745835895275403980781905 5059376921456552985586429)
                    ·
                      refine ⟨1897266345546207369594911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059376921456552985586429 1897266345546207369594911)
                      ·
                        rfl

theorem cell23_3694913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3694913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694913 prefixEnd_3694913 := by exact prefixLift 3694913
  have htrace : WordTrace (prefixWord ++ tailWord_3694913) baseStart_3694913 baseEnd_3694913 := by
    simpa [prefixWord, tailWord_3694913, baseEnd_3694913] using wordTrace_append hprefix tailTrace_3694913
  have hstable : (prefixWord ++ tailWord_3694913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694913).length < 2 ^ (prefixWord ++ tailWord_3694913).sum := by decide
  have hdescent : baseEnd_3694913 < baseStart_3694913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694935 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_3694935 : Nat := 118140960795 + 3694935 * 2 ^ 59
def prefixEnd_3694935 : Nat := 4983230072969 + 3 ^ 40 * 3694935 * 2
def baseEnd_3694935 : Nat := 1897277642120606283519809

theorem tailTrace_3694935 : CollatzResearch.WordTrace tailWord_3694935 prefixEnd_3694935 1897277642120606283519809 := by
  unfold tailWord_3694935
  simp only [CollatzResearch.WordTrace]
  refine ⟨134765350868889014503078259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89843567245926009668718839 134765350868889014503078259)
  ·
    refine ⟨202148026303333521754617389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134765350868889014503078259 202148026303333521754617389)
    ·
      refine ⟨75805509863750070657981521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202148026303333521754617389 75805509863750070657981521)
      ·
        refine ⟨56854132397812552993486141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75805509863750070657981521 56854132397812552993486141)
        ·
          refine ⟨21320299649179707372557303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56854132397812552993486141 21320299649179707372557303)
          ·
            refine ⟨31980449473769561058835955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21320299649179707372557303 31980449473769561058835955)
            ·
              refine ⟨47970674210654341588253933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31980449473769561058835955 47970674210654341588253933)
              ·
                refine ⟨17989002828995378095595225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47970674210654341588253933 17989002828995378095595225)
                ·
                  refine ⟨13491752121746533571696419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17989002828995378095595225 13491752121746533571696419)
                  ·
                    refine ⟨20237628182619800357544629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13491752121746533571696419 20237628182619800357544629)
                    ·
                      refine ⟨1897277642120606283519809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20237628182619800357544629 1897277642120606283519809)
                      ·
                        rfl

theorem cell23_3694935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_3694935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694935 prefixEnd_3694935 := by exact prefixLift 3694935
  have htrace : WordTrace (prefixWord ++ tailWord_3694935) baseStart_3694935 baseEnd_3694935 := by
    simpa [prefixWord, tailWord_3694935, baseEnd_3694935] using wordTrace_append hprefix tailTrace_3694935
  have hstable : (prefixWord ++ tailWord_3694935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694935).length < 2 ^ (prefixWord ++ tailWord_3694935).sum := by decide
  have hdescent : baseEnd_3694935 < baseStart_3694935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694952 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3694952 : Nat := 118140960795 + 3694952 * 2 ^ 59
def prefixEnd_3694952 : Nat := 4983230072969 + 3 ^ 40 * 3694952 * 2
def baseEnd_3694952 : Nat := 1897286371291732717007231

theorem tailTrace_3694952 : CollatzResearch.WordTrace tailWord_3694952 prefixEnd_3694952 1897286371291732717007231 := by
  unfold tailWord_3694952
  simp only [CollatzResearch.WordTrace]
  refine ⟨67382985454913713203223555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89843980606551617604298073 67382985454913713203223555)
  ·
    refine ⟨101074478182370569804835333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67382985454913713203223555 101074478182370569804835333)
    ·
      refine ⟨18951464659194481838406625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101074478182370569804835333 18951464659194481838406625)
      ·
        refine ⟨14213598494395861378804969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18951464659194481838406625 14213598494395861378804969)
        ·
          refine ⟨10660198870796896034103727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14213598494395861378804969 10660198870796896034103727)
          ·
            refine ⟨15990298306195344051155591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660198870796896034103727 15990298306195344051155591)
            ·
              refine ⟨23985447459293016076733387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15990298306195344051155591 23985447459293016076733387)
              ·
                refine ⟨35978171188939524115100081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23985447459293016076733387 35978171188939524115100081)
                ·
                  refine ⟨26983628391704643086325061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35978171188939524115100081 26983628391704643086325061)
                  ·
                    refine ⟨5059430323444620578685949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26983628391704643086325061 5059430323444620578685949)
                    ·
                      refine ⟨1897286371291732717007231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059430323444620578685949 1897286371291732717007231)
                      ·
                        rfl

theorem cell23_3694952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3694952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694952 prefixEnd_3694952 := by exact prefixLift 3694952
  have htrace : WordTrace (prefixWord ++ tailWord_3694952) baseStart_3694952 baseEnd_3694952 := by
    simpa [prefixWord, tailWord_3694952, baseEnd_3694952] using wordTrace_append hprefix tailTrace_3694952
  have hstable : (prefixWord ++ tailWord_3694952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694952).length < 2 ^ (prefixWord ++ tailWord_3694952).sum := by decide
  have hdescent : baseEnd_3694952 < baseStart_3694952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694962 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_3694962 : Nat := 118140960795 + 3694962 * 2 ^ 59
def prefixEnd_3694962 : Nat := 4983230072969 + 3 ^ 40 * 3694962 * 2
def baseEnd_3694962 : Nat := 1897291506098277677882185

theorem tailTrace_3694962 : CollatzResearch.WordTrace tailWord_3694962 prefixEnd_3694962 1897291506098277677882185 := by
  unfold tailWord_3694962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33691583909947799528577785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89844223759860798742874093 33691583909947799528577785)
  ·
    refine ⟨25268687932460849646433339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33691583909947799528577785 25268687932460849646433339)
    ·
      refine ⟨37903031898691274469650009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25268687932460849646433339 37903031898691274469650009)
      ·
        refine ⟨28427273924018455852237507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37903031898691274469650009 28427273924018455852237507)
        ·
          refine ⟨42640910886027683778356261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28427273924018455852237507 42640910886027683778356261)
          ·
            refine ⟨7995170791130190708441799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42640910886027683778356261 7995170791130190708441799)
            ·
              refine ⟨11992756186695286062662699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7995170791130190708441799 11992756186695286062662699)
              ·
                refine ⟨17989134280042929093994049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992756186695286062662699 17989134280042929093994049)
                ·
                  refine ⟨13491850710032196820495537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17989134280042929093994049 13491850710032196820495537)
                  ·
                    refine ⟨10118888032524147615371653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13491850710032196820495537 10118888032524147615371653)
                    ·
                      refine ⟨1897291506098277677882185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10118888032524147615371653 1897291506098277677882185)
                      ·
                        rfl

theorem cell23_3694962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_3694962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3694962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3694962 prefixEnd_3694962 := by exact prefixLift 3694962
  have htrace : WordTrace (prefixWord ++ tailWord_3694962) baseStart_3694962 baseEnd_3694962 := by
    simpa [prefixWord, tailWord_3694962, baseEnd_3694962] using wordTrace_append hprefix tailTrace_3694962
  have hstable : (prefixWord ++ tailWord_3694962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694962).length < 2 ^ (prefixWord ++ tailWord_3694962).sum := by decide
  have hdescent : baseEnd_3694962 < baseStart_3694962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695006 : List Nat := [4, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_3695006 : Nat := 118140960795 + 3695006 * 2 ^ 59
def prefixEnd_3695006 : Nat := 4983230072969 + 3 ^ 40 * 3695006 * 2
def baseEnd_3695006 : Nat := 210812677694119500636887

theorem tailTrace_3695006 : CollatzResearch.WordTrace tailWord_3695006 prefixEnd_3695006 210812677694119500636887 := by
  unfold tailWord_3695006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845992556453974203614109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89845293634421195752608581 16845992556453974203614109)
  ·
    refine ⟨6317247208670240326355291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16845992556453974203614109 6317247208670240326355291)
    ·
      refine ⟨9475870813005360489532937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6317247208670240326355291 9475870813005360489532937)
      ·
        refine ⟨7106903109754020367149703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9475870813005360489532937 7106903109754020367149703)
        ·
          refine ⟨10660354664631030550724555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106903109754020367149703 10660354664631030550724555)
          ·
            refine ⟨15990531996946545826086833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660354664631030550724555 15990531996946545826086833)
            ·
              refine ⟨11992898997709909369565125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15990531996946545826086833 11992898997709909369565125)
              ·
                refine ⟨2248668562070608006793461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11992898997709909369565125 2248668562070608006793461)
                ·
                  refine ⟨210812677694119500636887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2248668562070608006793461 210812677694119500636887)
                  ·
                    rfl

theorem cell23_3695006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_3695006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695006 prefixEnd_3695006 := by exact prefixLift 3695006
  have htrace : WordTrace (prefixWord ++ tailWord_3695006) baseStart_3695006 baseEnd_3695006 := by
    simpa [prefixWord, tailWord_3695006, baseEnd_3695006] using wordTrace_append hprefix tailTrace_3695006
  have hstable : (prefixWord ++ tailWord_3695006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695006).length < 2 ^ (prefixWord ++ tailWord_3695006).sum := by decide
  have hdescent : baseEnd_3695006 < baseStart_3695006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695089 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_3695089 : Nat := 118140960795 + 3695089 * 2 ^ 59
def prefixEnd_3695089 : Nat := 4983230072969 + 3 ^ 40 * 3695089 * 2
def baseEnd_3695089 : Nat := 1897356718141398680994101

theorem tailTrace_3695089 : CollatzResearch.WordTrace tailWord_3695089 prefixEnd_3695089 1897356718141398680994101 := by
  unfold tailWord_3695089
  simp only [CollatzResearch.WordTrace]
  refine ⟨134770967710331098804184321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89847311806887399202789547 134770967710331098804184321)
  ·
    refine ⟨101078225782748324103138241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134770967710331098804184321 101078225782748324103138241)
    ·
      refine ⟨75808669337061243077353681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101078225782748324103138241 75808669337061243077353681)
      ·
        refine ⟨56856502002795932308015261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75808669337061243077353681 56856502002795932308015261)
        ·
          refine ⟨21321188251048474615505723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56856502002795932308015261 21321188251048474615505723)
          ·
            refine ⟨31981782376572711923258585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21321188251048474615505723 31981782376572711923258585)
            ·
              refine ⟨23986336782429533942443939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31981782376572711923258585 23986336782429533942443939)
              ·
                refine ⟨35979505173644300913665909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23986336782429533942443939 35979505173644300913665909)
                ·
                  refine ⟨3373078610029153210656179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35979505173644300913665909 3373078610029153210656179)
                  ·
                    refine ⟨5059617915043729815984269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3373078610029153210656179 5059617915043729815984269)
                    ·
                      refine ⟨1897356718141398680994101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059617915043729815984269 1897356718141398680994101)
                      ·
                        rfl

theorem cell23_3695089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_3695089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695089 prefixEnd_3695089 := by exact prefixLift 3695089
  have htrace : WordTrace (prefixWord ++ tailWord_3695089) baseStart_3695089 baseEnd_3695089 := by
    simpa [prefixWord, tailWord_3695089, baseEnd_3695089] using wordTrace_append hprefix tailTrace_3695089
  have hstable : (prefixWord ++ tailWord_3695089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695089).length < 2 ^ (prefixWord ++ tailWord_3695089).sum := by decide
  have hdescent : baseEnd_3695089 < baseStart_3695089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695093 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3695093 : Nat := 118140960795 + 3695093 * 2 ^ 59
def prefixEnd_3695093 : Nat := 4983230072969 + 3 ^ 40 * 3695093 * 2
def baseEnd_3695093 : Nat := 1897358772064016665344083

theorem tailTrace_3695093 : CollatzResearch.WordTrace tailWord_3695093 prefixEnd_3695093 1897358772064016665344083 := by
  unfold tailWord_3695093
  simp only [CollatzResearch.WordTrace]
  refine ⟨134771113602316607487329933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89847409068211071658219955 134771113602316607487329933)
  ·
    refine ⟨50539167600868727807748725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134771113602316607487329933 50539167600868727807748725)
    ·
      refine ⟨4738046962581443231976443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50539167600868727807748725 4738046962581443231976443)
      ·
        refine ⟨7107070443872164847964665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738046962581443231976443 7107070443872164847964665)
        ·
          refine ⟨5330302832904123635973499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7107070443872164847964665 5330302832904123635973499)
          ·
            refine ⟨7995454249356185453960249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330302832904123635973499 7995454249356185453960249)
            ·
              refine ⟨5996590687017139090470187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7995454249356185453960249 5996590687017139090470187)
              ·
                refine ⟨8994886030525708635705281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996590687017139090470187 8994886030525708635705281)
                ·
                  refine ⟨6746164522894281476778961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8994886030525708635705281 6746164522894281476778961)
                  ·
                    refine ⟨5059623392170711107584221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6746164522894281476778961 5059623392170711107584221)
                    ·
                      refine ⟨1897358772064016665344083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059623392170711107584221 1897358772064016665344083)
                      ·
                        rfl

theorem cell23_3695093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3695093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695093 prefixEnd_3695093 := by exact prefixLift 3695093
  have htrace : WordTrace (prefixWord ++ tailWord_3695093) baseStart_3695093 baseEnd_3695093 := by
    simpa [prefixWord, tailWord_3695093, baseEnd_3695093] using wordTrace_append hprefix tailTrace_3695093
  have hstable : (prefixWord ++ tailWord_3695093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695093).length < 2 ^ (prefixWord ++ tailWord_3695093).sum := by decide
  have hdescent : baseEnd_3695093 < baseStart_3695093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695110 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3695110 : Nat := 118140960795 + 3695110 * 2 ^ 59
def prefixEnd_3695110 : Nat := 4983230072969 + 3 ^ 40 * 3695110 * 2
def baseEnd_3695110 : Nat := 1897367501235143098831505

theorem tailTrace_3695110 : CollatzResearch.WordTrace tailWord_3695110 prefixEnd_3695110 1897367501235143098831505 := by
  unfold tailWord_3695110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4211616676351719355959337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89847822428836679593799189 4211616676351719355959337)
  ·
    refine ⟨3158712507263789516969503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4211616676351719355959337 3158712507263789516969503)
    ·
      refine ⟨4738068760895684275454255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3158712507263789516969503 4738068760895684275454255)
      ·
        refine ⟨7107103141343526413181383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738068760895684275454255 7107103141343526413181383)
        ·
          refine ⟨10660654712015289619772075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107103141343526413181383 10660654712015289619772075)
          ·
            refine ⟨15990982068022934429658113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660654712015289619772075 15990982068022934429658113)
            ·
              refine ⟨11993236551017200822243585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15990982068022934429658113 11993236551017200822243585)
              ·
                refine ⟨8994927413262900616682689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11993236551017200822243585 8994927413262900616682689)
                ·
                  refine ⟨6746195559947175462512017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8994927413262900616682689 6746195559947175462512017)
                  ·
                    refine ⟨5059646669960381596884013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6746195559947175462512017 5059646669960381596884013)
                    ·
                      refine ⟨1897367501235143098831505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059646669960381596884013 1897367501235143098831505)
                      ·
                        rfl

theorem cell23_3695110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3695110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695110 prefixEnd_3695110 := by exact prefixLift 3695110
  have htrace : WordTrace (prefixWord ++ tailWord_3695110) baseStart_3695110 baseEnd_3695110 := by
    simpa [prefixWord, tailWord_3695110, baseEnd_3695110] using wordTrace_append hprefix tailTrace_3695110
  have hstable : (prefixWord ++ tailWord_3695110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695110).length < 2 ^ (prefixWord ++ tailWord_3695110).sum := by decide
  have hdescent : baseEnd_3695110 < baseStart_3695110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695116 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 2, 3, 2]
def baseStart_3695116 : Nat := 118140960795 + 3695116 * 2 ^ 59
def prefixEnd_3695116 : Nat := 4983230072969 + 3 ^ 40 * 3695116 * 2
def baseEnd_3695116 : Nat := 1897370582119070075356477

theorem tailTrace_3695116 : CollatzResearch.WordTrace tailWord_3695116 prefixEnd_3695116 1897370582119070075356477 := by
  unfold tailWord_3695116
  simp only [CollatzResearch.WordTrace]
  refine ⟨67385976240616641207708601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89847968320822188276944801 67385976240616641207708601)
  ·
    refine ⟨50539482180462480905781451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67385976240616641207708601 50539482180462480905781451)
    ·
      refine ⟨75809223270693721358672177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50539482180462480905781451 75809223270693721358672177)
      ·
        refine ⟨56856917453020291019004133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75809223270693721358672177 56856917453020291019004133)
        ·
          refine ⟨10660672022441304566063275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56856917453020291019004133 10660672022441304566063275)
          ·
            refine ⟨15991008033661956849094913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660672022441304566063275 15991008033661956849094913)
            ·
              refine ⟨11993256025246467636821185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15991008033661956849094913 11993256025246467636821185)
              ·
                refine ⟨8994942018934850727615889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11993256025246467636821185 8994942018934850727615889)
                ·
                  refine ⟨6746206514201138045711917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8994942018934850727615889 6746206514201138045711917)
                  ·
                    refine ⟨2529827442825426767141969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6746206514201138045711917 2529827442825426767141969)
                    ·
                      refine ⟨1897370582119070075356477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529827442825426767141969 1897370582119070075356477)
                      ·
                        rfl

theorem cell23_3695116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_3695116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695116 prefixEnd_3695116 := by exact prefixLift 3695116
  have htrace : WordTrace (prefixWord ++ tailWord_3695116) baseStart_3695116 baseEnd_3695116 := by
    simpa [prefixWord, tailWord_3695116, baseEnd_3695116] using wordTrace_append hprefix tailTrace_3695116
  have hstable : (prefixWord ++ tailWord_3695116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695116).length < 2 ^ (prefixWord ++ tailWord_3695116).sum := by decide
  have hdescent : baseEnd_3695116 < baseStart_3695116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695117 : List Nat := [1, 7, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3695117 : Nat := 118140960795 + 3695117 * 2 ^ 59
def prefixEnd_3695117 : Nat := 4983230072969 + 3 ^ 40 * 3695117 * 2
def baseEnd_3695117 : Nat := 632457031866574857147991

theorem tailTrace_3695117 : CollatzResearch.WordTrace tailWord_3695117 prefixEnd_3695117 632457031866574857147991 := by
  unfold tailWord_3695117
  simp only [CollatzResearch.WordTrace]
  refine ⟨134771988954229659586203605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89847992636153106390802403 134771988954229659586203605)
  ·
    refine ⟨3158718491114757646551647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 134771988954229659586203605 3158718491114757646551647)
    ·
      refine ⟨4738077736672136469827471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3158718491114757646551647 4738077736672136469827471)
      ·
        refine ⟨7107116605008204704741207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4738077736672136469827471 7107116605008204704741207)
        ·
          refine ⟨10660674907512307057111811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107116605008204704741207 10660674907512307057111811)
          ·
            refine ⟨15991012361268460585667717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660674907512307057111811 15991012361268460585667717)
            ·
              refine ⟨2998314817737836359812697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15991012361268460585667717 2998314817737836359812697)
              ·
                refine ⟨2248736113303377269859523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998314817737836359812697 2248736113303377269859523)
                ·
                  refine ⟨3373104169955065904789285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248736113303377269859523 3373104169955065904789285)
                  ·
                    refine ⟨632457031866574857147991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373104169955065904789285 632457031866574857147991)
                    ·
                      rfl

theorem cell23_3695117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3695117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695117 prefixEnd_3695117 := by exact prefixLift 3695117
  have htrace : WordTrace (prefixWord ++ tailWord_3695117) baseStart_3695117 baseEnd_3695117 := by
    simpa [prefixWord, tailWord_3695117, baseEnd_3695117] using wordTrace_append hprefix tailTrace_3695117
  have hstable : (prefixWord ++ tailWord_3695117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695117).length < 2 ^ (prefixWord ++ tailWord_3695117).sum := by decide
  have hdescent : baseEnd_3695117 < baseStart_3695117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695139 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 1, 6]
def baseStart_3695139 : Nat := 118140960795 + 3695139 * 2 ^ 59
def prefixEnd_3695139 : Nat := 4983230072969 + 3 ^ 40 * 3695139 * 2
def baseEnd_3695139 : Nat := 632460797391374495122957

theorem tailTrace_3695139 : CollatzResearch.WordTrace tailWord_3695139 prefixEnd_3695139 632460797391374495122957 := by
  unfold tailWord_3695139
  simp only [CollatzResearch.WordTrace]
  refine ⟨134772791360149957343504471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89848527573433304895669647 134772791360149957343504471)
  ·
    refine ⟨202159187040224936015256707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134772791360149957343504471 202159187040224936015256707)
    ·
      refine ⟨303238780560337404022885061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202159187040224936015256707 303238780560337404022885061)
      ·
        refine ⟨56857271355063263254290949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303238780560337404022885061 56857271355063263254290949)
        ·
          refine ⟨10660738379074361860179553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56857271355063263254290949 10660738379074361860179553)
          ·
            refine ⟨7995553784305771395134665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10660738379074361860179553 7995553784305771395134665)
            ·
              refine ⟨5996665338229328546350999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7995553784305771395134665 5996665338229328546350999)
              ·
                refine ⟨8994998007343992819526499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996665338229328546350999 8994998007343992819526499)
                ·
                  refine ⟨13492497011015989229289749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8994998007343992819526499 13492497011015989229289749)
                  ·
                    refine ⟨632460797391374495122957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13492497011015989229289749 632460797391374495122957)
                    ·
                      rfl

theorem cell23_3695139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 6].length) (baseStart_3695139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695139 prefixEnd_3695139 := by exact prefixLift 3695139
  have htrace : WordTrace (prefixWord ++ tailWord_3695139) baseStart_3695139 baseEnd_3695139 := by
    simpa [prefixWord, tailWord_3695139, baseEnd_3695139] using wordTrace_append hprefix tailTrace_3695139
  have hstable : (prefixWord ++ tailWord_3695139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695139).length < 2 ^ (prefixWord ++ tailWord_3695139).sum := by decide
  have hdescent : baseEnd_3695139 < baseStart_3695139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695150 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_3695150 : Nat := 118140960795 + 3695150 * 2 ^ 59
def prefixEnd_3695150 : Nat := 4983230072969 + 3 ^ 40 * 3695150 * 2
def baseEnd_3695150 : Nat := 1897388040461322942331321

theorem tailTrace_3695150 : CollatzResearch.WordTrace tailWord_3695150 prefixEnd_3695150 1897388040461322942331321 := by
  unfold tailWord_3695150
  simp only [CollatzResearch.WordTrace]
  refine ⟨16846649070388763277769363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89848795042073404148103269 16846649070388763277769363)
  ·
    refine ⟨25269973605583144916654045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16846649070388763277769363 25269973605583144916654045)
    ·
      refine ⟨9476240102093679343745267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25269973605583144916654045 9476240102093679343745267)
      ·
        refine ⟨14214360153140519015617901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9476240102093679343745267 14214360153140519015617901)
        ·
          refine ⟨5330385057427694630856713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14214360153140519015617901 5330385057427694630856713)
          ·
            refine ⟨3997788793070770973142535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5330385057427694630856713 3997788793070770973142535)
            ·
              refine ⟨5996683189606156459713803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997788793070770973142535 5996683189606156459713803)
              ·
                refine ⟨8995024784409234689570705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5996683189606156459713803 8995024784409234689570705)
                ·
                  refine ⟨6746268588306926017178029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8995024784409234689570705 6746268588306926017178029)
                  ·
                    refine ⟨2529850720615097256441761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6746268588306926017178029 2529850720615097256441761)
                    ·
                      refine ⟨1897388040461322942331321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529850720615097256441761 1897388040461322942331321)
                      ·
                        rfl

theorem cell23_3695150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_3695150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695150 prefixEnd_3695150 := by exact prefixLift 3695150
  have htrace : WordTrace (prefixWord ++ tailWord_3695150) baseStart_3695150 baseEnd_3695150 := by
    simpa [prefixWord, tailWord_3695150, baseEnd_3695150] using wordTrace_append hprefix tailTrace_3695150
  have hstable : (prefixWord ++ tailWord_3695150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695150).length < 2 ^ (prefixWord ++ tailWord_3695150).sum := by decide
  have hdescent : baseEnd_3695150 < baseStart_3695150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695182 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3695182 : Nat := 118140960795 + 3695182 * 2 ^ 59
def prefixEnd_3695182 : Nat := 4983230072969 + 3 ^ 40 * 3695182 * 2
def baseEnd_3695182 : Nat := 632468157280755605710391

theorem tailTrace_3695182 : CollatzResearch.WordTrace tailWord_3695182 prefixEnd_3695182 632468157280755605710391 := by
  unfold tailWord_3695182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16846794962374271960914975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89849573132662783791546533 16846794962374271960914975)
  ·
    refine ⟨25270192443561407941372463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16846794962374271960914975 25270192443561407941372463)
    ·
      refine ⟨37905288665342111912058695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25270192443561407941372463 37905288665342111912058695)
      ·
        refine ⟨56857932998013167868088043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37905288665342111912058695 56857932998013167868088043)
        ·
          refine ⟨85286899497019751802132065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56857932998013167868088043 85286899497019751802132065)
          ·
            refine ⟨63965174622764813851599049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85286899497019751802132065 63965174622764813851599049)
            ·
              refine ⟨47973880967073610388699287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63965174622764813851599049 47973880967073610388699287)
              ·
                refine ⟨71960821450610415583048931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47973880967073610388699287 71960821450610415583048931)
                ·
                  refine ⟨107941232175915623374573397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71960821450610415583048931 107941232175915623374573397)
                  ·
                    refine ⟨632468157280755605710391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 107941232175915623374573397 632468157280755605710391)
                    ·
                      rfl

theorem cell23_3695182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3695182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695182 prefixEnd_3695182 := by exact prefixLift 3695182
  have htrace : WordTrace (prefixWord ++ tailWord_3695182) baseStart_3695182 baseEnd_3695182 := by
    simpa [prefixWord, tailWord_3695182, baseEnd_3695182] using wordTrace_append hprefix tailTrace_3695182
  have hstable : (prefixWord ++ tailWord_3695182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695182).length < 2 ^ (prefixWord ++ tailWord_3695182).sum := by decide
  have hdescent : baseEnd_3695182 < baseStart_3695182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695212 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_3695212 : Nat := 118140960795 + 3695212 * 2 ^ 59
def prefixEnd_3695212 : Nat := 4983230072969 + 3 ^ 40 * 3695212 * 2
def baseEnd_3695212 : Nat := 632473292087300566585345

theorem tailTrace_3695212 : CollatzResearch.WordTrace tailWord_3695212 prefixEnd_3695212 632473292087300566585345 := by
  unfold tailWord_3695212
  simp only [CollatzResearch.WordTrace]
  refine ⟨67387726944442745405455945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89850302592590327207274593 67387726944442745405455945)
  ·
    refine ⟨50540795208332059054091959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67387726944442745405455945 50540795208332059054091959)
    ·
      refine ⟨75811192812498088581137939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50540795208332059054091959 75811192812498088581137939)
      ·
        refine ⟨113716789218747132871706909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75811192812498088581137939 113716789218747132871706909)
        ·
          refine ⟨42643795957030174826890091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113716789218747132871706909 42643795957030174826890091)
          ·
            refine ⟨63965693935545262240335137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42643795957030174826890091 63965693935545262240335137)
            ·
              refine ⟨47974270451658946680251353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63965693935545262240335137 47974270451658946680251353)
              ·
                refine ⟨35980702838744210010188515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47974270451658946680251353 35980702838744210010188515)
                ·
                  refine ⟨53971054258116315015282773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35980702838744210010188515 53971054258116315015282773)
                  ·
                    refine ⟨632473292087300566585345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53971054258116315015282773 632473292087300566585345)
                    ·
                      rfl

theorem cell23_3695212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_3695212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695212 prefixEnd_3695212 := by exact prefixLift 3695212
  have htrace : WordTrace (prefixWord ++ tailWord_3695212) baseStart_3695212 baseEnd_3695212 := by
    simpa [prefixWord, tailWord_3695212, baseEnd_3695212] using wordTrace_append hprefix tailTrace_3695212
  have hstable : (prefixWord ++ tailWord_3695212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695212).length < 2 ^ (prefixWord ++ tailWord_3695212).sum := by decide
  have hdescent : baseEnd_3695212 < baseStart_3695212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695239 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_3695239 : Nat := 118140960795 + 3695239 * 2 ^ 59
def prefixEnd_3695239 : Nat := 4983230072969 + 3 ^ 40 * 3695239 * 2
def baseEnd_3695239 : Nat := 1897433740239573094118411

theorem tailTrace_3695239 : CollatzResearch.WordTrace tailWord_3695239 prefixEnd_3695239 1897433740239573094118411 := by
  unfold tailWord_3695239
  simp only [CollatzResearch.WordTrace]
  refine ⟨134776438659787674422144771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89850959106525116281429847 134776438659787674422144771)
  ·
    refine ⟨202164657989681511633217157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134776438659787674422144771 202164657989681511633217157)
    ·
      refine ⟨37905873373065283431228217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202164657989681511633217157 37905873373065283431228217)
      ·
        refine ⟨28429405029798962573421163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37905873373065283431228217 28429405029798962573421163)
        ·
          refine ⟨42644107544698443860131745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28429405029798962573421163 42644107544698443860131745)
          ·
            refine ⟨31983080658523832895098809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42644107544698443860131745 31983080658523832895098809)
            ·
              refine ⟨23987310493892874671324107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31983080658523832895098809 23987310493892874671324107)
              ·
                refine ⟨35980965740839312006986161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23987310493892874671324107 35980965740839312006986161)
                ·
                  refine ⟨26985724305629484005239621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35980965740839312006986161 26985724305629484005239621)
                  ·
                    refine ⟨5059823307305528250982429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26985724305629484005239621 5059823307305528250982429)
                    ·
                      refine ⟨1897433740239573094118411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059823307305528250982429 1897433740239573094118411)
                      ·
                        rfl

theorem cell23_3695239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_3695239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695239 prefixEnd_3695239 := by exact prefixLift 3695239
  have htrace : WordTrace (prefixWord ++ tailWord_3695239) baseStart_3695239 baseEnd_3695239 := by
    simpa [prefixWord, tailWord_3695239, baseEnd_3695239] using wordTrace_append hprefix tailTrace_3695239
  have hstable : (prefixWord ++ tailWord_3695239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695239).length < 2 ^ (prefixWord ++ tailWord_3695239).sum := by decide
  have hdescent : baseEnd_3695239 < baseStart_3695239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695269 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_3695269 : Nat := 118140960795 + 3695269 * 2 ^ 59
def prefixEnd_3695269 : Nat := 4983230072969 + 3 ^ 40 * 3695269 * 2
def baseEnd_3695269 : Nat := 1897449144659207976743273

theorem tailTrace_3695269 : CollatzResearch.WordTrace tailWord_3695269 prefixEnd_3695269 1897449144659207976743273 := by
  unfold tailWord_3695269
  simp only [CollatzResearch.WordTrace]
  refine ⟨134777532849678989545736861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89851688566452659697157907 134777532849678989545736861)
  ·
    refine ⟨50541574818629621079651323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134777532849678989545736861 50541574818629621079651323)
    ·
      refine ⟨75812362227944431619476985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50541574818629621079651323 75812362227944431619476985)
      ·
        refine ⟨56859271670958323714607739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75812362227944431619476985 56859271670958323714607739)
        ·
          refine ⟨85288907506437485571911609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56859271670958323714607739 85288907506437485571911609)
          ·
            refine ⟨63966680629828114178933707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85288907506437485571911609 63966680629828114178933707)
            ·
              refine ⟨95950020944742171268400561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63966680629828114178933707 95950020944742171268400561)
              ·
                refine ⟨71962515708556628451300421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95950020944742171268400561 71962515708556628451300421)
                ·
                  refine ⟨13492971695354367834618829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71962515708556628451300421 13492971695354367834618829)
                  ·
                    refine ⟨5059864385757887937982061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13492971695354367834618829 5059864385757887937982061)
                    ·
                      refine ⟨1897449144659207976743273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5059864385757887937982061 1897449144659207976743273)
                      ·
                        rfl

theorem cell23_3695269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_3695269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695269 prefixEnd_3695269 := by exact prefixLift 3695269
  have htrace : WordTrace (prefixWord ++ tailWord_3695269) baseStart_3695269 baseEnd_3695269 := by
    simpa [prefixWord, tailWord_3695269, baseEnd_3695269] using wordTrace_append hprefix tailTrace_3695269
  have hstable : (prefixWord ++ tailWord_3695269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695269).length < 2 ^ (prefixWord ++ tailWord_3695269).sum := by decide
  have hdescent : baseEnd_3695269 < baseStart_3695269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695274 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3695274 : Nat := 118140960795 + 3695274 * 2 ^ 59
def prefixEnd_3695274 : Nat := 4983230072969 + 3 ^ 40 * 3695274 * 2
def baseEnd_3695274 : Nat := 1897451712062480457180751

theorem tailTrace_3695274 : CollatzResearch.WordTrace tailWord_3695274 prefixEnd_3695274 1897451712062480457180751 := by
  unfold tailWord_3695274
  simp only [CollatzResearch.WordTrace]
  refine ⟨33694428803665218849917219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89851810143107250266445917 33694428803665218849917219)
  ·
    refine ⟨50541643205497828274875829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33694428803665218849917219 50541643205497828274875829)
    ·
      refine ⟨4738279050515421400769609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50541643205497828274875829 4738279050515421400769609)
      ·
        refine ⟨3553709287886566050577207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4738279050515421400769609 3553709287886566050577207)
        ·
          refine ⟨5330563931829849075865811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553709287886566050577207 5330563931829849075865811)
          ·
            refine ⟨7995845897744773613798717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330563931829849075865811 7995845897744773613798717)
            ·
              refine ⟨2998442211654290105174519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7995845897744773613798717 2998442211654290105174519)
              ·
                refine ⟨4497663317481435157761779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998442211654290105174519 4497663317481435157761779)
                ·
                  refine ⟨6746494976222152736642669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497663317481435157761779 6746494976222152736642669)
                  ·
                    refine ⟨2529935616083307276241001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6746494976222152736642669 2529935616083307276241001)
                    ·
                      refine ⟨1897451712062480457180751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529935616083307276241001 1897451712062480457180751)
                      ·
                        rfl

theorem cell23_3695274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3695274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695274 prefixEnd_3695274 := by exact prefixLift 3695274
  have htrace : WordTrace (prefixWord ++ tailWord_3695274) baseStart_3695274 baseEnd_3695274 := by
    simpa [prefixWord, tailWord_3695274, baseEnd_3695274] using wordTrace_append hprefix tailTrace_3695274
  have hstable : (prefixWord ++ tailWord_3695274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695274).length < 2 ^ (prefixWord ++ tailWord_3695274).sum := by decide
  have hdescent : baseEnd_3695274 < baseStart_3695274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695293 : List Nat := [1, 4, 1, 2, 1, 3, 4, 2, 5]
def baseStart_3695293 : Nat := 118140960795 + 3695293 * 2 ^ 59
def prefixEnd_3695293 : Nat := 4983230072969 + 3 ^ 40 * 3695293 * 2
def baseEnd_3695293 : Nat := 210829052021657320315907

theorem tailTrace_3695293 : CollatzResearch.WordTrace tailWord_3695293 prefixEnd_3695293 210829052021657320315907 := by
  unfold tailWord_3695293
  simp only [CollatzResearch.WordTrace]
  refine ⟨134778408201592041644610533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89852272134394694429740355 134778408201592041644610533)
  ·
    refine ⟨25270951537798507808364475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134778408201592041644610533 25270951537798507808364475)
    ·
      refine ⟨37906427306697761712546713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25270951537798507808364475 37906427306697761712546713)
      ·
        refine ⟨28429820480023321284410035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37906427306697761712546713 28429820480023321284410035)
        ·
          refine ⟨42644730720034981926615053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28429820480023321284410035 42644730720034981926615053)
          ·
            refine ⟨15991774020013118222480645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42644730720034981926615053 15991774020013118222480645)
            ·
              refine ⟨2998457628752459666715121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15991774020013118222480645 2998457628752459666715121)
              ·
                refine ⟨2248843221564344750036341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998457628752459666715121 2248843221564344750036341)
                ·
                  refine ⟨210829052021657320315907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2248843221564344750036341 210829052021657320315907)
                  ·
                    rfl

theorem cell23_3695293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_3695293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695293 prefixEnd_3695293 := by exact prefixLift 3695293
  have htrace : WordTrace (prefixWord ++ tailWord_3695293) baseStart_3695293 baseEnd_3695293 := by
    simpa [prefixWord, tailWord_3695293, baseEnd_3695293] using wordTrace_append hprefix tailTrace_3695293
  have hstable : (prefixWord ++ tailWord_3695293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695293).length < 2 ^ (prefixWord ++ tailWord_3695293).sum := by decide
  have hdescent : baseEnd_3695293 < baseStart_3695293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695296 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 2, 5, 2]
def baseStart_3695296 : Nat := 118140960795 + 3695296 * 2 ^ 59
def prefixEnd_3695296 : Nat := 4983230072969 + 3 ^ 40 * 3695296 * 2
def baseEnd_3695296 : Nat := 1897463008636879371105649

theorem tailTrace_3695296 : CollatzResearch.WordTrace tailWord_3695296 prefixEnd_3695296 1897463008636879371105649 := by
  unfold tailWord_3695296
  simp only [CollatzResearch.WordTrace]
  refine ⟨67389258810290586578484871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89852345080387448771313161 67389258810290586578484871)
  ·
    refine ⟨101083888215435879867727307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67389258810290586578484871 101083888215435879867727307)
    ·
      refine ⟨151625832323153819801590961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101083888215435879867727307 151625832323153819801590961)
      ·
        refine ⟨113719374242365364851193221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151625832323153819801590961 113719374242365364851193221)
        ·
          refine ⟨21322382670443505909598729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113719374242365364851193221 21322382670443505909598729)
          ·
            refine ⟨15991787002832629432199047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21322382670443505909598729 15991787002832629432199047)
            ·
              refine ⟨23987680504248944148298571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15991787002832629432199047 23987680504248944148298571)
              ·
                refine ⟨35981520756373416222447857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23987680504248944148298571 35981520756373416222447857)
                ·
                  refine ⟨26986140567280062166835893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35981520756373416222447857 26986140567280062166835893)
                  ·
                    refine ⟨2529950678182505828140865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26986140567280062166835893 2529950678182505828140865)
                    ·
                      refine ⟨1897463008636879371105649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2529950678182505828140865 1897463008636879371105649)
                      ·
                        rfl

theorem cell23_3695296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_3695296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695296 prefixEnd_3695296 := by exact prefixLift 3695296
  have htrace : WordTrace (prefixWord ++ tailWord_3695296) baseStart_3695296 baseEnd_3695296 := by
    simpa [prefixWord, tailWord_3695296, baseEnd_3695296] using wordTrace_append hprefix tailTrace_3695296
  have hstable : (prefixWord ++ tailWord_3695296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695296).length < 2 ^ (prefixWord ++ tailWord_3695296).sum := by decide
  have hdescent : baseEnd_3695296 < baseStart_3695296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695416 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_3695416 : Nat := 118140960795 + 3695416 * 2 ^ 59
def prefixEnd_3695416 : Nat := 4983230072969 + 3 ^ 40 * 3695416 * 2
def baseEnd_3695416 : Nat := 1897524626315418901605097

theorem tailTrace_3695416 : CollatzResearch.WordTrace tailWord_3695416 prefixEnd_3695416 1897524626315418901605097 := by
  unfold tailWord_3695416
  simp only [CollatzResearch.WordTrace]
  refine ⟨67391447190073216825669051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89855262920097622434225401 67391447190073216825669051)
  ·
    refine ⟨101087170785109825238503577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67391447190073216825669051 101087170785109825238503577)
    ·
      refine ⟨75815378088832368928877683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101087170785109825238503577 75815378088832368928877683)
      ·
        refine ⟨113723067133248553393316525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75815378088832368928877683 113723067133248553393316525)
        ·
          refine ⟨42646150174968207522493697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113723067133248553393316525 42646150174968207522493697)
          ·
            refine ⟨31984612631226155641870273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42646150174968207522493697 31984612631226155641870273)
            ·
              refine ⟨23988459473419616731402705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31984612631226155641870273 23988459473419616731402705)
              ·
                refine ⟨17991344605064712548552029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23988459473419616731402705 17991344605064712548552029)
                ·
                  refine ⟨6746754226899267205707011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17991344605064712548552029 6746754226899267205707011)
                  ·
                    refine ⟨10120131340348900808560517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746754226899267205707011 10120131340348900808560517)
                    ·
                      refine ⟨1897524626315418901605097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10120131340348900808560517 1897524626315418901605097)
                      ·
                        rfl

theorem cell23_3695416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_3695416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695416 prefixEnd_3695416 := by exact prefixLift 3695416
  have htrace : WordTrace (prefixWord ++ tailWord_3695416) baseStart_3695416 baseEnd_3695416 := by
    simpa [prefixWord, tailWord_3695416, baseEnd_3695416] using wordTrace_append hprefix tailTrace_3695416
  have hstable : (prefixWord ++ tailWord_3695416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695416).length < 2 ^ (prefixWord ++ tailWord_3695416).sum := by decide
  have hdescent : baseEnd_3695416 < baseStart_3695416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695433 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 4]
def baseStart_3695433 : Nat := 118140960795 + 3695433 * 2 ^ 59
def prefixEnd_3695433 : Nat := 4983230072969 + 3 ^ 40 * 3695433 * 2
def baseEnd_3695433 : Nat := 1897533355486545335092519

theorem tailTrace_3695433 : CollatzResearch.WordTrace tailWord_3695433 prefixEnd_3695433 1897533355486545335092519 := by
  unfold tailWord_3695433
  simp only [CollatzResearch.WordTrace]
  refine ⟨134783514421084845554706953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89855676280723230369804635 134783514421084845554706953)
  ·
    refine ⟨101087635815813634166030215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134783514421084845554706953 101087635815813634166030215)
    ·
      refine ⟨151631453723720451249045323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101087635815813634166030215 151631453723720451249045323)
      ·
        refine ⟨227447180585580676873567985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151631453723720451249045323 227447180585580676873567985)
        ·
          refine ⟨170585385439185507655175989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227447180585580676873567985 170585385439185507655175989)
          ·
            refine ⟨15992379884923641342672749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170585385439185507655175989 15992379884923641342672749)
            ·
              refine ⟨5997142456846365503502281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15992379884923641342672749 5997142456846365503502281)
              ·
                refine ⟨4497856842634774127626711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997142456846365503502281 4497856842634774127626711)
                ·
                  refine ⟨6746785263952161191440067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497856842634774127626711 6746785263952161191440067)
                  ·
                    refine ⟨10120177895928241787160101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746785263952161191440067 10120177895928241787160101)
                    ·
                      refine ⟨1897533355486545335092519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10120177895928241787160101 1897533355486545335092519)
                      ·
                        rfl

theorem cell23_3695433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_3695433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695433 prefixEnd_3695433 := by exact prefixLift 3695433
  have htrace : WordTrace (prefixWord ++ tailWord_3695433) baseStart_3695433 baseEnd_3695433 := by
    simpa [prefixWord, tailWord_3695433, baseEnd_3695433] using wordTrace_append hprefix tailTrace_3695433
  have hstable : (prefixWord ++ tailWord_3695433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695433).length < 2 ^ (prefixWord ++ tailWord_3695433).sum := by decide
  have hdescent : baseEnd_3695433 < baseStart_3695433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695450 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4]
def baseStart_3695450 : Nat := 118140960795 + 3695450 * 2 ^ 59
def prefixEnd_3695450 : Nat := 4983230072969 + 3 ^ 40 * 3695450 * 2
def baseEnd_3695450 : Nat := 1897542084657671768579941

theorem tailTrace_3695450 : CollatzResearch.WordTrace tailWord_3695450 prefixEnd_3695450 1897542084657671768579941 := by
  unfold tailWord_3695450
  simp only [CollatzResearch.WordTrace]
  refine ⟨33696033615505814364518951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89856089641348838305383869 33696033615505814364518951)
  ·
    refine ⟨50544050423258721546778427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33696033615505814364518951 50544050423258721546778427)
    ·
      refine ⟨75816075634888082320167641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50544050423258721546778427 75816075634888082320167641)
      ·
        refine ⟨56862056726166061740125731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75816075634888082320167641 56862056726166061740125731)
        ·
          refine ⟨85293085089249092610188597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56862056726166061740125731 85293085089249092610188597)
          ·
            refine ⟨7996226727117102432205181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85293085089249092610188597 7996226727117102432205181)
            ·
              refine ⟨2998585022668913412076943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7996226727117102432205181 2998585022668913412076943)
              ·
                refine ⟨4497877534003370118115415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998585022668913412076943 4497877534003370118115415)
                ·
                  refine ⟨6746816301005055177173123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497877534003370118115415 6746816301005055177173123)
                  ·
                    refine ⟨10120224451507582765759685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6746816301005055177173123 10120224451507582765759685)
                    ·
                      refine ⟨1897542084657671768579941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10120224451507582765759685 1897542084657671768579941)
                      ·
                        rfl

theorem cell23_3695450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_3695450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695450 prefixEnd_3695450 := by exact prefixLift 3695450
  have htrace : WordTrace (prefixWord ++ tailWord_3695450) baseStart_3695450 baseEnd_3695450 := by
    simpa [prefixWord, tailWord_3695450, baseEnd_3695450] using wordTrace_append hprefix tailTrace_3695450
  have hstable : (prefixWord ++ tailWord_3695450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695450).length < 2 ^ (prefixWord ++ tailWord_3695450).sum := by decide
  have hdescent : baseEnd_3695450 < baseStart_3695450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695460 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_3695460 : Nat := 118140960795 + 3695460 * 2 ^ 59
def prefixEnd_3695460 : Nat := 4983230072969 + 3 ^ 40 * 3695460 * 2
def baseEnd_3695460 : Nat := 632515739821405576484965

theorem tailTrace_3695460 : CollatzResearch.WordTrace tailWord_3695460 prefixEnd_3695460 632515739821405576484965 := by
  unfold tailWord_3695460
  simp only [CollatzResearch.WordTrace]
  refine ⟨67392249595993514582969917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89856332794658019443959889 67392249595993514582969917)
  ·
    refine ⟨25272093598497567968613719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67392249595993514582969917 25272093598497567968613719)
    ·
      refine ⟨37908140397746351952920579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25272093598497567968613719 37908140397746351952920579)
      ·
        refine ⟨56862210596619527929380869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37908140397746351952920579 56862210596619527929380869)
        ·
          refine ⟨10661664486866161486758913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56862210596619527929380869 10661664486866161486758913)
          ·
            refine ⟨7996248365149621115069185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10661664486866161486758913 7996248365149621115069185)
            ·
              refine ⟨5997186273862215836301889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996248365149621115069185 5997186273862215836301889)
              ·
                refine ⟨4497889705396661877226417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997186273862215836301889 4497889705396661877226417)
                ·
                  refine ⟨3373417279047496407919813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4497889705396661877226417 3373417279047496407919813)
                  ·
                    refine ⟨632515739821405576484965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373417279047496407919813 632515739821405576484965)
                    ·
                      rfl

theorem cell23_3695460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_3695460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695460 prefixEnd_3695460 := by exact prefixLift 3695460
  have htrace : WordTrace (prefixWord ++ tailWord_3695460) baseStart_3695460 baseEnd_3695460 := by
    simpa [prefixWord, tailWord_3695460, baseEnd_3695460] using wordTrace_append hprefix tailTrace_3695460
  have hstable : (prefixWord ++ tailWord_3695460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695460).length < 2 ^ (prefixWord ++ tailWord_3695460).sum := by decide
  have hdescent : baseEnd_3695460 < baseStart_3695460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695523 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 3, 4, 2]
def baseStart_3695523 : Nat := 118140960795 + 3695523 * 2 ^ 59
def prefixEnd_3695523 : Nat := 4983230072969 + 3 ^ 40 * 3695523 * 2
def baseEnd_3695523 : Nat := 1897579568745449982967105

theorem tailTrace_3695523 : CollatzResearch.WordTrace tailWord_3695523 prefixEnd_3695523 1897579568745449982967105 := by
  unfold tailWord_3695523
  simp only [CollatzResearch.WordTrace]
  refine ⟨134786796990758790925483223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89857864660505860616988815 134786796990758790925483223)
  ·
    refine ⟨202180195486138186388224835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134786796990758790925483223 202180195486138186388224835)
    ·
      refine ⟨303270293229207279582337253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202180195486138186388224835 303270293229207279582337253)
      ·
        refine ⟨56863179980476364921688235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303270293229207279582337253 56863179980476364921688235)
        ·
          refine ⟨85294769970714547382532353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56863179980476364921688235 85294769970714547382532353)
          ·
            refine ⟨63971077478035910536899265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85294769970714547382532353 63971077478035910536899265)
            ·
              refine ⟨47978308108526932902674449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63971077478035910536899265 47978308108526932902674449)
              ·
                refine ⟨35983731081395199677005837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47978308108526932902674449 35983731081395199677005837)
                ·
                  refine ⟨13493899155523199878877189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35983731081395199677005837 13493899155523199878877189)
                  ·
                    refine ⟨2530106091660599977289473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13493899155523199878877189 2530106091660599977289473)
                    ·
                      refine ⟨1897579568745449982967105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530106091660599977289473 1897579568745449982967105)
                      ·
                        rfl

theorem cell23_3695523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_3695523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695523 prefixEnd_3695523 := by exact prefixLift 3695523
  have htrace : WordTrace (prefixWord ++ tailWord_3695523) baseStart_3695523 baseEnd_3695523 := by
    simpa [prefixWord, tailWord_3695523, baseEnd_3695523] using wordTrace_append hprefix tailTrace_3695523
  have hstable : (prefixWord ++ tailWord_3695523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695523).length < 2 ^ (prefixWord ++ tailWord_3695523).sum := by decide
  have hdescent : baseEnd_3695523 < baseStart_3695523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695546 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 7]
def baseStart_3695546 : Nat := 118140960795 + 3695546 * 2 ^ 59
def prefixEnd_3695546 : Nat := 4983230072969 + 3 ^ 40 * 3695546 * 2
def baseEnd_3695546 : Nat := 210843486533389265886611

theorem tailTrace_3695546 : CollatzResearch.WordTrace tailWord_3695546 prefixEnd_3695546 210843486533389265886611 := by
  unfold tailWord_3695546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33696908967418866463392623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89858423913116977235713661 33696908967418866463392623)
  ·
    refine ⟨50545363451128299695088935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33696908967418866463392623 50545363451128299695088935)
    ·
      refine ⟨75818045176692449542633403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50545363451128299695088935 75818045176692449542633403)
      ·
        refine ⟨113727067765038674313950105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75818045176692449542633403 113727067765038674313950105)
        ·
          refine ⟨85295300823779005735462579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113727067765038674313950105 85295300823779005735462579)
          ·
            refine ⟨127942951235668508603193869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85295300823779005735462579 127942951235668508603193869)
            ·
              refine ⟨47978606713375690726197701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127942951235668508603193869 47978606713375690726197701)
              ·
                refine ⟨8995988758757942011162069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47978606713375690726197701 8995988758757942011162069)
                ·
                  refine ⟨210843486533389265886611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8995988758757942011162069 210843486533389265886611)
                  ·
                    rfl

theorem cell23_3695546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_3695546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695546 prefixEnd_3695546 := by exact prefixLift 3695546
  have htrace : WordTrace (prefixWord ++ tailWord_3695546) baseStart_3695546 baseEnd_3695546 := by
    simpa [prefixWord, tailWord_3695546, baseEnd_3695546] using wordTrace_append hprefix tailTrace_3695546
  have hstable : (prefixWord ++ tailWord_3695546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695546).length < 2 ^ (prefixWord ++ tailWord_3695546).sum := by decide
  have hdescent : baseEnd_3695546 < baseStart_3695546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695574 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_3695574 : Nat := 118140960795 + 3695574 * 2 ^ 59
def prefixEnd_3695574 : Nat := 4983230072969 + 3 ^ 40 * 3695574 * 2
def baseEnd_3695574 : Nat := 1897605756258829283429371

theorem tailTrace_3695574 : CollatzResearch.WordTrace tailWord_3695574 prefixEnd_3695574 1897605756258829283429371 := by
  unfold tailWord_3695574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424291069598376664724361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89859104742382684423726517 8424291069598376664724361)
  ·
    refine ⟨6318218302198782498543271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8424291069598376664724361 6318218302198782498543271)
    ·
      refine ⟨9477327453298173747814907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6318218302198782498543271 9477327453298173747814907)
      ·
        refine ⟨14215991179947260621722361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9477327453298173747814907 14215991179947260621722361)
        ·
          refine ⟨10661993384960445466291771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14215991179947260621722361 10661993384960445466291771)
          ·
            refine ⟨15992990077440668199437657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10661993384960445466291771 15992990077440668199437657)
            ·
              refine ⟨11994742558080501149578243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15992990077440668199437657 11994742558080501149578243)
              ·
                refine ⟨17992113837120751724367365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11994742558080501149578243 17992113837120751724367365)
                ·
                  refine ⟨3373521344460140948318881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17992113837120751724367365 3373521344460140948318881)
                  ·
                    refine ⟨2530141008345105711239161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3373521344460140948318881 2530141008345105711239161)
                    ·
                      refine ⟨1897605756258829283429371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530141008345105711239161 1897605756258829283429371)
                      ·
                        rfl

theorem cell23_3695574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_3695574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695574 prefixEnd_3695574 := by exact prefixLift 3695574
  have htrace : WordTrace (prefixWord ++ tailWord_3695574) baseStart_3695574 baseEnd_3695574 := by
    simpa [prefixWord, tailWord_3695574, baseEnd_3695574] using wordTrace_append hprefix tailTrace_3695574
  have hstable : (prefixWord ++ tailWord_3695574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695574).length < 2 ^ (prefixWord ++ tailWord_3695574).sum := by decide
  have hdescent : baseEnd_3695574 < baseStart_3695574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695591 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_3695591 : Nat := 118140960795 + 3695591 * 2 ^ 59
def prefixEnd_3695591 : Nat := 4983230072969 + 3 ^ 40 * 3695591 * 2
def baseEnd_3695591 : Nat := 1897614485429955716916793

theorem tailTrace_3695591 : CollatzResearch.WordTrace tailWord_3695591 prefixEnd_3695591 1897614485429955716916793 := by
  unfold tailWord_3695591
  simp only [CollatzResearch.WordTrace]
  refine ⟨134789277154512438538958627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89859518103008292359305751 134789277154512438538958627)
  ·
    refine ⟨202183915731768657808437941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134789277154512438538958627 202183915731768657808437941)
    ·
      refine ⟨18954742099853311669541057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202183915731768657808437941 18954742099853311669541057)
      ·
        refine ⟨14216056574889983752155793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18954742099853311669541057 14216056574889983752155793)
        ·
          refine ⟨10662042431167487814116845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14216056574889983752155793 10662042431167487814116845)
          ·
            refine ⟨3998265911687807930293817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10662042431167487814116845 3998265911687807930293817)
            ·
              refine ⟨2998699433765855947720363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998265911687807930293817 2998699433765855947720363)
              ·
                refine ⟨4498049150648783921580545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998699433765855947720363 4498049150648783921580545)
                ·
                  refine ⟨3373536862986587941185409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4498049150648783921580545 3373536862986587941185409)
                  ·
                    refine ⟨2530152647239940955889057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3373536862986587941185409 2530152647239940955889057)
                    ·
                      refine ⟨1897614485429955716916793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530152647239940955889057 1897614485429955716916793)
                      ·
                        rfl

theorem cell23_3695591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_3695591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695591 prefixEnd_3695591 := by exact prefixLift 3695591
  have htrace : WordTrace (prefixWord ++ tailWord_3695591) baseStart_3695591 baseEnd_3695591 := by
    simpa [prefixWord, tailWord_3695591, baseEnd_3695591] using wordTrace_append hprefix tailTrace_3695591
  have hstable : (prefixWord ++ tailWord_3695591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695591).length < 2 ^ (prefixWord ++ tailWord_3695591).sum := by decide
  have hdescent : baseEnd_3695591 < baseStart_3695591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695630 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3695630 : Nat := 118140960795 + 3695630 * 2 ^ 59
def prefixEnd_3695630 : Nat := 4983230072969 + 3 ^ 40 * 3695630 * 2
def baseEnd_3695630 : Nat := 1897634511175481064329113

theorem tailTrace_3695630 : CollatzResearch.WordTrace tailWord_3695630 prefixEnd_3695630 1897634511175481064329113 := by
  unfold tailWord_3695630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16848837450171393524953543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89860466400914098799752229 16848837450171393524953543)
  ·
    refine ⟨25273256175257090287430315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16848837450171393524953543 25273256175257090287430315)
    ·
      refine ⟨37909884262885635431145473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25273256175257090287430315 37909884262885635431145473)
      ·
        refine ⟨28432413197164226573359105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37909884262885635431145473 28432413197164226573359105)
        ·
          refine ⟨21324309897873169930019329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28432413197164226573359105 21324309897873169930019329)
          ·
            refine ⟨15993232423404877447514497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21324309897873169930019329 15993232423404877447514497)
            ·
              refine ⟨11994924317553658085635873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15993232423404877447514497 11994924317553658085635873)
              ·
                refine ⟨8996193238165243564226905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11994924317553658085635873 8996193238165243564226905)
                ·
                  refine ⟨6747144928623932673170179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8996193238165243564226905 6747144928623932673170179)
                  ·
                    refine ⟨10120717392935899009755269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6747144928623932673170179 10120717392935899009755269)
                    ·
                      refine ⟨1897634511175481064329113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10120717392935899009755269 1897634511175481064329113)
                      ·
                        rfl

theorem cell23_3695630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3695630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695630 prefixEnd_3695630 := by exact prefixLift 3695630
  have htrace : WordTrace (prefixWord ++ tailWord_3695630) baseStart_3695630 baseEnd_3695630 := by
    simpa [prefixWord, tailWord_3695630, baseEnd_3695630] using wordTrace_append hprefix tailTrace_3695630
  have hstable : (prefixWord ++ tailWord_3695630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695630).length < 2 ^ (prefixWord ++ tailWord_3695630).sum := by decide
  have hdescent : baseEnd_3695630 < baseStart_3695630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695653 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 6]
def baseStart_3695653 : Nat := 118140960795 + 3695653 * 2 ^ 59
def prefixEnd_3695653 : Nat := 4983230072969 + 3 ^ 40 * 3695653 * 2
def baseEnd_3695653 : Nat := 210849591247837163815723

theorem tailTrace_3695653 : CollatzResearch.WordTrace tailWord_3695653 prefixEnd_3695653 210849591247837163815723 := by
  unfold tailWord_3695653
  simp only [CollatzResearch.WordTrace]
  refine ⟨134791538480287823127715613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89861025653525215418477075 134791538480287823127715613)
  ·
    refine ⟨50546826930107933672893355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134791538480287823127715613 50546826930107933672893355)
    ·
      refine ⟨75820240395161900509340033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50546826930107933672893355 75820240395161900509340033)
      ·
        refine ⟨56865180296371425382005025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75820240395161900509340033 56865180296371425382005025)
        ·
          refine ⟨42648885222278569036503769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56865180296371425382005025 42648885222278569036503769)
          ·
            refine ⟨31986663916708926777377827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42648885222278569036503769 31986663916708926777377827)
            ·
              refine ⟨47979995875063390166066741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31986663916708926777377827 47979995875063390166066741)
              ·
                refine ⟨4498124613287192828068757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47979995875063390166066741 4498124613287192828068757)
                ·
                  refine ⟨210849591247837163815723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4498124613287192828068757 210849591247837163815723)
                  ·
                    rfl

theorem cell23_3695653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_3695653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695653 prefixEnd_3695653 := by exact prefixLift 3695653
  have htrace : WordTrace (prefixWord ++ tailWord_3695653) baseStart_3695653 baseEnd_3695653 := by
    simpa [prefixWord, tailWord_3695653, baseEnd_3695653] using wordTrace_append hprefix tailTrace_3695653
  have hstable : (prefixWord ++ tailWord_3695653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695653).length < 2 ^ (prefixWord ++ tailWord_3695653).sum := by decide
  have hdescent : baseEnd_3695653 < baseStart_3695653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695680 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 5, 1, 3]
def baseStart_3695680 : Nat := 118140960795 + 3695680 * 2 ^ 59
def prefixEnd_3695680 : Nat := 4983230072969 + 3 ^ 40 * 3695680 * 2
def baseEnd_3695680 : Nat := 1897660185208205868703883

theorem tailTrace_3695680 : CollatzResearch.WordTrace tailWord_3695680 prefixEnd_3695680 1897660185208205868703883 := by
  unfold tailWord_3695680
  simp only [CollatzResearch.WordTrace]
  refine ⟨67396261625595003369474247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89861682167460004492632329 67396261625595003369474247)
  ·
    refine ⟨101094392438392505054211371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67396261625595003369474247 101094392438392505054211371)
    ·
      refine ⟨151641588657588757581317057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101094392438392505054211371 151641588657588757581317057)
      ·
        refine ⟨113731191493191568185987793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151641588657588757581317057 113731191493191568185987793)
        ·
          refine ⟨85298393619893676139490845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113731191493191568185987793 85298393619893676139490845)
          ·
            refine ⟨31986897607460128552309067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85298393619893676139490845 31986897607460128552309067)
            ·
              refine ⟨47980346411190192828463601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31986897607460128552309067 47980346411190192828463601)
              ·
                refine ⟨35985259808392644621347701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47980346411190192828463601 35985259808392644621347701)
                ·
                  refine ⟨3373618107036810433251347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35985259808392644621347701 3373618107036810433251347)
                  ·
                    refine ⟨5060427160555215649877021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3373618107036810433251347 5060427160555215649877021)
                    ·
                      refine ⟨1897660185208205868703883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5060427160555215649877021 1897660185208205868703883)
                      ·
                        rfl

theorem cell23_3695680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_3695680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695680 prefixEnd_3695680 := by exact prefixLift 3695680
  have htrace : WordTrace (prefixWord ++ tailWord_3695680) baseStart_3695680 baseEnd_3695680 := by
    simpa [prefixWord, tailWord_3695680, baseEnd_3695680] using wordTrace_append hprefix tailTrace_3695680
  have hstable : (prefixWord ++ tailWord_3695680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695680).length < 2 ^ (prefixWord ++ tailWord_3695680).sum := by decide
  have hdescent : baseEnd_3695680 < baseStart_3695680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695714 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3695714 : Nat := 118140960795 + 3695714 * 2 ^ 59
def prefixEnd_3695714 : Nat := 4983230072969 + 3 ^ 40 * 3695714 * 2
def baseEnd_3695714 : Nat := 1897677643550458735678727

theorem tailTrace_3695714 : CollatzResearch.WordTrace tailWord_3695714 prefixEnd_3695714 1897677643550458735678727 := by
  unfold tailWord_3695714
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698440833266707636421549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89862508888711220363790797 33698440833266707636421549)
  ·
    refine ⟨12636915312475015363658081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33698440833266707636421549 12636915312475015363658081)
    ·
      refine ⟨9477686484356261522743561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12636915312475015363658081 9477686484356261522743561)
      ·
        refine ⟨7108264863267196142057671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9477686484356261522743561 7108264863267196142057671)
        ·
          refine ⟨10662397294900794213086507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108264863267196142057671 10662397294900794213086507)
          ·
            refine ⟨15993595942351191319629761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662397294900794213086507 15993595942351191319629761)
            ·
              refine ⟨11995196956763393489722321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15993595942351191319629761 11995196956763393489722321)
              ·
                refine ⟨8996397717572545117291741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11995196956763393489722321 8996397717572545117291741)
                ·
                  refine ⟨3373649144089704418984403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8996397717572545117291741 3373649144089704418984403)
                  ·
                    refine ⟨5060473716134556628476605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3373649144089704418984403 5060473716134556628476605)
                    ·
                      refine ⟨1897677643550458735678727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5060473716134556628476605 1897677643550458735678727)
                      ·
                        rfl

theorem cell23_3695714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3695714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695714 prefixEnd_3695714 := by exact prefixLift 3695714
  have htrace : WordTrace (prefixWord ++ tailWord_3695714) baseStart_3695714 baseEnd_3695714 := by
    simpa [prefixWord, tailWord_3695714, baseEnd_3695714] using wordTrace_append hprefix tailTrace_3695714
  have hstable : (prefixWord ++ tailWord_3695714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695714).length < 2 ^ (prefixWord ++ tailWord_3695714).sum := by decide
  have hdescent : baseEnd_3695714 < baseStart_3695714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695723 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 3]
def baseStart_3695723 : Nat := 118140960795 + 3695723 * 2 ^ 59
def prefixEnd_3695723 : Nat := 4983230072969 + 3 ^ 40 * 3695723 * 2
def baseEnd_3695723 : Nat := 1897682264876349200466185

theorem tailTrace_3695723 : CollatzResearch.WordTrace tailWord_3695723 prefixEnd_3695723 1897682264876349200466185 := by
  unfold tailWord_3695723
  simp only [CollatzResearch.WordTrace]
  refine ⟨134794091590034225082763823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89862727726689483388509215 134794091590034225082763823)
  ·
    refine ⟨202191137385051337624145735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134794091590034225082763823 202191137385051337624145735)
    ·
      refine ⟨303286706077577006436218603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202191137385051337624145735 303286706077577006436218603)
      ·
        refine ⟨454930059116365509654327905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303286706077577006436218603 454930059116365509654327905)
        ·
          refine ⟨341197544337274132240745929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454930059116365509654327905 341197544337274132240745929)
          ·
            refine ⟨255898158252955599180559447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341197544337274132240745929 255898158252955599180559447)
            ·
              refine ⟨383847237379433398770839171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255898158252955599180559447 383847237379433398770839171)
              ·
                refine ⟨575770856069150098156258757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383847237379433398770839171 575770856069150098156258757)
                ·
                  refine ⟨107957035512965643404298517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575770856069150098156258757 107957035512965643404298517)
                  ·
                    refine ⟨5060486039670264534576493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107957035512965643404298517 5060486039670264534576493)
                    ·
                      refine ⟨1897682264876349200466185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5060486039670264534576493 1897682264876349200466185)
                      ·
                        rfl

theorem cell23_3695723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 3].length) (baseStart_3695723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695723 prefixEnd_3695723 := by exact prefixLift 3695723
  have htrace : WordTrace (prefixWord ++ tailWord_3695723) baseStart_3695723 baseEnd_3695723 := by
    simpa [prefixWord, tailWord_3695723, baseEnd_3695723] using wordTrace_append hprefix tailTrace_3695723
  have hstable : (prefixWord ++ tailWord_3695723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695723).length < 2 ^ (prefixWord ++ tailWord_3695723).sum := by decide
  have hdescent : baseEnd_3695723 < baseStart_3695723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695730 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3695730 : Nat := 118140960795 + 3695730 * 2 ^ 59
def prefixEnd_3695730 : Nat := 4983230072969 + 3 ^ 40 * 3695730 * 2
def baseEnd_3695730 : Nat := 632561953080310224359551

theorem tailTrace_3695730 : CollatzResearch.WordTrace tailWord_3695730 prefixEnd_3695730 632561953080310224359551 := by
  unfold tailWord_3695730
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698586725252216319567161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89862897934005910185512429 33698586725252216319567161)
  ·
    refine ⟨25273940043939162239675371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33698586725252216319567161 25273940043939162239675371)
    ·
      refine ⟨37910910065908743359513057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25273940043939162239675371 37910910065908743359513057)
      ·
        refine ⟨28433182549431557519634793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37910910065908743359513057 28433182549431557519634793)
        ·
          refine ⟨21324886912073668139726095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28433182549431557519634793 21324886912073668139726095)
          ·
            refine ⟨31987330368110502209589143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21324886912073668139726095 31987330368110502209589143)
            ·
              refine ⟨47980995552165753314383715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31987330368110502209589143 47980995552165753314383715)
              ·
                refine ⟨71971493328248629971575573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47980995552165753314383715 71971493328248629971575573)
                ·
                  refine ⟨3373663749761654529917605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71971493328248629971575573 3373663749761654529917605)
                  ·
                    refine ⟨632561953080310224359551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373663749761654529917605 632561953080310224359551)
                    ·
                      rfl

theorem cell23_3695730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3695730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695730 prefixEnd_3695730 := by exact prefixLift 3695730
  have htrace : WordTrace (prefixWord ++ tailWord_3695730) baseStart_3695730 baseEnd_3695730 := by
    simpa [prefixWord, tailWord_3695730, baseEnd_3695730] using wordTrace_append hprefix tailTrace_3695730
  have hstable : (prefixWord ++ tailWord_3695730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695730).length < 2 ^ (prefixWord ++ tailWord_3695730).sum := by decide
  have hdescent : baseEnd_3695730 < baseStart_3695730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695740 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_3695740 : Nat := 118140960795 + 3695740 * 2 ^ 59
def prefixEnd_3695740 : Nat := 4983230072969 + 3 ^ 40 * 3695740 * 2
def baseEnd_3695740 : Nat := 1897690994047475633953607

theorem tailTrace_3695740 : CollatzResearch.WordTrace tailWord_3695740 prefixEnd_3695740 1897690994047475633953607 := by
  unfold tailWord_3695740
  simp only [CollatzResearch.WordTrace]
  refine ⟨67397355815486318493066337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89863141087315091324088449 67397355815486318493066337)
  ·
    refine ⟨50548016861614738869799753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67397355815486318493066337 50548016861614738869799753)
    ·
      refine ⟨37911012646211054152349815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50548016861614738869799753 37911012646211054152349815)
      ·
        refine ⟨56866518969316581228524723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37911012646211054152349815 56866518969316581228524723)
        ·
          refine ⟨85299778453974871842787085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56866518969316581228524723 85299778453974871842787085)
          ·
            refine ⟨31987416920240576941045157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85299778453974871842787085 31987416920240576941045157)
            ·
              refine ⟨5997640672545108176445967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31987416920240576941045157 5997640672545108176445967)
              ·
                refine ⟨8996461008817662264668951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997640672545108176445967 8996461008817662264668951)
                ·
                  refine ⟨13494691513226493397003427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8996461008817662264668951 13494691513226493397003427)
                  ·
                    refine ⟨20242037269839740095505141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13494691513226493397003427 20242037269839740095505141)
                    ·
                      refine ⟨1897690994047475633953607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20242037269839740095505141 1897690994047475633953607)
                      ·
                        rfl

theorem cell23_3695740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_3695740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695740 prefixEnd_3695740 := by exact prefixLift 3695740
  have htrace : WordTrace (prefixWord ++ tailWord_3695740) baseStart_3695740 baseEnd_3695740 := by
    simpa [prefixWord, tailWord_3695740, baseEnd_3695740] using wordTrace_append hprefix tailTrace_3695740
  have hstable : (prefixWord ++ tailWord_3695740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695740).length < 2 ^ (prefixWord ++ tailWord_3695740).sum := by decide
  have hdescent : baseEnd_3695740 < baseStart_3695740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695774 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3695774 : Nat := 118140960795 + 3695774 * 2 ^ 59
def prefixEnd_3695774 : Nat := 4983230072969 + 3 ^ 40 * 3695774 * 2
def baseEnd_3695774 : Nat := 1897708452389728500928451

theorem tailTrace_3695774 : CollatzResearch.WordTrace tailWord_3695774 prefixEnd_3695774 1897708452389728500928451 := by
  unfold tailWord_3695774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16849493964106182599108797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89863967808566307195246917 16849493964106182599108797)
  ·
    refine ⟨6318560236539818474665799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16849493964106182599108797 6318560236539818474665799)
    ·
      refine ⟨9477840354809727711998699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6318560236539818474665799 9477840354809727711998699)
      ·
        refine ⟨14216760532214591567998049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9477840354809727711998699 14216760532214591567998049)
        ·
          refine ⟨10662570399160943675998537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14216760532214591567998049 10662570399160943675998537)
          ·
            refine ⟨7996927799370707756998903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10662570399160943675998537 7996927799370707756998903)
            ·
              refine ⟨11995391699056061635498355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996927799370707756998903 11995391699056061635498355)
              ·
                refine ⟨17993087548584092453247533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11995391699056061635498355 17993087548584092453247533)
                ·
                  refine ⟨6747407830719034669967825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17993087548584092453247533 6747407830719034669967825)
                  ·
                    refine ⟨5060555873039276002475869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6747407830719034669967825 5060555873039276002475869)
                    ·
                      refine ⟨1897708452389728500928451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5060555873039276002475869 1897708452389728500928451)
                      ·
                        rfl

theorem cell23_3695774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3695774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695774 prefixEnd_3695774 := by exact prefixLift 3695774
  have htrace : WordTrace (prefixWord ++ tailWord_3695774) baseStart_3695774 baseEnd_3695774 := by
    simpa [prefixWord, tailWord_3695774, baseEnd_3695774] using wordTrace_append hprefix tailTrace_3695774
  have hstable : (prefixWord ++ tailWord_3695774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695774).length < 2 ^ (prefixWord ++ tailWord_3695774).sum := by decide
  have hdescent : baseEnd_3695774 < baseStart_3695774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695798 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3695798 : Nat := 118140960795 + 3695798 * 2 ^ 59
def prefixEnd_3695798 : Nat := 4983230072969 + 3 ^ 40 * 3695798 * 2
def baseEnd_3695798 : Nat := 632573591975145469009447

theorem tailTrace_3695798 : CollatzResearch.WordTrace tailWord_3695798 prefixEnd_3695798 632573591975145469009447 := by
  unfold tailWord_3695798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424801691547657055734003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89864551376508341927829365 8424801691547657055734003)
  ·
    refine ⟨12637202537321485583601005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8424801691547657055734003 12637202537321485583601005)
    ·
      refine ⟨4738950951495557093850377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12637202537321485583601005 4738950951495557093850377)
      ·
        refine ⟨3554213213621667820387783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4738950951495557093850377 3554213213621667820387783)
        ·
          refine ⟨5331319820432501730581675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554213213621667820387783 5331319820432501730581675)
          ·
            refine ⟨7996979730648752595872513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331319820432501730581675 7996979730648752595872513)
            ·
              refine ⟨5997734797986564446904385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996979730648752595872513 5997734797986564446904385)
              ·
                refine ⟨4498301098489923335178289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997734797986564446904385 4498301098489923335178289)
                ·
                  refine ⟨3373725823867442501383717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4498301098489923335178289 3373725823867442501383717)
                  ·
                    refine ⟨632573591975145469009447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373725823867442501383717 632573591975145469009447)
                    ·
                      rfl

theorem cell23_3695798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3695798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695798 prefixEnd_3695798 := by exact prefixLift 3695798
  have htrace : WordTrace (prefixWord ++ tailWord_3695798) baseStart_3695798 baseEnd_3695798 := by
    simpa [prefixWord, tailWord_3695798, baseEnd_3695798] using wordTrace_append hprefix tailTrace_3695798
  have hstable : (prefixWord ++ tailWord_3695798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695798).length < 2 ^ (prefixWord ++ tailWord_3695798).sum := by decide
  have hdescent : baseEnd_3695798 < baseStart_3695798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695804 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3695804 : Nat := 118140960795 + 3695804 * 2 ^ 59
def prefixEnd_3695804 : Nat := 4983230072969 + 3 ^ 40 * 3695804 * 2
def baseEnd_3695804 : Nat := 1897723856809363383553313

theorem tailTrace_3695804 : CollatzResearch.WordTrace tailWord_3695804 prefixEnd_3695804 1897723856809363383553313 := by
  unfold tailWord_3695804
  simp only [CollatzResearch.WordTrace]
  refine ⟨67398522951370387958231233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89864697268493850610974977 67398522951370387958231233)
  ·
    refine ⟨50548892213527790968673425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67398522951370387958231233 50548892213527790968673425)
    ·
      refine ⟨37911669160145843226505069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50548892213527790968673425 37911669160145843226505069)
      ·
        refine ⟨14216875935054691209939401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37911669160145843226505069 14216875935054691209939401)
        ·
          refine ⟨10662656951291018407454551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14216875935054691209939401 10662656951291018407454551)
          ·
            refine ⟨15993985426936527611181827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662656951291018407454551 15993985426936527611181827)
            ·
              refine ⟨23990978140404791416772741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15993985426936527611181827 23990978140404791416772741)
              ·
                refine ⟨4498308401325898390644889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23990978140404791416772741 4498308401325898390644889)
                ·
                  refine ⟨3373731300994423792983667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4498308401325898390644889 3373731300994423792983667)
                  ·
                    refine ⟨5060596951491635689475501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3373731300994423792983667 5060596951491635689475501)
                    ·
                      refine ⟨1897723856809363383553313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5060596951491635689475501 1897723856809363383553313)
                      ·
                        rfl

theorem cell23_3695804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3695804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695804 prefixEnd_3695804 := by exact prefixLift 3695804
  have htrace : WordTrace (prefixWord ++ tailWord_3695804) baseStart_3695804 baseEnd_3695804 := by
    simpa [prefixWord, tailWord_3695804, baseEnd_3695804] using wordTrace_append hprefix tailTrace_3695804
  have hstable : (prefixWord ++ tailWord_3695804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695804).length < 2 ^ (prefixWord ++ tailWord_3695804).sum := by decide
  have hdescent : baseEnd_3695804 < baseStart_3695804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695901 : List Nat := [1, 4, 2, 3, 1, 3, 1, 3, 5]
def baseStart_3695901 : Nat := 118140960795 + 3695901 * 2 ^ 59
def prefixEnd_3695901 : Nat := 4983230072969 + 3 ^ 40 * 3695901 * 2
def baseEnd_3695901 : Nat := 210863740492538833782263

theorem tailTrace_3695901 : CollatzResearch.WordTrace tailWord_3695901 prefixEnd_3695901 210863740492538833782263 := by
  unfold tailWord_3695901
  simp only [CollatzResearch.WordTrace]
  refine ⟨134800583783389361482743557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89867055855592907655162371 134800583783389361482743557)
  ·
    refine ⟨25275109459385505278014417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134800583783389361482743557 25275109459385505278014417)
    ·
      refine ⟨18956332094539128958510813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25275109459385505278014417 18956332094539128958510813)
      ·
        refine ⟨7108624535452173359441555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18956332094539128958510813 7108624535452173359441555)
        ·
          refine ⟨10662936803178260039162333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108624535452173359441555 10662936803178260039162333)
          ·
            refine ⟨3998601301191847514685875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10662936803178260039162333 3998601301191847514685875)
            ·
              refine ⟨5997901951787771272028813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3998601301191847514685875 5997901951787771272028813)
              ·
                refine ⟨2249213231920414227010805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5997901951787771272028813 2249213231920414227010805)
                ·
                  refine ⟨210863740492538833782263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2249213231920414227010805 210863740492538833782263)
                  ·
                    rfl

theorem cell23_3695901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_3695901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695901 prefixEnd_3695901 := by exact prefixLift 3695901
  have htrace : WordTrace (prefixWord ++ tailWord_3695901) baseStart_3695901 baseEnd_3695901 := by
    simpa [prefixWord, tailWord_3695901, baseEnd_3695901] using wordTrace_append hprefix tailTrace_3695901
  have hstable : (prefixWord ++ tailWord_3695901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695901).length < 2 ^ (prefixWord ++ tailWord_3695901).sum := by decide
  have hdescent : baseEnd_3695901 < baseStart_3695901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695914 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3695914 : Nat := 118140960795 + 3695914 * 2 ^ 59
def prefixEnd_3695914 : Nat := 4983230072969 + 3 ^ 40 * 3695914 * 2
def baseEnd_3695914 : Nat := 632593446560452651059269

theorem tailTrace_3695914 : CollatzResearch.WordTrace tailWord_3695914 prefixEnd_3695914 632593446560452651059269 := by
  unfold tailWord_3695914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33700264483085566175741699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89867371954894843135311197 33700264483085566175741699)
  ·
    refine ⟨50550396724628349263612549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33700264483085566175741699 50550396724628349263612549)
    ·
      refine ⟨9478199385867815486927353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50550396724628349263612549 9478199385867815486927353)
      ·
        refine ⟨7108649539400861615195515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9478199385867815486927353 7108649539400861615195515)
        ·
          refine ⟨10662974309101292422793273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108649539400861615195515 10662974309101292422793273)
          ·
            refine ⟨7997230731825969317094955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10662974309101292422793273 7997230731825969317094955)
            ·
              refine ⟨11995846097738953975642433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997230731825969317094955 11995846097738953975642433)
              ·
                refine ⟨8996884573304215481731825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11995846097738953975642433 8996884573304215481731825)
                ·
                  refine ⟨6747663429978161611298869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8996884573304215481731825 6747663429978161611298869)
                  ·
                    refine ⟨632593446560452651059269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6747663429978161611298869 632593446560452651059269)
                    ·
                      rfl

theorem cell23_3695914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3695914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695914 prefixEnd_3695914 := by exact prefixLift 3695914
  have htrace : WordTrace (prefixWord ++ tailWord_3695914) baseStart_3695914 baseEnd_3695914 := by
    simpa [prefixWord, tailWord_3695914, baseEnd_3695914] using wordTrace_append hprefix tailTrace_3695914
  have hstable : (prefixWord ++ tailWord_3695914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695914).length < 2 ^ (prefixWord ++ tailWord_3695914).sum := by decide
  have hdescent : baseEnd_3695914 < baseStart_3695914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695934 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_3695934 : Nat := 118140960795 + 3695934 * 2 ^ 59
def prefixEnd_3695934 : Nat := 4983230072969 + 3 ^ 40 * 3695934 * 2
def baseEnd_3695934 : Nat := 1897790609294447874927715

theorem tailTrace_3695934 : CollatzResearch.WordTrace tailWord_3695934 prefixEnd_3695934 1897790609294447874927715 := by
  unfold tailWord_3695934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16850223424033726014836857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89867858261513205412463237 16850223424033726014836857)
  ·
    refine ⟨12637667568025294511127643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16850223424033726014836857 12637667568025294511127643)
    ·
      refine ⟨18956501352037941766691465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12637667568025294511127643 18956501352037941766691465)
      ·
        refine ⟨14217376014028456325018599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18956501352037941766691465 14217376014028456325018599)
        ·
          refine ⟨21326064021042684487527899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14217376014028456325018599 21326064021042684487527899)
          ·
            refine ⟨31989096031564026731291849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21326064021042684487527899 31989096031564026731291849)
            ·
              refine ⟨23991822023673020048468887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31989096031564026731291849 23991822023673020048468887)
              ·
                refine ⟨35987733035509530072703331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23991822023673020048468887 35987733035509530072703331)
                ·
                  refine ⟨53981599553264295109054997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35987733035509530072703331 53981599553264295109054997)
                  ·
                    refine ⟨2530387479059263833236953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53981599553264295109054997 2530387479059263833236953)
                    ·
                      refine ⟨1897790609294447874927715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530387479059263833236953 1897790609294447874927715)
                      ·
                        rfl

theorem cell23_3695934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_3695934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695934 prefixEnd_3695934 := by exact prefixLift 3695934
  have htrace : WordTrace (prefixWord ++ tailWord_3695934) baseStart_3695934 baseEnd_3695934 := by
    simpa [prefixWord, tailWord_3695934, baseEnd_3695934] using wordTrace_append hprefix tailTrace_3695934
  have hstable : (prefixWord ++ tailWord_3695934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695934).length < 2 ^ (prefixWord ++ tailWord_3695934).sum := by decide
  have hdescent : baseEnd_3695934 < baseStart_3695934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695978 : List Nat := [3, 1, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_3695978 : Nat := 118140960795 + 3695978 * 2 ^ 59
def prefixEnd_3695978 : Nat := 4983230072969 + 3 ^ 40 * 3695978 * 2
def baseEnd_3695978 : Nat := 632604400814415234259171

theorem tailTrace_3695978 : CollatzResearch.WordTrace tailWord_3695978 prefixEnd_3695978 632604400814415234259171 := by
  unfold tailWord_3695978
  simp only [CollatzResearch.WordTrace]
  refine ⟨33700848051027600908324147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89868928136073602422197725 33700848051027600908324147)
  ·
    refine ⟨50551272076541401362486221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33700848051027600908324147 50551272076541401362486221)
    ·
      refine ⟨18956727028703025510932333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50551272076541401362486221 18956727028703025510932333)
      ·
        refine ⟨7108772635763634566599625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18956727028703025510932333 7108772635763634566599625)
        ·
          refine ⟨5331579476822725924949719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7108772635763634566599625 5331579476822725924949719)
          ·
            refine ⟨7997369215234088887424579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331579476822725924949719 7997369215234088887424579)
            ·
              refine ⟨11996053822851133331136869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997369215234088887424579 11996053822851133331136869)
              ·
                refine ⟨2249260091784587499588163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11996053822851133331136869 2249260091784587499588163)
                ·
                  refine ⟨3373890137676881249382245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249260091784587499588163 3373890137676881249382245)
                  ·
                    refine ⟨632604400814415234259171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373890137676881249382245 632604400814415234259171)
                    ·
                      rfl

theorem cell23_3695978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_3695978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695978 prefixEnd_3695978 := by exact prefixLift 3695978
  have htrace : WordTrace (prefixWord ++ tailWord_3695978) baseStart_3695978 baseEnd_3695978 := by
    simpa [prefixWord, tailWord_3695978, baseEnd_3695978] using wordTrace_append hprefix tailTrace_3695978
  have hstable : (prefixWord ++ tailWord_3695978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695978).length < 2 ^ (prefixWord ++ tailWord_3695978).sum := by decide
  have hdescent : baseEnd_3695978 < baseStart_3695978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695984 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 3, 1, 3]
def baseStart_3695984 : Nat := 118140960795 + 3695984 * 2 ^ 59
def prefixEnd_3695984 : Nat := 4983230072969 + 3 ^ 40 * 3695984 * 2
def baseEnd_3695984 : Nat := 1897816283327172679302485

theorem tailTrace_3695984 : CollatzResearch.WordTrace tailWord_3695984 prefixEnd_3695984 1897816283327172679302485 := by
  unfold tailWord_3695984
  simp only [CollatzResearch.WordTrace]
  refine ⟨67401805521044333329007503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89869074028059111105343337 67401805521044333329007503)
  ·
    refine ⟨101102708281566499993511255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67401805521044333329007503 101102708281566499993511255)
    ·
      refine ⟨151654062422349749990266883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101102708281566499993511255 151654062422349749990266883)
      ·
        refine ⟨227481093633524624985400325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151654062422349749990266883 227481093633524624985400325)
        ·
          refine ⟨42652705056285867184762561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227481093633524624985400325 42652705056285867184762561)
          ·
            refine ⟨31989528792214400388571921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42652705056285867184762561 31989528792214400388571921)
            ·
              refine ⟨23992146594160800291428941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31989528792214400388571921 23992146594160800291428941)
              ·
                refine ⟨8997054972810300109285853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23992146594160800291428941 8997054972810300109285853)
                ·
                  refine ⟨3373895614803862540982195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8997054972810300109285853 3373895614803862540982195)
                  ·
                    refine ⟨5060843422205793811473293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3373895614803862540982195 5060843422205793811473293)
                    ·
                      refine ⟨1897816283327172679302485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5060843422205793811473293 1897816283327172679302485)
                      ·
                        rfl

theorem cell23_3695984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 3, 1, 3].length) (baseStart_3695984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3695984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3695984 prefixEnd_3695984 := by exact prefixLift 3695984
  have htrace : WordTrace (prefixWord ++ tailWord_3695984) baseStart_3695984 baseEnd_3695984 := by
    simpa [prefixWord, tailWord_3695984, baseEnd_3695984] using wordTrace_append hprefix tailTrace_3695984
  have hstable : (prefixWord ++ tailWord_3695984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695984).length < 2 ^ (prefixWord ++ tailWord_3695984).sum := by decide
  have hdescent : baseEnd_3695984 < baseStart_3695984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696017 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 6, 4]
def baseStart_3696017 : Nat := 118140960795 + 3696017 * 2 ^ 59
def prefixEnd_3696017 : Nat := 4983230072969 + 3 ^ 40 * 3696017 * 2
def baseEnd_3696017 : Nat := 632611076062923683396611

theorem tailTrace_3696017 : CollatzResearch.WordTrace tailWord_3696017 prefixEnd_3696017 632611076062923683396611 := by
  unfold tailWord_3696017
  simp only [CollatzResearch.WordTrace]
  refine ⟨134804814650969113293966305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89869876433979408862644203 134804814650969113293966305)
  ·
    refine ⟨101103610988226834970474729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134804814650969113293966305 101103610988226834970474729)
    ·
      refine ⟨75827708241170126227856047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101103610988226834970474729 75827708241170126227856047)
      ·
        refine ⟨113741562361755189341784071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75827708241170126227856047 113741562361755189341784071)
        ·
          refine ⟨170612343542632784012676107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113741562361755189341784071 170612343542632784012676107)
          ·
            refine ⟨255918515313949176019014161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170612343542632784012676107 255918515313949176019014161)
            ·
              refine ⟨191938886485461882014260621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255918515313949176019014161 191938886485461882014260621)
              ·
                refine ⟨71977082432048205755347733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191938886485461882014260621 71977082432048205755347733)
                ·
                  refine ⟨3373925739002259644781925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71977082432048205755347733 3373925739002259644781925)
                  ·
                    refine ⟨632611076062923683396611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3373925739002259644781925 632611076062923683396611)
                    ·
                      rfl

theorem cell23_3696017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_3696017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696017 prefixEnd_3696017 := by exact prefixLift 3696017
  have htrace : WordTrace (prefixWord ++ tailWord_3696017) baseStart_3696017 baseEnd_3696017 := by
    simpa [prefixWord, tailWord_3696017, baseEnd_3696017] using wordTrace_append hprefix tailTrace_3696017
  have hstable : (prefixWord ++ tailWord_3696017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696017).length < 2 ^ (prefixWord ++ tailWord_3696017).sum := by decide
  have hdescent : baseEnd_3696017 < baseStart_3696017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696061 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_3696061 : Nat := 118140960795 + 3696061 * 2 ^ 59
def prefixEnd_3696061 : Nat := 4983230072969 + 3 ^ 40 * 3696061 * 2
def baseEnd_3696061 : Nat := 1897855821337568878039631

theorem tailTrace_3696061 : CollatzResearch.WordTrace tailWord_3696061 prefixEnd_3696061 1897855821337568878039631 := by
  unfold tailWord_3696061
  simp only [CollatzResearch.WordTrace]
  refine ⟨134806419462809708808568037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89870946308539805872378691 134806419462809708808568037)
  ·
    refine ⟨25276203649276820401606507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134806419462809708808568037 25276203649276820401606507)
    ·
      refine ⟨37914305473915230602409761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25276203649276820401606507 37914305473915230602409761)
      ·
        refine ⟨28435729105436422951807321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37914305473915230602409761 28435729105436422951807321)
        ·
          refine ⟨21326796829077317213855491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28435729105436422951807321 21326796829077317213855491)
          ·
            refine ⟨31990195243615975820783237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21326796829077317213855491 31990195243615975820783237)
            ·
              refine ⟨5998161608177995466396857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31990195243615975820783237 5998161608177995466396857)
              ·
                refine ⟨4498621206133496599797643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5998161608177995466396857 4498621206133496599797643)
                ·
                  refine ⟨6747931809200244899696465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498621206133496599797643 6747931809200244899696465)
                  ·
                    refine ⟨5060948856900183674772349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6747931809200244899696465 5060948856900183674772349)
                    ·
                      refine ⟨1897855821337568878039631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5060948856900183674772349 1897855821337568878039631)
                      ·
                        rfl

theorem cell23_3696061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_3696061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696061 prefixEnd_3696061 := by exact prefixLift 3696061
  have htrace : WordTrace (prefixWord ++ tailWord_3696061) baseStart_3696061 baseEnd_3696061 := by
    simpa [prefixWord, tailWord_3696061, baseEnd_3696061] using wordTrace_append hprefix tailTrace_3696061
  have hstable : (prefixWord ++ tailWord_3696061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696061).length < 2 ^ (prefixWord ++ tailWord_3696061).sum := by decide
  have hdescent : baseEnd_3696061 < baseStart_3696061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696118 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_3696118 : Nat := 118140960795 + 3696118 * 2 ^ 59
def prefixEnd_3696118 : Nat := 4983230072969 + 3 ^ 40 * 3696118 * 2
def baseEnd_3696118 : Nat := 1897885089734875155026869

theorem tailTrace_3696118 : CollatzResearch.WordTrace tailWord_3696118 prefixEnd_3696118 1897885089734875155026869 := by
  unfold tailWord_3696118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425531151475200471462063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89872332282402138362262005 8425531151475200471462063)
  ·
    refine ⟨12638296727212800707193095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8425531151475200471462063 12638296727212800707193095)
    ·
      refine ⟨18957445090819201060789643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12638296727212800707193095 18957445090819201060789643)
      ·
        refine ⟨28436167636228801591184465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18957445090819201060789643 28436167636228801591184465)
        ·
          refine ⟨21327125727171601193388349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28436167636228801591184465 21327125727171601193388349)
          ·
            refine ⟨7997672147689350447520631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21327125727171601193388349 7997672147689350447520631)
            ·
              refine ⟨11996508221534025671280947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997672147689350447520631 11996508221534025671280947)
              ·
                refine ⟨17994762332301038506921421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11996508221534025671280947 17994762332301038506921421)
                ·
                  refine ⟨6748035874612889440095533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17994762332301038506921421 6748035874612889440095533)
                  ·
                    refine ⟨2530513452979833540035825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6748035874612889440095533 2530513452979833540035825)
                    ·
                      refine ⟨1897885089734875155026869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530513452979833540035825 1897885089734875155026869)
                      ·
                        rfl

theorem cell23_3696118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_3696118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696118 prefixEnd_3696118 := by exact prefixLift 3696118
  have htrace : WordTrace (prefixWord ++ tailWord_3696118) baseStart_3696118 baseEnd_3696118 := by
    simpa [prefixWord, tailWord_3696118, baseEnd_3696118] using wordTrace_append hprefix tailTrace_3696118
  have hstable : (prefixWord ++ tailWord_3696118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696118).length < 2 ^ (prefixWord ++ tailWord_3696118).sum := by decide
  have hdescent : baseEnd_3696118 < baseStart_3696118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696127 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_3696127 : Nat := 118140960795 + 3696127 * 2 ^ 59
def prefixEnd_3696127 : Nat := 4983230072969 + 3 ^ 40 * 3696127 * 2
def baseEnd_3696127 : Nat := 1897889711060765619814327

theorem tailTrace_3696127 : CollatzResearch.WordTrace tailWord_3696127 prefixEnd_3696127 1897889711060765619814327 := by
  unfold tailWord_3696127
  simp only [CollatzResearch.WordTrace]
  refine ⟨134808826680570602080470635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89872551120380401386980423 134808826680570602080470635)
  ·
    refine ⟨202213240020855903120705953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134808826680570602080470635 202213240020855903120705953)
    ·
      refine ⟨151659930015641927340529465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202213240020855903120705953 151659930015641927340529465)
      ·
        refine ⟨113744947511731445505397099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151659930015641927340529465 113744947511731445505397099)
        ·
          refine ⟨170617421267597168258095649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113744947511731445505397099 170617421267597168258095649)
          ·
            refine ⟨127963065950697876193571737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170617421267597168258095649 127963065950697876193571737)
            ·
              refine ⟨95972299463023407145178803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127963065950697876193571737 95972299463023407145178803)
              ·
                refine ⟨143958449194535110717768205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95972299463023407145178803 143958449194535110717768205)
                ·
                  refine ⟨53984418447950666519163077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143958449194535110717768205 53984418447950666519163077)
                  ·
                    refine ⟨10122078458990749972343077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53984418447950666519163077 10122078458990749972343077)
                    ·
                      refine ⟨1897889711060765619814327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10122078458990749972343077 1897889711060765619814327)
                      ·
                        rfl

theorem cell23_3696127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_3696127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696127 prefixEnd_3696127 := by exact prefixLift 3696127
  have htrace : WordTrace (prefixWord ++ tailWord_3696127) baseStart_3696127 baseEnd_3696127 := by
    simpa [prefixWord, tailWord_3696127, baseEnd_3696127] using wordTrace_append hprefix tailTrace_3696127
  have hstable : (prefixWord ++ tailWord_3696127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696127).length < 2 ^ (prefixWord ++ tailWord_3696127).sum := by decide
  have hdescent : baseEnd_3696127 < baseStart_3696127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696131 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 4, 2, 2]
def baseStart_3696131 : Nat := 118140960795 + 3696131 * 2 ^ 59
def prefixEnd_3696131 : Nat := 4983230072969 + 3 ^ 40 * 3696131 * 2
def baseEnd_3696131 : Nat := 1897891764983383604164309

theorem tailTrace_3696131 : CollatzResearch.WordTrace tailWord_3696131 prefixEnd_3696131 1897891764983383604164309 := by
  unfold tailWord_3696131
  simp only [CollatzResearch.WordTrace]
  refine ⟨134808972572556110763616247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89872648381704073842410831 134808972572556110763616247)
  ·
    refine ⟨202213458858834166145424371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134808972572556110763616247 202213458858834166145424371)
    ·
      refine ⟨303320188288251249218136557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202213458858834166145424371 303320188288251249218136557)
      ·
        refine ⟨113745070608094218456801209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303320188288251249218136557 113745070608094218456801209)
        ·
          refine ⟨85308802956070663842600907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113745070608094218456801209 85308802956070663842600907)
          ·
            refine ⟨127963204434105995763901361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85308802956070663842600907 127963204434105995763901361)
            ·
              refine ⟨95972403325579496822926021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127963204434105995763901361 95972403325579496822926021)
              ·
                refine ⟨17994825623546155654298629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95972403325579496822926021 17994825623546155654298629)
                ·
                  refine ⟨3374029804414904185180993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17994825623546155654298629 3374029804414904185180993)
                  ·
                    refine ⟨2530522353311178138885745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3374029804414904185180993 2530522353311178138885745)
                    ·
                      refine ⟨1897891764983383604164309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530522353311178138885745 1897891764983383604164309)
                      ·
                        rfl

theorem cell23_3696131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_3696131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696131 prefixEnd_3696131 := by exact prefixLift 3696131
  have htrace : WordTrace (prefixWord ++ tailWord_3696131) baseStart_3696131 baseEnd_3696131 := by
    simpa [prefixWord, tailWord_3696131, baseEnd_3696131] using wordTrace_append hprefix tailTrace_3696131
  have hstable : (prefixWord ++ tailWord_3696131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696131).length < 2 ^ (prefixWord ++ tailWord_3696131).sum := by decide
  have hdescent : baseEnd_3696131 < baseStart_3696131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696135 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_3696135 : Nat := 118140960795 + 3696135 * 2 ^ 59
def prefixEnd_3696135 : Nat := 4983230072969 + 3 ^ 40 * 3696135 * 2
def baseEnd_3696135 : Nat := 1897893818906001588514291

theorem tailTrace_3696135 : CollatzResearch.WordTrace tailWord_3696135 prefixEnd_3696135 1897893818906001588514291 := by
  unfold tailWord_3696135
  simp only [CollatzResearch.WordTrace]
  refine ⟨134809118464541619446761859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89872745643027746297841239 134809118464541619446761859)
  ·
    refine ⟨202213677696812429170142789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134809118464541619446761859 202213677696812429170142789)
    ·
      refine ⟨37915064568152330469401773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202213677696812429170142789 37915064568152330469401773)
      ·
        refine ⟨14218149213057123926025665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37915064568152330469401773 14218149213057123926025665)
        ·
          refine ⟨10663611909792842944519249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14218149213057123926025665 10663611909792842944519249)
          ·
            refine ⟨7997708932344632208389437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10663611909792842944519249 7997708932344632208389437)
            ·
              refine ⟨2999140849629237078146039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7997708932344632208389437 2999140849629237078146039)
              ·
                refine ⟨4498711274443855617219059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999140849629237078146039 4498711274443855617219059)
                ·
                  refine ⟨6748066911665783425828589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498711274443855617219059 6748066911665783425828589)
                  ·
                    refine ⟨2530525091874668784685721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6748066911665783425828589 2530525091874668784685721)
                    ·
                      refine ⟨1897893818906001588514291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2530525091874668784685721 1897893818906001588514291)
                      ·
                        rfl

theorem cell23_3696135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_3696135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696135 prefixEnd_3696135 := by exact prefixLift 3696135
  have htrace : WordTrace (prefixWord ++ tailWord_3696135) baseStart_3696135 baseEnd_3696135 := by
    simpa [prefixWord, tailWord_3696135, baseEnd_3696135] using wordTrace_append hprefix tailTrace_3696135
  have hstable : (prefixWord ++ tailWord_3696135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696135).length < 2 ^ (prefixWord ++ tailWord_3696135).sum := by decide
  have hdescent : baseEnd_3696135 < baseStart_3696135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696184 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 1, 7]
def baseStart_3696184 : Nat := 118140960795 + 3696184 * 2 ^ 59
def prefixEnd_3696184 : Nat := 4983230072969 + 3 ^ 40 * 3696184 * 2
def baseEnd_3696184 : Nat := 632639659819357298933855

theorem tailTrace_3696184 : CollatzResearch.WordTrace tailWord_3696184 prefixEnd_3696184 632639659819357298933855 := by
  unfold tailWord_3696184
  simp only [CollatzResearch.WordTrace]
  refine ⟨67405452820682050407647803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89873937094242733876863737 67405452820682050407647803)
  ·
    refine ⟨101108179231023075611471705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67405452820682050407647803 101108179231023075611471705)
    ·
      refine ⟨75831134423267306708603779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101108179231023075611471705 75831134423267306708603779)
      ·
        refine ⟨113746701634900960062905669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75831134423267306708603779 113746701634900960062905669)
        ·
          refine ⟨21327506556543930011794813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113746701634900960062905669 21327506556543930011794813)
          ·
            refine ⟨7997814958703973754423055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21327506556543930011794813 7997814958703973754423055)
            ·
              refine ⟨11996722438055960631634583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997814958703973754423055 11996722438055960631634583)
              ·
                refine ⟨17995083657083940947451875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11996722438055960631634583 17995083657083940947451875)
                ·
                  refine ⟨26992625485625911421177813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17995083657083940947451875 26992625485625911421177813)
                  ·
                    refine ⟨632639659819357298933855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26992625485625911421177813 632639659819357298933855)
                    ·
                      rfl

theorem cell23_3696184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_3696184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696184 prefixEnd_3696184 := by exact prefixLift 3696184
  have htrace : WordTrace (prefixWord ++ tailWord_3696184) baseStart_3696184 baseEnd_3696184 := by
    simpa [prefixWord, tailWord_3696184, baseEnd_3696184] using wordTrace_append hprefix tailTrace_3696184
  have hstable : (prefixWord ++ tailWord_3696184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696184).length < 2 ^ (prefixWord ++ tailWord_3696184).sum := by decide
  have hdescent : baseEnd_3696184 < baseStart_3696184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696188 : List Nat := [2, 2, 2, 2, 4, 1, 2, 3, 5]
def baseStart_3696188 : Nat := 118140960795 + 3696188 * 2 ^ 59
def prefixEnd_3696188 : Nat := 4983230072969 + 3 ^ 40 * 3696188 * 2
def baseEnd_3696188 : Nat := 210880114820076653461283

theorem tailTrace_3696188 : CollatzResearch.WordTrace tailWord_3696188 prefixEnd_3696188 210880114820076653461283 := by
  unfold tailWord_3696188
  simp only [CollatzResearch.WordTrace]
  refine ⟨67405525766674804749220609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89874034355566406332294145 67405525766674804749220609)
  ·
    refine ⟨50554144325006103561915457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67405525766674804749220609 50554144325006103561915457)
    ·
      refine ⟨37915608243754577671436593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50554144325006103561915457 37915608243754577671436593)
      ·
        refine ⟨28436706182815933253577445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37915608243754577671436593 28436706182815933253577445)
        ·
          refine ⟨5331882409277987485045771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28436706182815933253577445 5331882409277987485045771)
          ·
            refine ⟨7997823613916981227568657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331882409277987485045771 7997823613916981227568657)
            ·
              refine ⟨5998367710437735920676493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7997823613916981227568657 5998367710437735920676493)
              ·
                refine ⟨2249387891414150970253685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5998367710437735920676493 2249387891414150970253685)
                ·
                  refine ⟨210880114820076653461283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2249387891414150970253685 210880114820076653461283)
                  ·
                    rfl

theorem cell23_3696188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_3696188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696188 prefixEnd_3696188 := by exact prefixLift 3696188
  have htrace : WordTrace (prefixWord ++ tailWord_3696188) baseStart_3696188 baseEnd_3696188 := by
    simpa [prefixWord, tailWord_3696188, baseEnd_3696188] using wordTrace_append hprefix tailTrace_3696188
  have hstable : (prefixWord ++ tailWord_3696188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696188).length < 2 ^ (prefixWord ++ tailWord_3696188).sum := by decide
  have hdescent : baseEnd_3696188 < baseStart_3696188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696231 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 3, 4]
def baseStart_3696231 : Nat := 118140960795 + 3696231 * 2 ^ 59
def prefixEnd_3696231 : Nat := 4983230072969 + 3 ^ 40 * 3696231 * 2
def baseEnd_3696231 : Nat := 632647704349611070971283

theorem tailTrace_3696231 : CollatzResearch.WordTrace tailWord_3696231 prefixEnd_3696231 632647704349611070971283 := by
  unfold tailWord_3696231
  simp only [CollatzResearch.WordTrace]
  refine ⟨134812619872193827842256547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89875079914795885228171031 134812619872193827842256547)
  ·
    refine ⟨202218929808290741763384821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134812619872193827842256547 202218929808290741763384821)
    ·
      refine ⟨18958024669527257040317327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202218929808290741763384821 18958024669527257040317327)
      ·
        refine ⟨28437037004290885560475991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18958024669527257040317327 28437037004290885560475991)
        ·
          refine ⟨42655555506436328340713987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28437037004290885560475991 42655555506436328340713987)
          ·
            refine ⟨63983333259654492511070981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42655555506436328340713987 63983333259654492511070981)
            ·
              refine ⟨11996874986185217345825809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63983333259654492511070981 11996874986185217345825809)
              ·
                refine ⟨8997656239638913009369357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11996874986185217345825809 8997656239638913009369357)
                ·
                  refine ⟨3374121089864592378513509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8997656239638913009369357 3374121089864592378513509)
                  ·
                    refine ⟨632647704349611070971283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3374121089864592378513509 632647704349611070971283)
                    ·
                      rfl

theorem cell23_3696231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_3696231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3696231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3696231 prefixEnd_3696231 := by exact prefixLift 3696231
  have htrace : WordTrace (prefixWord ++ tailWord_3696231) baseStart_3696231 baseEnd_3696231 := by
    simpa [prefixWord, tailWord_3696231, baseEnd_3696231] using wordTrace_append hprefix tailTrace_3696231
  have hstable : (prefixWord ++ tailWord_3696231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696231).length < 2 ^ (prefixWord ++ tailWord_3696231).sum := by decide
  have hdescent : baseEnd_3696231 < baseStart_3696231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
