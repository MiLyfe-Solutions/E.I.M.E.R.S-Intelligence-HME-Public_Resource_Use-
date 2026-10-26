import V185TrunkScan23Chunk0627

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3713786 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_3713786 : Nat := 118140960795 + 3713786 * 2 ^ 59
def prefixEnd_3713786 : Nat := 4983230072969 + 3 ^ 40 * 3713786 * 2
def baseEnd_3713786 : Nat := 1906957265938512028895615

theorem tailTrace_3713786 : CollatzResearch.WordTrace tailWord_3713786 prefixEnd_3713786 1906957265938512028895615 := by
  unfold tailWord_3713786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33863225830898765249390303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90301935549063373998374141 33863225830898765249390303)
  ·
    refine ⟨50794838746348147874085455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33863225830898765249390303 50794838746348147874085455)
    ·
      refine ⟨76192258119522221811128183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50794838746348147874085455 76192258119522221811128183)
      ·
        refine ⟨114288387179283332716692275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76192258119522221811128183 114288387179283332716692275)
        ·
          refine ⟨171432580768924999075038413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114288387179283332716692275 171432580768924999075038413)
          ·
            refine ⟨64287217788346874653139405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171432580768924999075038413 64287217788346874653139405)
            ·
              refine ⟨24107706670630077994927277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64287217788346874653139405 24107706670630077994927277)
              ·
                refine ⟨9040390001486279248097729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24107706670630077994927277 9040390001486279248097729)
                ·
                  refine ⟨6780292501114709436073297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9040390001486279248097729 6780292501114709436073297)
                  ·
                    refine ⟨5085219375836032077054973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6780292501114709436073297 5085219375836032077054973)
                    ·
                      refine ⟨1906957265938512028895615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5085219375836032077054973 1906957265938512028895615)
                      ·
                        rfl

theorem cell23_3713786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_3713786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713786 prefixEnd_3713786 := by exact prefixLift 3713786
  have htrace : WordTrace (prefixWord ++ tailWord_3713786) baseStart_3713786 baseEnd_3713786 := by
    simpa [prefixWord, tailWord_3713786, baseEnd_3713786] using wordTrace_append hprefix tailTrace_3713786
  have hstable : (prefixWord ++ tailWord_3713786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713786).length < 2 ^ (prefixWord ++ tailWord_3713786).sum := by decide
  have hdescent : baseEnd_3713786 < baseStart_3713786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713793 : List Nat := [1, 2, 4, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3713793 : Nat := 118140960795 + 3713793 * 2 ^ 59
def prefixEnd_3713793 : Nat := 4983230072969 + 3 ^ 40 * 3713793 * 2
def baseEnd_3713793 : Nat := 635653620101031167169361

theorem tailTrace_3713793 : CollatzResearch.WordTrace tailWord_3713793 prefixEnd_3713793 635653620101031167169361 := by
  unfold tailWord_3713793
  simp only [CollatzResearch.WordTrace]
  refine ⟨135453158634569701193066033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90302105756379800795377355 135453158634569701193066033)
  ·
    refine ⟨101589868975927275894799525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135453158634569701193066033 101589868975927275894799525)
    ·
      refine ⟨19048100432986364230274911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101589868975927275894799525 19048100432986364230274911)
      ·
        refine ⟨28572150649479546345412367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19048100432986364230274911 28572150649479546345412367)
        ·
          refine ⟨42858225974219319518118551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28572150649479546345412367 42858225974219319518118551)
          ·
            refine ⟨64287338961328979277177827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42858225974219319518118551 64287338961328979277177827)
            ·
              refine ⟨96431008441993468915766741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64287338961328979277177827 96431008441993468915766741)
              ·
                refine ⟨2260101760359221927713283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96431008441993468915766741 2260101760359221927713283)
                ·
                  refine ⟨3390152640538832891569925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260101760359221927713283 3390152640538832891569925)
                  ·
                    refine ⟨635653620101031167169361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3390152640538832891569925 635653620101031167169361)
                    ·
                      rfl

theorem cell23_3713793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3713793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713793 prefixEnd_3713793 := by exact prefixLift 3713793
  have htrace : WordTrace (prefixWord ++ tailWord_3713793) baseStart_3713793 baseEnd_3713793 := by
    simpa [prefixWord, tailWord_3713793, baseEnd_3713793] using wordTrace_append hprefix tailTrace_3713793
  have hstable : (prefixWord ++ tailWord_3713793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713793).length < 2 ^ (prefixWord ++ tailWord_3713793).sum := by decide
  have hdescent : baseEnd_3713793 < baseStart_3713793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713829 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3713829 : Nat := 118140960795 + 3713829 * 2 ^ 59
def prefixEnd_3713829 : Nat := 4983230072969 + 3 ^ 40 * 3713829 * 2
def baseEnd_3713829 : Nat := 1906979345606655360657917

theorem tailTrace_3713829 : CollatzResearch.WordTrace tailWord_3713829 prefixEnd_3713829 1906979345606655360657917 := by
  unfold tailWord_3713829
  simp only [CollatzResearch.WordTrace]
  refine ⟨135454471662439279341376541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90302981108292852894251027 135454471662439279341376541)
  ·
    refine ⟨50795426873414729753016203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135454471662439279341376541 50795426873414729753016203)
    ·
      refine ⟨76193140310122094629524305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50795426873414729753016203 76193140310122094629524305)
      ·
        refine ⟨57144855232591570972143229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76193140310122094629524305 57144855232591570972143229)
        ·
          refine ⟨21429320712221839114553711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57144855232591570972143229 21429320712221839114553711)
          ·
            refine ⟨32143981068332758671830567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21429320712221839114553711 32143981068332758671830567)
            ·
              refine ⟨48215971602499138007745851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32143981068332758671830567 48215971602499138007745851)
              ·
                refine ⟨72323957403748707011618777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48215971602499138007745851 72323957403748707011618777)
                ·
                  refine ⟨54242968052811530258714083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72323957403748707011618777 54242968052811530258714083)
                  ·
                    refine ⟨81364452079217295388071125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54242968052811530258714083 81364452079217295388071125)
                    ·
                      refine ⟨1906979345606655360657917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81364452079217295388071125 1906979345606655360657917)
                      ·
                        rfl

theorem cell23_3713829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3713829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713829 prefixEnd_3713829 := by exact prefixLift 3713829
  have htrace : WordTrace (prefixWord ++ tailWord_3713829) baseStart_3713829 baseEnd_3713829 := by
    simpa [prefixWord, tailWord_3713829, baseEnd_3713829] using wordTrace_append hprefix tailTrace_3713829
  have hstable : (prefixWord ++ tailWord_3713829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713829).length < 2 ^ (prefixWord ++ tailWord_3713829).sum := by decide
  have hdescent : baseEnd_3713829 < baseStart_3713829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713836 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_3713836 : Nat := 118140960795 + 3713836 * 2 ^ 59
def prefixEnd_3713836 : Nat := 4983230072969 + 3 ^ 40 * 3713836 * 2
def baseEnd_3713836 : Nat := 635660979990412277756795

theorem tailTrace_3713836 : CollatzResearch.WordTrace tailWord_3713836 prefixEnd_3713836 635660979990412277756795 := by
  unfold tailWord_3713836
  simp only [CollatzResearch.WordTrace]
  refine ⟨67727363486706959768440681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90303151315609279691254241 67727363486706959768440681)
  ·
    refine ⟨50795522615030219826330511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67727363486706959768440681 50795522615030219826330511)
    ·
      refine ⟨76193283922545329739495767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50795522615030219826330511 76193283922545329739495767)
      ·
        refine ⟨114289925883817994609243651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76193283922545329739495767 114289925883817994609243651)
        ·
          refine ⟨171434888825726991913865477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114289925883817994609243651 171434888825726991913865477)
          ·
            refine ⟨32144041654823810983849777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171434888825726991913865477 32144041654823810983849777)
            ·
              refine ⟨24108031241117858237887333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32144041654823810983849777 24108031241117858237887333)
              ·
                refine ⟨4520255857709598419603875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24108031241117858237887333 4520255857709598419603875)
                ·
                  refine ⟨6780383786564397629405813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520255857709598419603875 6780383786564397629405813)
                  ·
                    refine ⟨635660979990412277756795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6780383786564397629405813 635660979990412277756795)
                    ·
                      rfl

theorem cell23_3713836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_3713836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713836 prefixEnd_3713836 := by exact prefixLift 3713836
  have htrace : WordTrace (prefixWord ++ tailWord_3713836) baseStart_3713836 baseEnd_3713836 := by
    simpa [prefixWord, tailWord_3713836, baseEnd_3713836] using wordTrace_append hprefix tailTrace_3713836
  have hstable : (prefixWord ++ tailWord_3713836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713836).length < 2 ^ (prefixWord ++ tailWord_3713836).sum := by decide
  have hdescent : baseEnd_3713836 < baseStart_3713836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713843 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 1, 5, 2]
def baseStart_3713843 : Nat := 118140960795 + 3713843 * 2 ^ 59
def prefixEnd_3713843 : Nat := 4983230072969 + 3 ^ 40 * 3713843 * 2
def baseEnd_3713843 : Nat := 1906986534335818305882853

theorem tailTrace_3713843 : CollatzResearch.WordTrace tailWord_3713843 prefixEnd_3713843 1906986534335818305882853 := by
  unfold tailWord_3713843
  simp only [CollatzResearch.WordTrace]
  refine ⟨135454982284388559732386183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90303321522925706488257455 135454982284388559732386183)
  ·
    refine ⟨203182473426582839598579275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135454982284388559732386183 203182473426582839598579275)
    ·
      refine ⟨304773710139874259397868913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203182473426582839598579275 304773710139874259397868913)
      ·
        refine ⟨228580282604905694548401685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304773710139874259397868913 228580282604905694548401685)
        ·
          refine ⟨10714700747104954431956329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228580282604905694548401685 10714700747104954431956329)
          ·
            refine ⟨8036025560328715823967247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10714700747104954431956329 8036025560328715823967247)
            ·
              refine ⟨12054038340493073735950871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036025560328715823967247 12054038340493073735950871)
              ·
                refine ⟨18081057510739610603926307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12054038340493073735950871 18081057510739610603926307)
                ·
                  refine ⟨27121586266109415905889461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18081057510739610603926307 27121586266109415905889461)
                  ·
                    refine ⟨2542648712447757741177137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27121586266109415905889461 2542648712447757741177137)
                    ·
                      refine ⟨1906986534335818305882853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542648712447757741177137 1906986534335818305882853)
                      ·
                        rfl

theorem cell23_3713843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5, 2].length) (baseStart_3713843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713843 prefixEnd_3713843 := by exact prefixLift 3713843
  have htrace : WordTrace (prefixWord ++ tailWord_3713843) baseStart_3713843 baseEnd_3713843 := by
    simpa [prefixWord, tailWord_3713843, baseEnd_3713843] using wordTrace_append hprefix tailTrace_3713843
  have hstable : (prefixWord ++ tailWord_3713843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713843).length < 2 ^ (prefixWord ++ tailWord_3713843).sum := by decide
  have hdescent : baseEnd_3713843 < baseStart_3713843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713856 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 8, 2]
def baseStart_3713856 : Nat := 118140960795 + 3713856 * 2 ^ 59
def prefixEnd_3713856 : Nat := 4983230072969 + 3 ^ 40 * 3713856 * 2
def baseEnd_3713856 : Nat := 1906993209584326755020293

theorem tailTrace_3713856 : CollatzResearch.WordTrace tailWord_3713856 prefixEnd_3713856 1906993209584326755020293 := by
  unfold tailWord_3713856
  simp only [CollatzResearch.WordTrace]
  refine ⟨67727728216670731476304711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90303637622227641968406281 67727728216670731476304711)
  ·
    refine ⟨101591592325006097214457067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67727728216670731476304711 101591592325006097214457067)
    ·
      refine ⟨152387388487509145821685601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101591592325006097214457067 152387388487509145821685601)
      ·
        refine ⟨114290541365631859366264201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152387388487509145821685601 114290541365631859366264201)
        ·
          refine ⟨85717906024223894524698151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114290541365631859366264201 85717906024223894524698151)
          ·
            refine ⟨128576859036335841787047227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85717906024223894524698151 128576859036335841787047227)
            ·
              refine ⟨192865288554503762680570841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128576859036335841787047227 192865288554503762680570841)
              ·
                refine ⟨144648966415877822010428131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192865288554503762680570841 144648966415877822010428131)
                ·
                  refine ⟨216973449623816733015642197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144648966415877822010428131 216973449623816733015642197)
                  ·
                    refine ⟨2542657612779102340027057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 216973449623816733015642197 2542657612779102340027057)
                    ·
                      refine ⟨1906993209584326755020293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542657612779102340027057 1906993209584326755020293)
                      ·
                        rfl

theorem cell23_3713856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 8, 2].length) (baseStart_3713856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713856 prefixEnd_3713856 := by exact prefixLift 3713856
  have htrace : WordTrace (prefixWord ++ tailWord_3713856) baseStart_3713856 baseEnd_3713856 := by
    simpa [prefixWord, tailWord_3713856, baseEnd_3713856] using wordTrace_append hprefix tailTrace_3713856
  have hstable : (prefixWord ++ tailWord_3713856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713856).length < 2 ^ (prefixWord ++ tailWord_3713856).sum := by decide
  have hdescent : baseEnd_3713856 < baseStart_3713856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713857 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 6]
def baseStart_3713857 : Nat := 118140960795 + 3713857 * 2 ^ 59
def prefixEnd_3713857 : Nat := 4983230072969 + 3 ^ 40 * 3713857 * 2
def baseEnd_3713857 : Nat := 211888191451664583456421

theorem tailTrace_3713857 : CollatzResearch.WordTrace tailWord_3713857 prefixEnd_3713857 211888191451664583456421 := by
  unfold tailWord_3713857
  simp only [CollatzResearch.WordTrace]
  refine ⟨135455492906337840123395825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90303661937558560082263883 135455492906337840123395825)
  ·
    refine ⟨101591619679753380092546869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135455492906337840123395825 101591619679753380092546869)
    ·
      refine ⟨9524214344976879383676269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101591619679753380092546869 9524214344976879383676269)
      ·
        refine ⟨3571580379366329768878601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9524214344976879383676269 3571580379366329768878601)
        ·
          refine ⟨2678685284524747326658951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571580379366329768878601 2678685284524747326658951)
          ·
            refine ⟨4018027926787120989988427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678685284524747326658951 4018027926787120989988427)
            ·
              refine ⟨6027041890180681484982641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018027926787120989988427 6027041890180681484982641)
              ·
                refine ⟨4520281417635511113736981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6027041890180681484982641 4520281417635511113736981)
                ·
                  refine ⟨211888191451664583456421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4520281417635511113736981 211888191451664583456421)
                  ·
                    rfl

theorem cell23_3713857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 6].length) (baseStart_3713857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713857 prefixEnd_3713857 := by exact prefixLift 3713857
  have htrace : WordTrace (prefixWord ++ tailWord_3713857) baseStart_3713857 baseEnd_3713857 := by
    simpa [prefixWord, tailWord_3713857, baseEnd_3713857] using wordTrace_append hprefix tailTrace_3713857
  have hstable : (prefixWord ++ tailWord_3713857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713857).length < 2 ^ (prefixWord ++ tailWord_3713857).sum := by decide
  have hdescent : baseEnd_3713857 < baseStart_3713857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713893 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3713893 : Nat := 118140960795 + 3713893 * 2 ^ 59
def prefixEnd_3713893 : Nat := 4983230072969 + 3 ^ 40 * 3713893 * 2
def baseEnd_3713893 : Nat := 1907012208368543110257623

theorem tailTrace_3713893 : CollatzResearch.WordTrace tailWord_3713893 prefixEnd_3713893 1907012208368543110257623 := by
  unfold tailWord_3713893
  simp only [CollatzResearch.WordTrace]
  refine ⟨135456805934207418271706333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90304537289471612181137555 135456805934207418271706333)
  ·
    refine ⟨50796302225327781851889875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135456805934207418271706333 50796302225327781851889875)
    ·
      refine ⟨76194453337991672777834813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50796302225327781851889875 76194453337991672777834813)
      ·
        refine ⟨28572920001746877291688055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76194453337991672777834813 28572920001746877291688055)
        ·
          refine ⟨42859380002620315937532083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28572920001746877291688055 42859380002620315937532083)
          ·
            refine ⟨64289070003930473906298125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42859380002620315937532083 64289070003930473906298125)
            ·
              refine ⟨24108401251473927714861797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64289070003930473906298125 24108401251473927714861797)
              ·
                refine ⟨4520325234651361446536587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24108401251473927714861797 4520325234651361446536587)
                ·
                  refine ⟨6780487851977042169804881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520325234651361446536587 6780487851977042169804881)
                  ·
                    refine ⟨5085365888982781627353661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6780487851977042169804881 5085365888982781627353661)
                    ·
                      refine ⟨1907012208368543110257623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5085365888982781627353661 1907012208368543110257623)
                      ·
                        rfl

theorem cell23_3713893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3713893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713893 prefixEnd_3713893 := by exact prefixLift 3713893
  have htrace : WordTrace (prefixWord ++ tailWord_3713893) baseStart_3713893 baseEnd_3713893 := by
    simpa [prefixWord, tailWord_3713893, baseEnd_3713893] using wordTrace_append hprefix tailTrace_3713893
  have hstable : (prefixWord ++ tailWord_3713893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713893).length < 2 ^ (prefixWord ++ tailWord_3713893).sum := by decide
  have hdescent : baseEnd_3713893 < baseStart_3713893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713896 : List Nat := [2, 1, 4, 2, 1, 3, 1, 9]
def baseStart_3713896 : Nat := 118140960795 + 3713896 * 2 ^ 59
def prefixEnd_3713896 : Nat := 4983230072969 + 3 ^ 40 * 3713896 * 2
def baseEnd_3713896 : Nat := 70630138844833577722967

theorem tailTrace_3713896 : CollatzResearch.WordTrace tailWord_3713896 prefixEnd_3713896 70630138844833577722967 := by
  unfold tailWord_3713896
  simp only [CollatzResearch.WordTrace]
  refine ⟨67728457676598274892032771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90304610235464366522710361 67728457676598274892032771)
  ·
    refine ⟨101592686514897412338049157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67728457676598274892032771 101592686514897412338049157)
    ·
      refine ⟨19048628721543264813384217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101592686514897412338049157 19048628721543264813384217)
      ·
        refine ⟨14286471541157448610038163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19048628721543264813384217 14286471541157448610038163)
        ·
          refine ⟨21429707311736172915057245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14286471541157448610038163 21429707311736172915057245)
          ·
            refine ⟨8036140241901064843146467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21429707311736172915057245 8036140241901064843146467)
            ·
              refine ⟨12054210362851597264719701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036140241901064843146467 12054210362851597264719701)
              ·
                refine ⟨70630138844833577722967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12054210362851597264719701 70630138844833577722967)
                ·
                  rfl

theorem cell23_3713896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 9].length) (baseStart_3713896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713896 prefixEnd_3713896 := by exact prefixLift 3713896
  have htrace : WordTrace (prefixWord ++ tailWord_3713896) baseStart_3713896 baseEnd_3713896 := by
    simpa [prefixWord, tailWord_3713896, baseEnd_3713896] using wordTrace_append hprefix tailTrace_3713896
  have hstable : (prefixWord ++ tailWord_3713896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713896).length < 2 ^ (prefixWord ++ tailWord_3713896).sum := by decide
  have hdescent : baseEnd_3713896 < baseStart_3713896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713907 : List Nat := [1, 1, 1, 2, 2, 1, 7, 3, 1, 2, 2]
def baseStart_3713907 : Nat := 118140960795 + 3713907 * 2 ^ 59
def prefixEnd_3713907 : Nat := 4983230072969 + 3 ^ 40 * 3713907 * 2
def baseEnd_3713907 : Nat := 1907019397097706055482559

theorem tailTrace_3713907 : CollatzResearch.WordTrace tailWord_3713907 prefixEnd_3713907 1907019397097706055482559 := by
  unfold tailWord_3713907
  simp only [CollatzResearch.WordTrace]
  refine ⟨135457316556156698662715975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90304877704104465775143983 135457316556156698662715975)
  ·
    refine ⟨203185974834235047994073963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135457316556156698662715975 203185974834235047994073963)
    ·
      refine ⟨304778962251352571991110945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203185974834235047994073963 304778962251352571991110945)
      ·
        refine ⟨228584221688514428993333209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304778962251352571991110945 228584221688514428993333209)
        ·
          refine ⟨171438166266385821744999907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228584221688514428993333209 171438166266385821744999907)
          ·
            refine ⟨257157249399578732617499861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171438166266385821744999907 257157249399578732617499861)
            ·
              refine ⟨6027123032802626545722653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 257157249399578732617499861 6027123032802626545722653)
              ·
                refine ⟨2260171137300984954645995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6027123032802626545722653 2260171137300984954645995)
                ·
                  refine ⟨3390256705951477431968993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260171137300984954645995 3390256705951477431968993)
                  ·
                    refine ⟨2542692529463608073976745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3390256705951477431968993 2542692529463608073976745)
                    ·
                      refine ⟨1907019397097706055482559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542692529463608073976745 1907019397097706055482559)
                      ·
                        rfl

theorem cell23_3713907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 1, 2, 2].length) (baseStart_3713907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713907 prefixEnd_3713907 := by exact prefixLift 3713907
  have htrace : WordTrace (prefixWord ++ tailWord_3713907) baseStart_3713907 baseEnd_3713907 := by
    simpa [prefixWord, tailWord_3713907, baseEnd_3713907] using wordTrace_append hprefix tailTrace_3713907
  have hstable : (prefixWord ++ tailWord_3713907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713907).length < 2 ^ (prefixWord ++ tailWord_3713907).sum := by decide
  have hdescent : baseEnd_3713907 < baseStart_3713907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713910 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3713910 : Nat := 118140960795 + 3713910 * 2 ^ 59
def prefixEnd_3713910 : Nat := 4983230072969 + 3 ^ 40 * 3713910 * 2
def baseEnd_3713910 : Nat := 1907020937539669543745045

theorem tailTrace_3713910 : CollatzResearch.WordTrace tailWord_3713910 prefixEnd_3713910 1907020937539669543745045 := by
  unfold tailWord_3713910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466089123446614385942199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90304950650097220116716789 8466089123446614385942199)
  ·
    refine ⟨12699133685169921578913299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8466089123446614385942199 12699133685169921578913299)
    ·
      refine ⟨19048700527754882368369949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699133685169921578913299 19048700527754882368369949)
      ·
        refine ⟨7143262697908080888138731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19048700527754882368369949 7143262697908080888138731)
        ·
          refine ⟨10714894046862121332208097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143262697908080888138731 10714894046862121332208097)
          ·
            refine ⟨8036170535146590999156073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10714894046862121332208097 8036170535146590999156073)
            ·
              refine ⟨6027127901359943249367055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8036170535146590999156073 6027127901359943249367055)
              ·
                refine ⟨9040691852039914874050583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6027127901359943249367055 9040691852039914874050583)
                ·
                  refine ⟨13561037778059872311075875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040691852039914874050583 13561037778059872311075875)
                  ·
                    refine ⟨20341556667089808466613813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13561037778059872311075875 20341556667089808466613813)
                    ·
                      refine ⟨1907020937539669543745045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20341556667089808466613813 1907020937539669543745045)
                      ·
                        rfl

theorem cell23_3713910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3713910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713910 prefixEnd_3713910 := by exact prefixLift 3713910
  have htrace : WordTrace (prefixWord ++ tailWord_3713910) baseStart_3713910 baseEnd_3713910 := by
    simpa [prefixWord, tailWord_3713910, baseEnd_3713910] using wordTrace_append hprefix tailTrace_3713910
  have hstable : (prefixWord ++ tailWord_3713910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713910).length < 2 ^ (prefixWord ++ tailWord_3713910).sum := by decide
  have hdescent : baseEnd_3713910 < baseStart_3713910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713923 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 3]
def baseStart_3713923 : Nat := 118140960795 + 3713923 * 2 ^ 59
def prefixEnd_3713923 : Nat := 4983230072969 + 3 ^ 40 * 3713923 * 2
def baseEnd_3713923 : Nat := 1907027612788177992882485

theorem tailTrace_3713923 : CollatzResearch.WordTrace tailWord_3713923 prefixEnd_3713923 1907027612788177992882485 := by
  unfold tailWord_3713923
  simp only [CollatzResearch.WordTrace]
  refine ⟨135457900124098733395298423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90305266749399155596865615 135457900124098733395298423)
  ·
    refine ⟨203186850186148100092947635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135457900124098733395298423 203186850186148100092947635)
    ·
      refine ⟨304780275279222150139421453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203186850186148100092947635 304780275279222150139421453)
      ·
        refine ⟨114292603229708306302283045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304780275279222150139421453 114292603229708306302283045)
        ·
          refine ⟨21429863105570307431678071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114292603229708306302283045 21429863105570307431678071)
          ·
            refine ⟨32144794658355461147517107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21429863105570307431678071 32144794658355461147517107)
            ·
              refine ⟨48217191987533191721275661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32144794658355461147517107 48217191987533191721275661)
              ·
                refine ⟨18081446995324946895478373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48217191987533191721275661 18081446995324946895478373)
                ·
                  refine ⟨3390271311623427542902195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18081446995324946895478373 3390271311623427542902195)
                  ·
                    refine ⟨5085406967435141314353293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3390271311623427542902195 5085406967435141314353293)
                    ·
                      refine ⟨1907027612788177992882485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5085406967435141314353293 1907027612788177992882485)
                      ·
                        rfl

theorem cell23_3713923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_3713923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713923 prefixEnd_3713923 := by exact prefixLift 3713923
  have htrace : WordTrace (prefixWord ++ tailWord_3713923) baseStart_3713923 baseEnd_3713923 := by
    simpa [prefixWord, tailWord_3713923, baseEnd_3713923] using wordTrace_append hprefix tailTrace_3713923
  have hstable : (prefixWord ++ tailWord_3713923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713923).length < 2 ^ (prefixWord ++ tailWord_3713923).sum := by decide
  have hdescent : baseEnd_3713923 < baseStart_3713923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3713963 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 1, 4, 2]
def baseStart_3713963 : Nat := 118140960795 + 3713963 * 2 ^ 59
def prefixEnd_3713963 : Nat := 4983230072969 + 3 ^ 40 * 3713963 * 2
def baseEnd_3713963 : Nat := 1907048152014357836382301

theorem tailTrace_3713963 : CollatzResearch.WordTrace tailWord_3713963 prefixEnd_3713963 1907048152014357836382301 := by
  unfold tailWord_3713963
  simp only [CollatzResearch.WordTrace]
  refine ⟨135459359043953820226754543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90306239362635880151169695 135459359043953820226754543)
  ·
    refine ⟨203189038565930730340131815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135459359043953820226754543 203189038565930730340131815)
    ·
      refine ⟨304783557848896095510197723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203189038565930730340131815 304783557848896095510197723)
      ·
        refine ⟨457175336773344143265296585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304783557848896095510197723 457175336773344143265296585)
        ·
          refine ⟨342881502580008107448972439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457175336773344143265296585 342881502580008107448972439)
          ·
            refine ⟨514322253870012161173458659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342881502580008107448972439 514322253870012161173458659)
            ·
              refine ⟨771483380805018241760187989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514322253870012161173458659 771483380805018241760187989)
              ·
                refine ⟨9040820868808807520627203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 771483380805018241760187989 9040820868808807520627203)
                ·
                  refine ⟨13561231303213211280940805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040820868808807520627203 13561231303213211280940805)
                  ·
                    refine ⟨2542730869352477115176401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13561231303213211280940805 2542730869352477115176401)
                    ·
                      refine ⟨1907048152014357836382301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542730869352477115176401 1907048152014357836382301)
                      ·
                        rfl

theorem cell23_3713963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4, 2].length) (baseStart_3713963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3713963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3713963 prefixEnd_3713963 := by exact prefixLift 3713963
  have htrace : WordTrace (prefixWord ++ tailWord_3713963) baseStart_3713963 baseEnd_3713963 := by
    simpa [prefixWord, tailWord_3713963, baseEnd_3713963] using wordTrace_append hprefix tailTrace_3713963
  have hstable : (prefixWord ++ tailWord_3713963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3713963).length < 2 ^ (prefixWord ++ tailWord_3713963).sum := by decide
  have hdescent : baseEnd_3713963 < baseStart_3713963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3713963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714037 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 7]
def baseStart_3714037 : Nat := 118140960795 + 3714037 * 2 ^ 59
def prefixEnd_3714037 : Nat := 4983230072969 + 3 ^ 40 * 3714037 * 2
def baseEnd_3714037 : Nat := 211898461064754505206329

theorem tailTrace_3714037 : CollatzResearch.WordTrace tailWord_3714037 prefixEnd_3714037 211898461064754505206329 := by
  unfold tailWord_3714037
  simp only [CollatzResearch.WordTrace]
  refine ⟨135462058045685730864948365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90308038697123820576632243 135462058045685730864948365)
  ·
    refine ⟨50798271767132149074355637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135462058045685730864948365 50798271767132149074355637)
    ·
      refine ⟨4762337978168638975720841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50798271767132149074355637 4762337978168638975720841)
      ·
        refine ⟨3571753483626479231790631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4762337978168638975720841 3571753483626479231790631)
        ·
          refine ⟨5357630225439718847685947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571753483626479231790631 5357630225439718847685947)
          ·
            refine ⟨8036445338159578271528921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357630225439718847685947 8036445338159578271528921)
            ·
              refine ⟨6027334003619683703646691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8036445338159578271528921 6027334003619683703646691)
              ·
                refine ⟨9041001005429525555470037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6027334003619683703646691 9041001005429525555470037)
                ·
                  refine ⟨211898461064754505206329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9041001005429525555470037 211898461064754505206329)
                  ·
                    rfl

theorem cell23_3714037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_3714037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714037 prefixEnd_3714037 := by exact prefixLift 3714037
  have htrace : WordTrace (prefixWord ++ tailWord_3714037) baseStart_3714037 baseEnd_3714037 := by
    simpa [prefixWord, tailWord_3714037, baseEnd_3714037] using wordTrace_append hprefix tailTrace_3714037
  have hstable : (prefixWord ++ tailWord_3714037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714037).length < 2 ^ (prefixWord ++ tailWord_3714037).sum := by decide
  have hdescent : baseEnd_3714037 < baseStart_3714037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714073 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 3]
def baseStart_3714073 : Nat := 118140960795 + 3714073 * 2 ^ 59
def prefixEnd_3714073 : Nat := 4983230072969 + 3 ^ 40 * 3714073 * 2
def baseEnd_3714073 : Nat := 1907104634886352406006795

theorem tailTrace_3714073 : CollatzResearch.WordTrace tailWord_3714073 prefixEnd_3714073 1907104634886352406006795 := by
  unfold tailWord_3714073
  simp only [CollatzResearch.WordTrace]
  refine ⟨135463371073555309013258873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90308914049036872675505915 135463371073555309013258873)
  ·
    refine ⟨101597528305166481759944155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135463371073555309013258873 101597528305166481759944155)
    ·
      refine ⟨152396292457749722639916233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101597528305166481759944155 152396292457749722639916233)
      ·
        refine ⟨114297219343312291979937175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152396292457749722639916233 114297219343312291979937175)
        ·
          refine ⟨171445829014968437969905763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114297219343312291979937175 171445829014968437969905763)
          ·
            refine ⟨257168743522452656954858645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171445829014968437969905763 257168743522452656954858645)
            ·
              refine ⟨12054784852614968294758999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 257168743522452656954858645 12054784852614968294758999)
              ·
                refine ⟨18082177278922452442138499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12054784852614968294758999 18082177278922452442138499)
                ·
                  refine ⟨27123265918383678663207749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18082177278922452442138499 27123265918383678663207749)
                  ·
                    refine ⟨5085612359696939749351453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27123265918383678663207749 5085612359696939749351453)
                    ·
                      refine ⟨1907104634886352406006795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5085612359696939749351453 1907104634886352406006795)
                      ·
                        rfl

theorem cell23_3714073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_3714073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714073 prefixEnd_3714073 := by exact prefixLift 3714073
  have htrace : WordTrace (prefixWord ++ tailWord_3714073) baseStart_3714073 baseEnd_3714073 := by
    simpa [prefixWord, tailWord_3714073, baseEnd_3714073] using wordTrace_append hprefix tailTrace_3714073
  have hstable : (prefixWord ++ tailWord_3714073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714073).length < 2 ^ (prefixWord ++ tailWord_3714073).sum := by decide
  have hdescent : baseEnd_3714073 < baseStart_3714073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714087 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3714087 : Nat := 118140960795 + 3714087 * 2 ^ 59
def prefixEnd_3714087 : Nat := 4983230072969 + 3 ^ 40 * 3714087 * 2
def baseEnd_3714087 : Nat := 1907111823615515351231731

theorem tailTrace_3714087 : CollatzResearch.WordTrace tailWord_3714087 prefixEnd_3714087 1907111823615515351231731 := by
  unfold tailWord_3714087
  simp only [CollatzResearch.WordTrace]
  refine ⟨135463881695504589404268515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90309254463669726269512343 135463881695504589404268515)
  ·
    refine ⟨203195822543256884106402773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135463881695504589404268515 203195822543256884106402773)
    ·
      refine ⟨4762402090857583221243815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 203195822543256884106402773 4762402090857583221243815)
      ·
        refine ⟨7143603136286374831865723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4762402090857583221243815 7143603136286374831865723)
        ·
          refine ⟨10715404704429562247798585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143603136286374831865723 10715404704429562247798585)
          ·
            refine ⟨8036553528322171685848939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10715404704429562247798585 8036553528322171685848939)
            ·
              refine ⟨12054830292483257528773409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036553528322171685848939 12054830292483257528773409)
              ·
                refine ⟨9041122719362443146580057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12054830292483257528773409 9041122719362443146580057)
                ·
                  refine ⟨6780842039521832359935043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9041122719362443146580057 6780842039521832359935043)
                  ·
                    refine ⟨10171263059282748539902565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6780842039521832359935043 10171263059282748539902565)
                    ·
                      refine ⟨1907111823615515351231731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10171263059282748539902565 1907111823615515351231731)
                      ·
                        rfl

theorem cell23_3714087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3714087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714087 prefixEnd_3714087 := by exact prefixLift 3714087
  have htrace : WordTrace (prefixWord ++ tailWord_3714087) baseStart_3714087 baseEnd_3714087 := by
    simpa [prefixWord, tailWord_3714087, baseEnd_3714087] using wordTrace_append hprefix tailTrace_3714087
  have hstable : (prefixWord ++ tailWord_3714087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714087).length < 2 ^ (prefixWord ++ tailWord_3714087).sum := by decide
  have hdescent : baseEnd_3714087 < baseStart_3714087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714120 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_3714120 : Nat := 118140960795 + 3714120 * 2 ^ 59
def prefixEnd_3714120 : Nat := 4983230072969 + 3 ^ 40 * 3714120 * 2
def baseEnd_3714120 : Nat := 1907128768477113722119079

theorem tailTrace_3714120 : CollatzResearch.WordTrace tailWord_3714120 prefixEnd_3714120 1907128768477113722119079 := by
  unfold tailWord_3714120
  simp only [CollatzResearch.WordTrace]
  refine ⟨67732542652192518020109907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90310056869590024026813209 67732542652192518020109907)
  ·
    refine ⟨101598813978288777030164861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67732542652192518020109907 101598813978288777030164861)
    ·
      refine ⟨38099555241858291386311823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101598813978288777030164861 38099555241858291386311823)
      ·
        refine ⟨57149332862787437079467735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38099555241858291386311823 57149332862787437079467735)
        ·
          refine ⟨85723999294181155619201603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57149332862787437079467735 85723999294181155619201603)
          ·
            refine ⟨128585998941271733428802405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85723999294181155619201603 128585998941271733428802405)
            ·
              refine ⟨24109874801488450017900451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128585998941271733428802405 24109874801488450017900451)
              ·
                refine ⟨36164812202232675026850677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24109874801488450017900451 36164812202232675026850677)
                ·
                  refine ⟨3390451143959313283767251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36164812202232675026850677 3390451143959313283767251)
                  ·
                    refine ⟨5085676715938969925650877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3390451143959313283767251 5085676715938969925650877)
                    ·
                      refine ⟨1907128768477113722119079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5085676715938969925650877 1907128768477113722119079)
                      ·
                        rfl

theorem cell23_3714120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_3714120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714120 prefixEnd_3714120 := by exact prefixLift 3714120
  have htrace : WordTrace (prefixWord ++ tailWord_3714120) baseStart_3714120 baseEnd_3714120 := by
    simpa [prefixWord, tailWord_3714120, baseEnd_3714120] using wordTrace_append hprefix tailTrace_3714120
  have hstable : (prefixWord ++ tailWord_3714120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714120).length < 2 ^ (prefixWord ++ tailWord_3714120).sum := by decide
  have hdescent : baseEnd_3714120 < baseStart_3714120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714181 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 2, 3, 2]
def baseStart_3714181 : Nat := 118140960795 + 3714181 * 2 ^ 59
def prefixEnd_3714181 : Nat := 4983230072969 + 3 ^ 40 * 3714181 * 2
def baseEnd_3714181 : Nat := 1907160090797037983456299

theorem tailTrace_3714181 : CollatzResearch.WordTrace tailWord_3714181 prefixEnd_3714181 1907160090797037983456299 := by
  unfold tailWord_3714181
  simp only [CollatzResearch.WordTrace]
  refine ⟨135467310157164043458190397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90311540104776028972126931 135467310157164043458190397)
  ·
    refine ⟨50800241308936516296821399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135467310157164043458190397 50800241308936516296821399)
    ·
      refine ⟨76200361963404774445232099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50800241308936516296821399 76200361963404774445232099)
      ·
        refine ⟨114300542945107161667848149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76200361963404774445232099 114300542945107161667848149)
        ·
          refine ⟨2678918975275949101590191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 114300542945107161667848149 2678918975275949101590191)
          ·
            refine ⟨4018378462913923652385287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678918975275949101590191 4018378462913923652385287)
            ·
              refine ⟨6027567694370885478577931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018378462913923652385287 6027567694370885478577931)
              ·
                refine ⟨9041351541556328217866897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6027567694370885478577931 9041351541556328217866897)
                ·
                  refine ⟨6781013656167246163400173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9041351541556328217866897 6781013656167246163400173)
                  ·
                    refine ⟨2542880121062717311275065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6781013656167246163400173 2542880121062717311275065)
                    ·
                      refine ⟨1907160090797037983456299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542880121062717311275065 1907160090797037983456299)
                      ·
                        rfl

theorem cell23_3714181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_3714181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714181 prefixEnd_3714181 := by exact prefixLift 3714181
  have htrace : WordTrace (prefixWord ++ tailWord_3714181) baseStart_3714181 baseEnd_3714181 := by
    simpa [prefixWord, tailWord_3714181, baseEnd_3714181] using wordTrace_append hprefix tailTrace_3714181
  have hstable : (prefixWord ++ tailWord_3714181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714181).length < 2 ^ (prefixWord ++ tailWord_3714181).sum := by decide
  have hdescent : baseEnd_3714181 < baseStart_3714181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714194 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_3714194 : Nat := 118140960795 + 3714194 * 2 ^ 59
def prefixEnd_3714194 : Nat := 4983230072969 + 3 ^ 40 * 3714194 * 2
def baseEnd_3714194 : Nat := 1907166766045546432593739

theorem tailTrace_3714194 : CollatzResearch.WordTrace tailWord_3714194 prefixEnd_3714194 1907166766045546432593739 := by
  unfold tailWord_3714194
  simp only [CollatzResearch.WordTrace]
  refine ⟨33866946076529236669603409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90311856204077964452275757 33866946076529236669603409)
  ·
    refine ⟨25400209557396927502202557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33866946076529236669603409 25400209557396927502202557)
    ·
      refine ⟨9525078584023847813325959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25400209557396927502202557 9525078584023847813325959)
      ·
        refine ⟨14287617876035771719988939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9525078584023847813325959 14287617876035771719988939)
        ·
          refine ⟨21431426814053657579983409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14287617876035771719988939 21431426814053657579983409)
          ·
            refine ⟨16073570110540243184987557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21431426814053657579983409 16073570110540243184987557)
            ·
              refine ⟨3013794395726295597185167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16073570110540243184987557 3013794395726295597185167)
              ·
                refine ⟨4520691593589443395777751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013794395726295597185167 4520691593589443395777751)
                ·
                  refine ⟨6781037390384165093666627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520691593589443395777751 6781037390384165093666627)
                  ·
                    refine ⟨10171556085576247640499941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781037390384165093666627 10171556085576247640499941)
                    ·
                      refine ⟨1907166766045546432593739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10171556085576247640499941 1907166766045546432593739)
                      ·
                        rfl

theorem cell23_3714194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_3714194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714194 prefixEnd_3714194 := by exact prefixLift 3714194
  have htrace : WordTrace (prefixWord ++ tailWord_3714194) baseStart_3714194 baseEnd_3714194 := by
    simpa [prefixWord, tailWord_3714194, baseEnd_3714194] using wordTrace_append hprefix tailTrace_3714194
  have hstable : (prefixWord ++ tailWord_3714194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714194).length < 2 ^ (prefixWord ++ tailWord_3714194).sum := by decide
  have hdescent : baseEnd_3714194 < baseStart_3714194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714204 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_3714204 : Nat := 118140960795 + 3714204 * 2 ^ 59
def prefixEnd_3714204 : Nat := 4983230072969 + 3 ^ 40 * 3714204 * 2
def baseEnd_3714204 : Nat := 635723966950697131156231

theorem tailTrace_3714204 : CollatzResearch.WordTrace tailWord_3714204 prefixEnd_3714204 635723966950697131156231 := by
  unfold tailWord_3714204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67734074518040359193138833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90312099357387145590851777 67734074518040359193138833)
  ·
    refine ⟨50800555888530269394854125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67734074518040359193138833 50800555888530269394854125)
    ·
      refine ⟨19050208458198851023070297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50800555888530269394854125 19050208458198851023070297)
      ·
        refine ⟨14287656343649138267302723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19050208458198851023070297 14287656343649138267302723)
        ·
          refine ⟨21431484515473707400954085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14287656343649138267302723 21431484515473707400954085)
          ·
            refine ⟨4018403346651320137678891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21431484515473707400954085 4018403346651320137678891)
            ·
              refine ⟨6027605019976980206518337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018403346651320137678891 6027605019976980206518337)
              ·
                refine ⟨4520703764982735154888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6027605019976980206518337 4520703764982735154888753)
                ·
                  refine ⟨3390527823737051366166565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4520703764982735154888753 3390527823737051366166565)
                  ·
                    refine ⟨635723966950697131156231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3390527823737051366166565 635723966950697131156231)
                    ·
                      rfl

theorem cell23_3714204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_3714204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714204 prefixEnd_3714204 := by exact prefixLift 3714204
  have htrace : WordTrace (prefixWord ++ tailWord_3714204) baseStart_3714204 baseEnd_3714204 := by
    simpa [prefixWord, tailWord_3714204, baseEnd_3714204] using wordTrace_append hprefix tailTrace_3714204
  have hstable : (prefixWord ++ tailWord_3714204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714204).length < 2 ^ (prefixWord ++ tailWord_3714204).sum := by decide
  have hdescent : baseEnd_3714204 < baseStart_3714204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714220 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 7, 2]
def baseStart_3714220 : Nat := 118140960795 + 3714220 * 2 ^ 59
def prefixEnd_3714220 : Nat := 4983230072969 + 3 ^ 40 * 3714220 * 2
def baseEnd_3714220 : Nat := 1907180116542563330868619

theorem tailTrace_3714220 : CollatzResearch.WordTrace tailWord_3714220 prefixEnd_3714220 1907180116542563330868619 := by
  unfold tailWord_3714220
  simp only [CollatzResearch.WordTrace]
  refine ⟨67734366302011376559430057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90312488402681835412573409 67734366302011376559430057)
  ·
    refine ⟨50800774726508532419572543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67734366302011376559430057 50800774726508532419572543)
    ·
      refine ⟨76201162089762798629358815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50800774726508532419572543 76201162089762798629358815)
      ·
        refine ⟨114301743134644197944038223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76201162089762798629358815 114301743134644197944038223)
        ·
          refine ⟨171452614701966296916057335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114301743134644197944038223 171452614701966296916057335)
          ·
            refine ⟨257178922052949445374086003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171452614701966296916057335 257178922052949445374086003)
            ·
              refine ⟨385768383079424168061129005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257178922052949445374086003 385768383079424168061129005)
              ·
                refine ⟨144663143654784063022923377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385768383079424168061129005 144663143654784063022923377)
                ·
                  refine ⟨108497357741088047267192533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144663143654784063022923377 108497357741088047267192533)
                  ·
                    refine ⟨2542906822056751107824825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 108497357741088047267192533 2542906822056751107824825)
                    ·
                      refine ⟨1907180116542563330868619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542906822056751107824825 1907180116542563330868619)
                      ·
                        rfl

theorem cell23_3714220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_3714220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714220 prefixEnd_3714220 := by exact prefixLift 3714220
  have htrace : WordTrace (prefixWord ++ tailWord_3714220) baseStart_3714220 baseEnd_3714220 := by
    simpa [prefixWord, tailWord_3714220, baseEnd_3714220] using wordTrace_append hprefix tailTrace_3714220
  have hstable : (prefixWord ++ tailWord_3714220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714220).length < 2 ^ (prefixWord ++ tailWord_3714220).sum := by decide
  have hdescent : baseEnd_3714220 < baseStart_3714220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714221 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_3714221 : Nat := 118140960795 + 3714221 * 2 ^ 59
def prefixEnd_3714221 : Nat := 4983230072969 + 3 ^ 40 * 3714221 * 2
def baseEnd_3714221 : Nat := 635726876674405942318705

theorem tailTrace_3714221 : CollatzResearch.WordTrace tailWord_3714221 prefixEnd_3714221 635726876674405942318705 := by
  unfold tailWord_3714221
  simp only [CollatzResearch.WordTrace]
  refine ⟨135468769077019130289646517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90312512718012753526431011 135468769077019130289646517)
  ·
    refine ⟨12700197100970543464654361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135468769077019130289646517 12700197100970543464654361)
    ·
      refine ⟨9525147825727907598490771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12700197100970543464654361 9525147825727907598490771)
      ·
        refine ⟨14287721738591861397736157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9525147825727907598490771 14287721738591861397736157)
        ·
          refine ⟨5357895651971948024151059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14287721738591861397736157 5357895651971948024151059)
          ·
            refine ⟨8036843477957922036226589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357895651971948024151059 8036843477957922036226589)
            ·
              refine ⟨3013816304234220763584971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8036843477957922036226589 3013816304234220763584971)
              ·
                refine ⟨4520724456351331145377457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013816304234220763584971 4520724456351331145377457)
                ·
                  refine ⟨3390543342263498359033093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4520724456351331145377457 3390543342263498359033093)
                  ·
                    refine ⟨635726876674405942318705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3390543342263498359033093 635726876674405942318705)
                    ·
                      rfl

theorem cell23_3714221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_3714221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714221 prefixEnd_3714221 := by exact prefixLift 3714221
  have htrace : WordTrace (prefixWord ++ tailWord_3714221) baseStart_3714221 baseEnd_3714221 := by
    simpa [prefixWord, tailWord_3714221, baseEnd_3714221] using wordTrace_append hprefix tailTrace_3714221
  have hstable : (prefixWord ++ tailWord_3714221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714221).length < 2 ^ (prefixWord ++ tailWord_3714221).sum := by decide
  have hdescent : baseEnd_3714221 < baseStart_3714221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714227 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 3]
def baseStart_3714227 : Nat := 118140960795 + 3714227 * 2 ^ 59
def prefixEnd_3714227 : Nat := 4983230072969 + 3 ^ 40 * 3714227 * 2
def baseEnd_3714227 : Nat := 1907183710907144803481087

theorem tailTrace_3714227 : CollatzResearch.WordTrace tailWord_3714227 prefixEnd_3714227 1907183710907144803481087 := by
  unfold tailWord_3714227
  simp only [CollatzResearch.WordTrace]
  refine ⟨135468987914997393314364935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90312658609998262209576623 135468987914997393314364935)
  ·
    refine ⟨203203481872496089971547403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135468987914997393314364935 203203481872496089971547403)
    ·
      refine ⟨304805222808744134957321105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203203481872496089971547403 304805222808744134957321105)
      ·
        refine ⟨228603917106558101217990829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304805222808744134957321105 228603917106558101217990829)
        ·
          refine ⟨85726468914959287956746561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228603917106558101217990829 85726468914959287956746561)
          ·
            refine ⟨64294851686219465967559921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85726468914959287956746561 64294851686219465967559921)
            ·
              refine ⟨48221138764664599475669941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64294851686219465967559921 48221138764664599475669941)
              ·
                refine ⟨4520731759187306200844057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48221138764664599475669941 4520731759187306200844057)
                ·
                  refine ⟨3390548819390479650633043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4520731759187306200844057 3390548819390479650633043)
                  ·
                    refine ⟨5085823229085719475949565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3390548819390479650633043 5085823229085719475949565)
                    ·
                      refine ⟨1907183710907144803481087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5085823229085719475949565 1907183710907144803481087)
                      ·
                        rfl

theorem cell23_3714227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 3].length) (baseStart_3714227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714227 prefixEnd_3714227 := by exact prefixLift 3714227
  have htrace : WordTrace (prefixWord ++ tailWord_3714227) baseStart_3714227 baseEnd_3714227 := by
    simpa [prefixWord, tailWord_3714227, baseEnd_3714227] using wordTrace_append hprefix tailTrace_3714227
  have hstable : (prefixWord ++ tailWord_3714227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714227).length < 2 ^ (prefixWord ++ tailWord_3714227).sum := by decide
  have hdescent : baseEnd_3714227 < baseStart_3714227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714237 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 3, 3, 2]
def baseStart_3714237 : Nat := 118140960795 + 3714237 * 2 ^ 59
def prefixEnd_3714237 : Nat := 4983230072969 + 3 ^ 40 * 3714237 * 2
def baseEnd_3714237 : Nat := 1907188845713689764356041

theorem tailTrace_3714237 : CollatzResearch.WordTrace tailWord_3714237 prefixEnd_3714237 1907188845713689764356041 := by
  unfold tailWord_3714237
  simp only [CollatzResearch.WordTrace]
  refine ⟨135469352644961165022228965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90312901763307443348152643 135469352644961165022228965)
  ·
    refine ⟨25400503620930218441667931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135469352644961165022228965 25400503620930218441667931)
    ·
      refine ⟨38100755431395327662501897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25400503620930218441667931 38100755431395327662501897)
      ·
        refine ⟨28575566573546495746876423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38100755431395327662501897 28575566573546495746876423)
        ·
          refine ⟨42863349860319743620314635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28575566573546495746876423 42863349860319743620314635)
          ·
            refine ⟨64295024790479615430471953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42863349860319743620314635 64295024790479615430471953)
            ·
              refine ⟨48221268592859711572853965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64295024790479615430471953 48221268592859711572853965)
              ·
                refine ⟨18082975722322391839820237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48221268592859711572853965 18082975722322391839820237)
                ·
                  refine ⟨6781115895870896939932589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18082975722322391839820237 6781115895870896939932589)
                  ·
                    refine ⟨2542918460951586352474721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6781115895870896939932589 2542918460951586352474721)
                    ·
                      refine ⟨1907188845713689764356041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542918460951586352474721 1907188845713689764356041)
                      ·
                        rfl

theorem cell23_3714237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_3714237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714237 prefixEnd_3714237 := by exact prefixLift 3714237
  have htrace : WordTrace (prefixWord ++ tailWord_3714237) baseStart_3714237 baseEnd_3714237 := by
    simpa [prefixWord, tailWord_3714237, baseEnd_3714237] using wordTrace_append hprefix tailTrace_3714237
  have hstable : (prefixWord ++ tailWord_3714237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714237).length < 2 ^ (prefixWord ++ tailWord_3714237).sum := by decide
  have hdescent : baseEnd_3714237 < baseStart_3714237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714243 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 4, 6]
def baseStart_3714243 : Nat := 118140960795 + 3714243 * 2 ^ 59
def prefixEnd_3714243 : Nat := 4983230072969 + 3 ^ 40 * 3714243 * 2
def baseEnd_3714243 : Nat := 635730642199205580293671

theorem tailTrace_3714243 : CollatzResearch.WordTrace tailWord_3714243 prefixEnd_3714243 635730642199205580293671 := by
  unfold tailWord_3714243
  simp only [CollatzResearch.WordTrace]
  refine ⟨135469571482939428046947383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90313047655292952031298255 135469571482939428046947383)
  ·
    refine ⟨203204357224409142070421075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135469571482939428046947383 203204357224409142070421075)
    ·
      refine ⟨304806535836613713105631613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203204357224409142070421075 304806535836613713105631613)
      ·
        refine ⟨114302450938730142414611855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304806535836613713105631613 114302450938730142414611855)
        ·
          refine ⟨171453676408095213621917783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114302450938730142414611855 171453676408095213621917783)
          ·
            refine ⟨257180514612142820432876675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171453676408095213621917783 257180514612142820432876675)
            ·
              refine ⟨385770771918214230649315013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257180514612142820432876675 385770771918214230649315013)
              ·
                refine ⟨72332019734665168246746565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385770771918214230649315013 72332019734665168246746565)
                ·
                  refine ⟨13562253700249719046264981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72332019734665168246746565 13562253700249719046264981)
                  ·
                    refine ⟨635730642199205580293671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13562253700249719046264981 635730642199205580293671)
                    ·
                      rfl

theorem cell23_3714243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 6].length) (baseStart_3714243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714243 prefixEnd_3714243 := by exact prefixLift 3714243
  have htrace : WordTrace (prefixWord ++ tailWord_3714243) baseStart_3714243 baseEnd_3714243 := by
    simpa [prefixWord, tailWord_3714243, baseEnd_3714243] using wordTrace_append hprefix tailTrace_3714243
  have hstable : (prefixWord ++ tailWord_3714243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714243).length < 2 ^ (prefixWord ++ tailWord_3714243).sum := by decide
  have hdescent : baseEnd_3714243 < baseStart_3714243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714262 : List Nat := [5, 2, 1, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3714262 : Nat := 118140960795 + 3714262 * 2 ^ 59
def prefixEnd_3714262 : Nat := 4983230072969 + 3 ^ 40 * 3714262 * 2
def baseEnd_3714262 : Nat := 1907201682730052166543427

theorem tailTrace_3714262 : CollatzResearch.WordTrace tailWord_3714262 prefixEnd_3714262 1907201682730052166543427 := by
  unfold tailWord_3714262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8466891529366912143243065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90313509646580396194592693 8466891529366912143243065)
  ·
    refine ⟨6350168647025184107432299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8466891529366912143243065 6350168647025184107432299)
    ·
      refine ⟨9525252970537776161148449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6350168647025184107432299 9525252970537776161148449)
      ·
        refine ⟨7143939727903332120861337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9525252970537776161148449 7143939727903332120861337)
        ·
          refine ⟨5357954795927499090646003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7143939727903332120861337 5357954795927499090646003)
          ·
            refine ⟨8036932193891248635969005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357954795927499090646003 8036932193891248635969005)
            ·
              refine ⟨3013849572709218238488377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8036932193891248635969005 3013849572709218238488377)
              ·
                refine ⟨2260387179531913678866283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013849572709218238488377 2260387179531913678866283)
                ·
                  refine ⟨3390580769297870518299425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260387179531913678866283 3390580769297870518299425)
                  ·
                    refine ⟨2542935576973402888724569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3390580769297870518299425 2542935576973402888724569)
                    ·
                      refine ⟨1907201682730052166543427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542935576973402888724569 1907201682730052166543427)
                      ·
                        rfl

theorem cell23_3714262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3714262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714262 prefixEnd_3714262 := by exact prefixLift 3714262
  have htrace : WordTrace (prefixWord ++ tailWord_3714262) baseStart_3714262 baseEnd_3714262 := by
    simpa [prefixWord, tailWord_3714262, baseEnd_3714262] using wordTrace_append hprefix tailTrace_3714262
  have hstable : (prefixWord ++ tailWord_3714262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714262).length < 2 ^ (prefixWord ++ tailWord_3714262).sum := by decide
  have hdescent : baseEnd_3714262 < baseStart_3714262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714267 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 8, 2, 2]
def baseStart_3714267 : Nat := 118140960795 + 3714267 * 2 ^ 59
def prefixEnd_3714267 : Nat := 4983230072969 + 3 ^ 40 * 3714267 * 2
def baseEnd_3714267 : Nat := 1907204250133324646980903

theorem tailTrace_3714267 : CollatzResearch.WordTrace tailWord_3714267 prefixEnd_3714267 1907204250133324646980903 := by
  unfold tailWord_3714267
  simp only [CollatzResearch.WordTrace]
  refine ⟨135470446834852480145821055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90313631223234986763880703 135470446834852480145821055)
  ·
    refine ⟨203205670252278720218731583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135470446834852480145821055 203205670252278720218731583)
    ·
      refine ⟨304808505378418080328097375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203205670252278720218731583 304808505378418080328097375)
      ·
        refine ⟨457212758067627120492146063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304808505378418080328097375 457212758067627120492146063)
        ·
          refine ⟨685819137101440680738219095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457212758067627120492146063 685819137101440680738219095)
          ·
            refine ⟨1028728705652161021107328643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685819137101440680738219095 1028728705652161021107328643)
            ·
              refine ⟨1543093058478241531660992965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028728705652161021107328643 1543093058478241531660992965)
              ·
                refine ⟨289329948464670287186436181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1543093058478241531660992965 289329948464670287186436181)
                ·
                  refine ⟨3390585333570354927966049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 289329948464670287186436181 3390585333570354927966049)
                  ·
                    refine ⟨2542939000177766195974537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3390585333570354927966049 2542939000177766195974537)
                    ·
                      refine ⟨1907204250133324646980903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542939000177766195974537 1907204250133324646980903)
                      ·
                        rfl

theorem cell23_3714267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 2, 2].length) (baseStart_3714267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714267 prefixEnd_3714267 := by exact prefixLift 3714267
  have htrace : WordTrace (prefixWord ++ tailWord_3714267) baseStart_3714267 baseEnd_3714267 := by
    simpa [prefixWord, tailWord_3714267, baseEnd_3714267] using wordTrace_append hprefix tailTrace_3714267
  have hstable : (prefixWord ++ tailWord_3714267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714267).length < 2 ^ (prefixWord ++ tailWord_3714267).sum := by decide
  have hdescent : baseEnd_3714267 < baseStart_3714267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714280 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3714280 : Nat := 118140960795 + 3714280 * 2 ^ 59
def prefixEnd_3714280 : Nat := 4983230072969 + 3 ^ 40 * 3714280 * 2
def baseEnd_3714280 : Nat := 1907210925381833096118343

theorem tailTrace_3714280 : CollatzResearch.WordTrace tailWord_3714280 prefixEnd_3714280 1907210925381833096118343 := by
  unfold tailWord_3714280
  simp only [CollatzResearch.WordTrace]
  refine ⟨67735460491902691683022147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90313947322536922244029529 67735460491902691683022147)
  ·
    refine ⟨101603190737854037524533221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67735460491902691683022147 101603190737854037524533221)
    ·
      refine ⟨19050598263347632035849979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101603190737854037524533221 19050598263347632035849979)
      ·
        refine ⟨28575897395021448053774969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19050598263347632035849979 28575897395021448053774969)
        ·
          refine ⟨21431923046266086040331227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28575897395021448053774969 21431923046266086040331227)
          ·
            refine ⟨32147884569399129060496841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21431923046266086040331227 32147884569399129060496841)
            ·
              refine ⟨24110913427049346795372631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32147884569399129060496841 24110913427049346795372631)
              ·
                refine ⟨36166370140574020193058947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24110913427049346795372631 36166370140574020193058947)
                ·
                  refine ⟨54249555210861030289588421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36166370140574020193058947 54249555210861030289588421)
                  ·
                    refine ⟨10171791602036443179297829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54249555210861030289588421 10171791602036443179297829)
                    ·
                      refine ⟨1907210925381833096118343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10171791602036443179297829 1907210925381833096118343)
                      ·
                        rfl

theorem cell23_3714280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3714280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714280 prefixEnd_3714280 := by exact prefixLift 3714280
  have htrace : WordTrace (prefixWord ++ tailWord_3714280) baseStart_3714280 baseEnd_3714280 := by
    simpa [prefixWord, tailWord_3714280, baseEnd_3714280] using wordTrace_append hprefix tailTrace_3714280
  have hstable : (prefixWord ++ tailWord_3714280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714280).length < 2 ^ (prefixWord ++ tailWord_3714280).sum := by decide
  have hdescent : baseEnd_3714280 < baseStart_3714280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714327 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 7, 2]
def baseStart_3714327 : Nat := 118140960795 + 3714327 * 2 ^ 59
def prefixEnd_3714327 : Nat := 4983230072969 + 3 ^ 40 * 3714327 * 2
def baseEnd_3714327 : Nat := 1907235058972594412230627

theorem tailTrace_3714327 : CollatzResearch.WordTrace tailWord_3714327 prefixEnd_3714327 1907235058972594412230627 := by
  unfold tailWord_3714327
  simp only [CollatzResearch.WordTrace]
  refine ⟨135472635214635110393005235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90315090143090073595336823 135472635214635110393005235)
  ·
    refine ⟨203208952821952665589507853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135472635214635110393005235 203208952821952665589507853)
    ·
      refine ⟨76203357308232249596065445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203208952821952665589507853 76203357308232249596065445)
      ·
        refine ⟨14288129495293546799262271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76203357308232249596065445 14288129495293546799262271)
        ·
          refine ⟨21432194242940320198893407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14288129495293546799262271 21432194242940320198893407)
          ·
            refine ⟨32148291364410480298340111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21432194242940320198893407 32148291364410480298340111)
            ·
              refine ⟨48222437046615720447510167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32148291364410480298340111 48222437046615720447510167)
              ·
                refine ⟨72333655569923580671265251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48222437046615720447510167 72333655569923580671265251)
                ·
                  refine ⟨108500483354885371006897877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72333655569923580671265251 108500483354885371006897877)
                  ·
                    refine ⟨2542980078630125882974169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 108500483354885371006897877 2542980078630125882974169)
                    ·
                      refine ⟨1907235058972594412230627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2542980078630125882974169 1907235058972594412230627)
                      ·
                        rfl

theorem cell23_3714327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_3714327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714327 prefixEnd_3714327 := by exact prefixLift 3714327
  have htrace : WordTrace (prefixWord ++ tailWord_3714327) baseStart_3714327 baseEnd_3714327 := by
    simpa [prefixWord, tailWord_3714327, baseEnd_3714327] using wordTrace_append hprefix tailTrace_3714327
  have hstable : (prefixWord ++ tailWord_3714327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714327).length < 2 ^ (prefixWord ++ tailWord_3714327).sum := by decide
  have hdescent : baseEnd_3714327 < baseStart_3714327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714354 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3714354 : Nat := 118140960795 + 3714354 * 2 ^ 59
def prefixEnd_3714354 : Nat := 4983230072969 + 3 ^ 40 * 3714354 * 2
def baseEnd_3714354 : Nat := 635749640983421935531001

theorem tailTrace_3714354 : CollatzResearch.WordTrace tailWord_3714354 prefixEnd_3714354 635749640983421935531001 := by
  unfold tailWord_3714354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33868404996384323501059529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90315746657024862669492077 33868404996384323501059529)
  ·
    refine ⟨25401303747288242625794647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33868404996384323501059529 25401303747288242625794647)
    ·
      refine ⟨38101955620932363938691971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25401303747288242625794647 38101955620932363938691971)
      ·
        refine ⟨57152933431398545908037957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38101955620932363938691971 57152933431398545908037957)
        ·
          refine ⟨10716175018387227357757117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57152933431398545908037957 10716175018387227357757117)
          ·
            refine ⟨4018565631895210259158919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10716175018387227357757117 4018565631895210259158919)
            ·
              refine ⟨6027848447842815388738379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018565631895210259158919 6027848447842815388738379)
              ·
                refine ⟨9041772671764223083107569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6027848447842815388738379 9041772671764223083107569)
                ·
                  refine ⟨6781329503823167312330677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9041772671764223083107569 6781329503823167312330677)
                  ·
                    refine ⟨635749640983421935531001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6781329503823167312330677 635749640983421935531001)
                    ·
                      rfl

theorem cell23_3714354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3714354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714354 prefixEnd_3714354 := by exact prefixLift 3714354
  have htrace : WordTrace (prefixWord ++ tailWord_3714354) baseStart_3714354 baseEnd_3714354 := by
    simpa [prefixWord, tailWord_3714354, baseEnd_3714354] using wordTrace_append hprefix tailTrace_3714354
  have hstable : (prefixWord ++ tailWord_3714354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714354).length < 2 ^ (prefixWord ++ tailWord_3714354).sum := by decide
  have hdescent : baseEnd_3714354 < baseStart_3714354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714357 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_3714357 : Nat := 118140960795 + 3714357 * 2 ^ 59
def prefixEnd_3714357 : Nat := 4983230072969 + 3 ^ 40 * 3714357 * 2
def baseEnd_3714357 : Nat := 1907250463392229294855489

theorem tailTrace_3714357 : CollatzResearch.WordTrace tailWord_3714357 prefixEnd_3714357 1907250463392229294855489 := by
  unfold tailWord_3714357
  simp only [CollatzResearch.WordTrace]
  refine ⟨135473729404526425516597325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90315819603017617011064883 135473729404526425516597325)
  ·
    refine ⟨50802648526697409568723997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135473729404526425516597325 50802648526697409568723997)
    ·
      refine ⟨19050993197511528588271499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50802648526697409568723997 19050993197511528588271499)
      ·
        refine ⟨28576489796267292882407249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19050993197511528588271499 28576489796267292882407249)
        ·
          refine ⟨21432367347200469661805437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28576489796267292882407249 21432367347200469661805437)
          ·
            refine ⟨8037137755200176123177039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21432367347200469661805437 8037137755200176123177039)
            ·
              refine ⟨12055706632800264184765559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8037137755200176123177039 12055706632800264184765559)
              ·
                refine ⟨18083559949200396277148339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12055706632800264184765559 18083559949200396277148339)
                ·
                  refine ⟨27125339923800594415722509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18083559949200396277148339 27125339923800594415722509)
                  ·
                    refine ⟨10172002471425222905895941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27125339923800594415722509 10172002471425222905895941)
                    ·
                      refine ⟨1907250463392229294855489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10172002471425222905895941 1907250463392229294855489)
                      ·
                        rfl

theorem cell23_3714357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_3714357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714357 prefixEnd_3714357 := by exact prefixLift 3714357
  have htrace : WordTrace (prefixWord ++ tailWord_3714357) baseStart_3714357 baseEnd_3714357 := by
    simpa [prefixWord, tailWord_3714357, baseEnd_3714357] using wordTrace_append hprefix tailTrace_3714357
  have hstable : (prefixWord ++ tailWord_3714357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714357).length < 2 ^ (prefixWord ++ tailWord_3714357).sum := by decide
  have hdescent : baseEnd_3714357 < baseStart_3714357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714358 : List Nat := [5, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_3714358 : Nat := 118140960795 + 3714358 * 2 ^ 59
def prefixEnd_3714358 : Nat := 4983230072969 + 3 ^ 40 * 3714358 * 2
def baseEnd_3714358 : Nat := 211916775208098198993665

theorem tailTrace_3714358 : CollatzResearch.WordTrace tailWord_3714358 prefixEnd_3714358 211916775208098198993665 := by
  unfold tailWord_3714358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467110367345175167961483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90315843918348535124922485 8467110367345175167961483)
  ·
    refine ⟨12700665551017762751942225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8467110367345175167961483 12700665551017762751942225)
    ·
      refine ⟨9525499163263322063956669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12700665551017762751942225 9525499163263322063956669)
      ·
        refine ⟨3572062186223745773983751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9525499163263322063956669 3572062186223745773983751)
        ·
          refine ⟨5358093279335618660975627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572062186223745773983751 5358093279335618660975627)
          ·
            refine ⟨8037139919003427991463441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358093279335618660975627 8037139919003427991463441)
            ·
              refine ⟨6027854939252570993597581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8037139919003427991463441 6027854939252570993597581)
              ·
                refine ⟨2260445602219714122599093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6027854939252570993597581 2260445602219714122599093)
                ·
                  refine ⟨211916775208098198993665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2260445602219714122599093 211916775208098198993665)
                  ·
                    rfl

theorem cell23_3714358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_3714358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714358 prefixEnd_3714358 := by exact prefixLift 3714358
  have htrace : WordTrace (prefixWord ++ tailWord_3714358) baseStart_3714358 baseEnd_3714358 := by
    simpa [prefixWord, tailWord_3714358, baseEnd_3714358] using wordTrace_append hprefix tailTrace_3714358
  have hstable : (prefixWord ++ tailWord_3714358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714358).length < 2 ^ (prefixWord ++ tailWord_3714358).sum := by decide
  have hdescent : baseEnd_3714358 < baseStart_3714358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714377 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 3]
def baseStart_3714377 : Nat := 118140960795 + 3714377 * 2 ^ 59
def prefixEnd_3714377 : Nat := 4983230072969 + 3 ^ 40 * 3714377 * 2
def baseEnd_3714377 : Nat := 1907260733005319216605397

theorem tailTrace_3714377 : CollatzResearch.WordTrace tailWord_3714377 prefixEnd_3714377 1907260733005319216605397 := by
  unfold tailWord_3714377
  simp only [CollatzResearch.WordTrace]
  refine ⟨135474458864453968932325385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90316305909635979288216923 135474458864453968932325385)
  ·
    refine ⟨101605844148340476699244039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135474458864453968932325385 101605844148340476699244039)
    ·
      refine ⟨152408766222510715048866059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101605844148340476699244039 152408766222510715048866059)
      ·
        refine ⟨228613149333766072573299089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152408766222510715048866059 228613149333766072573299089)
        ·
          refine ⟨171459862000324554429974317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228613149333766072573299089 171459862000324554429974317)
          ·
            refine ⟨64297448250121707911240369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171459862000324554429974317 64297448250121707911240369)
            ·
              refine ⟨48223086187591280933430277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64297448250121707911240369 48223086187591280933430277)
              ·
                refine ⟨9041828660173365175018177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48223086187591280933430277 9041828660173365175018177)
                ·
                  refine ⟨6781371495130023881263633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9041828660173365175018177 6781371495130023881263633)
                  ·
                    refine ⟨5086028621347517910947725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6781371495130023881263633 5086028621347517910947725)
                    ·
                      refine ⟨1907260733005319216605397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5086028621347517910947725 1907260733005319216605397)
                      ·
                        rfl

theorem cell23_3714377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_3714377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714377 prefixEnd_3714377 := by exact prefixLift 3714377
  have htrace : WordTrace (prefixWord ++ tailWord_3714377) baseStart_3714377 baseEnd_3714377 := by
    simpa [prefixWord, tailWord_3714377, baseEnd_3714377] using wordTrace_append hprefix tailTrace_3714377
  have hstable : (prefixWord ++ tailWord_3714377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714377).length < 2 ^ (prefixWord ++ tailWord_3714377).sum := by decide
  have hdescent : baseEnd_3714377 < baseStart_3714377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714384 : List Nat := [2, 1, 1, 1, 1, 5, 1, 6, 1, 4]
def baseStart_3714384 : Nat := 118140960795 + 3714384 * 2 ^ 59
def prefixEnd_3714384 : Nat := 4983230072969 + 3 ^ 40 * 3714384 * 2
def baseEnd_3714384 : Nat := 635754775789966896405955

theorem tailTrace_3714384 : CollatzResearch.WordTrace tailWord_3714384 prefixEnd_3714384 635754775789966896405955 := by
  unfold tailWord_3714384
  simp only [CollatzResearch.WordTrace]
  refine ⟨67737357087714304563915103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90316476116952406085220137 67737357087714304563915103)
  ·
    refine ⟨101606035631571456845872655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67737357087714304563915103 101606035631571456845872655)
    ·
      refine ⟨152409053447357185268808983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101606035631571456845872655 152409053447357185268808983)
      ·
        refine ⟨228613580171035777903213475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152409053447357185268808983 228613580171035777903213475)
        ·
          refine ⟨342920370256553666854820213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228613580171035777903213475 342920370256553666854820213)
          ·
            refine ⟨32148784711551906267639395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342920370256553666854820213 32148784711551906267639395)
            ·
              refine ⟨48223177067327859401459093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32148784711551906267639395 48223177067327859401459093)
              ·
                refine ⟨2260461425030993409443395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48223177067327859401459093 2260461425030993409443395)
                ·
                  refine ⟨3390692137546490114165093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260461425030993409443395 3390692137546490114165093)
                  ·
                    refine ⟨635754775789966896405955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3390692137546490114165093 635754775789966896405955)
                    ·
                      rfl

theorem cell23_3714384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 4].length) (baseStart_3714384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714384 prefixEnd_3714384 := by exact prefixLift 3714384
  have htrace : WordTrace (prefixWord ++ tailWord_3714384) baseStart_3714384 baseEnd_3714384 := by
    simpa [prefixWord, tailWord_3714384, baseEnd_3714384] using wordTrace_append hprefix tailTrace_3714384
  have hstable : (prefixWord ++ tailWord_3714384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714384).length < 2 ^ (prefixWord ++ tailWord_3714384).sum := by decide
  have hdescent : baseEnd_3714384 < baseStart_3714384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714427 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 1, 5]
def baseStart_3714427 : Nat := 118140960795 + 3714427 * 2 ^ 59
def prefixEnd_3714427 : Nat := 4983230072969 + 3 ^ 40 * 3714427 * 2
def baseEnd_3714427 : Nat := 635762135679348006993389

theorem tailTrace_3714427 : CollatzResearch.WordTrace tailWord_3714427 prefixEnd_3714427 635762135679348006993389 := by
  unfold tailWord_3714427
  simp only [CollatzResearch.WordTrace]
  refine ⟨135476282514272827471645535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90317521676181884981097023 135476282514272827471645535)
  ·
    refine ⟨203214423771409241207468303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135476282514272827471645535 203214423771409241207468303)
    ·
      refine ⟨304821635657113861811202455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203214423771409241207468303 304821635657113861811202455)
      ·
        refine ⟨457232453485670792716803683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304821635657113861811202455 457232453485670792716803683)
        ·
          refine ⟨685848680228506189075205525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457232453485670792716803683 685848680228506189075205525)
          ·
            refine ⟨32149156885711227612900259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 685848680228506189075205525 32149156885711227612900259)
            ·
              refine ⟨48223735328566841419350389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32149156885711227612900259 48223735328566841419350389)
              ·
                refine ⟨4520975187053141383064099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48223735328566841419350389 4520975187053141383064099)
                ·
                  refine ⟨6781462780579712074596149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520975187053141383064099 6781462780579712074596149)
                  ·
                    refine ⟨635762135679348006993389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6781462780579712074596149 635762135679348006993389)
                    ·
                      rfl

theorem cell23_3714427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 5].length) (baseStart_3714427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714427 prefixEnd_3714427 := by exact prefixLift 3714427
  have htrace : WordTrace (prefixWord ++ tailWord_3714427) baseStart_3714427 baseEnd_3714427 := by
    simpa [prefixWord, tailWord_3714427, baseEnd_3714427] using wordTrace_append hprefix tailTrace_3714427
  have hstable : (prefixWord ++ tailWord_3714427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714427).length < 2 ^ (prefixWord ++ tailWord_3714427).sum := by decide
  have hdescent : baseEnd_3714427 < baseStart_3714427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714461 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3714461 : Nat := 118140960795 + 3714461 * 2 ^ 59
def prefixEnd_3714461 : Nat := 4983230072969 + 3 ^ 40 * 3714461 * 2
def baseEnd_3714461 : Nat := 635767955126765629318337

theorem tailTrace_3714461 : CollatzResearch.WordTrace tailWord_3714461 prefixEnd_3714461 635767955126765629318337 := by
  unfold tailWord_3714461
  simp only [CollatzResearch.WordTrace]
  refine ⟨135477522596149651278383237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90318348397433100852255491 135477522596149651278383237)
  ·
    refine ⟨25402035486778059614696857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135477522596149651278383237 25402035486778059614696857)
    ·
      refine ⟨19051526615083544711022643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25402035486778059614696857 19051526615083544711022643)
      ·
        refine ⟨28577289922625317066533965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19051526615083544711022643 28577289922625317066533965)
        ·
          refine ⟨10716483720984493899950237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28577289922625317066533965 10716483720984493899950237)
          ·
            refine ⟨4018681395369185212481339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10716483720984493899950237 4018681395369185212481339)
            ·
              refine ⟨6028022093053777818722009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018681395369185212481339 6028022093053777818722009)
              ·
                refine ⟨4521016569790333364041507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6028022093053777818722009 4521016569790333364041507)
                ·
                  refine ⟨6781524854685500046062261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521016569790333364041507 6781524854685500046062261)
                  ·
                    refine ⟨635767955126765629318337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6781524854685500046062261 635767955126765629318337)
                    ·
                      rfl

theorem cell23_3714461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3714461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714461 prefixEnd_3714461 := by exact prefixLift 3714461
  have htrace : WordTrace (prefixWord ++ tailWord_3714461) baseStart_3714461 baseEnd_3714461 := by
    simpa [prefixWord, tailWord_3714461, baseEnd_3714461] using wordTrace_append hprefix tailTrace_3714461
  have hstable : (prefixWord ++ tailWord_3714461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714461).length < 2 ^ (prefixWord ++ tailWord_3714461).sum := by decide
  have hdescent : baseEnd_3714461 < baseStart_3714461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714481 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 1, 1, 4]
def baseStart_3714481 : Nat := 118140960795 + 3714481 * 2 ^ 59
def prefixEnd_3714481 : Nat := 4983230072969 + 3 ^ 40 * 3714481 * 2
def baseEnd_3714481 : Nat := 1907314134993386809704919

theorem tailTrace_3714481 : CollatzResearch.WordTrace tailWord_3714481 prefixEnd_3714481 1907314134993386809704919 := by
  unfold tailWord_3714481
  simp only [CollatzResearch.WordTrace]
  refine ⟨135478252056077194694111297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90318834704051463129407531 135478252056077194694111297)
  ·
    refine ⟨101608689042057896020583473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135478252056077194694111297 101608689042057896020583473)
    ·
      refine ⟨76206516781543422015437605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101608689042057896020583473 76206516781543422015437605)
      ·
        refine ⟨14288721896539391627894551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76206516781543422015437605 14288721896539391627894551)
        ·
          refine ⟨21433082844809087441841827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14288721896539391627894551 21433082844809087441841827)
          ·
            refine ⟨32149624267213631162762741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21433082844809087441841827 32149624267213631162762741)
            ·
              refine ⟨3014027275051277921509007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32149624267213631162762741 3014027275051277921509007)
              ·
                refine ⟨4521040912576916882263511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014027275051277921509007 4521040912576916882263511)
                ·
                  refine ⟨6781561368865375323395267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521040912576916882263511 6781561368865375323395267)
                  ·
                    refine ⟨10172342053298062985092901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781561368865375323395267 10172342053298062985092901)
                    ·
                      refine ⟨1907314134993386809704919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10172342053298062985092901 1907314134993386809704919)
                      ·
                        rfl

theorem cell23_3714481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_3714481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714481 prefixEnd_3714481 := by exact prefixLift 3714481
  have htrace : WordTrace (prefixWord ++ tailWord_3714481) baseStart_3714481 baseEnd_3714481 := by
    simpa [prefixWord, tailWord_3714481, baseEnd_3714481] using wordTrace_append hprefix tailTrace_3714481
  have hstable : (prefixWord ++ tailWord_3714481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714481).length < 2 ^ (prefixWord ++ tailWord_3714481).sum := by decide
  have hdescent : baseEnd_3714481 < baseStart_3714481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714492 : List Nat := [2, 2, 2, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3714492 : Nat := 118140960795 + 3714492 * 2 ^ 59
def prefixEnd_3714492 : Nat := 4983230072969 + 3 ^ 40 * 3714492 * 2
def baseEnd_3714492 : Nat := 1907319783280586266667369

theorem tailTrace_3714492 : CollatzResearch.WordTrace tailWord_3714492 prefixEnd_3714492 1907319783280586266667369 := by
  unfold tailWord_3714492
  simp only [CollatzResearch.WordTrace]
  refine ⟨67739326629518671786380865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90319102172691562381841153 67739326629518671786380865)
  ·
    refine ⟨50804494972139003839785649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67739326629518671786380865 50804494972139003839785649)
    ·
      refine ⟨38103371229104252879839237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50804494972139003839785649 38103371229104252879839237)
      ·
        refine ⟨7144382105457047414969857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38103371229104252879839237 7144382105457047414969857)
        ·
          refine ⟨5358286579092785561227393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7144382105457047414969857 5358286579092785561227393)
          ·
            refine ⟨4018714934319589170920545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5358286579092785561227393 4018714934319589170920545)
            ·
              refine ⟨3014036200739691878190409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4018714934319589170920545 3014036200739691878190409)
              ·
                refine ⟨2260527150554768908642807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3014036200739691878190409 2260527150554768908642807)
                ·
                  refine ⟨3390790725832153362964211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2260527150554768908642807 3390790725832153362964211)
                  ·
                    refine ⟨5086186088748230044446317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3390790725832153362964211 5086186088748230044446317)
                    ·
                      refine ⟨1907319783280586266667369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5086186088748230044446317 1907319783280586266667369)
                      ·
                        rfl

theorem cell23_3714492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3714492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714492 prefixEnd_3714492 := by exact prefixLift 3714492
  have htrace : WordTrace (prefixWord ++ tailWord_3714492) baseStart_3714492 baseEnd_3714492 := by
    simpa [prefixWord, tailWord_3714492, baseEnd_3714492] using wordTrace_append hprefix tailTrace_3714492
  have hstable : (prefixWord ++ tailWord_3714492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714492).length < 2 ^ (prefixWord ++ tailWord_3714492).sum := by decide
  have hdescent : baseEnd_3714492 < baseStart_3714492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714517 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3714517 : Nat := 118140960795 + 3714517 * 2 ^ 59
def prefixEnd_3714517 : Nat := 4983230072969 + 3 ^ 40 * 3714517 * 2
def baseEnd_3714517 : Nat := 635777540098982889618251

theorem tailTrace_3714517 : CollatzResearch.WordTrace tailWord_3714517 prefixEnd_3714517 635777540098982889618251 := by
  unfold tailWord_3714517
  simp only [CollatzResearch.WordTrace]
  refine ⟨135479565083946772842421805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90319710055964515228281203 135479565083946772842421805)
  ·
    refine ⟨50804836906480039815908177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135479565083946772842421805 50804836906480039815908177)
    ·
      refine ⟨38103627679860029861931133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50804836906480039815908177 38103627679860029861931133)
      ·
        refine ⟨14288860379947511198224175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38103627679860029861931133 14288860379947511198224175)
        ·
          refine ⟨21433290569921266797336263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14288860379947511198224175 21433290569921266797336263)
          ·
            refine ⟨32149935854881900196004395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21433290569921266797336263 32149935854881900196004395)
            ·
              refine ⟨48224903782322850294006593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32149935854881900196004395 48224903782322850294006593)
              ·
                refine ⟨36168677836742137720504945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48224903782322850294006593 36168677836742137720504945)
                ·
                  refine ⟨27126508377556603290378709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36168677836742137720504945 27126508377556603290378709)
                  ·
                    refine ⟨635777540098982889618251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27126508377556603290378709 635777540098982889618251)
                    ·
                      rfl

theorem cell23_3714517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3714517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714517 prefixEnd_3714517 := by exact prefixLift 3714517
  have htrace : WordTrace (prefixWord ++ tailWord_3714517) baseStart_3714517 baseEnd_3714517 := by
    simpa [prefixWord, tailWord_3714517, baseEnd_3714517] using wordTrace_append hprefix tailTrace_3714517
  have hstable : (prefixWord ++ tailWord_3714517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714517).length < 2 ^ (prefixWord ++ tailWord_3714517).sum := by decide
  have hdescent : baseEnd_3714517 < baseStart_3714517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714527 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_3714527 : Nat := 118140960795 + 3714527 * 2 ^ 59
def prefixEnd_3714527 : Nat := 4983230072969 + 3 ^ 40 * 3714527 * 2
def baseEnd_3714527 : Nat := 1907337755103493629729707

theorem tailTrace_3714527 : CollatzResearch.WordTrace tailWord_3714527 prefixEnd_3714527 1907337755103493629729707 := by
  unfold tailWord_3714527
  simp only [CollatzResearch.WordTrace]
  refine ⟨135479929813910544550285835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90319953209273696366857223 135479929813910544550285835)
  ·
    refine ⟨203219894720865816825428753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135479929813910544550285835 203219894720865816825428753)
    ·
      refine ⟨152414921040649362619071565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203219894720865816825428753 152414921040649362619071565)
      ·
        refine ⟨57155595390243510982151837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152414921040649362619071565 57155595390243510982151837)
        ·
          refine ⟨21433348271341316618306939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57155595390243510982151837 21433348271341316618306939)
          ·
            refine ⟨32150022407011974927460409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21433348271341316618306939 32150022407011974927460409)
            ·
              refine ⟨24112516805258981195595307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32150022407011974927460409 24112516805258981195595307)
              ·
                refine ⟨36168775207888471793392961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24112516805258981195595307 36168775207888471793392961)
                ·
                  refine ⟨27126581405916353845044721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36168775207888471793392961 27126581405916353845044721)
                  ·
                    refine ⟨20344936054437265383783541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27126581405916353845044721 20344936054437265383783541)
                    ·
                      refine ⟨1907337755103493629729707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20344936054437265383783541 1907337755103493629729707)
                      ·
                        rfl

theorem cell23_3714527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_3714527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714527 prefixEnd_3714527 := by exact prefixLift 3714527
  have htrace : WordTrace (prefixWord ++ tailWord_3714527) baseStart_3714527 baseEnd_3714527 := by
    simpa [prefixWord, tailWord_3714527, baseEnd_3714527] using wordTrace_append hprefix tailTrace_3714527
  have hstable : (prefixWord ++ tailWord_3714527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714527).length < 2 ^ (prefixWord ++ tailWord_3714527).sum := by decide
  have hdescent : baseEnd_3714527 < baseStart_3714527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714577 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 7]
def baseStart_3714577 : Nat := 118140960795 + 3714577 * 2 ^ 59
def prefixEnd_3714577 : Nat := 4983230072969 + 3 ^ 40 * 3714577 * 2
def baseEnd_3714577 : Nat := 211929269904024270456053

theorem tailTrace_3714577 : CollatzResearch.WordTrace tailWord_3714577 prefixEnd_3714577 211929269904024270456053 := by
  unfold tailWord_3714577
  simp only [CollatzResearch.WordTrace]
  refine ⟨135481753463729403089605985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90321168975819602059737323 135481753463729403089605985)
  ·
    refine ⟨101611315097797052317204489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135481753463729403089605985 101611315097797052317204489)
    ·
      refine ⟨76208486323347789237903367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101611315097797052317204489 76208486323347789237903367)
      ·
        refine ⟨114312729485021683856855051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76208486323347789237903367 114312729485021683856855051)
        ·
          refine ⟨171469094227532525785282577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114312729485021683856855051 171469094227532525785282577)
          ·
            refine ⟨128601820670649394338961933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171469094227532525785282577 128601820670649394338961933)
            ·
              refine ⟨48225682751493522877110725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128601820670649394338961933 48225682751493522877110725)
              ·
                refine ⟨9042315515905035539458261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48225682751493522877110725 9042315515905035539458261)
                ·
                  refine ⟨211929269904024270456053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9042315515905035539458261 211929269904024270456053)
                  ·
                    rfl

theorem cell23_3714577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 7].length) (baseStart_3714577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714577 prefixEnd_3714577 := by exact prefixLift 3714577
  have htrace : WordTrace (prefixWord ++ tailWord_3714577) baseStart_3714577 baseEnd_3714577 := by
    simpa [prefixWord, tailWord_3714577, baseEnd_3714577] using wordTrace_append hprefix tailTrace_3714577
  have hstable : (prefixWord ++ tailWord_3714577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714577).length < 2 ^ (prefixWord ++ tailWord_3714577).sum := by decide
  have hdescent : baseEnd_3714577 < baseStart_3714577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714661 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3714661 : Nat := 118140960795 + 3714661 * 2 ^ 59
def prefixEnd_3714661 : Nat := 4983230072969 + 3 ^ 40 * 3714661 * 2
def baseEnd_3714661 : Nat := 1907406561511196105454091

theorem tailTrace_3714661 : CollatzResearch.WordTrace tailWord_3714661 prefixEnd_3714661 1907406561511196105454091 := by
  unfold tailWord_3714661
  simp only [CollatzResearch.WordTrace]
  refine ⟨135484817195425085435663837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90323211463616723623775891 135484817195425085435663837)
  ·
    refine ⟨50806806448284407038373939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135484817195425085435663837 50806806448284407038373939)
    ·
      refine ⟨76210209672426610557560909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50806806448284407038373939 76210209672426610557560909)
      ·
        refine ⟨28578828627159978959085341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76210209672426610557560909 28578828627159978959085341)
        ·
          refine ⟨10717060735184992109657003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28578828627159978959085341 10717060735184992109657003)
          ·
            refine ⟨16075591102777488164485505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10717060735184992109657003 16075591102777488164485505)
            ·
              refine ⟨12056693327083116123364129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16075591102777488164485505 12056693327083116123364129)
              ·
                refine ⟨9042519995312337092523097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12056693327083116123364129 9042519995312337092523097)
                ·
                  refine ⟨6781889996484252819392323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9042519995312337092523097 6781889996484252819392323)
                  ·
                    refine ⟨10172834994726379229088485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6781889996484252819392323 10172834994726379229088485)
                    ·
                      refine ⟨1907406561511196105454091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10172834994726379229088485 1907406561511196105454091)
                      ·
                        rfl

theorem cell23_3714661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3714661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714661 prefixEnd_3714661 := by exact prefixLift 3714661
  have htrace : WordTrace (prefixWord ++ tailWord_3714661) baseStart_3714661 baseEnd_3714661 := by
    simpa [prefixWord, tailWord_3714661, baseEnd_3714661] using wordTrace_append hprefix tailTrace_3714661
  have hstable : (prefixWord ++ tailWord_3714661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714661).length < 2 ^ (prefixWord ++ tailWord_3714661).sum := by decide
  have hdescent : baseEnd_3714661 < baseStart_3714661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714667 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 12]
def baseStart_3714667 : Nat := 118140960795 + 3714667 * 2 ^ 59
def prefixEnd_3714667 : Nat := 4983230072969 + 3 ^ 40 * 3714667 * 2
def baseEnd_3714667 : Nat := 211934404710569231331007

theorem tailTrace_3714667 : CollatzResearch.WordTrace tailWord_3714667 prefixEnd_3714667 211934404710569231331007 := by
  unfold tailWord_3714667
  simp only [CollatzResearch.WordTrace]
  refine ⟨135485036033403348460382255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90323357355602232306921503 135485036033403348460382255)
  ·
    refine ⟨203227554050105022690573383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135485036033403348460382255 203227554050105022690573383)
    ·
      refine ⟨304841331075157534035860075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203227554050105022690573383 304841331075157534035860075)
      ·
        refine ⟨457261996612736301053790113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304841331075157534035860075 457261996612736301053790113)
        ·
          refine ⟨342946497459552225790342585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457261996612736301053790113 342946497459552225790342585)
          ·
            refine ⟨257209873094664169342756939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342946497459552225790342585 257209873094664169342756939)
            ·
              refine ⟨385814809641996254014135409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257209873094664169342756939 385814809641996254014135409)
              ·
                refine ⟨289361107231497190510601557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385814809641996254014135409 289361107231497190510601557)
                ·
                  refine ⟨211934404710569231331007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 289361107231497190510601557 211934404710569231331007)
                  ·
                    rfl

theorem cell23_3714667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 12].length) (baseStart_3714667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714667 prefixEnd_3714667 := by exact prefixLift 3714667
  have htrace : WordTrace (prefixWord ++ tailWord_3714667) baseStart_3714667 baseEnd_3714667 := by
    simpa [prefixWord, tailWord_3714667, baseEnd_3714667] using wordTrace_append hprefix tailTrace_3714667
  have hstable : (prefixWord ++ tailWord_3714667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714667).length < 2 ^ (prefixWord ++ tailWord_3714667).sum := by decide
  have hdescent : baseEnd_3714667 < baseStart_3714667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714678 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_3714678 : Nat := 118140960795 + 3714678 * 2 ^ 59
def prefixEnd_3714678 : Nat := 4983230072969 + 3 ^ 40 * 3714678 * 2
def baseEnd_3714678 : Nat := 1907415290682322538941513

theorem tailTrace_3714678 : CollatzResearch.WordTrace tailWord_3714678 prefixEnd_3714678 1907415290682322538941513 := by
  unfold tailWord_3714678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467839827272718583689543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90323624824242331559355125 8467839827272718583689543)
  ·
    refine ⟨12701759740909077875534315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8467839827272718583689543 12701759740909077875534315)
    ·
      refine ⟨19052639611363616813301473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12701759740909077875534315 19052639611363616813301473)
      ·
        refine ⟨14289479708522712609976105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19052639611363616813301473 14289479708522712609976105)
        ·
          refine ⟨10717109781392034457482079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14289479708522712609976105 10717109781392034457482079)
          ·
            refine ⟨16075664672088051686223119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10717109781392034457482079 16075664672088051686223119)
            ·
              refine ⟨24113497008132077529334679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16075664672088051686223119 24113497008132077529334679)
              ·
                refine ⟨36170245512198116294002019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24113497008132077529334679 36170245512198116294002019)
                ·
                  refine ⟨54255368268297174441003029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36170245512198116294002019 54255368268297174441003029)
                  ·
                    refine ⟨2543220387576430051922017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54255368268297174441003029 2543220387576430051922017)
                    ·
                      refine ⟨1907415290682322538941513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543220387576430051922017 1907415290682322538941513)
                      ·
                        rfl

theorem cell23_3714678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_3714678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714678 prefixEnd_3714678 := by exact prefixLift 3714678
  have htrace : WordTrace (prefixWord ++ tailWord_3714678) baseStart_3714678 baseEnd_3714678 := by
    simpa [prefixWord, tailWord_3714678, baseEnd_3714678] using wordTrace_append hprefix tailTrace_3714678
  have hstable : (prefixWord ++ tailWord_3714678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714678).length < 2 ^ (prefixWord ++ tailWord_3714678).sum := by decide
  have hdescent : baseEnd_3714678 < baseStart_3714678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714698 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3714698 : Nat := 118140960795 + 3714698 * 2 ^ 59
def prefixEnd_3714698 : Nat := 4983230072969 + 3 ^ 40 * 3714698 * 2
def baseEnd_3714698 : Nat := 1907425560295412460691421

theorem tailTrace_3714698 : CollatzResearch.WordTrace tailWord_3714698 prefixEnd_3714698 1907425560295412460691421 := by
  unfold tailWord_3714698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33871541674072760188690187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90324111130860693836507165 33871541674072760188690187)
  ·
    refine ⟨50807312511109140283035281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33871541674072760188690187 50807312511109140283035281)
    ·
      refine ⟨38105484383331855212276461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50807312511109140283035281 38105484383331855212276461)
      ·
        refine ⟨14289556643749445704603673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38105484383331855212276461 14289556643749445704603673)
        ·
          refine ⟨10717167482812084278452755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14289556643749445704603673 10717167482812084278452755)
          ·
            refine ⟨16075751224218126417679133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10717167482812084278452755 16075751224218126417679133)
            ·
              refine ⟨6028406709081797406629675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16075751224218126417679133 6028406709081797406629675)
              ·
                refine ⟨9042610063622696109944513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028406709081797406629675 9042610063622696109944513)
                ·
                  refine ⟨6781957547717022082458385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9042610063622696109944513 6781957547717022082458385)
                  ·
                    refine ⟨5086468160787766561843789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6781957547717022082458385 5086468160787766561843789)
                    ·
                      refine ⟨1907425560295412460691421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5086468160787766561843789 1907425560295412460691421)
                      ·
                        rfl

theorem cell23_3714698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3714698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714698 prefixEnd_3714698 := by exact prefixLift 3714698
  have htrace : WordTrace (prefixWord ++ tailWord_3714698) baseStart_3714698 baseEnd_3714698 := by
    simpa [prefixWord, tailWord_3714698, baseEnd_3714698] using wordTrace_append hprefix tailTrace_3714698
  have hstable : (prefixWord ++ tailWord_3714698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714698).length < 2 ^ (prefixWord ++ tailWord_3714698).sum := by decide
  have hdescent : baseEnd_3714698 < baseStart_3714698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714718 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3714718 : Nat := 118140960795 + 3714718 * 2 ^ 59
def prefixEnd_3714718 : Nat := 4983230072969 + 3 ^ 40 * 3714718 * 2
def baseEnd_3714718 : Nat := 211937314434278042493481

theorem tailTrace_3714718 : CollatzResearch.WordTrace tailWord_3714718 prefixEnd_3714718 211937314434278042493481 := by
  unfold tailWord_3714718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16935862019527323021311101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90324597437479056113659205 16935862019527323021311101)
  ·
    refine ⟨6350948257322746132991663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16935862019527323021311101 6350948257322746132991663)
    ·
      refine ⟨9526422385984119199487495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6350948257322746132991663 9526422385984119199487495)
      ·
        refine ⟨14289633578976178799231243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9526422385984119199487495 14289633578976178799231243)
        ·
          refine ⟨21434450368464268198846865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14289633578976178799231243 21434450368464268198846865)
          ·
            refine ⟨16075837776348201149135149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21434450368464268198846865 16075837776348201149135149)
            ·
              refine ⟨6028439166130575430925681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16075837776348201149135149 6028439166130575430925681)
              ·
                refine ⟨4521329374597931573194261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6028439166130575430925681 4521329374597931573194261)
                ·
                  refine ⟨211937314434278042493481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4521329374597931573194261 211937314434278042493481)
                  ·
                    rfl

theorem cell23_3714718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3714718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714718 prefixEnd_3714718 := by exact prefixLift 3714718
  have htrace : WordTrace (prefixWord ++ tailWord_3714718) baseStart_3714718 baseEnd_3714718 := by
    simpa [prefixWord, tailWord_3714718, baseEnd_3714718] using wordTrace_append hprefix tailTrace_3714718
  have hstable : (prefixWord ++ tailWord_3714718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714718).length < 2 ^ (prefixWord ++ tailWord_3714718).sum := by decide
  have hdescent : baseEnd_3714718 < baseStart_3714718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714748 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_3714748 : Nat := 118140960795 + 3714748 * 2 ^ 59
def prefixEnd_3714748 : Nat := 4983230072969 + 3 ^ 40 * 3714748 * 2
def baseEnd_3714748 : Nat := 635817078109379088355397

theorem tailTrace_3714748 : CollatzResearch.WordTrace tailWord_3714748 prefixEnd_3714748 635817078109379088355397 := by
  unfold tailWord_3714748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67743995173054949647040449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90325326897406599529387265 67743995173054949647040449)
  ·
    refine ⟨50807996379791212235280337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67743995173054949647040449 50807996379791212235280337)
    ·
      refine ⟨38105997284843409176460253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50807996379791212235280337 38105997284843409176460253)
      ·
        refine ⟨14289748981816278441172595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38105997284843409176460253 14289748981816278441172595)
        ·
          refine ⟨21434623472724417661758893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14289748981816278441172595 21434623472724417661758893)
          ·
            refine ⟨8037983802271656623159585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21434623472724417661758893 8037983802271656623159585)
            ·
              refine ⟨6028487851703742467369689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8037983802271656623159585 6028487851703742467369689)
              ·
                refine ⟨4521365888777806850527267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6028487851703742467369689 4521365888777806850527267)
                ·
                  refine ⟨6782048833166710275790901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521365888777806850527267 6782048833166710275790901)
                  ·
                    refine ⟨635817078109379088355397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6782048833166710275790901 635817078109379088355397)
                    ·
                      rfl

theorem cell23_3714748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_3714748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714748 prefixEnd_3714748 := by exact prefixLift 3714748
  have htrace : WordTrace (prefixWord ++ tailWord_3714748) baseStart_3714748 baseEnd_3714748 := by
    simpa [prefixWord, tailWord_3714748, baseEnd_3714748] using wordTrace_append hprefix tailTrace_3714748
  have hstable : (prefixWord ++ tailWord_3714748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714748).length < 2 ^ (prefixWord ++ tailWord_3714748).sum := by decide
  have hdescent : baseEnd_3714748 < baseStart_3714748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714751 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 2, 6, 2]
def baseStart_3714751 : Nat := 118140960795 + 3714751 * 2 ^ 59
def prefixEnd_3714751 : Nat := 4983230072969 + 3 ^ 40 * 3714751 * 2
def baseEnd_3714751 : Nat := 1907452774770100753328677

theorem tailTrace_3714751 : CollatzResearch.WordTrace tailWord_3714751 prefixEnd_3714751 1907452774770100753328677 := by
  unfold tailWord_3714751
  simp only [CollatzResearch.WordTrace]
  refine ⟨135488099765099030806440107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90325399843399353870960071 135488099765099030806440107)
  ·
    refine ⟨203232149647648546209660161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135488099765099030806440107 203232149647648546209660161)
    ·
      refine ⟨152424112235736409657245121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203232149647648546209660161 152424112235736409657245121)
      ·
        refine ⟨114318084176802307242933841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152424112235736409657245121 114318084176802307242933841)
        ·
          refine ⟨85738563132601730432200381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114318084176802307242933841 85738563132601730432200381)
          ·
            refine ⟨32151961174725648912075143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85738563132601730432200381 32151961174725648912075143)
            ·
              refine ⟨48227941762088473368112715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32151961174725648912075143 48227941762088473368112715)
              ·
                refine ⟨72341912643132710052169073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48227941762088473368112715 72341912643132710052169073)
                ·
                  refine ⟨54256434482349532539126805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72341912643132710052169073 54256434482349532539126805)
                  ·
                    refine ⟨2543270366360134337771569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54256434482349532539126805 2543270366360134337771569)
                    ·
                      refine ⟨1907452774770100753328677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543270366360134337771569 1907452774770100753328677)
                      ·
                        rfl

theorem cell23_3714751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_3714751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714751 prefixEnd_3714751 := by exact prefixLift 3714751
  have htrace : WordTrace (prefixWord ++ tailWord_3714751) baseStart_3714751 baseEnd_3714751 := by
    simpa [prefixWord, tailWord_3714751, baseEnd_3714751] using wordTrace_append hprefix tailTrace_3714751
  have hstable : (prefixWord ++ tailWord_3714751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714751).length < 2 ^ (prefixWord ++ tailWord_3714751).sum := by decide
  have hdescent : baseEnd_3714751 < baseStart_3714751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714765 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3714765 : Nat := 118140960795 + 3714765 * 2 ^ 59
def prefixEnd_3714765 : Nat := 4983230072969 + 3 ^ 40 * 3714765 * 2
def baseEnd_3714765 : Nat := 635819987833087899517871

theorem tailTrace_3714765 : CollatzResearch.WordTrace tailWord_3714765 prefixEnd_3714765 635819987833087899517871 := by
  unfold tailWord_3714765
  simp only [CollatzResearch.WordTrace]
  refine ⟨135488610387048311197449749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90325740258032207464966499 135488610387048311197449749)
  ·
    refine ⟨6351028611892889587380457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135488610387048311197449749 6351028611892889587380457)
    ·
      refine ⟨4763271458919667190535343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6351028611892889587380457 4763271458919667190535343)
      ·
        refine ⟨7144907188379500785803015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763271458919667190535343 7144907188379500785803015)
        ·
          refine ⟨10717360782569251178704523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7144907188379500785803015 10717360782569251178704523)
          ·
            refine ⟨16076041173853876768056785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10717360782569251178704523 16076041173853876768056785)
            ·
              refine ⟨12057030880390407576042589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16076041173853876768056785 12057030880390407576042589)
              ·
                refine ⟨4521386580146402841015971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12057030880390407576042589 4521386580146402841015971)
                ·
                  refine ⟨6782079870219604261523957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521386580146402841015971 6782079870219604261523957)
                  ·
                    refine ⟨635819987833087899517871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6782079870219604261523957 635819987833087899517871)
                    ·
                      rfl

theorem cell23_3714765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3714765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714765 prefixEnd_3714765 := by exact prefixLift 3714765
  have htrace : WordTrace (prefixWord ++ tailWord_3714765) baseStart_3714765 baseEnd_3714765 := by
    simpa [prefixWord, tailWord_3714765, baseEnd_3714765] using wordTrace_append hprefix tailTrace_3714765
  have hstable : (prefixWord ++ tailWord_3714765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714765).length < 2 ^ (prefixWord ++ tailWord_3714765).sum := by decide
  have hdescent : baseEnd_3714765 < baseStart_3714765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714879 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 1, 3, 2]
def baseStart_3714879 : Nat := 118140960795 + 3714879 * 2 ^ 59
def prefixEnd_3714879 : Nat := 4983230072969 + 3 ^ 40 * 3714879 * 2
def baseEnd_3714879 : Nat := 1907518500293876252528089

theorem tailTrace_3714879 : CollatzResearch.WordTrace tailWord_3714879 prefixEnd_3714879 1907518500293876252528089 := by
  unfold tailWord_3714879
  simp only [CollatzResearch.WordTrace]
  refine ⟨135492768308635308667099691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90328512205756872444733127 135492768308635308667099691)
  ·
    refine ⟨203239152462952963000649537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135492768308635308667099691 203239152462952963000649537)
    ·
      refine ⟨152429364347214722250487153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203239152462952963000649537 152429364347214722250487153)
      ·
        refine ⟨114322023260411041687865365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152429364347214722250487153 114322023260411041687865365)
        ·
          refine ⟨5358844840331767579118689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114322023260411041687865365 5358844840331767579118689)
          ·
            refine ⟨4019133630248825684339017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5358844840331767579118689 4019133630248825684339017)
            ·
              refine ⟨3014350222686619263254263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4019133630248825684339017 3014350222686619263254263)
              ·
                refine ⟨4521525334029928894881395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014350222686619263254263 4521525334029928894881395)
                ·
                  refine ⟨6782288001044893342322093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521525334029928894881395 6782288001044893342322093)
                  ·
                    refine ⟨2543358000391835003370785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6782288001044893342322093 2543358000391835003370785)
                    ·
                      refine ⟨1907518500293876252528089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543358000391835003370785 1907518500293876252528089)
                      ·
                        rfl

theorem cell23_3714879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_3714879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714879 prefixEnd_3714879 := by exact prefixLift 3714879
  have htrace : WordTrace (prefixWord ++ tailWord_3714879) baseStart_3714879 baseEnd_3714879 := by
    simpa [prefixWord, tailWord_3714879, baseEnd_3714879] using wordTrace_append hprefix tailTrace_3714879
  have hstable : (prefixWord ++ tailWord_3714879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714879).length < 2 ^ (prefixWord ++ tailWord_3714879).sum := by decide
  have hdescent : baseEnd_3714879 < baseStart_3714879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714886 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3714886 : Nat := 118140960795 + 3714886 * 2 ^ 59
def prefixEnd_3714886 : Nat := 4983230072969 + 3 ^ 40 * 3714886 * 2
def baseEnd_3714886 : Nat := 1907522094658457725140557

theorem tailTrace_3714886 : CollatzResearch.WordTrace tailWord_3714886 prefixEnd_3714886 1907522094658457725140557 := by
  unfold tailWord_3714886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234156988112810901956391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90328682413073299241736341 4234156988112810901956391)
  ·
    refine ⟨6351235482169216352934587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4234156988112810901956391 6351235482169216352934587)
    ·
      refine ⟨9526853223253824529401881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351235482169216352934587 9526853223253824529401881)
      ·
        refine ⟨7145139917440368397051411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9526853223253824529401881 7145139917440368397051411)
        ·
          refine ⟨10717709876160552595577117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145139917440368397051411 10717709876160552595577117)
          ·
            refine ⟨4019141203560207223341419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10717709876160552595577117 4019141203560207223341419)
            ·
              refine ⟨6028711805340310835012129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019141203560207223341419 6028711805340310835012129)
              ·
                refine ⟨4521533854005233126259097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6028711805340310835012129 4521533854005233126259097)
                ·
                  refine ⟨3391150390503924844694323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4521533854005233126259097 3391150390503924844694323)
                  ·
                    refine ⟨5086725585755887267041485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3391150390503924844694323 5086725585755887267041485)
                    ·
                      refine ⟨1907522094658457725140557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5086725585755887267041485 1907522094658457725140557)
                      ·
                        rfl

theorem cell23_3714886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3714886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714886 prefixEnd_3714886 := by exact prefixLift 3714886
  have htrace : WordTrace (prefixWord ++ tailWord_3714886) baseStart_3714886 baseEnd_3714886 := by
    simpa [prefixWord, tailWord_3714886, baseEnd_3714886] using wordTrace_append hprefix tailTrace_3714886
  have hstable : (prefixWord ++ tailWord_3714886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714886).length < 2 ^ (prefixWord ++ tailWord_3714886).sum := by decide
  have hdescent : baseEnd_3714886 < baseStart_3714886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714892 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 4, 2, 2]
def baseStart_3714892 : Nat := 118140960795 + 3714892 * 2 ^ 59
def prefixEnd_3714892 : Nat := 4983230072969 + 3 ^ 40 * 3714892 * 2
def baseEnd_3714892 : Nat := 1907525175542384701665529

theorem tailTrace_3714892 : CollatzResearch.WordTrace tailWord_3714892 prefixEnd_3714892 1907525175542384701665529 := by
  unfold tailWord_3714892
  simp only [CollatzResearch.WordTrace]
  refine ⟨67746621228794105943661465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90328828305058807924881953 67746621228794105943661465)
  ·
    refine ⟨50809965921595579457746099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67746621228794105943661465 50809965921595579457746099)
    ·
      refine ⟨76214948882393369186619149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50809965921595579457746099 76214948882393369186619149)
      ·
        refine ⟨28580605830897513444982181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76214948882393369186619149 28580605830897513444982181)
        ·
          refine ⟨5358863593293283770934159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28580605830897513444982181 5358863593293283770934159)
          ·
            refine ⟨8038295389939925656401239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5358863593293283770934159 8038295389939925656401239)
            ·
              refine ⟨12057443084909888484601859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038295389939925656401239 12057443084909888484601859)
              ·
                refine ⟨18086164627364832726902789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12057443084909888484601859 18086164627364832726902789)
                ·
                  refine ⟨3391155867630906136294273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18086164627364832726902789 3391155867630906136294273)
                  ·
                    refine ⟨2543366900723179602220705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3391155867630906136294273 2543366900723179602220705)
                    ·
                      refine ⟨1907525175542384701665529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543366900723179602220705 1907525175542384701665529)
                      ·
                        rfl

theorem cell23_3714892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_3714892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714892 prefixEnd_3714892 := by exact prefixLift 3714892
  have htrace : WordTrace (prefixWord ++ tailWord_3714892) baseStart_3714892 baseEnd_3714892 := by
    simpa [prefixWord, tailWord_3714892, baseEnd_3714892] using wordTrace_append hprefix tailTrace_3714892
  have hstable : (prefixWord ++ tailWord_3714892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714892).length < 2 ^ (prefixWord ++ tailWord_3714892).sum := by decide
  have hdescent : baseEnd_3714892 < baseStart_3714892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714898 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 7]
def baseStart_3714898 : Nat := 118140960795 + 3714898 * 2 ^ 59
def prefixEnd_3714898 : Nat := 4983230072969 + 3 ^ 40 * 3714898 * 2
def baseEnd_3714898 : Nat := 211947584047367964243389

theorem tailTrace_3714898 : CollatzResearch.WordTrace tailWord_3714898 prefixEnd_3714898 211947584047367964243389 := by
  unfold tailWord_3714898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33873365323891618728010337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90328974197044316608027565 33873365323891618728010337)
  ·
    refine ⟨25405023992918714046007753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33873365323891618728010337 25405023992918714046007753)
    ·
      refine ⟨19053767994689035534505815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25405023992918714046007753 19053767994689035534505815)
      ·
        refine ⟨28580651992033553301758723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19053767994689035534505815 28580651992033553301758723)
        ·
          refine ⟨42870977988050329952638085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28580651992033553301758723 42870977988050329952638085)
          ·
            refine ⟨8038308372759436866119641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42870977988050329952638085 8038308372759436866119641)
            ·
              refine ⟨6028731279569577649589731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8038308372759436866119641 6028731279569577649589731)
              ·
                refine ⟨9043096919354366474384597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6028731279569577649589731 9043096919354366474384597)
                ·
                  refine ⟨211947584047367964243389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9043096919354366474384597 211947584047367964243389)
                  ·
                    rfl

theorem cell23_3714898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_3714898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714898 prefixEnd_3714898 := by exact prefixLift 3714898
  have htrace : WordTrace (prefixWord ++ tailWord_3714898) baseStart_3714898 baseEnd_3714898 := by
    simpa [prefixWord, tailWord_3714898, baseEnd_3714898] using wordTrace_append hprefix tailTrace_3714898
  have hstable : (prefixWord ++ tailWord_3714898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714898).length < 2 ^ (prefixWord ++ tailWord_3714898).sum := by decide
  have hdescent : baseEnd_3714898 < baseStart_3714898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714911 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 1, 7]
def baseStart_3714911 : Nat := 118140960795 + 3714911 * 2 ^ 59
def prefixEnd_3714911 : Nat := 4983230072969 + 3 ^ 40 * 3714911 * 2
def baseEnd_3714911 : Nat := 635844977224940042442647

theorem tailTrace_3714911 : CollatzResearch.WordTrace tailWord_3714911 prefixEnd_3714911 635844977224940042442647 := by
  unfold tailWord_3714911
  simp only [CollatzResearch.WordTrace]
  refine ⟨135493935444519378132264587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90329290296346252088176391 135493935444519378132264587)
  ·
    refine ⟨203240903166779067198396881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135493935444519378132264587 203240903166779067198396881)
    ·
      refine ⟨152430677375084300398797661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203240903166779067198396881 152430677375084300398797661)
      ·
        refine ⟨57161504015656612649549123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152430677375084300398797661 57161504015656612649549123)
        ·
          refine ⟨85742256023484918974323685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57161504015656612649549123 85742256023484918974323685)
          ·
            refine ⟨16076673004403422307685691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85742256023484918974323685 16076673004403422307685691)
            ·
              refine ⟨24115009506605133461528537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16076673004403422307685691 24115009506605133461528537)
              ·
                refine ⟨18086257129953850096146403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24115009506605133461528537 18086257129953850096146403)
                ·
                  refine ⟨27129385694930775144219605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18086257129953850096146403 27129385694930775144219605)
                  ·
                    refine ⟨635844977224940042442647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27129385694930775144219605 635844977224940042442647)
                    ·
                      rfl

theorem cell23_3714911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_3714911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714911 prefixEnd_3714911 := by exact prefixLift 3714911
  have htrace : WordTrace (prefixWord ++ tailWord_3714911) baseStart_3714911 baseEnd_3714911 := by
    simpa [prefixWord, tailWord_3714911, baseEnd_3714911] using wordTrace_append hprefix tailTrace_3714911
  have hstable : (prefixWord ++ tailWord_3714911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714911).length < 2 ^ (prefixWord ++ tailWord_3714911).sum := by decide
  have hdescent : baseEnd_3714911 < baseStart_3714911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714948 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3714948 : Nat := 118140960795 + 3714948 * 2 ^ 59
def prefixEnd_3714948 : Nat := 4983230072969 + 3 ^ 40 * 3714948 * 2
def baseEnd_3714948 : Nat := 1907553930459036482565271

theorem tailTrace_3714948 : CollatzResearch.WordTrace tailWord_3714948 prefixEnd_3714948 1907553930459036482565271 := by
  unfold tailWord_3714948
  simp only [CollatzResearch.WordTrace]
  refine ⟨67747642472692666725680749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90330189963590222300907665 67747642472692666725680749)
  ·
    refine ⟨25405365927259750022130281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67747642472692666725680749 25405365927259750022130281)
    ·
      refine ⟨19054024445444812516597711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25405365927259750022130281 19054024445444812516597711)
      ·
        refine ⟨28581036668167218774896567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19054024445444812516597711 28581036668167218774896567)
        ·
          refine ⟨42871555002250828162344851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28581036668167218774896567 42871555002250828162344851)
          ·
            refine ⟨64307332503376242243517277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42871555002250828162344851 64307332503376242243517277)
            ·
              refine ⟨24115249688766090841318979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64307332503376242243517277 24115249688766090841318979)
              ·
                refine ⟨36172874533149136261978469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24115249688766090841318979 36172874533149136261978469)
                ·
                  refine ⟨6782413974965463049120963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36172874533149136261978469 6782413974965463049120963)
                  ·
                    refine ⟨10173620962448194573681445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6782413974965463049120963 10173620962448194573681445)
                    ·
                      refine ⟨1907553930459036482565271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10173620962448194573681445 1907553930459036482565271)
                      ·
                        rfl

theorem cell23_3714948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3714948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714948 prefixEnd_3714948 := by exact prefixLift 3714948
  have htrace : WordTrace (prefixWord ++ tailWord_3714948) baseStart_3714948 baseEnd_3714948 := by
    simpa [prefixWord, tailWord_3714948, baseEnd_3714948] using wordTrace_append hprefix tailTrace_3714948
  have hstable : (prefixWord ++ tailWord_3714948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714948).length < 2 ^ (prefixWord ++ tailWord_3714948).sum := by decide
  have hdescent : baseEnd_3714948 < baseStart_3714948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3714961 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3714961 : Nat := 118140960795 + 3714961 * 2 ^ 59
def prefixEnd_3714961 : Nat := 4983230072969 + 3 ^ 40 * 3714961 * 2
def baseEnd_3714961 : Nat := 1907560605707544931702711

theorem tailTrace_3714961 : CollatzResearch.WordTrace tailWord_3714961 prefixEnd_3714961 1907560605707544931702711 := by
  unfold tailWord_3714961
  simp only [CollatzResearch.WordTrace]
  refine ⟨135495759094338236671584737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90330506062892157781056491 135495759094338236671584737)
  ·
    refine ⟨101621819320753677503688553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135495759094338236671584737 101621819320753677503688553)
    ·
      refine ⟨76216364490565258127766415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101621819320753677503688553 76216364490565258127766415)
      ·
        refine ⟨114324546735847887191649623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76216364490565258127766415 114324546735847887191649623)
        ·
          refine ⟨171486820103771830787474435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114324546735847887191649623 171486820103771830787474435)
          ·
            refine ⟨257230230155657746181211653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171486820103771830787474435 257230230155657746181211653)
            ·
              refine ⟨48230668154185827408977185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257230230155657746181211653 48230668154185827408977185)
              ·
                refine ⟨36173001115639370556732889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48230668154185827408977185 36173001115639370556732889)
                ·
                  refine ⟨27129750836729527917549667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36173001115639370556732889 27129750836729527917549667)
                  ·
                    refine ⟨40694626255094291876324501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27129750836729527917549667 40694626255094291876324501)
                    ·
                      refine ⟨1907560605707544931702711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40694626255094291876324501 1907560605707544931702711)
                      ·
                        rfl

theorem cell23_3714961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3714961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3714961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3714961 prefixEnd_3714961 := by exact prefixLift 3714961
  have htrace : WordTrace (prefixWord ++ tailWord_3714961) baseStart_3714961 baseEnd_3714961 := by
    simpa [prefixWord, tailWord_3714961, baseEnd_3714961] using wordTrace_append hprefix tailTrace_3714961
  have hstable : (prefixWord ++ tailWord_3714961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3714961).length < 2 ^ (prefixWord ++ tailWord_3714961).sum := by decide
  have hdescent : baseEnd_3714961 < baseStart_3714961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3714961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715005 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 6]
def baseStart_3715005 : Nat := 118140960795 + 3715005 * 2 ^ 59
def prefixEnd_3715005 : Nat := 4983230072969 + 3 ^ 40 * 3715005 * 2
def baseEnd_3715005 : Nat := 211953688761815862172501

theorem tailTrace_3715005 : CollatzResearch.WordTrace tailWord_3715005 prefixEnd_3715005 211953688761815862172501 := by
  unfold tailWord_3715005
  simp only [CollatzResearch.WordTrace]
  refine ⟨135497363906178832186186469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90331575937452554790790979 135497363906178832186186469)
  ·
    refine ⟨25405755732408531034909963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135497363906178832186186469 25405755732408531034909963)
    ·
      refine ⟨38108633598612796552364945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25405755732408531034909963 38108633598612796552364945)
      ·
        refine ⟨28581475198959597414273709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38108633598612796552364945 28581475198959597414273709)
        ·
          refine ⟨10718053199609849030352641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28581475198959597414273709 10718053199609849030352641)
          ·
            refine ⟨8038539899707386772764481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10718053199609849030352641 8038539899707386772764481)
            ·
              refine ⟨6028904924780540079573361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8038539899707386772764481 6028904924780540079573361)
              ·
                refine ⟨4521678693585405059680021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6028904924780540079573361 4521678693585405059680021)
                ·
                  refine ⟨211953688761815862172501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4521678693585405059680021 211953688761815862172501)
                  ·
                    rfl

theorem cell23_3715005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_3715005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715005 prefixEnd_3715005 := by exact prefixLift 3715005
  have htrace : WordTrace (prefixWord ++ tailWord_3715005) baseStart_3715005 baseEnd_3715005 := by
    simpa [prefixWord, tailWord_3715005, baseEnd_3715005] using wordTrace_append hprefix tailTrace_3715005
  have hstable : (prefixWord ++ tailWord_3715005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715005).length < 2 ^ (prefixWord ++ tailWord_3715005).sum := by decide
  have hdescent : baseEnd_3715005 < baseStart_3715005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715011 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7]
def baseStart_3715011 : Nat := 118140960795 + 3715011 * 2 ^ 59
def prefixEnd_3715011 : Nat := 4983230072969 + 3 ^ 40 * 3715011 * 2
def baseEnd_3715011 : Nat := 1907586279740269736077481

theorem tailTrace_3715011 : CollatzResearch.WordTrace tailWord_3715011 prefixEnd_3715011 1907586279740269736077481 := by
  unfold tailWord_3715011
  simp only [CollatzResearch.WordTrace]
  refine ⟨135497582744157095210904887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90331721829438063473936591 135497582744157095210904887)
  ·
    refine ⟨203246374116235642816357331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135497582744157095210904887 203246374116235642816357331)
    ·
      refine ⟨304869561174353464224535997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203246374116235642816357331 304869561174353464224535997)
      ·
        refine ⟨114326085440382549084200999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304869561174353464224535997 114326085440382549084200999)
        ·
          refine ⟨171489128160573823626301499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114326085440382549084200999 171489128160573823626301499)
          ·
            refine ⟨257233692240860735439452249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171489128160573823626301499 257233692240860735439452249)
            ·
              refine ⟨192925269180645551579589187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257233692240860735439452249 192925269180645551579589187)
              ·
                refine ⟨289387903770968327369383781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192925269180645551579589187 289387903770968327369383781)
                ·
                  refine ⟨54260231957056561381759459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289387903770968327369383781 54260231957056561381759459)
                  ·
                    refine ⟨81390347935584842072639189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54260231957056561381759459 81390347935584842072639189)
                    ·
                      refine ⟨1907586279740269736077481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81390347935584842072639189 1907586279740269736077481)
                      ·
                        rfl

theorem cell23_3715011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_3715011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715011 prefixEnd_3715011 := by exact prefixLift 3715011
  have htrace : WordTrace (prefixWord ++ tailWord_3715011) baseStart_3715011 baseEnd_3715011 := by
    simpa [prefixWord, tailWord_3715011, baseEnd_3715011] using wordTrace_append hprefix tailTrace_3715011
  have hstable : (prefixWord ++ tailWord_3715011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715011).length < 2 ^ (prefixWord ++ tailWord_3715011).sum := by decide
  have hdescent : baseEnd_3715011 < baseStart_3715011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715015 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_3715015 : Nat := 118140960795 + 3715015 * 2 ^ 59
def prefixEnd_3715015 : Nat := 4983230072969 + 3 ^ 40 * 3715015 * 2
def baseEnd_3715015 : Nat := 1907588333662887720427463

theorem tailTrace_3715015 : CollatzResearch.WordTrace tailWord_3715015 prefixEnd_3715015 1907588333662887720427463 := by
  unfold tailWord_3715015
  simp only [CollatzResearch.WordTrace]
  refine ⟨135497728636142603894050499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90331819090761735929366999 135497728636142603894050499)
  ·
    refine ⟨203246592954213905841075749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135497728636142603894050499 203246592954213905841075749)
    ·
      refine ⟨38108736178915107345201703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203246592954213905841075749 38108736178915107345201703)
      ·
        refine ⟨57163104268372661017802555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38108736178915107345201703 57163104268372661017802555)
        ·
          refine ⟨85744656402558991526703833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57163104268372661017802555 85744656402558991526703833)
          ·
            refine ⟨64308492301919243645027875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85744656402558991526703833 64308492301919243645027875)
            ·
              refine ⟨96462738452878865467541813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64308492301919243645027875 96462738452878865467541813)
              ·
                refine ⟨9043381729957393637582045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96462738452878865467541813 9043381729957393637582045)
                ·
                  refine ⟨3391268148734022614093267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9043381729957393637582045 3391268148734022614093267)
                  ·
                    refine ⟨5086902223101033921139901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3391268148734022614093267 5086902223101033921139901)
                    ·
                      refine ⟨1907588333662887720427463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5086902223101033921139901 1907588333662887720427463)
                      ·
                        rfl

theorem cell23_3715015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_3715015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715015 prefixEnd_3715015 := by exact prefixLift 3715015
  have htrace : WordTrace (prefixWord ++ tailWord_3715015) baseStart_3715015 baseEnd_3715015 := by
    simpa [prefixWord, tailWord_3715015, baseEnd_3715015] using wordTrace_append hprefix tailTrace_3715015
  have hstable : (prefixWord ++ tailWord_3715015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715015).length < 2 ^ (prefixWord ++ tailWord_3715015).sum := by decide
  have hdescent : baseEnd_3715015 < baseStart_3715015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715018 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 3, 5]
def baseStart_3715018 : Nat := 118140960795 + 3715018 * 2 ^ 59
def prefixEnd_3715018 : Nat := 4983230072969 + 3 ^ 40 * 3715018 * 2
def baseEnd_3715018 : Nat := 635863291368283736229983

theorem tailTrace_3715018 : CollatzResearch.WordTrace tailWord_3715018 prefixEnd_3715018 635863291368283736229983 := by
  unfold tailWord_3715018
  simp only [CollatzResearch.WordTrace]
  refine ⟨33874459513782933851602427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90331892036754490270939805 33874459513782933851602427)
  ·
    refine ⟨50811689270674400777403641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33874459513782933851602427 50811689270674400777403641)
    ·
      refine ⟨38108766953005800583052731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50811689270674400777403641 38108766953005800583052731)
      ·
        refine ⟨57163150429508700874579097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38108766953005800583052731 57163150429508700874579097)
        ·
          refine ⟨42872362822131525655934323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57163150429508700874579097 42872362822131525655934323)
          ·
            refine ⟨64308544233197288483901485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42872362822131525655934323 64308544233197288483901485)
            ·
              refine ⟨24115704087448983181463057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64308544233197288483901485 24115704087448983181463057)
              ·
                refine ⟨18086778065586737386097293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24115704087448983181463057 18086778065586737386097293)
                ·
                  refine ⟨6782541774595026519786485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18086778065586737386097293 6782541774595026519786485)
                  ·
                    refine ⟨635863291368283736229983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6782541774595026519786485 635863291368283736229983)
                    ·
                      rfl

theorem cell23_3715018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_3715018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715018 prefixEnd_3715018 := by exact prefixLift 3715018
  have htrace : WordTrace (prefixWord ++ tailWord_3715018) baseStart_3715018 baseEnd_3715018 := by
    simpa [prefixWord, tailWord_3715018, baseEnd_3715018] using wordTrace_append hprefix tailTrace_3715018
  have hstable : (prefixWord ++ tailWord_3715018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715018).length < 2 ^ (prefixWord ++ tailWord_3715018).sum := by decide
  have hdescent : baseEnd_3715018 < baseStart_3715018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715028 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3715028 : Nat := 118140960795 + 3715028 * 2 ^ 59
def prefixEnd_3715028 : Nat := 4983230072969 + 3 ^ 40 * 3715028 * 2
def baseEnd_3715028 : Nat := 1907595008911396169564903

theorem tailTrace_3715028 : CollatzResearch.WordTrace tailWord_3715028 prefixEnd_3715028 1907595008911396169564903 := by
  unfold tailWord_3715028
  simp only [CollatzResearch.WordTrace]
  refine ⟨67749101392547753557136869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90332135190063671409515825 67749101392547753557136869)
  ·
    refine ⟨12702956511102703791963163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67749101392547753557136869 12702956511102703791963163)
    ·
      refine ⟨19054434766654055687944745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12702956511102703791963163 19054434766654055687944745)
      ·
        refine ⟨14290826074990541765958559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19054434766654055687944745 14290826074990541765958559)
        ·
          refine ⟨21436239112485812648937839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14290826074990541765958559 21436239112485812648937839)
          ·
            refine ⟨32154358668728718973406759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21436239112485812648937839 32154358668728718973406759)
            ·
              refine ⟨48231538003093078460110139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32154358668728718973406759 48231538003093078460110139)
              ·
                refine ⟨72347307004639617690165209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48231538003093078460110139 72347307004639617690165209)
                ·
                  refine ⟨54260480253479713267623907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72347307004639617690165209 54260480253479713267623907)
                  ·
                    refine ⟨81390720380219569901435861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54260480253479713267623907 81390720380219569901435861)
                    ·
                      refine ⟨1907595008911396169564903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 81390720380219569901435861 1907595008911396169564903)
                      ·
                        rfl

theorem cell23_3715028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3715028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715028 prefixEnd_3715028 := by exact prefixLift 3715028
  have htrace : WordTrace (prefixWord ++ tailWord_3715028) baseStart_3715028 baseEnd_3715028 := by
    simpa [prefixWord, tailWord_3715028, baseEnd_3715028] using wordTrace_append hprefix tailTrace_3715028
  have hstable : (prefixWord ++ tailWord_3715028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715028).length < 2 ^ (prefixWord ++ tailWord_3715028).sum := by decide
  have hdescent : baseEnd_3715028 < baseStart_3715028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715055 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 4]
def baseStart_3715055 : Nat := 118140960795 + 3715055 * 2 ^ 59
def prefixEnd_3715055 : Nat := 4983230072969 + 3 ^ 40 * 3715055 * 2
def baseEnd_3715055 : Nat := 1907608872889067563927279

theorem tailTrace_3715055 : CollatzResearch.WordTrace tailWord_3715055 prefixEnd_3715055 1907608872889067563927279 := by
  unfold tailWord_3715055
  simp only [CollatzResearch.WordTrace]
  refine ⟨135499187555997690725506619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90332791703998460483671079 135499187555997690725506619)
  ·
    refine ⟨203248781333996536088259929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135499187555997690725506619 203248781333996536088259929)
    ·
      refine ⟨152436586000497402066194947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203248781333996536088259929 152436586000497402066194947)
      ·
        refine ⟨228654879000746103099292421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152436586000497402066194947 228654879000746103099292421)
        ·
          refine ⟨42872789812639894331117329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228654879000746103099292421 42872789812639894331117329)
          ·
            refine ⟨32154592359479920748337997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42872789812639894331117329 32154592359479920748337997)
            ·
              refine ⟨12057972134804970280626749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32154592359479920748337997 12057972134804970280626749)
              ·
                refine ⟨4521739550551863855235031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12057972134804970280626749 4521739550551863855235031)
                ·
                  refine ⟨6782609325827795782852547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4521739550551863855235031 6782609325827795782852547)
                  ·
                    refine ⟨10173913988741693674278821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6782609325827795782852547 10173913988741693674278821)
                    ·
                      refine ⟨1907608872889067563927279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10173913988741693674278821 1907608872889067563927279)
                      ·
                        rfl

theorem cell23_3715055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_3715055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715055 prefixEnd_3715055 := by exact prefixLift 3715055
  have htrace : WordTrace (prefixWord ++ tailWord_3715055) baseStart_3715055 baseEnd_3715055 := by
    simpa [prefixWord, tailWord_3715055, baseEnd_3715055] using wordTrace_append hprefix tailTrace_3715055
  have hstable : (prefixWord ++ tailWord_3715055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715055).length < 2 ^ (prefixWord ++ tailWord_3715055).sum := by decide
  have hdescent : baseEnd_3715055 < baseStart_3715055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715065 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 4, 4]
def baseStart_3715065 : Nat := 118140960795 + 3715065 * 2 ^ 59
def prefixEnd_3715065 : Nat := 4983230072969 + 3 ^ 40 * 3715065 * 2
def baseEnd_3715065 : Nat := 635871335898537508267411

theorem tailTrace_3715065 : CollatzResearch.WordTrace tailWord_3715065 prefixEnd_3715065 635871335898537508267411 := by
  unfold tailWord_3715065
  simp only [CollatzResearch.WordTrace]
  refine ⟨135499552285961462433370649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90333034857307641622247099 135499552285961462433370649)
  ·
    refine ⟨101624664214471096825027987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135499552285961462433370649 101624664214471096825027987)
    ·
      refine ⟨152436996321706645237541981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101624664214471096825027987 152436996321706645237541981)
      ·
        refine ⟨57163873620639991964078243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152436996321706645237541981 57163873620639991964078243)
        ·
          refine ⟨85745810430959987946117365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57163873620639991964078243 85745810430959987946117365)
          ·
            refine ⟨8038669727902498869948503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85745810430959987946117365 8038669727902498869948503)
            ·
              refine ⟨12058004591853748304922755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038669727902498869948503 12058004591853748304922755)
              ·
                refine ⟨18087006887780622457384133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058004591853748304922755 18087006887780622457384133)
                ·
                  refine ⟨3391313791458866710759525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18087006887780622457384133 3391313791458866710759525)
                  ·
                    refine ⟨635871335898537508267411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3391313791458866710759525 635871335898537508267411)
                    ·
                      rfl

theorem cell23_3715065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_3715065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715065 prefixEnd_3715065 := by exact prefixLift 3715065
  have htrace : WordTrace (prefixWord ++ tailWord_3715065) baseStart_3715065 baseEnd_3715065 := by
    simpa [prefixWord, tailWord_3715065, baseEnd_3715065] using wordTrace_append hprefix tailTrace_3715065
  have hstable : (prefixWord ++ tailWord_3715065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715065).length < 2 ^ (prefixWord ++ tailWord_3715065).sum := by decide
  have hdescent : baseEnd_3715065 < baseStart_3715065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715068 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3715068 : Nat := 118140960795 + 3715068 * 2 ^ 59
def prefixEnd_3715068 : Nat := 4983230072969 + 3 ^ 40 * 3715068 * 2
def baseEnd_3715068 : Nat := 1907615548137576013064719

theorem tailTrace_3715068 : CollatzResearch.WordTrace tailWord_3715068 prefixEnd_3715068 1907615548137576013064719 := by
  unfold tailWord_3715068
  simp only [CollatzResearch.WordTrace]
  refine ⟨67749830852475296972864929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90333107803300395963819905 67749830852475296972864929)
  ·
    refine ⟨50812373139356472729648697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67749830852475296972864929 50812373139356472729648697)
    ·
      refine ⟨38109279854517354547236523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50812373139356472729648697 38109279854517354547236523)
      ·
        refine ⟨57163919781776031820854785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38109279854517354547236523 57163919781776031820854785)
        ·
          refine ⟨42872939836332023865641089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57163919781776031820854785 42872939836332023865641089)
          ·
            refine ⟨32154704877249017899230817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42872939836332023865641089 32154704877249017899230817)
            ·
              refine ⟨24116028657936763424423113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32154704877249017899230817 24116028657936763424423113)
              ·
                refine ⟨18087021493452572568317335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24116028657936763424423113 18087021493452572568317335)
                ·
                  refine ⟨27130532240178858852476003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18087021493452572568317335 27130532240178858852476003)
                  ·
                    refine ⟨40695798360268288278714005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27130532240178858852476003 40695798360268288278714005)
                    ·
                      refine ⟨1907615548137576013064719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40695798360268288278714005 1907615548137576013064719)
                      ·
                        rfl

theorem cell23_3715068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3715068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715068 prefixEnd_3715068 := by exact prefixLift 3715068
  have htrace : WordTrace (prefixWord ++ tailWord_3715068) baseStart_3715068 baseEnd_3715068 := by
    simpa [prefixWord, tailWord_3715068, baseEnd_3715068] using wordTrace_append hprefix tailTrace_3715068
  have hstable : (prefixWord ++ tailWord_3715068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715068).length < 2 ^ (prefixWord ++ tailWord_3715068).sum := by decide
  have hdescent : baseEnd_3715068 < baseStart_3715068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715082 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_3715082 : Nat := 118140960795 + 3715082 * 2 ^ 59
def prefixEnd_3715082 : Nat := 4983230072969 + 3 ^ 40 * 3715082 * 2
def baseEnd_3715082 : Nat := 635874245622246319429885

theorem tailTrace_3715082 : CollatzResearch.WordTrace tailWord_3715082 prefixEnd_3715082 635874245622246319429885 := by
  unfold tailWord_3715082
  simp only [CollatzResearch.WordTrace]
  refine ⟨33875043081724968584184875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90333448217933249557826333 33875043081724968584184875)
  ·
    refine ⟨50812564622587452876277313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33875043081724968584184875 50812564622587452876277313)
    ·
      refine ⟨38109423466940589657207985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50812564622587452876277313 38109423466940589657207985)
      ·
        refine ⟨28582067600205442242905989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38109423466940589657207985 28582067600205442242905989)
        ·
          refine ⟨5359137675038520420544873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28582067600205442242905989 5359137675038520420544873)
          ·
            refine ⟨4019353256278890315408655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5359137675038520420544873 4019353256278890315408655)
            ·
              refine ⟨6029029884418335473112983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019353256278890315408655 6029029884418335473112983)
              ·
                refine ⟨9043544826627503209669475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029029884418335473112983 9043544826627503209669475)
                ·
                  refine ⟨13565317239941254814504213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9043544826627503209669475 13565317239941254814504213)
                  ·
                    refine ⟨635874245622246319429885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13565317239941254814504213 635874245622246319429885)
                    ·
                      rfl

theorem cell23_3715082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_3715082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715082 prefixEnd_3715082 := by exact prefixLift 3715082
  have htrace : WordTrace (prefixWord ++ tailWord_3715082) baseStart_3715082 baseEnd_3715082 := by
    simpa [prefixWord, tailWord_3715082, baseEnd_3715082] using wordTrace_append hprefix tailTrace_3715082
  have hstable : (prefixWord ++ tailWord_3715082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715082).length < 2 ^ (prefixWord ++ tailWord_3715082).sum := by decide
  have hdescent : baseEnd_3715082 < baseStart_3715082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715095 : List Nat := [1, 1, 3, 5, 2, 1, 1, 9]
def baseStart_3715095 : Nat := 118140960795 + 3715095 * 2 ^ 59
def prefixEnd_3715095 : Nat := 4983230072969 + 3 ^ 40 * 3715095 * 2
def baseEnd_3715095 : Nat := 70652941189453607682485

theorem tailTrace_3715095 : CollatzResearch.WordTrace tailWord_3715095 prefixEnd_3715095 70652941189453607682485 := by
  unfold tailWord_3715095
  simp only [CollatzResearch.WordTrace]
  refine ⟨135500646475852777556962739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90333764317235185037975159 135500646475852777556962739)
  ·
    refine ⟨203250969713779166335444109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135500646475852777556962739 203250969713779166335444109)
    ·
      refine ⟨76219113642667187375791541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203250969713779166335444109 76219113642667187375791541)
      ·
        refine ⟨7145541904000048816480457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76219113642667187375791541 7145541904000048816480457)
        ·
          refine ⟨5359156428000036612360343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7145541904000048816480457 5359156428000036612360343)
          ·
            refine ⟨8038734642000054918540515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359156428000036612360343 8038734642000054918540515)
            ·
              refine ⟨12058101963000082377810773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038734642000054918540515 12058101963000082377810773)
              ·
                refine ⟨70652941189453607682485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12058101963000082377810773 70652941189453607682485)
                ·
                  rfl

theorem cell23_3715095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 9].length) (baseStart_3715095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715095 prefixEnd_3715095 := by exact prefixLift 3715095
  have htrace : WordTrace (prefixWord ++ tailWord_3715095) baseStart_3715095 baseEnd_3715095 := by
    simpa [prefixWord, tailWord_3715095, baseEnd_3715095] using wordTrace_append hprefix tailTrace_3715095
  have hstable : (prefixWord ++ tailWord_3715095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715095).length < 2 ^ (prefixWord ++ tailWord_3715095).sum := by decide
  have hdescent : baseEnd_3715095 < baseStart_3715095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715112 : List Nat := [2, 1, 5, 3, 1, 2, 9]
def baseStart_3715112 : Nat := 118140960795 + 3715112 * 2 ^ 59
def prefixEnd_3715112 : Nat := 4983230072969 + 3 ^ 40 * 3715112 * 2
def baseEnd_3715112 : Nat := 23551088164029306677957

theorem tailTrace_3715112 : CollatzResearch.WordTrace tailWord_3715112 prefixEnd_3715112 23551088164029306677957 := by
  unfold tailWord_3715112
  simp only [CollatzResearch.WordTrace]
  refine ⟨67750633258395594730165795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90334177677860792973554393 67750633258395594730165795)
  ·
    refine ⟨101625949887593392095248693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67750633258395594730165795 101625949887593392095248693)
    ·
      refine ⟨9527432801961880508929565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101625949887593392095248693 9527432801961880508929565)
      ·
        refine ⟨3572787300735705190848587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9527432801961880508929565 3572787300735705190848587)
        ·
          refine ⟨5359180951103557786272881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572787300735705190848587 5359180951103557786272881)
          ·
            refine ⟨4019385713327668339704661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5359180951103557786272881 4019385713327668339704661)
            ·
              refine ⟨23551088164029306677957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4019385713327668339704661 23551088164029306677957)
              ·
                rfl

theorem cell23_3715112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 9].length) (baseStart_3715112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715112 prefixEnd_3715112 := by exact prefixLift 3715112
  have htrace : WordTrace (prefixWord ++ tailWord_3715112) baseStart_3715112 baseEnd_3715112 := by
    simpa [prefixWord, tailWord_3715112, baseEnd_3715112] using wordTrace_append hprefix tailTrace_3715112
  have hstable : (prefixWord ++ tailWord_3715112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715112).length < 2 ^ (prefixWord ++ tailWord_3715112).sum := by decide
  have hdescent : baseEnd_3715112 < baseStart_3715112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715122 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_3715122 : Nat := 118140960795 + 3715122 * 2 ^ 59
def prefixEnd_3715122 : Nat := 4983230072969 + 3 ^ 40 * 3715122 * 2
def baseEnd_3715122 : Nat := 1907643276092918801789471

theorem tailTrace_3715122 : CollatzResearch.WordTrace tailWord_3715122 prefixEnd_3715122 1907643276092918801789471 := by
  unfold tailWord_3715122
  simp only [CollatzResearch.WordTrace]
  refine ⟨33875407811688740292048905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90334420831169974112130413 33875407811688740292048905)
  ·
    refine ⟨25406555858766555219036679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33875407811688740292048905 25406555858766555219036679)
    ·
      refine ⟨38109833788149832828555019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25406555858766555219036679 38109833788149832828555019)
      ·
        refine ⟨57164750682224749242832529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38109833788149832828555019 57164750682224749242832529)
        ·
          refine ⟨42873563011668561932124397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57164750682224749242832529 42873563011668561932124397)
          ·
            refine ⟨16077586129375710724546649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42873563011668561932124397 16077586129375710724546649)
            ·
              refine ⟨12058189597031783043409987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16077586129375710724546649 12058189597031783043409987)
              ·
                refine ⟨18087284395547674565114981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058189597031783043409987 18087284395547674565114981)
                ·
                  refine ⟨3391365824165188980959059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18087284395547674565114981 3391365824165188980959059)
                  ·
                    refine ⟨5087048736247783471438589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3391365824165188980959059 5087048736247783471438589)
                    ·
                      refine ⟨1907643276092918801789471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5087048736247783471438589 1907643276092918801789471)
                      ·
                        rfl

theorem cell23_3715122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_3715122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715122 prefixEnd_3715122 := by exact prefixLift 3715122
  have htrace : WordTrace (prefixWord ++ tailWord_3715122) baseStart_3715122 baseEnd_3715122 := by
    simpa [prefixWord, tailWord_3715122, baseEnd_3715122] using wordTrace_append hprefix tailTrace_3715122
  have hstable : (prefixWord ++ tailWord_3715122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715122).length < 2 ^ (prefixWord ++ tailWord_3715122).sum := by decide
  have hdescent : baseEnd_3715122 < baseStart_3715122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715132 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_3715132 : Nat := 118140960795 + 3715132 * 2 ^ 59
def prefixEnd_3715132 : Nat := 4983230072969 + 3 ^ 40 * 3715132 * 2
def baseEnd_3715132 : Nat := 1907648410899463762664425

theorem tailTrace_3715132 : CollatzResearch.WordTrace tailWord_3715132 prefixEnd_3715132 1907648410899463762664425 := by
  unfold tailWord_3715132
  simp only [CollatzResearch.WordTrace]
  refine ⟨67750997988359366438029825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90334663984479155250706433 67750997988359366438029825)
  ·
    refine ⟨50813248491269524828522369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67750997988359366438029825 50813248491269524828522369)
    ·
      refine ⟨38109936368452143621391777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50813248491269524828522369 38109936368452143621391777)
      ·
        refine ⟨28582452276339107716043833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38109936368452143621391777 28582452276339107716043833)
        ·
          refine ⟨21436839207254330787032875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28582452276339107716043833 21436839207254330787032875)
          ·
            refine ⟨32155258810881496180549313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21436839207254330787032875 32155258810881496180549313)
            ·
              refine ⟨24116444108161122135411985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32155258810881496180549313 24116444108161122135411985)
              ·
                refine ⟨18087333081120841601558989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24116444108161122135411985 18087333081120841601558989)
                ·
                  refine ⟨6782749905420315600584621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18087333081120841601558989 6782749905420315600584621)
                  ·
                    refine ⟨2543531214532618350219233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6782749905420315600584621 2543531214532618350219233)
                    ·
                      refine ⟨1907648410899463762664425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543531214532618350219233 1907648410899463762664425)
                      ·
                        rfl

theorem cell23_3715132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_3715132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715132 prefixEnd_3715132 := by exact prefixLift 3715132
  have htrace : WordTrace (prefixWord ++ tailWord_3715132) baseStart_3715132 baseEnd_3715132 := by
    simpa [prefixWord, tailWord_3715132, baseEnd_3715132] using wordTrace_append hprefix tailTrace_3715132
  have hstable : (prefixWord ++ tailWord_3715132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715132).length < 2 ^ (prefixWord ++ tailWord_3715132).sum := by decide
  have hdescent : baseEnd_3715132 < baseStart_3715132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715149 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_3715149 : Nat := 118140960795 + 3715149 * 2 ^ 59
def prefixEnd_3715149 : Nat := 4983230072969 + 3 ^ 40 * 3715149 * 2
def baseEnd_3715149 : Nat := 1907657140070590196151847

theorem tailTrace_3715149 : CollatzResearch.WordTrace tailWord_3715149 prefixEnd_3715149 1907657140070590196151847 := by
  unfold tailWord_3715149
  simp only [CollatzResearch.WordTrace]
  refine ⟨135502616017657144779428501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90335077345104763186285667 135502616017657144779428501)
  ·
    refine ⟨6351685125827678661535711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135502616017657144779428501 6351685125827678661535711)
    ·
      refine ⟨9527527688741517992303567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351685125827678661535711 9527527688741517992303567)
      ·
        refine ⟨14291291533112276988455351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9527527688741517992303567 14291291533112276988455351)
        ·
          refine ⟨21436937299668415482683027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14291291533112276988455351 21436937299668415482683027)
          ·
            refine ⟨32155405949502623224024541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21436937299668415482683027 32155405949502623224024541)
            ·
              refine ⟨12058277231063483709009203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32155405949502623224024541 12058277231063483709009203)
              ·
                refine ⟨18087415846595225563513805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058277231063483709009203 18087415846595225563513805)
                ·
                  refine ⟨6782780942473209586317677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18087415846595225563513805 6782780942473209586317677)
                  ·
                    refine ⟨2543542853427453594869129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6782780942473209586317677 2543542853427453594869129)
                    ·
                      refine ⟨1907657140070590196151847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543542853427453594869129 1907657140070590196151847)
                      ·
                        rfl

theorem cell23_3715149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_3715149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715149 prefixEnd_3715149 := by exact prefixLift 3715149
  have htrace : WordTrace (prefixWord ++ tailWord_3715149) baseStart_3715149 baseEnd_3715149 := by
    simpa [prefixWord, tailWord_3715149, baseEnd_3715149] using wordTrace_append hprefix tailTrace_3715149
  have hstable : (prefixWord ++ tailWord_3715149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715149).length < 2 ^ (prefixWord ++ tailWord_3715149).sum := by decide
  have hdescent : baseEnd_3715149 < baseStart_3715149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715162 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2]
def baseStart_3715162 : Nat := 118140960795 + 3715162 * 2 ^ 59
def prefixEnd_3715162 : Nat := 4983230072969 + 3 ^ 40 * 3715162 * 2
def baseEnd_3715162 : Nat := 1907663815319098645289287

theorem tailTrace_3715162 : CollatzResearch.WordTrace tailWord_3715162 prefixEnd_3715162 1907663815319098645289287 := by
  unfold tailWord_3715162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33875772541652511999912935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90335393444406698666434493 33875772541652511999912935)
  ·
    refine ⟨50813658812478767999869403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33875772541652511999912935 50813658812478767999869403)
    ·
      refine ⟨76220488218718151999804105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50813658812478767999869403 76220488218718151999804105)
      ·
        refine ⟨57165366164038613999853079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76220488218718151999804105 57165366164038613999853079)
        ·
          refine ⟨85748049246057920999779619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57165366164038613999853079 85748049246057920999779619)
          ·
            refine ⟨128622073869086881499669429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85748049246057920999779619 128622073869086881499669429)
            ·
              refine ⟨12058319425226895140594009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128622073869086881499669429 12058319425226895140594009)
              ·
                refine ⟨9043739568920171355445507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12058319425226895140594009 9043739568920171355445507)
                ·
                  refine ⟨13565609353380257033168261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9043739568920171355445507 13565609353380257033168261)
                  ·
                    refine ⟨2543551753758798193719049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13565609353380257033168261 2543551753758798193719049)
                    ·
                      refine ⟨1907663815319098645289287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543551753758798193719049 1907663815319098645289287)
                      ·
                        rfl

theorem cell23_3715162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_3715162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715162 prefixEnd_3715162 := by exact prefixLift 3715162
  have htrace : WordTrace (prefixWord ++ tailWord_3715162) baseStart_3715162 baseEnd_3715162 := by
    simpa [prefixWord, tailWord_3715162, baseEnd_3715162] using wordTrace_append hprefix tailTrace_3715162
  have hstable : (prefixWord ++ tailWord_3715162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715162).length < 2 ^ (prefixWord ++ tailWord_3715162).sum := by decide
  have hdescent : baseEnd_3715162 < baseStart_3715162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715175 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_3715175 : Nat := 118140960795 + 3715175 * 2 ^ 59
def prefixEnd_3715175 : Nat := 4983230072969 + 3 ^ 40 * 3715175 * 2
def baseEnd_3715175 : Nat := 1907670490567607094426727

theorem tailTrace_3715175 : CollatzResearch.WordTrace tailWord_3715175 prefixEnd_3715175 1907670490567607094426727 := by
  unfold tailWord_3715175
  simp only [CollatzResearch.WordTrace]
  refine ⟨135503564315562951219874979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90335709543708634146583319 135503564315562951219874979)
  ·
    refine ⟨203255346473344426829812469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135503564315562951219874979 203255346473344426829812469)
    ·
      refine ⟨19055188731876040015294919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203255346473344426829812469 19055188731876040015294919)
      ·
        refine ⟨28582783097814060022942379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19055188731876040015294919 28582783097814060022942379)
        ·
          refine ⟨42874174646721090034413569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28582783097814060022942379 42874174646721090034413569)
          ·
            refine ⟨32155630985040817525810177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42874174646721090034413569 32155630985040817525810177)
            ·
              refine ⟨24116723238780613144357633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32155630985040817525810177 24116723238780613144357633)
              ·
                refine ⟨18087542429085459858268225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24116723238780613144357633 18087542429085459858268225)
                ·
                  refine ⟨13565656821814094893701169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18087542429085459858268225 13565656821814094893701169)
                  ·
                    refine ⟨10174242616360571170275877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13565656821814094893701169 10174242616360571170275877)
                    ·
                      refine ⟨1907670490567607094426727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10174242616360571170275877 1907670490567607094426727)
                      ·
                        rfl

theorem cell23_3715175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_3715175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715175 prefixEnd_3715175 := by exact prefixLift 3715175
  have htrace : WordTrace (prefixWord ++ tailWord_3715175) baseStart_3715175 baseEnd_3715175 := by
    simpa [prefixWord, tailWord_3715175, baseEnd_3715175] using wordTrace_append hprefix tailTrace_3715175
  have hstable : (prefixWord ++ tailWord_3715175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715175).length < 2 ^ (prefixWord ++ tailWord_3715175).sum := by decide
  have hdescent : baseEnd_3715175 < baseStart_3715175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715230 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_3715230 : Nat := 118140960795 + 3715230 * 2 ^ 59
def prefixEnd_3715230 : Nat := 4983230072969 + 3 ^ 40 * 3715230 * 2
def baseEnd_3715230 : Nat := 1907698732003604379238975

theorem tailTrace_3715230 : CollatzResearch.WordTrace tailWord_3715230 prefixEnd_3715230 1907698732003604379238975 := by
  unfold tailWord_3715230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16938196291295461951640893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90337046886909130408751429 16938196291295461951640893)
  ·
    refine ⟨6351823609235798231865335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16938196291295461951640893 6351823609235798231865335)
    ·
      refine ⟨9527735413853697347798003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351823609235798231865335 9527735413853697347798003)
      ·
        refine ⟨14291603120780546021697005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9527735413853697347798003 14291603120780546021697005)
        ·
          refine ⟨5359351170292704758136377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14291603120780546021697005 5359351170292704758136377)
          ·
            refine ⟨4019513377719528568602283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5359351170292704758136377 4019513377719528568602283)
            ·
              refine ⟨6029270066579292852903425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019513377719528568602283 6029270066579292852903425)
              ·
                refine ⟨4521952549934469639677569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6029270066579292852903425 4521952549934469639677569)
                ·
                  refine ⟨3391464412450852229758177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4521952549934469639677569 3391464412450852229758177)
                  ·
                    refine ⟨2543598309338139172318633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3391464412450852229758177 2543598309338139172318633)
                    ·
                      refine ⟨1907698732003604379238975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543598309338139172318633 1907698732003604379238975)
                      ·
                        rfl

theorem cell23_3715230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_3715230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715230 prefixEnd_3715230 := by exact prefixLift 3715230
  have htrace : WordTrace (prefixWord ++ tailWord_3715230) baseStart_3715230 baseEnd_3715230 := by
    simpa [prefixWord, tailWord_3715230, baseEnd_3715230] using wordTrace_append hprefix tailTrace_3715230
  have hstable : (prefixWord ++ tailWord_3715230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715230).length < 2 ^ (prefixWord ++ tailWord_3715230).sum := by decide
  have hdescent : baseEnd_3715230 < baseStart_3715230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715272 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_3715272 : Nat := 118140960795 + 3715272 * 2 ^ 59
def prefixEnd_3715272 : Nat := 4983230072969 + 3 ^ 40 * 3715272 * 2
def baseEnd_3715272 : Nat := 1907720298191093214913781

theorem tailTrace_3715272 : CollatzResearch.WordTrace tailWord_3715272 prefixEnd_3715272 1907720298191093214913781 := by
  unfold tailWord_3715272
  simp only [CollatzResearch.WordTrace]
  refine ⟨67753551098105768393078035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90338068130807691190770713 67753551098105768393078035)
  ·
    refine ⟨101630326647158652589617053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67753551098105768393078035 101630326647158652589617053)
    ·
      refine ⟨38111372492684494721106395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101630326647158652589617053 38111372492684494721106395)
      ·
        refine ⟨57167058739026742081659593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38111372492684494721106395 57167058739026742081659593)
        ·
          refine ⟨42875294054270056561244695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57167058739026742081659593 42875294054270056561244695)
          ·
            refine ⟨64312941081405084841867043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42875294054270056561244695 64312941081405084841867043)
            ·
              refine ⟨96469411622107627262800565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64312941081405084841867043 96469411622107627262800565)
              ·
                refine ⟨9044007339572590055887553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96469411622107627262800565 9044007339572590055887553)
                ·
                  refine ⟨6783005504679442541915665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9044007339572590055887553 6783005504679442541915665)
                  ·
                    refine ⟨5087254128509581906436749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6783005504679442541915665 5087254128509581906436749)
                    ·
                      refine ⟨1907720298191093214913781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5087254128509581906436749 1907720298191093214913781)
                      ·
                        rfl

theorem cell23_3715272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_3715272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715272 prefixEnd_3715272 := by exact prefixLift 3715272
  have htrace : WordTrace (prefixWord ++ tailWord_3715272) baseStart_3715272 baseEnd_3715272 := by
    simpa [prefixWord, tailWord_3715272, baseEnd_3715272] using wordTrace_append hprefix tailTrace_3715272
  have hstable : (prefixWord ++ tailWord_3715272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715272).length < 2 ^ (prefixWord ++ tailWord_3715272).sum := by decide
  have hdescent : baseEnd_3715272 < baseStart_3715272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715286 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3715286 : Nat := 118140960795 + 3715286 * 2 ^ 59
def prefixEnd_3715286 : Nat := 4983230072969 + 3 ^ 40 * 3715286 * 2
def baseEnd_3715286 : Nat := 1907727486920256160138717

theorem tailTrace_3715286 : CollatzResearch.WordTrace tailWord_3715286 prefixEnd_3715286 1907727486920256160138717 := by
  unfold tailWord_3715286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8469225801135051073572857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90338408545440544784777141 8469225801135051073572857)
  ·
    refine ⟨6351919350851288305179643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8469225801135051073572857 6351919350851288305179643)
    ·
      refine ⟨9527879026276932457769465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351919350851288305179643 9527879026276932457769465)
      ·
        refine ⟨7145909269707699343327099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9527879026276932457769465 7145909269707699343327099)
        ·
          refine ⟨10718863904561549014990649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145909269707699343327099 10718863904561549014990649)
          ·
            refine ⟨8039147928421161761242987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10718863904561549014990649 8039147928421161761242987)
            ·
              refine ⟨12058721892631742641864481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039147928421161761242987 12058721892631742641864481)
              ·
                refine ⟨9044041419473806981398361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12058721892631742641864481 9044041419473806981398361)
                ·
                  refine ⟨6783031064605355236048771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9044041419473806981398361 6783031064605355236048771)
                  ·
                    refine ⟨10174546596908032854073157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6783031064605355236048771 10174546596908032854073157)
                    ·
                      refine ⟨1907727486920256160138717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10174546596908032854073157 1907727486920256160138717)
                      ·
                        rfl

theorem cell23_3715286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3715286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715286 prefixEnd_3715286 := by exact prefixLift 3715286
  have htrace : WordTrace (prefixWord ++ tailWord_3715286) baseStart_3715286 baseEnd_3715286 := by
    simpa [prefixWord, tailWord_3715286, baseEnd_3715286] using wordTrace_append hprefix tailTrace_3715286
  have hstable : (prefixWord ++ tailWord_3715286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715286).length < 2 ^ (prefixWord ++ tailWord_3715286).sum := by decide
  have hdescent : baseEnd_3715286 < baseStart_3715286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715296 : List Nat := [2, 1, 1, 3, 1, 3, 5, 2, 1, 4]
def baseStart_3715296 : Nat := 118140960795 + 3715296 * 2 ^ 59
def prefixEnd_3715296 : Nat := 4983230072969 + 3 ^ 40 * 3715296 * 2
def baseEnd_3715296 : Nat := 635910873908933707004557

theorem tailTrace_3715296 : CollatzResearch.WordTrace tailWord_3715296 prefixEnd_3715296 635910873908933707004557 := by
  unfold tailWord_3715296
  simp only [CollatzResearch.WordTrace]
  refine ⟨67753988774062294442514871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90338651698749725923353161 67753988774062294442514871)
  ·
    refine ⟨101630983161093441663772307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67753988774062294442514871 101630983161093441663772307)
    ·
      refine ⟨152446474741640162495658461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101630983161093441663772307 152446474741640162495658461)
      ·
        refine ⟨57167428028115060935871923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152446474741640162495658461 57167428028115060935871923)
        ·
          refine ⟨85751142042172591403807885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57167428028115060935871923 85751142042172591403807885)
          ·
            refine ⟨32156678265814721776427957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85751142042172591403807885 32156678265814721776427957)
            ·
              refine ⟨3014688587420130166540121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32156678265814721776427957 3014688587420130166540121)
              ·
                refine ⟨2261016440565097624905091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3014688587420130166540121 2261016440565097624905091)
                ·
                  refine ⟨3391524660847646437357637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261016440565097624905091 3391524660847646437357637)
                  ·
                    refine ⟨635910873908933707004557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3391524660847646437357637 635910873908933707004557)
                    ·
                      rfl

theorem cell23_3715296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 4].length) (baseStart_3715296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715296 prefixEnd_3715296 := by exact prefixLift 3715296
  have htrace : WordTrace (prefixWord ++ tailWord_3715296) baseStart_3715296 baseEnd_3715296 := by
    simpa [prefixWord, tailWord_3715296, baseEnd_3715296] using wordTrace_append hprefix tailTrace_3715296
  have hstable : (prefixWord ++ tailWord_3715296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715296).length < 2 ^ (prefixWord ++ tailWord_3715296).sum := by decide
  have hdescent : baseEnd_3715296 < baseStart_3715296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715305 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 5, 5]
def baseStart_3715305 : Nat := 118140960795 + 3715305 * 2 ^ 59
def prefixEnd_3715305 : Nat := 4983230072969 + 3 ^ 40 * 3715305 * 2
def baseEnd_3715305 : Nat := 635912414350897195267043

theorem tailTrace_3715305 : CollatzResearch.WordTrace tailWord_3715305 prefixEnd_3715305 635912414350897195267043 := by
  unfold tailWord_3715305
  simp only [CollatzResearch.WordTrace]
  refine ⟨135508305805091983422107369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90338870536727988948071579 135508305805091983422107369)
  ·
    refine ⟨101631229353818987566580527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135508305805091983422107369 101631229353818987566580527)
    ·
      refine ⟨152446844030728481349870791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101631229353818987566580527 152446844030728481349870791)
      ·
        refine ⟨228670266046092722024806187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152446844030728481349870791 228670266046092722024806187)
        ·
          refine ⟨343005399069139083037209281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228670266046092722024806187 343005399069139083037209281)
          ·
            refine ⟨257254049301854312277906961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343005399069139083037209281 257254049301854312277906961)
            ·
              refine ⟨192940536976390734208430221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257254049301854312277906961 192940536976390734208430221)
              ·
                refine ⟨72352701366146525328161333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192940536976390734208430221 72352701366146525328161333)
                ·
                  refine ⟨6783065753076236749515125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72352701366146525328161333 6783065753076236749515125)
                  ·
                    refine ⟨635912414350897195267043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6783065753076236749515125 635912414350897195267043)
                    ·
                      rfl

theorem cell23_3715305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_3715305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715305 prefixEnd_3715305 := by exact prefixLift 3715305
  have htrace : WordTrace (prefixWord ++ tailWord_3715305) baseStart_3715305 baseEnd_3715305 := by
    simpa [prefixWord, tailWord_3715305, baseEnd_3715305] using wordTrace_append hprefix tailTrace_3715305
  have hstable : (prefixWord ++ tailWord_3715305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715305).length < 2 ^ (prefixWord ++ tailWord_3715305).sum := by decide
  have hdescent : baseEnd_3715305 < baseStart_3715305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715309 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 6]
def baseStart_3715309 : Nat := 118140960795 + 3715309 * 2 ^ 59
def prefixEnd_3715309 : Nat := 4983230072969 + 3 ^ 40 * 3715309 * 2
def baseEnd_3715309 : Nat := 211971032997256618905679

theorem tailTrace_3715309 : CollatzResearch.WordTrace tailWord_3715309 prefixEnd_3715309 211971032997256618905679 := by
  unfold tailWord_3715309
  simp only [CollatzResearch.WordTrace]
  refine ⟨135508451697077492105252981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90338967798051661403501987 135508451697077492105252981)
  ·
    refine ⟨12703917346601014884867467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135508451697077492105252981 12703917346601014884867467)
    ·
      refine ⟨19055876019901522327301201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703917346601014884867467 19055876019901522327301201)
      ·
        refine ⟨14291907014926141745475901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19055876019901522327301201 14291907014926141745475901)
        ·
          refine ⟨5359465130597303154553463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14291907014926141745475901 5359465130597303154553463)
          ·
            refine ⟨8039197695895954731830195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359465130597303154553463 8039197695895954731830195)
            ·
              refine ⟨12058796543843932097745293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039197695895954731830195 12058796543843932097745293)
              ·
                refine ⟨4522048703941474536654485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12058796543843932097745293 4522048703941474536654485)
                ·
                  refine ⟨211971032997256618905679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4522048703941474536654485 211971032997256618905679)
                  ·
                    rfl

theorem cell23_3715309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_3715309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715309 prefixEnd_3715309 := by exact prefixLift 3715309
  have htrace : WordTrace (prefixWord ++ tailWord_3715309) baseStart_3715309 baseEnd_3715309 := by
    simpa [prefixWord, tailWord_3715309, baseEnd_3715309] using wordTrace_append hprefix tailTrace_3715309
  have hstable : (prefixWord ++ tailWord_3715309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715309).length < 2 ^ (prefixWord ++ tailWord_3715309).sum := by decide
  have hdescent : baseEnd_3715309 < baseStart_3715309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715312 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 3, 5, 2]
def baseStart_3715312 : Nat := 118140960795 + 3715312 * 2 ^ 59
def prefixEnd_3715312 : Nat := 4983230072969 + 3 ^ 40 * 3715312 * 2
def baseEnd_3715312 : Nat := 1907740837417273058413597

theorem tailTrace_3715312 : CollatzResearch.WordTrace tailWord_3715312 prefixEnd_3715312 1907740837417273058413597 := by
  unfold tailWord_3715312
  simp only [CollatzResearch.WordTrace]
  refine ⟨67754280558033311808806095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90339040744044415745074793 67754280558033311808806095)
  ·
    refine ⟨101631420837049967713209143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67754280558033311808806095 101631420837049967713209143)
    ·
      refine ⟨152447131255574951569813715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101631420837049967713209143 152447131255574951569813715)
      ·
        refine ⟨228670696883362427354720573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152447131255574951569813715 228670696883362427354720573)
        ·
          refine ⟨85751511331260910258020215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228670696883362427354720573 85751511331260910258020215)
          ·
            refine ⟨128627266996891365387030323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85751511331260910258020215 128627266996891365387030323)
            ·
              refine ⟨192940900495337048080545485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128627266996891365387030323 192940900495337048080545485)
              ·
                refine ⟨72352837685751393030204557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192940900495337048080545485 72352837685751393030204557)
                ·
                  refine ⟨27132314132156772386326709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72352837685751393030204557 27132314132156772386326709)
                  ·
                    refine ⟨2543654449889697411218129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27132314132156772386326709 2543654449889697411218129)
                    ·
                      refine ⟨1907740837417273058413597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543654449889697411218129 1907740837417273058413597)
                      ·
                        rfl

theorem cell23_3715312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 5, 2].length) (baseStart_3715312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715312 prefixEnd_3715312 := by exact prefixLift 3715312
  have htrace : WordTrace (prefixWord ++ tailWord_3715312) baseStart_3715312 baseEnd_3715312 := by
    simpa [prefixWord, tailWord_3715312, baseEnd_3715312] using wordTrace_append hprefix tailTrace_3715312
  have hstable : (prefixWord ++ tailWord_3715312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715312).length < 2 ^ (prefixWord ++ tailWord_3715312).sum := by decide
  have hdescent : baseEnd_3715312 < baseStart_3715312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715322 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_3715322 : Nat := 118140960795 + 3715322 * 2 ^ 59
def prefixEnd_3715322 : Nat := 4983230072969 + 3 ^ 40 * 3715322 * 2
def baseEnd_3715322 : Nat := 635915324074606006429517

theorem tailTrace_3715322 : CollatzResearch.WordTrace tailWord_3715322 prefixEnd_3715322 635915324074606006429517 := by
  unfold tailWord_3715322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33877231461507598831369055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90339283897353596883650813 33877231461507598831369055)
  ·
    refine ⟨50815847192261398247053583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33877231461507598831369055 50815847192261398247053583)
    ·
      refine ⟨76223770788392097370580375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50815847192261398247053583 76223770788392097370580375)
      ·
        refine ⟨114335656182588146055870563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76223770788392097370580375 114335656182588146055870563)
        ·
          refine ⟨171503484273882219083805845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114335656182588146055870563 171503484273882219083805845)
          ·
            refine ⟨8039225825338229019553399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171503484273882219083805845 8039225825338229019553399)
            ·
              refine ⟨12058838738007343529330099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8039225825338229019553399 12058838738007343529330099)
              ·
                refine ⟨18088258107011015293995149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12058838738007343529330099 18088258107011015293995149)
                ·
                  refine ⟨6783096790129130735248181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18088258107011015293995149 6783096790129130735248181)
                  ·
                    refine ⟨635915324074606006429517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6783096790129130735248181 635915324074606006429517)
                    ·
                      rfl

theorem cell23_3715322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_3715322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715322 prefixEnd_3715322 := by exact prefixLift 3715322
  have htrace : WordTrace (prefixWord ++ tailWord_3715322) baseStart_3715322 baseEnd_3715322 := by
    simpa [prefixWord, tailWord_3715322, baseEnd_3715322] using wordTrace_append hprefix tailTrace_3715322
  have hstable : (prefixWord ++ tailWord_3715322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715322).length < 2 ^ (prefixWord ++ tailWord_3715322).sum := by decide
  have hdescent : baseEnd_3715322 < baseStart_3715322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715339 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 1, 5]
def baseStart_3715339 : Nat := 118140960795 + 3715339 * 2 ^ 59
def prefixEnd_3715339 : Nat := 4983230072969 + 3 ^ 40 * 3715339 * 2
def baseEnd_3715339 : Nat := 635918233798314817591991

theorem tailTrace_3715339 : CollatzResearch.WordTrace tailWord_3715339 prefixEnd_3715339 635918233798314817591991 := by
  unfold tailWord_3715339
  simp only [CollatzResearch.WordTrace]
  refine ⟨135509545886968807228845071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90339697257979204819230047 135509545886968807228845071)
  ·
    refine ⟨203264318830453210843267607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135509545886968807228845071 203264318830453210843267607)
    ·
      refine ⟨304896478245679816264901411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203264318830453210843267607 304896478245679816264901411)
      ·
        refine ⟨457344717368519724397352117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304896478245679816264901411 457344717368519724397352117)
        ·
          refine ⟨42876067253298724162251761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 457344717368519724397352117 42876067253298724162251761)
          ·
            refine ⟨32157050439974043121688821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42876067253298724162251761 32157050439974043121688821)
            ·
              refine ⟨3014723478747566542658327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32157050439974043121688821 3014723478747566542658327)
              ·
                refine ⟨4522085218121349813987491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014723478747566542658327 4522085218121349813987491)
                ·
                  refine ⟨6783127827182024720981237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4522085218121349813987491 6783127827182024720981237)
                  ·
                    refine ⟨635918233798314817591991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6783127827182024720981237 635918233798314817591991)
                    ·
                      rfl

theorem cell23_3715339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 5].length) (baseStart_3715339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715339 prefixEnd_3715339 := by exact prefixLift 3715339
  have htrace : WordTrace (prefixWord ++ tailWord_3715339) baseStart_3715339 baseEnd_3715339 := by
    simpa [prefixWord, tailWord_3715339, baseEnd_3715339] using wordTrace_append hprefix tailTrace_3715339
  have hstable : (prefixWord ++ tailWord_3715339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715339).length < 2 ^ (prefixWord ++ tailWord_3715339).sum := by decide
  have hdescent : baseEnd_3715339 < baseStart_3715339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715355 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6]
def baseStart_3715355 : Nat := 118140960795 + 3715355 * 2 ^ 59
def prefixEnd_3715355 : Nat := 4983230072969 + 3 ^ 40 * 3715355 * 2
def baseEnd_3715355 : Nat := 1907762917085416390175899

theorem tailTrace_3715355 : CollatzResearch.WordTrace tailWord_3715355 prefixEnd_3715355 1907762917085416390175899 := by
  unfold tailWord_3715355
  simp only [CollatzResearch.WordTrace]
  refine ⟨135510129454910841961427519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90340086303273894640951679 135510129454910841961427519)
  ·
    refine ⟨203265194182366262942141279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135510129454910841961427519 203265194182366262942141279)
    ·
      refine ⟨304897791273549394413211919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203265194182366262942141279 304897791273549394413211919)
      ·
        refine ⟨457346686910324091619817879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304897791273549394413211919 457346686910324091619817879)
        ·
          refine ⟨686020030365486137429726819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457346686910324091619817879 686020030365486137429726819)
          ·
            refine ⟨1029030045548229206144590229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686020030365486137429726819 1029030045548229206144590229)
            ·
              refine ⟨48235783385073244038027667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1029030045548229206144590229 48235783385073244038027667)
              ·
                refine ⟨72353675077609866057041501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48235783385073244038027667 72353675077609866057041501)
                ·
                  refine ⟨27132628154103699771390563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72353675077609866057041501 27132628154103699771390563)
                  ·
                    refine ⟨40698942231155549657085845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27132628154103699771390563 40698942231155549657085845)
                    ·
                      refine ⟨1907762917085416390175899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40698942231155549657085845 1907762917085416390175899)
                      ·
                        rfl

theorem cell23_3715355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_3715355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715355 prefixEnd_3715355 := by exact prefixLift 3715355
  have htrace : WordTrace (prefixWord ++ tailWord_3715355) baseStart_3715355 baseEnd_3715355 := by
    simpa [prefixWord, tailWord_3715355, baseEnd_3715355] using wordTrace_append hprefix tailTrace_3715355
  have hstable : (prefixWord ++ tailWord_3715355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715355).length < 2 ^ (prefixWord ++ tailWord_3715355).sum := by decide
  have hdescent : baseEnd_3715355 < baseStart_3715355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715372 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_3715372 : Nat := 118140960795 + 3715372 * 2 ^ 59
def prefixEnd_3715372 : Nat := 4983230072969 + 3 ^ 40 * 3715372 * 2
def baseEnd_3715372 : Nat := 1907771646256542823663321

theorem tailTrace_3715372 : CollatzResearch.WordTrace tailWord_3715372 prefixEnd_3715372 1907771646256542823663321 := by
  unfold tailWord_3715372
  simp only [CollatzResearch.WordTrace]
  refine ⟨67755374747924626932398185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90340499663899502576530913 67755374747924626932398185)
  ·
    refine ⟨50816531060943470199298639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67755374747924626932398185 50816531060943470199298639)
    ·
      refine ⟨76224796591415205298947959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50816531060943470199298639 76224796591415205298947959)
      ·
        refine ⟨114337194887122807948421939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76224796591415205298947959 114337194887122807948421939)
        ·
          refine ⟨171505792330684211922632909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114337194887122807948421939 171505792330684211922632909)
          ·
            refine ⟨64314672124006579470987341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171505792330684211922632909 64314672124006579470987341)
            ·
              refine ⟨24118002046502467301620253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64314672124006579470987341 24118002046502467301620253)
              ·
                refine ⟨9044250767438425238107595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24118002046502467301620253 9044250767438425238107595)
                ·
                  refine ⟨13566376151157637857161393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9044250767438425238107595 13566376151157637857161393)
                  ·
                    refine ⟨10174782113368228392871045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13566376151157637857161393 10174782113368228392871045)
                    ·
                      refine ⟨1907771646256542823663321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10174782113368228392871045 1907771646256542823663321)
                      ·
                        rfl

theorem cell23_3715372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_3715372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715372 prefixEnd_3715372 := by exact prefixLift 3715372
  have htrace : WordTrace (prefixWord ++ tailWord_3715372) baseStart_3715372 baseEnd_3715372 := by
    simpa [prefixWord, tailWord_3715372, baseEnd_3715372] using wordTrace_append hprefix tailTrace_3715372
  have hstable : (prefixWord ++ tailWord_3715372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715372).length < 2 ^ (prefixWord ++ tailWord_3715372).sum := by decide
  have hdescent : baseEnd_3715372 < baseStart_3715372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715379 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 3]
def baseStart_3715379 : Nat := 118140960795 + 3715379 * 2 ^ 59
def prefixEnd_3715379 : Nat := 4983230072969 + 3 ^ 40 * 3715379 * 2
def baseEnd_3715379 : Nat := 1907775240621124296275789

theorem tailTrace_3715379 : CollatzResearch.WordTrace tailWord_3715379 prefixEnd_3715379 1907775240621124296275789 := by
  unfold tailWord_3715379
  simp only [CollatzResearch.WordTrace]
  refine ⟨135511004806823894060301191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90340669871215929373534127 135511004806823894060301191)
  ·
    refine ⟨203266507210235841090451787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135511004806823894060301191 203266507210235841090451787)
    ·
      refine ⟨304899760815353761635677681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203266507210235841090451787 304899760815353761635677681)
      ·
        refine ⟨228674820611515321226758261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304899760815353761635677681 228674820611515321226758261)
        ·
          refine ⟨21438264432329561365008587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228674820611515321226758261 21438264432329561365008587)
          ·
            refine ⟨32157396648494342047512881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21438264432329561365008587 32157396648494342047512881)
            ·
              refine ⟨24118047486370756535634661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32157396648494342047512881 24118047486370756535634661)
              ·
                refine ⟨4522133903694516850431499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24118047486370756535634661 4522133903694516850431499)
                ·
                  refine ⟨6783200855541775275647249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4522133903694516850431499 6783200855541775275647249)
                  ·
                    refine ⟨5087400641656331456735437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6783200855541775275647249 5087400641656331456735437)
                    ·
                      refine ⟨1907775240621124296275789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5087400641656331456735437 1907775240621124296275789)
                      ·
                        rfl

theorem cell23_3715379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 2, 3].length) (baseStart_3715379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715379 prefixEnd_3715379 := by exact prefixLift 3715379
  have htrace : WordTrace (prefixWord ++ tailWord_3715379) baseStart_3715379 baseEnd_3715379 := by
    simpa [prefixWord, tailWord_3715379, baseEnd_3715379] using wordTrace_append hprefix tailTrace_3715379
  have hstable : (prefixWord ++ tailWord_3715379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715379).length < 2 ^ (prefixWord ++ tailWord_3715379).sum := by decide
  have hdescent : baseEnd_3715379 < baseStart_3715379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715392 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3]
def baseStart_3715392 : Nat := 118140960795 + 3715392 * 2 ^ 59
def prefixEnd_3715392 : Nat := 4983230072969 + 3 ^ 40 * 3715392 * 2
def baseEnd_3715392 : Nat := 1907781915869632745413229

theorem tailTrace_3715392 : CollatzResearch.WordTrace tailWord_3715392 prefixEnd_3715392 1907781915869632745413229 := by
  unfold tailWord_3715392
  simp only [CollatzResearch.WordTrace]
  refine ⟨67755739477888398640262215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90340985970517864853682953 67755739477888398640262215)
  ·
    refine ⟨101633609216832597960393323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67755739477888398640262215 101633609216832597960393323)
    ·
      refine ⟨152450413825248896940589985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101633609216832597960393323 152450413825248896940589985)
      ·
        refine ⟨114337810368936672705442489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152450413825248896940589985 114337810368936672705442489)
        ·
          refine ⟨85753357776702504529081867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114337810368936672705442489 85753357776702504529081867)
          ·
            refine ⟨128630036665053756793622801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85753357776702504529081867 128630036665053756793622801)
            ·
              refine ⟨96472527498790317595217101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128630036665053756793622801 96472527498790317595217101)
              ·
                refine ⟨36177197812046369098206413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96472527498790317595217101 36177197812046369098206413)
                ·
                  refine ⟨13566449179517388411827405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36177197812046369098206413 13566449179517388411827405)
                  ·
                    refine ⟨5087418442319020654435277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13566449179517388411827405 5087418442319020654435277)
                    ·
                      refine ⟨1907781915869632745413229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5087418442319020654435277 1907781915869632745413229)
                      ·
                        rfl

theorem cell23_3715392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_3715392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715392 prefixEnd_3715392 := by exact prefixLift 3715392
  have htrace : WordTrace (prefixWord ++ tailWord_3715392) baseStart_3715392 baseEnd_3715392 := by
    simpa [prefixWord, tailWord_3715392, baseEnd_3715392] using wordTrace_append hprefix tailTrace_3715392
  have hstable : (prefixWord ++ tailWord_3715392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715392).length < 2 ^ (prefixWord ++ tailWord_3715392).sum := by decide
  have hdescent : baseEnd_3715392 < baseStart_3715392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715420 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_3715420 : Nat := 118140960795 + 3715420 * 2 ^ 59
def prefixEnd_3715420 : Nat := 4983230072969 + 3 ^ 40 * 3715420 * 2
def baseEnd_3715420 : Nat := 635932097775986211954367

theorem tailTrace_3715420 : CollatzResearch.WordTrace tailWord_3715420 prefixEnd_3715420 635932097775986211954367 := by
  unfold tailWord_3715420
  simp only [CollatzResearch.WordTrace]
  refine ⟨67756250099837679031271857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90341666799783572041695809 67756250099837679031271857)
  ·
    refine ⟨50817187574878259273453893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67756250099837679031271857 50817187574878259273453893)
    ·
      refine ⟨9528222670289673613772605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50817187574878259273453893 9528222670289673613772605)
      ·
        refine ⟨3573083501358627605164727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9528222670289673613772605 3573083501358627605164727)
        ·
          refine ⟨5359625252037941407747091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573083501358627605164727 5359625252037941407747091)
          ·
            refine ⟨8039437878056912111620637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359625252037941407747091 8039437878056912111620637)
            ·
              refine ⟨3014789204271342041857739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8039437878056912111620637 3014789204271342041857739)
              ·
                refine ⟨4522183806407013062786609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014789204271342041857739 4522183806407013062786609)
                ·
                  refine ⟨3391637854805259797089957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4522183806407013062786609 3391637854805259797089957)
                  ·
                    refine ⟨635932097775986211954367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3391637854805259797089957 635932097775986211954367)
                    ·
                      rfl

theorem cell23_3715420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_3715420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715420 prefixEnd_3715420 := by exact prefixLift 3715420
  have htrace : WordTrace (prefixWord ++ tailWord_3715420) baseStart_3715420 baseEnd_3715420 := by
    simpa [prefixWord, tailWord_3715420, baseEnd_3715420] using wordTrace_append hprefix tailTrace_3715420
  have hstable : (prefixWord ++ tailWord_3715420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715420).length < 2 ^ (prefixWord ++ tailWord_3715420).sum := by decide
  have hdescent : baseEnd_3715420 < baseStart_3715420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715426 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3715426 : Nat := 118140960795 + 3715426 * 2 ^ 59
def prefixEnd_3715426 : Nat := 4983230072969 + 3 ^ 40 * 3715426 * 2
def baseEnd_3715426 : Nat := 1907799374211885612388073

theorem tailTrace_3715426 : CollatzResearch.WordTrace tailWord_3715426 prefixEnd_3715426 1907799374211885612388073 := by
  unfold tailWord_3715426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33878179759413405271815533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90341812691769080724841421 33878179759413405271815533)
  ·
    refine ⟨12704317409780026976930825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33878179759413405271815533 12704317409780026976930825)
    ·
      refine ⟨9528238057335020232698119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12704317409780026976930825 9528238057335020232698119)
      ·
        refine ⟨14292357086002530349047179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9528238057335020232698119 14292357086002530349047179)
        ·
          refine ⟨21438535629003795523570769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14292357086002530349047179 21438535629003795523570769)
          ·
            refine ⟨16078901721752846642678077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21438535629003795523570769 16078901721752846642678077)
            ·
              refine ⟨6029588145657317491004279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16078901721752846642678077 6029588145657317491004279)
              ·
                refine ⟨9044382218485976236506419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029588145657317491004279 9044382218485976236506419)
                ·
                  refine ⟨13566573327728964354759629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9044382218485976236506419 13566573327728964354759629)
                  ·
                    refine ⟨5087464997898361633034861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13566573327728964354759629 5087464997898361633034861)
                    ·
                      refine ⟨1907799374211885612388073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5087464997898361633034861 1907799374211885612388073)
                      ·
                        rfl

theorem cell23_3715426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3715426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715426 prefixEnd_3715426 := by exact prefixLift 3715426
  have htrace : WordTrace (prefixWord ++ tailWord_3715426) baseStart_3715426 baseEnd_3715426 := by
    simpa [prefixWord, tailWord_3715426, baseEnd_3715426] using wordTrace_append hprefix tailTrace_3715426
  have hstable : (prefixWord ++ tailWord_3715426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715426).length < 2 ^ (prefixWord ++ tailWord_3715426).sum := by decide
  have hdescent : baseEnd_3715426 < baseStart_3715426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715449 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 3, 4, 2]
def baseStart_3715449 : Nat := 118140960795 + 3715449 * 2 ^ 59
def prefixEnd_3715449 : Nat := 4983230072969 + 3 ^ 40 * 3715449 * 2
def baseEnd_3715449 : Nat := 1907811184266939022400467

theorem tailTrace_3715449 : CollatzResearch.WordTrace tailWord_3715449 prefixEnd_3715449 1907811184266939022400467 := by
  unfold tailWord_3715449
  simp only [CollatzResearch.WordTrace]
  refine ⟨135513557916570296015349401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90342371944380197343566267 135513557916570296015349401)
  ·
    refine ⟨101635168437427722011512051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135513557916570296015349401 101635168437427722011512051)
    ·
      refine ⟨152452752656141583017268077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101635168437427722011512051 152452752656141583017268077)
      ·
        refine ⟨57169782246053093631475529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152452752656141583017268077 57169782246053093631475529)
        ·
          refine ⟨42877336684539820223606647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57169782246053093631475529 42877336684539820223606647)
          ·
            refine ⟨64316005026809730335409971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42877336684539820223606647 64316005026809730335409971)
            ·
              refine ⟨96474007540214595503114957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64316005026809730335409971 96474007540214595503114957)
              ·
                refine ⟨36177752827580473313668109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96474007540214595503114957 36177752827580473313668109)
                ·
                  refine ⟨13566657310342677492625541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36177752827580473313668109 13566657310342677492625541)
                  ·
                    refine ⟨2543748245689252029867289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13566657310342677492625541 2543748245689252029867289)
                    ·
                      refine ⟨1907811184266939022400467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543748245689252029867289 1907811184266939022400467)
                      ·
                        rfl

theorem cell23_3715449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_3715449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715449 prefixEnd_3715449 := by exact prefixLift 3715449
  have htrace : WordTrace (prefixWord ++ tailWord_3715449) baseStart_3715449 baseEnd_3715449 := by
    simpa [prefixWord, tailWord_3715449, baseEnd_3715449] using wordTrace_append hprefix tailTrace_3715449
  have hstable : (prefixWord ++ tailWord_3715449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715449).length < 2 ^ (prefixWord ++ tailWord_3715449).sum := by decide
  have hdescent : baseEnd_3715449 < baseStart_3715449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715486 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3715486 : Nat := 118140960795 + 3715486 * 2 ^ 59
def prefixEnd_3715486 : Nat := 4983230072969 + 3 ^ 40 * 3715486 * 2
def baseEnd_3715486 : Nat := 1907830183051155377637797

theorem tailTrace_3715486 : CollatzResearch.WordTrace tailWord_3715486 prefixEnd_3715486 1907830183051155377637797 := by
  unfold tailWord_3715486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16939363427179531416805789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90343271611624167556297541 16939363427179531416805789)
  ·
    refine ⟨6352261285192324281302171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16939363427179531416805789 6352261285192324281302171)
    ·
      refine ⟨9528391927788486421953257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6352261285192324281302171 9528391927788486421953257)
      ·
        refine ⟨7146293945841364816464943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9528391927788486421953257 7146293945841364816464943)
        ·
          refine ⟨10719440918762047224697415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7146293945841364816464943 10719440918762047224697415)
          ·
            refine ⟨16079161378143070837046123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10719440918762047224697415 16079161378143070837046123)
            ·
              refine ⟨24118742067214606255569185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16079161378143070837046123 24118742067214606255569185)
              ·
                refine ⟨18089056550410954691676889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24118742067214606255569185 18089056550410954691676889)
                ·
                  refine ⟨13566792412808216018757667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18089056550410954691676889 13566792412808216018757667)
                  ·
                    refine ⟨20350188619212324028136501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13566792412808216018757667 20350188619212324028136501)
                    ·
                      refine ⟨1907830183051155377637797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20350188619212324028136501 1907830183051155377637797)
                      ·
                        rfl

theorem cell23_3715486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3715486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715486 prefixEnd_3715486 := by exact prefixLift 3715486
  have htrace : WordTrace (prefixWord ++ tailWord_3715486) baseStart_3715486 baseEnd_3715486 := by
    simpa [prefixWord, tailWord_3715486, baseEnd_3715486] using wordTrace_append hprefix tailTrace_3715486
  have hstable : (prefixWord ++ tailWord_3715486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715486).length < 2 ^ (prefixWord ++ tailWord_3715486).sum := by decide
  have hdescent : baseEnd_3715486 < baseStart_3715486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715590 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3715590 : Nat := 118140960795 + 3715590 * 2 ^ 59
def prefixEnd_3715590 : Nat := 4983230072969 + 3 ^ 40 * 3715590 * 2
def baseEnd_3715590 : Nat := 1907883585039222970737319

theorem tailTrace_3715590 : CollatzResearch.WordTrace tailWord_3715590 prefixEnd_3715590 1907883585039222970737319 := by
  unfold tailWord_3715590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234959394033108659257257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90345800406039651397488149 4234959394033108659257257)
  ·
    refine ⟨3176219545524831494442943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4234959394033108659257257 3176219545524831494442943)
    ·
      refine ⟨4764329318287247241664415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3176219545524831494442943 4764329318287247241664415)
      ·
        refine ⟨7146493977430870862496623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4764329318287247241664415 7146493977430870862496623)
        ·
          refine ⟨10719740966146306293744935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7146493977430870862496623 10719740966146306293744935)
          ·
            refine ⟨16079611449219459440617403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10719740966146306293744935 16079611449219459440617403)
            ·
              refine ⟨24119417173829189160926105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16079611449219459440617403 24119417173829189160926105)
              ·
                refine ⟨18089562880371891870694579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24119417173829189160926105 18089562880371891870694579)
                ·
                  refine ⟨27134344320557837806041869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18089562880371891870694579 27134344320557837806041869)
                  ·
                    refine ⟨10175379120209189177265701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27134344320557837806041869 10175379120209189177265701)
                    ·
                      refine ⟨1907883585039222970737319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10175379120209189177265701 1907883585039222970737319)
                      ·
                        rfl

theorem cell23_3715590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3715590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715590 prefixEnd_3715590 := by exact prefixLift 3715590
  have htrace : WordTrace (prefixWord ++ tailWord_3715590) baseStart_3715590 baseEnd_3715590 := by
    simpa [prefixWord, tailWord_3715590, baseEnd_3715590] using wordTrace_append hprefix tailTrace_3715590
  have hstable : (prefixWord ++ tailWord_3715590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715590).length < 2 ^ (prefixWord ++ tailWord_3715590).sum := by decide
  have hdescent : baseEnd_3715590 < baseStart_3715590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715659 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6]
def baseStart_3715659 : Nat := 118140960795 + 3715659 * 2 ^ 59
def prefixEnd_3715659 : Nat := 4983230072969 + 3 ^ 40 * 3715659 * 2
def baseEnd_3715659 : Nat := 1907919015204383200774501

theorem tailTrace_3715659 : CollatzResearch.WordTrace tailWord_3715659 prefixEnd_3715659 1907919015204383200774501 := by
  unfold tailWord_3715659
  simp only [CollatzResearch.WordTrace]
  refine ⟨135521217245809501880494031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90347478163873001253662687 135521217245809501880494031)
  ·
    refine ⟨203281825868714252820741047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135521217245809501880494031 203281825868714252820741047)
    ·
      refine ⟨304922738803071379231111571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203281825868714252820741047 304922738803071379231111571)
      ·
        refine ⟨457384108204607068846667357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304922738803071379231111571 457384108204607068846667357)
        ·
          refine ⟨171519040576727650817500259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457384108204607068846667357 171519040576727650817500259)
          ·
            refine ⟨257278560865091476226250389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171519040576727650817500259 257278560865091476226250389)
            ·
              refine ⟨12059932540551162948105487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 257278560865091476226250389 12059932540551162948105487)
              ·
                refine ⟨18089898810826744422158231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12059932540551162948105487 18089898810826744422158231)
                ·
                  refine ⟨27134848216240116633237347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18089898810826744422158231 27134848216240116633237347)
                  ·
                    refine ⟨40702272324360174949856021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27134848216240116633237347 40702272324360174949856021)
                    ·
                      refine ⟨1907919015204383200774501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40702272324360174949856021 1907919015204383200774501)
                      ·
                        rfl

theorem cell23_3715659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_3715659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715659 prefixEnd_3715659 := by exact prefixLift 3715659
  have htrace : WordTrace (prefixWord ++ tailWord_3715659) baseStart_3715659 baseEnd_3715659 := by
    simpa [prefixWord, tailWord_3715659, baseEnd_3715659] using wordTrace_append hprefix tailTrace_3715659
  have hstable : (prefixWord ++ tailWord_3715659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715659).length < 2 ^ (prefixWord ++ tailWord_3715659).sum := by decide
  have hdescent : baseEnd_3715659 < baseStart_3715659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715663 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 3, 2, 2]
def baseStart_3715663 : Nat := 118140960795 + 3715663 * 2 ^ 59
def prefixEnd_3715663 : Nat := 4983230072969 + 3 ^ 40 * 3715663 * 2
def baseEnd_3715663 : Nat := 1907921069127001185124483

theorem tailTrace_3715663 : CollatzResearch.WordTrace tailWord_3715663 prefixEnd_3715663 1907921069127001185124483 := by
  unfold tailWord_3715663
  simp only [CollatzResearch.WordTrace]
  refine ⟨135521363137795010563639643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90347575425196673709093095 135521363137795010563639643)
  ·
    refine ⟨203282044706692515845459465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135521363137795010563639643 203282044706692515845459465)
    ·
      refine ⟨152461533530019386884094599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203282044706692515845459465 152461533530019386884094599)
      ·
        refine ⟨228692300295029080326141899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152461533530019386884094599 228692300295029080326141899)
        ·
          refine ⟨343038450442543620489212849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228692300295029080326141899 343038450442543620489212849)
          ·
            refine ⟨257278837831907715366909637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343038450442543620489212849 257278837831907715366909637)
            ·
              refine ⟨48239782093482696631295557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257278837831907715366909637 48239782093482696631295557)
              ·
                refine ⟨9044959142528005618367917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48239782093482696631295557 9044959142528005618367917)
                ·
                  refine ⟨3391859678448002106887969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9044959142528005618367917 3391859678448002106887969)
                  ·
                    refine ⟨2543894758836001580165977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3391859678448002106887969 2543894758836001580165977)
                    ·
                      refine ⟨1907921069127001185124483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2543894758836001580165977 1907921069127001185124483)
                      ·
                        rfl

theorem cell23_3715663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 2, 2].length) (baseStart_3715663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715663 prefixEnd_3715663 := by exact prefixLift 3715663
  have htrace : WordTrace (prefixWord ++ tailWord_3715663) baseStart_3715663 baseEnd_3715663 := by
    simpa [prefixWord, tailWord_3715663, baseEnd_3715663] using wordTrace_append hprefix tailTrace_3715663
  have hstable : (prefixWord ++ tailWord_3715663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715663).length < 2 ^ (prefixWord ++ tailWord_3715663).sum := by decide
  have hdescent : baseEnd_3715663 < baseStart_3715663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715669 : List Nat := [1, 3, 2, 2, 1, 1, 4, 9]
def baseStart_3715669 : Nat := 118140960795 + 3715669 * 2 ^ 59
def prefixEnd_3715669 : Nat := 4983230072969 + 3 ^ 40 * 3715669 * 2
def baseEnd_3715669 : Nat := 70663857407812154135165

theorem tailTrace_3715669 : CollatzResearch.WordTrace tailWord_3715669 prefixEnd_3715669 70663857407812154135165 := by
  unfold tailWord_3715669
  simp only [CollatzResearch.WordTrace]
  refine ⟨135521581975773273588358061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90347721317182182392238707 135521581975773273588358061)
  ·
    refine ⟨50820593240914977595634273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135521581975773273588358061 50820593240914977595634273)
    ·
      refine ⟨38115444930686233196725705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50820593240914977595634273 38115444930686233196725705)
      ·
        refine ⟨28586583698014674897544279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38115444930686233196725705 28586583698014674897544279)
        ·
          refine ⟨42879875547022012346316419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28586583698014674897544279 42879875547022012346316419)
          ·
            refine ⟨64319813320533018519474629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42879875547022012346316419 64319813320533018519474629)
            ·
              refine ⟨12059964997599940972401493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64319813320533018519474629 12059964997599940972401493)
              ·
                refine ⟨70663857407812154135165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12059964997599940972401493 70663857407812154135165)
                ·
                  rfl

theorem cell23_3715669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 9].length) (baseStart_3715669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715669 prefixEnd_3715669 := by exact prefixLift 3715669
  have htrace : WordTrace (prefixWord ++ tailWord_3715669) baseStart_3715669 baseEnd_3715669 := by
    simpa [prefixWord, tailWord_3715669, baseEnd_3715669] using wordTrace_append hprefix tailTrace_3715669
  have hstable : (prefixWord ++ tailWord_3715669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715669).length < 2 ^ (prefixWord ++ tailWord_3715669).sum := by decide
  have hdescent : baseEnd_3715669 < baseStart_3715669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715713 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3715713 : Nat := 118140960795 + 3715713 * 2 ^ 59
def prefixEnd_3715713 : Nat := 4983230072969 + 3 ^ 40 * 3715713 * 2
def baseEnd_3715713 : Nat := 1907946743159725989499253

theorem tailTrace_3715713 : CollatzResearch.WordTrace tailWord_3715713 prefixEnd_3715713 1907946743159725989499253 := by
  unfold tailWord_3715713
  simp only [CollatzResearch.WordTrace]
  refine ⟨135523186787613869102959793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90348791191742579401973195 135523186787613869102959793)
  ·
    refine ⟨101642390090710401827219845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135523186787613869102959793 101642390090710401827219845)
    ·
      refine ⟨19057948142008200342603721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101642390090710401827219845 19057948142008200342603721)
      ·
        refine ⟨14293461106506150256952791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19057948142008200342603721 14293461106506150256952791)
        ·
          refine ⟨21440191659759225385429187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14293461106506150256952791 21440191659759225385429187)
          ·
            refine ⟨32160287489638838078143781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21440191659759225385429187 32160287489638838078143781)
            ·
              refine ⟨6030053904307282139651959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32160287489638838078143781 6030053904307282139651959)
              ·
                refine ⟨9045080856460923209477939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030053904307282139651959 9045080856460923209477939)
                ·
                  refine ⟨13567621284691384814216909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9045080856460923209477939 13567621284691384814216909)
                  ·
                    refine ⟨5087857981759269305331341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13567621284691384814216909 5087857981759269305331341)
                    ·
                      refine ⟨1907946743159725989499253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5087857981759269305331341 1907946743159725989499253)
                      ·
                        rfl

theorem cell23_3715713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3715713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715713 prefixEnd_3715713 := by exact prefixLift 3715713
  have htrace : WordTrace (prefixWord ++ tailWord_3715713) baseStart_3715713 baseEnd_3715713 := by
    simpa [prefixWord, tailWord_3715713, baseEnd_3715713] using wordTrace_append hprefix tailTrace_3715713
  have hstable : (prefixWord ++ tailWord_3715713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715713).length < 2 ^ (prefixWord ++ tailWord_3715713).sum := by decide
  have hdescent : baseEnd_3715713 < baseStart_3715713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715726 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3715726 : Nat := 118140960795 + 3715726 * 2 ^ 59
def prefixEnd_3715726 : Nat := 4983230072969 + 3 ^ 40 * 3715726 * 2
def baseEnd_3715726 : Nat := 1907953418408234438636693

theorem tailTrace_3715726 : CollatzResearch.WordTrace tailWord_3715726 prefixEnd_3715726 1907953418408234438636693 := by
  unfold tailWord_3715726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940457617070846540397879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90349107291044514882122021 16940457617070846540397879)
  ·
    refine ⟨25410686425606269810596819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16940457617070846540397879 25410686425606269810596819)
    ·
      refine ⟨38116029638409404715895229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25410686425606269810596819 38116029638409404715895229)
      ·
        refine ⟨14293511114403526768460711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38116029638409404715895229 14293511114403526768460711)
        ·
          refine ⟨21440266671605290152691067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14293511114403526768460711 21440266671605290152691067)
          ·
            refine ⟨32160400007407935229036601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21440266671605290152691067 32160400007407935229036601)
            ·
              refine ⟨24120300005555951421777451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32160400007407935229036601 24120300005555951421777451)
              ·
                refine ⟨36180450008333927132666177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24120300005555951421777451 36180450008333927132666177)
                ·
                  refine ⟨27135337506250445349499633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36180450008333927132666177 27135337506250445349499633)
                  ·
                    refine ⟨20351503129687834012124725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27135337506250445349499633 20351503129687834012124725)
                    ·
                      refine ⟨1907953418408234438636693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20351503129687834012124725 1907953418408234438636693)
                      ·
                        rfl

theorem cell23_3715726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3715726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715726 prefixEnd_3715726 := by exact prefixLift 3715726
  have htrace : WordTrace (prefixWord ++ tailWord_3715726) baseStart_3715726 baseEnd_3715726 := by
    simpa [prefixWord, tailWord_3715726, baseEnd_3715726] using wordTrace_append hprefix tailTrace_3715726
  have hstable : (prefixWord ++ tailWord_3715726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715726).length < 2 ^ (prefixWord ++ tailWord_3715726).sum := by decide
  have hdescent : baseEnd_3715726 < baseStart_3715726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715739 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5]
def baseStart_3715739 : Nat := 118140960795 + 3715739 * 2 ^ 59
def prefixEnd_3715739 : Nat := 4983230072969 + 3 ^ 40 * 3715739 * 2
def baseEnd_3715739 : Nat := 1907960093656742887774133

theorem tailTrace_3715739 : CollatzResearch.WordTrace tailWord_3715739 prefixEnd_3715739 1907960093656742887774133 := by
  unfold tailWord_3715739
  simp only [CollatzResearch.WordTrace]
  refine ⟨135524135085519675543406271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90349423390346450362270847 135524135085519675543406271)
  ·
    refine ⟨203286202628279513315109407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135524135085519675543406271 203286202628279513315109407)
    ·
      refine ⟨304929303942419269972664111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203286202628279513315109407 304929303942419269972664111)
      ·
        refine ⟨457393955913628904958996167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304929303942419269972664111 457393955913628904958996167)
        ·
          refine ⟨686090933870443357438494251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457393955913628904958996167 686090933870443357438494251)
          ·
            refine ⟨1029136400805665036157741377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686090933870443357438494251 1029136400805665036157741377)
            ·
              refine ⟨771852300604248777118306033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029136400805665036157741377 771852300604248777118306033)
              ·
                refine ⟨578889225453186582838729525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771852300604248777118306033 578889225453186582838729525)
                ·
                  refine ⟨54270864886236242141130893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 578889225453186582838729525 54270864886236242141130893)
                  ·
                    refine ⟨20351574332338590802924085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54270864886236242141130893 20351574332338590802924085)
                    ·
                      refine ⟨1907960093656742887774133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20351574332338590802924085 1907960093656742887774133)
                      ·
                        rfl

theorem cell23_3715739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_3715739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715739 prefixEnd_3715739 := by exact prefixLift 3715739
  have htrace : WordTrace (prefixWord ++ tailWord_3715739) baseStart_3715739 baseEnd_3715739 := by
    simpa [prefixWord, tailWord_3715739, baseEnd_3715739] using wordTrace_append hprefix tailTrace_3715739
  have hstable : (prefixWord ++ tailWord_3715739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715739).length < 2 ^ (prefixWord ++ tailWord_3715739).sum := by decide
  have hdescent : baseEnd_3715739 < baseStart_3715739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715776 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 7]
def baseStart_3715776 : Nat := 118140960795 + 3715776 * 2 ^ 59
def prefixEnd_3715776 : Nat := 4983230072969 + 3 ^ 40 * 3715776 * 2
def baseEnd_3715776 : Nat := 211997676937884360334607

theorem tailTrace_3715776 : CollatzResearch.WordTrace tailWord_3715776 prefixEnd_3715776 211997676937884360334607 := by
  unfold tailWord_3715776
  simp only [CollatzResearch.WordTrace]
  refine ⟨67762742293192815431251591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90350323057590420575002121 67762742293192815431251591)
  ·
    refine ⟨101644113439789223146877387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67762742293192815431251591 101644113439789223146877387)
    ·
      refine ⟨152466170159683834720316081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101644113439789223146877387 152466170159683834720316081)
      ·
        refine ⟨114349627619762876040237061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152466170159683834720316081 114349627619762876040237061)
        ·
          refine ⟨21440555178705539257544449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114349627619762876040237061 21440555178705539257544449)
          ·
            refine ⟨16080416384029154443158337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21440555178705539257544449 16080416384029154443158337)
            ·
              refine ⟨12060312288021865832368753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16080416384029154443158337 12060312288021865832368753)
              ·
                refine ⟨9045234216016399374276565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12060312288021865832368753 9045234216016399374276565)
                ·
                  refine ⟨211997676937884360334607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9045234216016399374276565 211997676937884360334607)
                  ·
                    rfl

theorem cell23_3715776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_3715776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715776 prefixEnd_3715776 := by exact prefixLift 3715776
  have htrace : WordTrace (prefixWord ++ tailWord_3715776) baseStart_3715776 baseEnd_3715776 := by
    simpa [prefixWord, tailWord_3715776, baseEnd_3715776] using wordTrace_append hprefix tailTrace_3715776
  have hstable : (prefixWord ++ tailWord_3715776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715776).length < 2 ^ (prefixWord ++ tailWord_3715776).sum := by decide
  have hdescent : baseEnd_3715776 < baseStart_3715776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715843 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 4, 4, 2]
def baseStart_3715843 : Nat := 118140960795 + 3715843 * 2 ^ 59
def prefixEnd_3715843 : Nat := 4983230072969 + 3 ^ 40 * 3715843 * 2
def baseEnd_3715843 : Nat := 1908013495644810480873655

theorem tailTrace_3715843 : CollatzResearch.WordTrace tailWord_3715843 prefixEnd_3715843 1908013495644810480873655 := by
  unfold tailWord_3715843
  simp only [CollatzResearch.WordTrace]
  refine ⟨135527928277142901305192183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90351952184761934203461455 135527928277142901305192183)
  ·
    refine ⟨203291892415714351957788275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135527928277142901305192183 203291892415714351957788275)
    ·
      refine ⟨304937838623571527936682413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203291892415714351957788275 304937838623571527936682413)
      ·
        refine ⟨114351689483839322976255905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304937838623571527936682413 114351689483839322976255905)
        ·
          refine ⟨85763767112879492232191929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114351689483839322976255905 85763767112879492232191929)
          ·
            refine ⟨64322825334659619174143947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85763767112879492232191929 64322825334659619174143947)
            ·
              refine ⟨96484238001989428761215921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64322825334659619174143947 96484238001989428761215921)
              ·
                refine ⟨72363178501492071570911941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96484238001989428761215921 72363178501492071570911941)
                ·
                  refine ⟨13568095969029763419545989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72363178501492071570911941 13568095969029763419545989)
                  ·
                    refine ⟨2544017994193080641164873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13568095969029763419545989 2544017994193080641164873)
                    ·
                      refine ⟨1908013495644810480873655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544017994193080641164873 1908013495644810480873655)
                      ·
                        rfl

theorem cell23_3715843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_3715843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715843 prefixEnd_3715843 := by exact prefixLift 3715843
  have htrace : WordTrace (prefixWord ++ tailWord_3715843) baseStart_3715843 baseEnd_3715843 := by
    simpa [prefixWord, tailWord_3715843, baseEnd_3715843] using wordTrace_append hprefix tailTrace_3715843
  have hstable : (prefixWord ++ tailWord_3715843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715843).length < 2 ^ (prefixWord ++ tailWord_3715843).sum := by decide
  have hdescent : baseEnd_3715843 < baseStart_3715843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715894 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3715894 : Nat := 118140960795 + 3715894 * 2 ^ 59
def prefixEnd_3715894 : Nat := 4983230072969 + 3 ^ 40 * 3715894 * 2
def baseEnd_3715894 : Nat := 1908039683158189781335921

theorem tailTrace_3715894 : CollatzResearch.WordTrace tailWord_3715894 prefixEnd_3715894 1908039683158189781335921 := by
  unfold tailWord_3715894
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470611774997383563456171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90353192266638758010199157 8470611774997383563456171)
  ·
    refine ⟨12705917662496075345184257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8470611774997383563456171 12705917662496075345184257)
    ·
      refine ⟨9529438246872056508888193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12705917662496075345184257 9529438246872056508888193)
      ·
        refine ⟨7147078685154042381666145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9529438246872056508888193 7147078685154042381666145)
        ·
          refine ⟨5360309013865531786249609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7147078685154042381666145 5360309013865531786249609)
          ·
            refine ⟨4020231760399148839687207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5360309013865531786249609 4020231760399148839687207)
            ·
              refine ⟨6030347640598723259530811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020231760399148839687207 6030347640598723259530811)
              ·
                refine ⟨9045521460898084889296217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030347640598723259530811 9045521460898084889296217)
                ·
                  refine ⟨6784141095673563666972163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9045521460898084889296217 6784141095673563666972163)
                  ·
                    refine ⟨10176211643510345500458245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6784141095673563666972163 10176211643510345500458245)
                    ·
                      refine ⟨1908039683158189781335921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10176211643510345500458245 1908039683158189781335921)
                      ·
                        rfl

theorem cell23_3715894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3715894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715894 prefixEnd_3715894 := by exact prefixLift 3715894
  have htrace : WordTrace (prefixWord ++ tailWord_3715894) baseStart_3715894 baseEnd_3715894 := by
    simpa [prefixWord, tailWord_3715894, baseEnd_3715894] using wordTrace_append hprefix tailTrace_3715894
  have hstable : (prefixWord ++ tailWord_3715894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715894).length < 2 ^ (prefixWord ++ tailWord_3715894).sum := by decide
  have hdescent : baseEnd_3715894 < baseStart_3715894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715920 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 2, 3, 2]
def baseStart_3715920 : Nat := 118140960795 + 3715920 * 2 ^ 59
def prefixEnd_3715920 : Nat := 4983230072969 + 3 ^ 40 * 3715920 * 2
def baseEnd_3715920 : Nat := 1908053033655206679610801

theorem tailTrace_3715920 : CollatzResearch.WordTrace tailWord_3715920 prefixEnd_3715920 1908053033655206679610801 := by
  unfold tailWord_3715920
  simp only [CollatzResearch.WordTrace]
  refine ⟨67765368348931971727872607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90353824465242628970496809 67765368348931971727872607)
  ·
    refine ⟨101648052523397957591808911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67765368348931971727872607 101648052523397957591808911)
    ·
      refine ⟨152472078785096936387713367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101648052523397957591808911 152472078785096936387713367)
      ·
        refine ⟨228708118177645404581570051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152472078785096936387713367 228708118177645404581570051)
        ·
          refine ⟨343062177266468106872355077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228708118177645404581570051 343062177266468106872355077)
          ·
            refine ⟨64324158237462770038566577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343062177266468106872355077 64324158237462770038566577)
            ·
              refine ⟨48243118678097077528924933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64324158237462770038566577 48243118678097077528924933)
              ·
                refine ⟨9045584752143202036673425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48243118678097077528924933 9045584752143202036673425)
                ·
                  refine ⟨6784188564107401527505069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9045584752143202036673425 6784188564107401527505069)
                  ·
                    refine ⟨2544070711540275572814401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6784188564107401527505069 2544070711540275572814401)
                    ·
                      refine ⟨1908053033655206679610801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544070711540275572814401 1908053033655206679610801)
                      ·
                        rfl

theorem cell23_3715920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 2, 3, 2].length) (baseStart_3715920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715920 prefixEnd_3715920 := by exact prefixLift 3715920
  have htrace : WordTrace (prefixWord ++ tailWord_3715920) baseStart_3715920 baseEnd_3715920 := by
    simpa [prefixWord, tailWord_3715920, baseEnd_3715920] using wordTrace_append hprefix tailTrace_3715920
  have hstable : (prefixWord ++ tailWord_3715920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715920).length < 2 ^ (prefixWord ++ tailWord_3715920).sum := by decide
  have hdescent : baseEnd_3715920 < baseStart_3715920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715927 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_3715927 : Nat := 118140960795 + 3715927 * 2 ^ 59
def prefixEnd_3715927 : Nat := 4983230072969 + 3 ^ 40 * 3715927 * 2
def baseEnd_3715927 : Nat := 1908056628019788152223269

theorem tailTrace_3715927 : CollatzResearch.WordTrace tailWord_3715927 prefixEnd_3715927 1908056628019788152223269 := by
  unfold tailWord_3715927
  simp only [CollatzResearch.WordTrace]
  refine ⟨135530992008838583651250035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90353994672559055767500023 135530992008838583651250035)
  ·
    refine ⟨203296488013257875476875053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135530992008838583651250035 203296488013257875476875053)
    ·
      refine ⟨76236183004971703303828145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203296488013257875476875053 76236183004971703303828145)
      ·
        refine ⟨57177137253728777477871109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76236183004971703303828145 57177137253728777477871109)
        ·
          refine ⟨10720713235074145777100833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57177137253728777477871109 10720713235074145777100833)
          ·
            refine ⟨8040534926305609332825625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10720713235074145777100833 8040534926305609332825625)
            ·
              refine ⟨6030401194729206999619219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8040534926305609332825625 6030401194729206999619219)
              ·
                refine ⟨9045601792093810499428829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030401194729206999619219 9045601792093810499428829)
                ·
                  refine ⟨3392100672035178937285811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9045601792093810499428829 3392100672035178937285811)
                  ·
                    refine ⟨5088151008052768405928717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392100672035178937285811 5088151008052768405928717)
                    ·
                      refine ⟨1908056628019788152223269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5088151008052768405928717 1908056628019788152223269)
                      ·
                        rfl

theorem cell23_3715927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_3715927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715927 prefixEnd_3715927 := by exact prefixLift 3715927
  have htrace : WordTrace (prefixWord ++ tailWord_3715927) baseStart_3715927 baseEnd_3715927 := by
    simpa [prefixWord, tailWord_3715927, baseEnd_3715927] using wordTrace_append hprefix tailTrace_3715927
  have hstable : (prefixWord ++ tailWord_3715927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715927).length < 2 ^ (prefixWord ++ tailWord_3715927).sum := by decide
  have hdescent : baseEnd_3715927 < baseStart_3715927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715963 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4]
def baseStart_3715963 : Nat := 118140960795 + 3715963 * 2 ^ 59
def prefixEnd_3715963 : Nat := 4983230072969 + 3 ^ 40 * 3715963 * 2
def baseEnd_3715963 : Nat := 1908075113323350011373103

theorem tailTrace_3715963 : CollatzResearch.WordTrace tailWord_3715963 prefixEnd_3715963 1908075113323350011373103 := by
  unfold tailWord_3715963
  simp only [CollatzResearch.WordTrace]
  refine ⟨135532305036708161799560543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90354870024472107866373695 135532305036708161799560543)
  ·
    refine ⟨203298457555062242699340815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135532305036708161799560543 203298457555062242699340815)
    ·
      refine ⟨304947686332593364049011223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203298457555062242699340815 304947686332593364049011223)
      ·
        refine ⟨457421529498890046073516835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304947686332593364049011223 457421529498890046073516835)
        ·
          refine ⟨686132294248335069110275253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457421529498890046073516835 686132294248335069110275253)
          ·
            refine ⟨64324902585781412729088305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 686132294248335069110275253 64324902585781412729088305)
            ·
              refine ⟨48243676939336059546816229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64324902585781412729088305 48243676939336059546816229)
              ·
                refine ⟨9045689426125511165028043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48243676939336059546816229 9045689426125511165028043)
                ·
                  refine ⟨13568534139188266747542065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9045689426125511165028043 13568534139188266747542065)
                  ·
                    refine ⟨10176400604391200060656549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13568534139188266747542065 10176400604391200060656549)
                    ·
                      refine ⟨1908075113323350011373103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10176400604391200060656549 1908075113323350011373103)
                      ·
                        rfl

theorem cell23_3715963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 4].length) (baseStart_3715963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715963 prefixEnd_3715963 := by exact prefixLift 3715963
  have htrace : WordTrace (prefixWord ++ tailWord_3715963) baseStart_3715963 baseEnd_3715963 := by
    simpa [prefixWord, tailWord_3715963, baseEnd_3715963] using wordTrace_append hprefix tailTrace_3715963
  have hstable : (prefixWord ++ tailWord_3715963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715963).length < 2 ^ (prefixWord ++ tailWord_3715963).sum := by decide
  have hdescent : baseEnd_3715963 < baseStart_3715963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3715973 : List Nat := [1, 3, 1, 1, 3, 5, 9]
def baseStart_3715973 : Nat := 118140960795 + 3715973 * 2 ^ 59
def prefixEnd_3715973 : Nat := 4983230072969 + 3 ^ 40 * 3715973 * 2
def baseEnd_3715973 : Nat := 23556546273208579904297

theorem tailTrace_3715973 : CollatzResearch.WordTrace tailWord_3715973 prefixEnd_3715973 23556546273208579904297 := by
  unfold tailWord_3715973
  simp only [CollatzResearch.WordTrace]
  refine ⟨135532669766671933507424573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90355113177781289004949715 135532669766671933507424573)
  ·
    refine ⟨50824751162501975065284215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135532669766671933507424573 50824751162501975065284215)
    ·
      refine ⟨76237126743752962597926323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50824751162501975065284215 76237126743752962597926323)
      ·
        refine ⟨114355690115629443896889485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76237126743752962597926323 114355690115629443896889485)
        ·
          refine ⟨42883383793361041461333557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114355690115629443896889485 42883383793361041461333557)
          ·
            refine ⟨4020317230627597637000021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42883383793361041461333557 4020317230627597637000021)
            ·
              refine ⟨23556546273208579904297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4020317230627597637000021 23556546273208579904297)
              ·
                rfl

theorem cell23_3715973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 9].length) (baseStart_3715973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3715973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3715973 prefixEnd_3715973 := by exact prefixLift 3715973
  have htrace : WordTrace (prefixWord ++ tailWord_3715973) baseStart_3715973 baseEnd_3715973 := by
    simpa [prefixWord, tailWord_3715973, baseEnd_3715973] using wordTrace_append hprefix tailTrace_3715973
  have hstable : (prefixWord ++ tailWord_3715973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3715973).length < 2 ^ (prefixWord ++ tailWord_3715973).sum := by decide
  have hdescent : baseEnd_3715973 < baseStart_3715973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3715973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716017 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3716017 : Nat := 118140960795 + 3716017 * 2 ^ 59
def prefixEnd_3716017 : Nat := 4983230072969 + 3 ^ 40 * 3716017 * 2
def baseEnd_3716017 : Nat := 1908102841278692800097855

theorem tailTrace_3716017 : CollatzResearch.WordTrace tailWord_3716017 prefixEnd_3716017 1908102841278692800097855 := by
  unfold tailWord_3716017
  simp only [CollatzResearch.WordTrace]
  refine ⟨135534274578512529022026305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90356183052341686014684203 135534274578512529022026305)
  ·
    refine ⟨101650705933884396766519729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135534274578512529022026305 101650705933884396766519729)
    ·
      refine ⟨76238029450413297574889797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101650705933884396766519729 76238029450413297574889797)
      ·
        refine ⟨14294630521952493295291837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76238029450413297574889797 14294630521952493295291837)
        ·
          refine ⟨5360486445732184985734439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14294630521952493295291837 5360486445732184985734439)
          ·
            refine ⟨8040729668598277478601659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360486445732184985734439 8040729668598277478601659)
            ·
              refine ⟨12061094502897416217902489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8040729668598277478601659 12061094502897416217902489)
              ·
                refine ⟨9045820877173062163426867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12061094502897416217902489 9045820877173062163426867)
                ·
                  refine ⟨13568731315759593245140301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9045820877173062163426867 13568731315759593245140301)
                  ·
                    refine ⟨5088274243409847466927613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13568731315759593245140301 5088274243409847466927613)
                    ·
                      refine ⟨1908102841278692800097855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5088274243409847466927613 1908102841278692800097855)
                      ·
                        rfl

theorem cell23_3716017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3716017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716017 prefixEnd_3716017 := by exact prefixLift 3716017
  have htrace : WordTrace (prefixWord ++ tailWord_3716017) baseStart_3716017 baseEnd_3716017 := by
    simpa [prefixWord, tailWord_3716017, baseEnd_3716017] using wordTrace_append hprefix tailTrace_3716017
  have hstable : (prefixWord ++ tailWord_3716017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716017).length < 2 ^ (prefixWord ++ tailWord_3716017).sum := by decide
  have hdescent : baseEnd_3716017 < baseStart_3716017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716050 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3716050 : Nat := 118140960795 + 3716050 * 2 ^ 59
def prefixEnd_3716050 : Nat := 4983230072969 + 3 ^ 40 * 3716050 * 2
def baseEnd_3716050 : Nat := 636039928713430390328401

theorem tailTrace_3716050 : CollatzResearch.WordTrace tailWord_3716050 prefixEnd_3716050 636039928713430390328401 := by
  unfold tailWord_3716050
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883869546848243914494401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90356985458261983771985069 33883869546848243914494401)
  ·
    refine ⟨25412902160136182935870801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33883869546848243914494401 25412902160136182935870801)
    ·
      refine ⟨19059676620102137201903101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25412902160136182935870801 19059676620102137201903101)
      ·
        refine ⟨7147378732538301450713663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19059676620102137201903101 7147378732538301450713663)
        ·
          refine ⟨10721068098807452176070495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7147378732538301450713663 10721068098807452176070495)
          ·
            refine ⟨16081602148211178264105743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721068098807452176070495 16081602148211178264105743)
            ·
              refine ⟨24122403222316767396158615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16081602148211178264105743 24122403222316767396158615)
              ·
                refine ⟨36183604833475151094237923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24122403222316767396158615 36183604833475151094237923)
                ·
                  refine ⟨54275407250212726641356885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36183604833475151094237923 54275407250212726641356885)
                  ·
                    refine ⟨636039928713430390328401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54275407250212726641356885 636039928713430390328401)
                    ·
                      rfl

theorem cell23_3716050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3716050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716050 prefixEnd_3716050 := by exact prefixLift 3716050
  have htrace : WordTrace (prefixWord ++ tailWord_3716050) baseStart_3716050 baseEnd_3716050 := by
    simpa [prefixWord, tailWord_3716050, baseEnd_3716050] using wordTrace_append hprefix tailTrace_3716050
  have hstable : (prefixWord ++ tailWord_3716050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716050).length < 2 ^ (prefixWord ++ tailWord_3716050).sum := by decide
  have hdescent : baseEnd_3716050 < baseStart_3716050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716057 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 1, 4, 2]
def baseStart_3716057 : Nat := 118140960795 + 3716057 * 2 ^ 59
def prefixEnd_3716057 : Nat := 4983230072969 + 3 ^ 40 * 3716057 * 2
def baseEnd_3716057 : Nat := 1908123380504872643597671

theorem tailTrace_3716057 : CollatzResearch.WordTrace tailWord_3716057 prefixEnd_3716057 1908123380504872643597671 := by
  unfold tailWord_3716057
  simp only [CollatzResearch.WordTrace]
  refine ⟨135535733498367615853482425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90357155665578410568988283 135535733498367615853482425)
  ·
    refine ⟨101651800123775711890111819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135535733498367615853482425 101651800123775711890111819)
    ·
      refine ⟨152477700185663567835167729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101651800123775711890111819 152477700185663567835167729)
      ·
        refine ⟨114358275139247675876375797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152477700185663567835167729 114358275139247675876375797)
        ·
          refine ⟨10721088294304469613410231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114358275139247675876375797 10721088294304469613410231)
          ·
            refine ⟨16081632441456704420115347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721088294304469613410231 16081632441456704420115347)
            ·
              refine ⟨24122448662185056630173021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16081632441456704420115347 24122448662185056630173021)
              ·
                refine ⟨9045918248319396236314883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24122448662185056630173021 9045918248319396236314883)
                ·
                  refine ⟨13568877372479094354472325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9045918248319396236314883 13568877372479094354472325)
                  ·
                    refine ⟨2544164507339830191463561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13568877372479094354472325 2544164507339830191463561)
                    ·
                      refine ⟨1908123380504872643597671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544164507339830191463561 1908123380504872643597671)
                      ·
                        rfl

theorem cell23_3716057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_3716057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716057 prefixEnd_3716057 := by exact prefixLift 3716057
  have htrace : WordTrace (prefixWord ++ tailWord_3716057) baseStart_3716057 baseEnd_3716057 := by
    simpa [prefixWord, tailWord_3716057, baseEnd_3716057] using wordTrace_append hprefix tailTrace_3716057
  have hstable : (prefixWord ++ tailWord_3716057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716057).length < 2 ^ (prefixWord ++ tailWord_3716057).sum := by decide
  have hdescent : baseEnd_3716057 < baseStart_3716057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716078 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_3716078 : Nat := 118140960795 + 3716078 * 2 ^ 59
def prefixEnd_3716078 : Nat := 4983230072969 + 3 ^ 40 * 3716078 * 2
def baseEnd_3716078 : Nat := 1908134163598617061435075

theorem tailTrace_3716078 : CollatzResearch.WordTrace tailWord_3716078 prefixEnd_3716078 1908134163598617061435075 := by
  unfold tailWord_3716078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16942062428911442054999611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90357666287527690959997925 16942062428911442054999611)
  ·
    refine ⟨25413093643367163082499417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16942062428911442054999611 25413093643367163082499417)
    ·
      refine ⟨19059820232525372311874563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25413093643367163082499417 19059820232525372311874563)
      ·
        refine ⟨28589730348788058467811845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19059820232525372311874563 28589730348788058467811845)
        ·
          refine ⟨5360574440397760962714721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28589730348788058467811845 5360574440397760962714721)
          ·
            refine ⟨4020430830298320722036041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5360574440397760962714721 4020430830298320722036041)
            ·
              refine ⟨3015323122723740541527031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020430830298320722036041 3015323122723740541527031)
              ·
                refine ⟨4522984684085610812290547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015323122723740541527031 4522984684085610812290547)
                ·
                  refine ⟨6784477026128416218435821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4522984684085610812290547 6784477026128416218435821)
                  ·
                    refine ⟨2544178884798156081913433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6784477026128416218435821 2544178884798156081913433)
                    ·
                      refine ⟨1908134163598617061435075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544178884798156081913433 1908134163598617061435075)
                      ·
                        rfl

theorem cell23_3716078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_3716078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716078 prefixEnd_3716078 := by exact prefixLift 3716078
  have htrace : WordTrace (prefixWord ++ tailWord_3716078) baseStart_3716078 baseEnd_3716078 := by
    simpa [prefixWord, tailWord_3716078, baseEnd_3716078] using wordTrace_append hprefix tailTrace_3716078
  have hstable : (prefixWord ++ tailWord_3716078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716078).length < 2 ^ (prefixWord ++ tailWord_3716078).sum := by decide
  have hdescent : baseEnd_3716078 < baseStart_3716078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716085 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3716085 : Nat := 118140960795 + 3716085 * 2 ^ 59
def prefixEnd_3716085 : Nat := 4983230072969 + 3 ^ 40 * 3716085 * 2
def baseEnd_3716085 : Nat := 1908137757963198534047543

theorem tailTrace_3716085 : CollatzResearch.WordTrace tailWord_3716085 prefixEnd_3716085 1908137757963198534047543 := by
  unfold tailWord_3716085
  simp only [CollatzResearch.WordTrace]
  refine ⟨135536754742266176635501709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90357836494844117757001139 135536754742266176635501709)
  ·
    refine ⟨50826283028349816238313141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135536754742266176635501709 50826283028349816238313141)
    ·
      refine ⟨4764964033907795272341857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50826283028349816238313141 4764964033907795272341857)
      ·
        refine ⟨3573723025430846454256393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4764964033907795272341857 3573723025430846454256393)
        ·
          refine ⟨2680292269073134840692295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3573723025430846454256393 2680292269073134840692295)
          ·
            refine ⟨4020438403609702261038443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680292269073134840692295 4020438403609702261038443)
            ·
              refine ⟨6030657605414553391557665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020438403609702261038443 6030657605414553391557665)
              ·
                refine ⟨4522993204060915043668249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6030657605414553391557665 4522993204060915043668249)
                ·
                  refine ⟨3392244903045686282751187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4522993204060915043668249 3392244903045686282751187)
                  ·
                    refine ⟨5088367354568529424126781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392244903045686282751187 5088367354568529424126781)
                    ·
                      refine ⟨1908137757963198534047543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5088367354568529424126781 1908137757963198534047543)
                      ·
                        rfl

theorem cell23_3716085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3716085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716085 prefixEnd_3716085 := by exact prefixLift 3716085
  have htrace : WordTrace (prefixWord ++ tailWord_3716085) baseStart_3716085 baseEnd_3716085 := by
    simpa [prefixWord, tailWord_3716085, baseEnd_3716085] using wordTrace_append hprefix tailTrace_3716085
  have hstable : (prefixWord ++ tailWord_3716085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716085).length < 2 ^ (prefixWord ++ tailWord_3716085).sum := by decide
  have hdescent : baseEnd_3716085 < baseStart_3716085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716097 : List Nat := [1, 2, 4, 1, 2, 2, 2, 4, 5]
def baseStart_3716097 : Nat := 118140960795 + 3716097 * 2 ^ 59
def prefixEnd_3716097 : Nat := 4983230072969 + 3 ^ 40 * 3716097 * 2
def baseEnd_3716097 : Nat := 212015991081228054121943

theorem tailTrace_3716097 : CollatzResearch.WordTrace tailWord_3716097 prefixEnd_3716097 212015991081228054121943 := by
  unfold tailWord_3716097
  simp only [CollatzResearch.WordTrace]
  refine ⟨135537192418222702684938545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90358128278815135123292363 135537192418222702684938545)
  ·
    refine ⟨101652894313667027013703909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135537192418222702684938545 101652894313667027013703909)
    ·
      refine ⟨19059917683812567565069483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101652894313667027013703909 19059917683812567565069483)
      ·
        refine ⟨28589876525718851347604225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19059917683812567565069483 28589876525718851347604225)
        ·
          refine ⟨21442407394289138510703169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28589876525718851347604225 21442407394289138510703169)
          ·
            refine ⟨16081805545716853883027377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21442407394289138510703169 16081805545716853883027377)
            ·
              refine ⟨12061354159287640412270533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16081805545716853883027377 12061354159287640412270533)
              ·
                refine ⟨2261503904866432577300725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12061354159287640412270533 2261503904866432577300725)
                ·
                  refine ⟨212015991081228054121943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2261503904866432577300725 212015991081228054121943)
                  ·
                    rfl

theorem cell23_3716097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 5].length) (baseStart_3716097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716097 prefixEnd_3716097 := by exact prefixLift 3716097
  have htrace : WordTrace (prefixWord ++ tailWord_3716097) baseStart_3716097 baseEnd_3716097 := by
    simpa [prefixWord, tailWord_3716097, baseEnd_3716097] using wordTrace_append hprefix tailTrace_3716097
  have hstable : (prefixWord ++ tailWord_3716097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716097).length < 2 ^ (prefixWord ++ tailWord_3716097).sum := by decide
  have hdescent : baseEnd_3716097 < baseStart_3716097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716110 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3716110 : Nat := 118140960795 + 3716110 * 2 ^ 59
def prefixEnd_3716110 : Nat := 4983230072969 + 3 ^ 40 * 3716110 * 2
def baseEnd_3716110 : Nat := 636050198326520312078309

theorem tailTrace_3716110 : CollatzResearch.WordTrace tailWord_3716110 prefixEnd_3716110 636050198326520312078309 := by
  unfold tailWord_3716110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16942208320896950738145223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90358444378117070603441189 16942208320896950738145223)
  ·
    refine ⟨25413312481345426107217835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16942208320896950738145223 25413312481345426107217835)
    ·
      refine ⟨38119968722018139160826753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25413312481345426107217835 38119968722018139160826753)
      ·
        refine ⟨28589976541513604370620065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38119968722018139160826753 28589976541513604370620065)
        ·
          refine ⟨21442482406135203277965049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28589976541513604370620065 21442482406135203277965049)
          ·
            refine ⟨16081861804601402458473787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21442482406135203277965049 16081861804601402458473787)
            ·
              refine ⟨24122792706902103687710681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16081861804601402458473787 24122792706902103687710681)
              ·
                refine ⟨18092094530176577765783011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24122792706902103687710681 18092094530176577765783011)
                ·
                  refine ⟨27138141795264866648674517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18092094530176577765783011 27138141795264866648674517)
                  ·
                    refine ⟨636050198326520312078309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27138141795264866648674517 636050198326520312078309)
                    ·
                      rfl

theorem cell23_3716110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3716110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716110 prefixEnd_3716110 := by exact prefixLift 3716110
  have htrace : WordTrace (prefixWord ++ tailWord_3716110) baseStart_3716110 baseEnd_3716110 := by
    simpa [prefixWord, tailWord_3716110, baseEnd_3716110] using wordTrace_append hprefix tailTrace_3716110
  have hstable : (prefixWord ++ tailWord_3716110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716110).length < 2 ^ (prefixWord ++ tailWord_3716110).sum := by decide
  have hdescent : baseEnd_3716110 < baseStart_3716110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716240 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_3716240 : Nat := 118140960795 + 3716240 * 2 ^ 59
def prefixEnd_3716240 : Nat := 4983230072969 + 3 ^ 40 * 3716240 * 2
def baseEnd_3716240 : Nat := 1908217347464645427609329

theorem tailTrace_3716240 : CollatzResearch.WordTrace tailWord_3716240 prefixEnd_3716240 1908217347464645427609329 := by
  unfold tailWord_3716240
  simp only [CollatzResearch.WordTrace]
  refine ⟨67771204028352319053697087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90361605371136425404929449 67771204028352319053697087)
  ·
    refine ⟨101656806042528478580545631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67771204028352319053697087 101656806042528478580545631)
    ·
      refine ⟨152485209063792717870818447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101656806042528478580545631 152485209063792717870818447)
      ·
        refine ⟨228727813595689076806227671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152485209063792717870818447 228727813595689076806227671)
        ·
          refine ⟨343091720393533615209341507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228727813595689076806227671 343091720393533615209341507)
          ·
            refine ⟨514637580590300422814012261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343091720393533615209341507 514637580590300422814012261)
            ·
              refine ⟨96494546360681329277627299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 514637580590300422814012261 96494546360681329277627299)
              ·
                refine ⟨144741819541021993916440949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96494546360681329277627299 144741819541021993916440949)
                ·
                  refine ⟨13569545581970811929666339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144741819541021993916440949 13569545581970811929666339)
                  ·
                    refine ⟨20354318372956217894499509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13569545581970811929666339 20354318372956217894499509)
                    ·
                      refine ⟨1908217347464645427609329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20354318372956217894499509 1908217347464645427609329)
                      ·
                        rfl

theorem cell23_3716240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_3716240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716240 prefixEnd_3716240 := by exact prefixLift 3716240
  have htrace : WordTrace (prefixWord ++ tailWord_3716240) baseStart_3716240 baseEnd_3716240 := by
    simpa [prefixWord, tailWord_3716240, baseEnd_3716240] using wordTrace_append hprefix tailTrace_3716240
  have hstable : (prefixWord ++ tailWord_3716240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716240).length < 2 ^ (prefixWord ++ tailWord_3716240).sum := by decide
  have hdescent : baseEnd_3716240 < baseStart_3716240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716247 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 1, 6]
def baseStart_3716247 : Nat := 118140960795 + 3716247 * 2 ^ 59
def prefixEnd_3716247 : Nat := 4983230072969 + 3 ^ 40 * 3716247 * 2
def baseEnd_3716247 : Nat := 636073647276408966740599

theorem tailTrace_3716247 : CollatzResearch.WordTrace tailWord_3716247 prefixEnd_3716247 636073647276408966740599 := by
  unfold tailWord_3716247
  simp only [CollatzResearch.WordTrace]
  refine ⟨135542663367679278302898995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90361775578452852201932663 135542663367679278302898995)
  ·
    refine ⟨203313995051518917454348493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135542663367679278302898995 203313995051518917454348493)
    ·
      refine ⟨76242748144319594045380685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203313995051518917454348493 76242748144319594045380685)
      ·
        refine ⟨28591030554119847767017757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76242748144319594045380685 28591030554119847767017757)
        ·
          refine ⟨10721636457794942912631659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28591030554119847767017757 10721636457794942912631659)
          ·
            refine ⟨16082454686692414368947489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721636457794942912631659 16082454686692414368947489)
            ·
              refine ⟨12061841015019310776710617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16082454686692414368947489 12061841015019310776710617)
              ·
                refine ⟨9046380761264483082532963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12061841015019310776710617 9046380761264483082532963)
                ·
                  refine ⟨13569571141896724623799445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9046380761264483082532963 13569571141896724623799445)
                  ·
                    refine ⟨636073647276408966740599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13569571141896724623799445 636073647276408966740599)
                    ·
                      rfl

theorem cell23_3716247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_3716247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716247 prefixEnd_3716247 := by exact prefixLift 3716247
  have htrace : WordTrace (prefixWord ++ tailWord_3716247) baseStart_3716247 baseEnd_3716247 := by
    simpa [prefixWord, tailWord_3716247, baseEnd_3716247] using wordTrace_append hprefix tailTrace_3716247
  have hstable : (prefixWord ++ tailWord_3716247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716247).length < 2 ^ (prefixWord ++ tailWord_3716247).sum := by decide
  have hdescent : baseEnd_3716247 < baseStart_3716247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716248 : List Nat := [2, 1, 2, 4, 2, 2, 2, 3, 1, 1, 3]
def baseStart_3716248 : Nat := 118140960795 + 3716248 * 2 ^ 59
def prefixEnd_3716248 : Nat := 4983230072969 + 3 ^ 40 * 3716248 * 2
def baseEnd_3716248 : Nat := 1908221455309881396309293

theorem tailTrace_3716248 : CollatzResearch.WordTrace tailWord_3716248 prefixEnd_3716248 1908221455309881396309293 := by
  unfold tailWord_3716248
  simp only [CollatzResearch.WordTrace]
  refine ⟨67771349920337827736842699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90361799893783770315790265 67771349920337827736842699)
  ·
    refine ⟨101657024880506741605264049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67771349920337827736842699 101657024880506741605264049)
    ·
      refine ⟨76242768660380056203948037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101657024880506741605264049 76242768660380056203948037)
      ·
        refine ⟨14295519123821260538240257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76242768660380056203948037 14295519123821260538240257)
        ·
          refine ⟨10721639342865945403680193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14295519123821260538240257 10721639342865945403680193)
          ·
            refine ⟨8041229507149459052760145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10721639342865945403680193 8041229507149459052760145)
            ·
              refine ⟨6030922130362094289570109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8041229507149459052760145 6030922130362094289570109)
              ·
                refine ⟨2261595798885785358588791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6030922130362094289570109 2261595798885785358588791)
                ·
                  refine ⟨3392393698328678037883187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261595798885785358588791 3392393698328678037883187)
                  ·
                    refine ⟨5088590547493017056824781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392393698328678037883187 5088590547493017056824781)
                    ·
                      refine ⟨1908221455309881396309293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5088590547493017056824781 1908221455309881396309293)
                      ·
                        rfl

theorem cell23_3716248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_3716248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716248 prefixEnd_3716248 := by exact prefixLift 3716248
  have htrace : WordTrace (prefixWord ++ tailWord_3716248) baseStart_3716248 baseEnd_3716248 := by
    simpa [prefixWord, tailWord_3716248, baseEnd_3716248] using wordTrace_append hprefix tailTrace_3716248
  have hstable : (prefixWord ++ tailWord_3716248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716248).length < 2 ^ (prefixWord ++ tailWord_3716248).sum := by decide
  have hdescent : baseEnd_3716248 < baseStart_3716248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716257 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3716257 : Nat := 118140960795 + 3716257 * 2 ^ 59
def prefixEnd_3716257 : Nat := 4983230072969 + 3 ^ 40 * 3716257 * 2
def baseEnd_3716257 : Nat := 1908226076635771861096751

theorem tailTrace_3716257 : CollatzResearch.WordTrace tailWord_3716257 prefixEnd_3716257 1908226076635771861096751 := by
  unfold tailWord_3716257
  simp only [CollatzResearch.WordTrace]
  refine ⟨135543028097643050010763025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90362018731762033340508683 135543028097643050010763025)
  ·
    refine ⟨101657271073232287508072269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135543028097643050010763025 101657271073232287508072269)
    ·
      refine ⟨38121476652462107815527101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101657271073232287508072269 38121476652462107815527101)
      ·
        refine ⟨14295553744673290430822663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38121476652462107815527101 14295553744673290430822663)
        ·
          refine ⟨21443330617009935646233995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14295553744673290430822663 21443330617009935646233995)
          ·
            refine ⟨32164995925514903469350993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21443330617009935646233995 32164995925514903469350993)
            ·
              refine ⟨24123746944136177602013245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32164995925514903469350993 24123746944136177602013245)
              ·
                refine ⟨9046405104051066600754967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24123746944136177602013245 9046405104051066600754967)
                ·
                  refine ⟨13569607656076599901132451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9046405104051066600754967 13569607656076599901132451)
                  ·
                    refine ⟨20354411484114899851698677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13569607656076599901132451 20354411484114899851698677)
                    ·
                      refine ⟨1908226076635771861096751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20354411484114899851698677 1908226076635771861096751)
                      ·
                        rfl

theorem cell23_3716257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3716257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716257 prefixEnd_3716257 := by exact prefixLift 3716257
  have htrace : WordTrace (prefixWord ++ tailWord_3716257) baseStart_3716257 baseEnd_3716257 := by
    simpa [prefixWord, tailWord_3716257, baseEnd_3716257] using wordTrace_append hprefix tailTrace_3716257
  have hstable : (prefixWord ++ tailWord_3716257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716257).length < 2 ^ (prefixWord ++ tailWord_3716257).sum := by decide
  have hdescent : baseEnd_3716257 < baseStart_3716257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716280 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_3716280 : Nat := 118140960795 + 3716280 * 2 ^ 59
def prefixEnd_3716280 : Nat := 4983230072969 + 3 ^ 40 * 3716280 * 2
def baseEnd_3716280 : Nat := 1908237886690825271109145

theorem tailTrace_3716280 : CollatzResearch.WordTrace tailWord_3716280 prefixEnd_3716280 1908237886690825271109145 := by
  unfold tailWord_3716280
  simp only [CollatzResearch.WordTrace]
  refine ⟨67771933488279862469425147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90362577984373149959233529 67771933488279862469425147)
  ·
    refine ⟨101657900232419793704137721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67771933488279862469425147 101657900232419793704137721)
    ·
      refine ⟨76243425174314845278103291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101657900232419793704137721 76243425174314845278103291)
      ·
        refine ⟨114365137761472267917154937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76243425174314845278103291 114365137761472267917154937)
        ·
          refine ⟨85773853321104200937866203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114365137761472267917154937 85773853321104200937866203)
          ·
            refine ⟨128660779981656301406799305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85773853321104200937866203 128660779981656301406799305)
            ·
              refine ⟨96495584986242226055099479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128660779981656301406799305 96495584986242226055099479)
              ·
                refine ⟨144743377479363339082649219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96495584986242226055099479 144743377479363339082649219)
                ·
                  refine ⟨217115066219045008623973829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144743377479363339082649219 217115066219045008623973829)
                  ·
                    refine ⟨40709074916070939116995093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217115066219045008623973829 40709074916070939116995093)
                    ·
                      refine ⟨1908237886690825271109145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40709074916070939116995093 1908237886690825271109145)
                      ·
                        rfl

theorem cell23_3716280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_3716280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716280 prefixEnd_3716280 := by exact prefixLift 3716280
  have htrace : WordTrace (prefixWord ++ tailWord_3716280) baseStart_3716280 baseEnd_3716280 := by
    simpa [prefixWord, tailWord_3716280, baseEnd_3716280] using wordTrace_append hprefix tailTrace_3716280
  have hstable : (prefixWord ++ tailWord_3716280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716280).length < 2 ^ (prefixWord ++ tailWord_3716280).sum := by decide
  have hdescent : baseEnd_3716280 < baseStart_3716280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716281 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 2, 4]
def baseStart_3716281 : Nat := 118140960795 + 3716281 * 2 ^ 59
def prefixEnd_3716281 : Nat := 4983230072969 + 3 ^ 40 * 3716281 * 2
def baseEnd_3716281 : Nat := 636079466723826589065547

theorem tailTrace_3716281 : CollatzResearch.WordTrace tailWord_3716281 prefixEnd_3716281 636079466723826589065547 := by
  unfold tailWord_3716281
  simp only [CollatzResearch.WordTrace]
  refine ⟨135543903449556102109636697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90362602299704068073091131 135543903449556102109636697)
  ·
    refine ⟨101657927587167076582227523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135543903449556102109636697 101657927587167076582227523)
    ·
      refine ⟨152486891380750614873341285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101657927587167076582227523 152486891380750614873341285)
      ·
        refine ⟨28591292133890740288751491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152486891380750614873341285 28591292133890740288751491)
        ·
          refine ⟨42886938200836110433127237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28591292133890740288751491 42886938200836110433127237)
          ·
            refine ⟨8041300912656770706211357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42886938200836110433127237 8041300912656770706211357)
            ·
              refine ⟨3015487842246289014829259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8041300912656770706211357 3015487842246289014829259)
              ·
                refine ⟨4523231763369433522243889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015487842246289014829259 4523231763369433522243889)
                ·
                  refine ⟨3392423822527075141682917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523231763369433522243889 3392423822527075141682917)
                  ·
                    refine ⟨636079466723826589065547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3392423822527075141682917 636079466723826589065547)
                    ·
                      rfl

theorem cell23_3716281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 4].length) (baseStart_3716281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716281 prefixEnd_3716281 := by exact prefixLift 3716281
  have htrace : WordTrace (prefixWord ++ tailWord_3716281) baseStart_3716281 baseEnd_3716281 := by
    simpa [prefixWord, tailWord_3716281, baseEnd_3716281] using wordTrace_append hprefix tailTrace_3716281
  have hstable : (prefixWord ++ tailWord_3716281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716281).length < 2 ^ (prefixWord ++ tailWord_3716281).sum := by decide
  have hdescent : baseEnd_3716281 < baseStart_3716281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716284 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3716284 : Nat := 118140960795 + 3716284 * 2 ^ 59
def prefixEnd_3716284 : Nat := 4983230072969 + 3 ^ 40 * 3716284 * 2
def baseEnd_3716284 : Nat := 1908239940613443255459127

theorem tailTrace_3716284 : CollatzResearch.WordTrace tailWord_3716284 prefixEnd_3716284 1908239940613443255459127 := by
  unfold tailWord_3716284
  simp only [CollatzResearch.WordTrace]
  refine ⟨67772006434272616810997953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90362675245696822414663937 67772006434272616810997953)
  ·
    refine ⟨50829004825704462608248465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67772006434272616810997953 50829004825704462608248465)
    ·
      refine ⟨38121753619278346956186349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50829004825704462608248465 38121753619278346956186349)
      ·
        refine ⟨14295657607229380108569881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38121753619278346956186349 14295657607229380108569881)
        ·
          refine ⟨10721743205422035081427411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14295657607229380108569881 10721743205422035081427411)
          ·
            refine ⟨16082614808133052622141117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10721743205422035081427411 16082614808133052622141117)
            ·
              refine ⟨6030980553049894733302919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16082614808133052622141117 6030980553049894733302919)
              ·
                refine ⟨9046470829574842099954379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6030980553049894733302919 9046470829574842099954379)
                ·
                  refine ⟨13569706244362263149931569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9046470829574842099954379 13569706244362263149931569)
                  ·
                    refine ⟨10177279683271697362448677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13569706244362263149931569 10177279683271697362448677)
                    ·
                      refine ⟨1908239940613443255459127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10177279683271697362448677 1908239940613443255459127)
                      ·
                        rfl

theorem cell23_3716284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3716284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716284 prefixEnd_3716284 := by exact prefixLift 3716284
  have htrace : WordTrace (prefixWord ++ tailWord_3716284) baseStart_3716284 baseEnd_3716284 := by
    simpa [prefixWord, tailWord_3716284, baseEnd_3716284] using wordTrace_append hprefix tailTrace_3716284
  have hstable : (prefixWord ++ tailWord_3716284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716284).length < 2 ^ (prefixWord ++ tailWord_3716284).sum := by decide
  have hdescent : baseEnd_3716284 < baseStart_3716284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716314 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2]
def baseStart_3716314 : Nat := 118140960795 + 3716314 * 2 ^ 59
def prefixEnd_3716314 : Nat := 4983230072969 + 3 ^ 40 * 3716314 * 2
def baseEnd_3716314 : Nat := 1908255345033078138083989

theorem tailTrace_3716314 : CollatzResearch.WordTrace tailWord_3716314 prefixEnd_3716314 1908255345033078138083989 := by
  unfold tailWord_3716314
  simp only [CollatzResearch.WordTrace]
  refine ⟨33886276764609137186396999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90363404705624365830391997 33886276764609137186396999)
  ·
    refine ⟨50829415146913705779595499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33886276764609137186396999 50829415146913705779595499)
    ·
      refine ⟨76244122720370558669393249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50829415146913705779595499 76244122720370558669393249)
      ·
        refine ⟨57183092040277919002044937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76244122720370558669393249 57183092040277919002044937)
        ·
          refine ⟨42887319030208439251533703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57183092040277919002044937 42887319030208439251533703)
          ·
            refine ⟨64330978545312658877300555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42887319030208439251533703 64330978545312658877300555)
            ·
              refine ⟨96496467817968988315950833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64330978545312658877300555 96496467817968988315950833)
              ·
                refine ⟨72372350863476741236963125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96496467817968988315950833 72372350863476741236963125)
                ·
                  refine ⟨6784907893450944490965293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72372350863476741236963125 6784907893450944490965293)
                  ·
                    refine ⟨2544340460044104184111985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6784907893450944490965293 2544340460044104184111985)
                    ·
                      refine ⟨1908255345033078138083989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544340460044104184111985 1908255345033078138083989)
                      ·
                        rfl

theorem cell23_3716314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_3716314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716314 prefixEnd_3716314 := by exact prefixLift 3716314
  have htrace : WordTrace (prefixWord ++ tailWord_3716314) baseStart_3716314 baseEnd_3716314 := by
    simpa [prefixWord, tailWord_3716314, baseEnd_3716314] using wordTrace_append hprefix tailTrace_3716314
  have hstable : (prefixWord ++ tailWord_3716314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716314).length < 2 ^ (prefixWord ++ tailWord_3716314).sum := by decide
  have hdescent : baseEnd_3716314 < baseStart_3716314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716338 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3716338 : Nat := 118140960795 + 3716338 * 2 ^ 59
def prefixEnd_3716338 : Nat := 4983230072969 + 3 ^ 40 * 3716338 * 2
def baseEnd_3716338 : Nat := 1908267668568786044183879

theorem tailTrace_3716338 : CollatzResearch.WordTrace tailWord_3716338 prefixEnd_3716338 1908267668568786044183879 := by
  unfold tailWord_3716338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33886495602587400211115417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90363988273566400562974445 33886495602587400211115417)
  ·
    refine ⟨25414871701940550158336563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33886495602587400211115417 25414871701940550158336563)
    ·
      refine ⟨38122307552910825237504845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25414871701940550158336563 38122307552910825237504845)
      ·
        refine ⟨14295865332341559464064317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38122307552910825237504845 14295865332341559464064317)
        ·
          refine ⟨5360949499628084799024119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14295865332341559464064317 5360949499628084799024119)
          ·
            refine ⟨8041424249442127198536179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360949499628084799024119 8041424249442127198536179)
            ·
              refine ⟨12062136374163190797804269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041424249442127198536179 12062136374163190797804269)
              ·
                refine ⟨4523301140311196549176601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12062136374163190797804269 4523301140311196549176601)
                ·
                  refine ⟨3392475855233397411882451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523301140311196549176601 3392475855233397411882451)
                  ·
                    refine ⟨5088713782850096117823677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392475855233397411882451 5088713782850096117823677)
                    ·
                      refine ⟨1908267668568786044183879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5088713782850096117823677 1908267668568786044183879)
                      ·
                        rfl

theorem cell23_3716338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3716338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716338 prefixEnd_3716338 := by exact prefixLift 3716338
  have htrace : WordTrace (prefixWord ++ tailWord_3716338) baseStart_3716338 baseEnd_3716338 := by
    simpa [prefixWord, tailWord_3716338, baseEnd_3716338] using wordTrace_append hprefix tailTrace_3716338
  have hstable : (prefixWord ++ tailWord_3716338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716338).length < 2 ^ (prefixWord ++ tailWord_3716338).sum := by decide
  have hdescent : baseEnd_3716338 < baseStart_3716338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716377 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 3]
def baseStart_3716377 : Nat := 118140960795 + 3716377 * 2 ^ 59
def prefixEnd_3716377 : Nat := 4983230072969 + 3 ^ 40 * 3716377 * 2
def baseEnd_3716377 : Nat := 1908287694314311391596199

theorem tailTrace_3716377 : CollatzResearch.WordTrace tailWord_3716377 prefixEnd_3716377 1908287694314311391596199 := by
  unfold tailWord_3716377
  simp only [CollatzResearch.WordTrace]
  refine ⟨135547404857208310505131385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90364936571472207003420923 135547404857208310505131385)
  ·
    refine ⟨101660553642906232878848539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135547404857208310505131385 101660553642906232878848539)
    ·
      refine ⟨152490830464359349318272809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101660553642906232878848539 152490830464359349318272809)
      ·
        refine ⟨114368122848269511988704607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152490830464359349318272809 114368122848269511988704607)
        ·
          refine ⟨171552184272404267983056911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114368122848269511988704607 171552184272404267983056911)
          ·
            refine ⟨257328276408606401974585367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171552184272404267983056911 257328276408606401974585367)
            ·
              refine ⟨385992414612909602961878051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257328276408606401974585367 385992414612909602961878051)
              ·
                refine ⟨578988621919364404442817077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385992414612909602961878051 578988621919364404442817077)
                ·
                  refine ⟨54280183304940412916514101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 578988621919364404442817077 54280183304940412916514101)
                  ·
                    refine ⟨5088767184838163710923197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54280183304940412916514101 5088767184838163710923197)
                    ·
                      refine ⟨1908287694314311391596199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5088767184838163710923197 1908287694314311391596199)
                      ·
                        rfl

theorem cell23_3716377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_3716377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716377 prefixEnd_3716377 := by exact prefixLift 3716377
  have htrace : WordTrace (prefixWord ++ tailWord_3716377) baseStart_3716377 baseEnd_3716377 := by
    simpa [prefixWord, tailWord_3716377, baseEnd_3716377] using wordTrace_append hprefix tailTrace_3716377
  have hstable : (prefixWord ++ tailWord_3716377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716377).length < 2 ^ (prefixWord ++ tailWord_3716377).sum := by decide
  have hdescent : baseEnd_3716377 < baseStart_3716377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716378 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2]
def baseStart_3716378 : Nat := 118140960795 + 3716378 * 2 ^ 59
def prefixEnd_3716378 : Nat := 4983230072969 + 3 ^ 40 * 3716378 * 2
def baseEnd_3716378 : Nat := 1908288207794965887683695

theorem tailTrace_3716378 : CollatzResearch.WordTrace tailWord_3716378 prefixEnd_3716378 1908288207794965887683695 := by
  unfold tailWord_3716378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33886860332551171918979447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90364960886803125117278525 33886860332551171918979447)
  ·
    refine ⟨50830290498826757878469171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33886860332551171918979447 50830290498826757878469171)
    ·
      refine ⟨76245435748240136817703757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50830290498826757878469171 76245435748240136817703757)
      ·
        refine ⟨28592038405590051306638909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76245435748240136817703757 28592038405590051306638909)
        ·
          refine ⟨10722014402096269239989591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28592038405590051306638909 10722014402096269239989591)
          ·
            refine ⟨16083021603144403859984387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10722014402096269239989591 16083021603144403859984387)
            ·
              refine ⟨24124532404716605789976581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16083021603144403859984387 24124532404716605789976581)
              ·
                refine ⟨4523349825884363585620609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24124532404716605789976581 4523349825884363585620609)
                ·
                  refine ⟨3392512369413272689215457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523349825884363585620609 3392512369413272689215457)
                  ·
                    refine ⟨2544384277059954516911593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3392512369413272689215457 2544384277059954516911593)
                    ·
                      refine ⟨1908288207794965887683695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544384277059954516911593 1908288207794965887683695)
                      ·
                        rfl

theorem cell23_3716378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_3716378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716378 prefixEnd_3716378 := by exact prefixLift 3716378
  have htrace : WordTrace (prefixWord ++ tailWord_3716378) baseStart_3716378 baseEnd_3716378 := by
    simpa [prefixWord, tailWord_3716378, baseEnd_3716378] using wordTrace_append hprefix tailTrace_3716378
  have hstable : (prefixWord ++ tailWord_3716378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716378).length < 2 ^ (prefixWord ++ tailWord_3716378).sum := by decide
  have hdescent : baseEnd_3716378 < baseStart_3716378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716414 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3716414 : Nat := 118140960795 + 3716414 * 2 ^ 59
def prefixEnd_3716414 : Nat := 4983230072969 + 3 ^ 40 * 3716414 * 2
def baseEnd_3716414 : Nat := 636102231032842582277843

theorem tailTrace_3716414 : CollatzResearch.WordTrace tailWord_3716414 prefixEnd_3716414 636102231032842582277843 := by
  unfold tailWord_3716414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16943594294759283228028537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90365836238716177216152197 16943594294759283228028537)
  ·
    refine ⟨12707695721069462421021403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16943594294759283228028537 12707695721069462421021403)
    ·
      refine ⟨19061543581604193631532105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12707695721069462421021403 19061543581604193631532105)
      ·
        refine ⟨14296157686203145223649079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19061543581604193631532105 14296157686203145223649079)
        ·
          refine ⟨21444236529304717835473619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296157686203145223649079 21444236529304717835473619)
          ·
            refine ⟨32166354793957076753210429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21444236529304717835473619 32166354793957076753210429)
            ·
              refine ⟨12062383047733903782453911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32166354793957076753210429 12062383047733903782453911)
              ·
                refine ⟨18093574571600855673680867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12062383047733903782453911 18093574571600855673680867)
                ·
                  refine ⟨27140361857401283510521301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18093574571600855673680867 27140361857401283510521301)
                  ·
                    refine ⟨636102231032842582277843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27140361857401283510521301 636102231032842582277843)
                    ·
                      rfl

theorem cell23_3716414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3716414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716414 prefixEnd_3716414 := by exact prefixLift 3716414
  have htrace : WordTrace (prefixWord ++ tailWord_3716414) baseStart_3716414 baseEnd_3716414 := by
    simpa [prefixWord, tailWord_3716414, baseEnd_3716414] using wordTrace_append hprefix tailTrace_3716414
  have hstable : (prefixWord ++ tailWord_3716414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716414).length < 2 ^ (prefixWord ++ tailWord_3716414).sum := by decide
  have hdescent : baseEnd_3716414 < baseStart_3716414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716429 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_3716429 : Nat := 118140960795 + 3716429 * 2 ^ 59
def prefixEnd_3716429 : Nat := 4983230072969 + 3 ^ 40 * 3716429 * 2
def baseEnd_3716429 : Nat := 1908314395308345188145961

theorem tailTrace_3716429 : CollatzResearch.WordTrace tailWord_3716429 prefixEnd_3716429 1908314395308345188145961 := by
  unfold tailWord_3716429
  simp only [CollatzResearch.WordTrace]
  refine ⟨135549301453019923386024341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90366200968679948924016227 135549301453019923386024341)
  ·
    refine ⟨6353873505610308908719891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 135549301453019923386024341 6353873505610308908719891)
    ·
      refine ⟨9530810258415463363079837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353873505610308908719891 9530810258415463363079837)
      ·
        refine ⟨3574053846905798761154939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9530810258415463363079837 3574053846905798761154939)
        ·
          refine ⟨5361080770358698141732409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574053846905798761154939 5361080770358698141732409)
          ·
            refine ⟨4020810577769023606299307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5361080770358698141732409 4020810577769023606299307)
            ·
              refine ⟨6031215866653535409448961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4020810577769023606299307 6031215866653535409448961)
              ·
                refine ⟨4523411899990151557086721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6031215866653535409448961 4523411899990151557086721)
                ·
                  refine ⟨3392558924992613667815041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523411899990151557086721 3392558924992613667815041)
                  ·
                    refine ⟨2544419193744460250861281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3392558924992613667815041 2544419193744460250861281)
                    ·
                      refine ⟨1908314395308345188145961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544419193744460250861281 1908314395308345188145961)
                      ·
                        rfl

theorem cell23_3716429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_3716429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716429 prefixEnd_3716429 := by exact prefixLift 3716429
  have htrace : WordTrace (prefixWord ++ tailWord_3716429) baseStart_3716429 baseEnd_3716429 := by
    simpa [prefixWord, tailWord_3716429, baseEnd_3716429] using wordTrace_append hprefix tailTrace_3716429
  have hstable : (prefixWord ++ tailWord_3716429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716429).length < 2 ^ (prefixWord ++ tailWord_3716429).sum := by decide
  have hdescent : baseEnd_3716429 < baseStart_3716429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716434 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3716434 : Nat := 118140960795 + 3716434 * 2 ^ 59
def prefixEnd_3716434 : Nat := 4983230072969 + 3 ^ 40 * 3716434 * 2
def baseEnd_3716434 : Nat := 1908316962711617668583437

theorem tailTrace_3716434 : CollatzResearch.WordTrace tailWord_3716434 prefixEnd_3716434 1908316962711617668583437 := by
  unfold tailWord_3716434
  simp only [CollatzResearch.WordTrace]
  refine ⟨33887370954500452309989089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90366322545334539493304237 33887370954500452309989089)
  ·
    refine ⟨25415528215875339232491817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33887370954500452309989089 25415528215875339232491817)
    ·
      refine ⟨19061646161906504424368863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25415528215875339232491817 19061646161906504424368863)
      ·
        refine ⟨28592469242859756636553295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19061646161906504424368863 28592469242859756636553295)
        ·
          refine ⟨42888703864289634954829943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28592469242859756636553295 42888703864289634954829943)
          ·
            refine ⟨64333055796434452432244915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42888703864289634954829943 64333055796434452432244915)
            ·
              refine ⟨96499583694651678648367373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64333055796434452432244915 96499583694651678648367373)
              ·
                refine ⟨36187343885494379493137765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96499583694651678648367373 36187343885494379493137765)
                ·
                  refine ⟨6785126978530196154963331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36187343885494379493137765 6785126978530196154963331)
                  ·
                    refine ⟨10177690467795294232444997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6785126978530196154963331 10177690467795294232444997)
                    ·
                      refine ⟨1908316962711617668583437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10177690467795294232444997 1908316962711617668583437)
                      ·
                        rfl

theorem cell23_3716434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3716434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716434 prefixEnd_3716434 := by exact prefixLift 3716434
  have htrace : WordTrace (prefixWord ++ tailWord_3716434) baseStart_3716434 baseEnd_3716434 := by
    simpa [prefixWord, tailWord_3716434, baseEnd_3716434] using wordTrace_append hprefix tailTrace_3716434
  have hstable : (prefixWord ++ tailWord_3716434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716434).length < 2 ^ (prefixWord ++ tailWord_3716434).sum := by decide
  have hdescent : baseEnd_3716434 < baseStart_3716434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716447 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_3716447 : Nat := 118140960795 + 3716447 * 2 ^ 59
def prefixEnd_3716447 : Nat := 4983230072969 + 3 ^ 40 * 3716447 * 2
def baseEnd_3716447 : Nat := 1908323637960126117720877

theorem tailTrace_3716447 : CollatzResearch.WordTrace tailWord_3716447 prefixEnd_3716447 1908323637960126117720877 := by
  unfold tailWord_3716447
  simp only [CollatzResearch.WordTrace]
  refine ⟨135549957966954712460179595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90366638644636474973453063 135549957966954712460179595)
  ·
    refine ⟨203324936950432068690269393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135549957966954712460179595 203324936950432068690269393)
    ·
      refine ⟨152493702712824051517702045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203324936950432068690269393 152493702712824051517702045)
      ·
        refine ⟨57185138517309019319138267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152493702712824051517702045 57185138517309019319138267)
        ·
          refine ⟨85777707775963528978707401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57185138517309019319138267 85777707775963528978707401)
          ·
            refine ⟨64333280831972646734030551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85777707775963528978707401 64333280831972646734030551)
            ·
              refine ⟨96499921247958970101045827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64333280831972646734030551 96499921247958970101045827)
              ·
                refine ⟨144749881871938455151568741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96499921247958970101045827 144749881871938455151568741)
                ·
                  refine ⟨27140602850988460340919139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144749881871938455151568741 27140602850988460340919139)
                  ·
                    refine ⟨40710904276482690511378709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27140602850988460340919139 40710904276482690511378709)
                    ·
                      refine ⟨1908323637960126117720877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40710904276482690511378709 1908323637960126117720877)
                      ·
                        rfl

theorem cell23_3716447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_3716447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716447 prefixEnd_3716447 := by exact prefixLift 3716447
  have htrace : WordTrace (prefixWord ++ tailWord_3716447) baseStart_3716447 baseEnd_3716447 := by
    simpa [prefixWord, tailWord_3716447, baseEnd_3716447] using wordTrace_append hprefix tailTrace_3716447
  have hstable : (prefixWord ++ tailWord_3716447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716447).length < 2 ^ (prefixWord ++ tailWord_3716447).sum := by decide
  have hdescent : baseEnd_3716447 < baseStart_3716447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716451 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 2, 4, 2]
def baseStart_3716451 : Nat := 118140960795 + 3716451 * 2 ^ 59
def prefixEnd_3716451 : Nat := 4983230072969 + 3 ^ 40 * 3716451 * 2
def baseEnd_3716451 : Nat := 1908325691882744102070859

theorem tailTrace_3716451 : CollatzResearch.WordTrace tailWord_3716451 prefixEnd_3716451 1908325691882744102070859 := by
  unfold tailWord_3716451
  simp only [CollatzResearch.WordTrace]
  refine ⟨135550103858940221143325207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90366735905960147428883471 135550103858940221143325207)
  ·
    refine ⟨203325155788410331714987811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135550103858940221143325207 203325155788410331714987811)
    ·
      refine ⟨304987733682615497572481717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203325155788410331714987811 304987733682615497572481717)
      ·
        refine ⟨28592600032745202897420161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304987733682615497572481717 28592600032745202897420161)
        ·
          refine ⟨21444450024558902173065121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28592600032745202897420161 21444450024558902173065121)
          ·
            refine ⟨16083337518419176629798841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21444450024558902173065121 16083337518419176629798841)
            ·
              refine ⟨12062503138814382472349131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16083337518419176629798841 12062503138814382472349131)
              ·
                refine ⟨18093754708221573708523697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12062503138814382472349131 18093754708221573708523697)
                ·
                  refine ⟨13570316031166180281392773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18093754708221573708523697 13570316031166180281392773)
                  ·
                    refine ⟨2544434255843658802761145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13570316031166180281392773 2544434255843658802761145)
                    ·
                      refine ⟨1908325691882744102070859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544434255843658802761145 1908325691882744102070859)
                      ·
                        rfl

theorem cell23_3716451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_3716451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716451 prefixEnd_3716451 := by exact prefixLift 3716451
  have htrace : WordTrace (prefixWord ++ tailWord_3716451) baseStart_3716451 baseEnd_3716451 := by
    simpa [prefixWord, tailWord_3716451, baseEnd_3716451] using wordTrace_append hprefix tailTrace_3716451
  have hstable : (prefixWord ++ tailWord_3716451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716451).length < 2 ^ (prefixWord ++ tailWord_3716451).sum := by decide
  have hdescent : baseEnd_3716451 < baseStart_3716451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716461 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_3716461 : Nat := 118140960795 + 3716461 * 2 ^ 59
def prefixEnd_3716461 : Nat := 4983230072969 + 3 ^ 40 * 3716461 * 2
def baseEnd_3716461 : Nat := 636110275563096354315271

theorem tailTrace_3716461 : CollatzResearch.WordTrace tailWord_3716461 prefixEnd_3716461 636110275563096354315271 := by
  unfold tailWord_3716461
  simp only [CollatzResearch.WordTrace]
  refine ⟨135550468588903992851189237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90366979059269328567459491 135550468588903992851189237)
  ·
    refine ⟨12707856430209749329798991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135550468588903992851189237 12707856430209749329798991)
    ·
      refine ⟨19061784645314623994698487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12707856430209749329798991 19061784645314623994698487)
      ·
        refine ⟨28592676967971935992047731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19061784645314623994698487 28592676967971935992047731)
        ·
          refine ⟨42889015451957903988071597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28592676967971935992047731 42889015451957903988071597)
          ·
            refine ⟨16083380794484213995526849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42889015451957903988071597 16083380794484213995526849)
            ·
              refine ⟨12062535595863160496645137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16083380794484213995526849 12062535595863160496645137)
              ·
                refine ⟨9046901696897370372483853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12062535595863160496645137 9046901696897370372483853)
                ·
                  refine ⟨3392588136336513889681445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9046901696897370372483853 3392588136336513889681445)
                  ·
                    refine ⟨636110275563096354315271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3392588136336513889681445 636110275563096354315271)
                    ·
                      rfl

theorem cell23_3716461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_3716461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716461 prefixEnd_3716461 := by exact prefixLift 3716461
  have htrace : WordTrace (prefixWord ++ tailWord_3716461) baseStart_3716461 baseEnd_3716461 := by
    simpa [prefixWord, tailWord_3716461, baseEnd_3716461] using wordTrace_append hprefix tailTrace_3716461
  have hstable : (prefixWord ++ tailWord_3716461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716461).length < 2 ^ (prefixWord ++ tailWord_3716461).sum := by decide
  have hdescent : baseEnd_3716461 < baseStart_3716461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716508 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 6]
def baseStart_3716508 : Nat := 118140960795 + 3716508 * 2 ^ 59
def prefixEnd_3716508 : Nat := 4983230072969 + 3 ^ 40 * 3716508 * 2
def baseEnd_3716508 : Nat := 212039440031116708784233

theorem tailTrace_3716508 : CollatzResearch.WordTrace tailWord_3716508 prefixEnd_3716508 212039440031116708784233 := by
  unfold tailWord_3716508
  simp only [CollatzResearch.WordTrace]
  refine ⟨67776091409866859939075089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90368121879822479918766785 67776091409866859939075089)
  ·
    refine ⟨50832068557400144954306317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67776091409866859939075089 50832068557400144954306317)
    ·
      refine ⟨19062025709025054357864869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50832068557400144954306317 19062025709025054357864869)
      ·
        refine ⟨3574129820442197692099663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19062025709025054357864869 3574129820442197692099663)
        ·
          refine ⟨5361194730663296538149495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574129820442197692099663 5361194730663296538149495)
          ·
            refine ⟨8041792095994944807224243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361194730663296538149495 8041792095994944807224243)
            ·
              refine ⟨12062688143992417210836365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041792095994944807224243 12062688143992417210836365)
              ·
                refine ⟨4523508053997156454063637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12062688143992417210836365 4523508053997156454063637)
                ·
                  refine ⟨212039440031116708784233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4523508053997156454063637 212039440031116708784233)
                  ·
                    rfl

theorem cell23_3716508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_3716508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716508 prefixEnd_3716508 := by exact prefixLift 3716508
  have htrace : WordTrace (prefixWord ++ tailWord_3716508) baseStart_3716508 baseEnd_3716508 := by
    simpa [prefixWord, tailWord_3716508, baseEnd_3716508] using wordTrace_append hprefix tailTrace_3716508
  have hstable : (prefixWord ++ tailWord_3716508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716508).length < 2 ^ (prefixWord ++ tailWord_3716508).sum := by decide
  have hdescent : baseEnd_3716508 < baseStart_3716508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716546 : List Nat := [3, 5, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3716546 : Nat := 118140960795 + 3716546 * 2 ^ 59
def prefixEnd_3716546 : Nat := 4983230072969 + 3 ^ 40 * 3716546 * 2
def baseEnd_3716546 : Nat := 636124824181640410127641

theorem tailTrace_3716546 : CollatzResearch.WordTrace tailWord_3716546 prefixEnd_3716546 636124824181640410127641 := by
  unfold tailWord_3716546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33888392198399013092008373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90369045862397368245355661 33888392198399013092008373)
  ·
    refine ⟨3177036768599907477375785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33888392198399013092008373 3177036768599907477375785)
    ·
      refine ⟨2382777576449930608031839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3177036768599907477375785 2382777576449930608031839)
      ·
        refine ⟨3574166364674895912047759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382777576449930608031839 3574166364674895912047759)
        ·
          refine ⟨5361249547012343868071639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574166364674895912047759 5361249547012343868071639)
          ·
            refine ⟨8041874320518515802107459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361249547012343868071639 8041874320518515802107459)
            ·
              refine ⟨12062811480777773703161189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041874320518515802107459 12062811480777773703161189)
              ·
                refine ⟨2261777152645832569342723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12062811480777773703161189 2261777152645832569342723)
                ·
                  refine ⟨3392665728968748854014085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261777152645832569342723 3392665728968748854014085)
                  ·
                    refine ⟨636124824181640410127641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3392665728968748854014085 636124824181640410127641)
                    ·
                      rfl

theorem cell23_3716546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3716546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716546 prefixEnd_3716546 := by exact prefixLift 3716546
  have htrace : WordTrace (prefixWord ++ tailWord_3716546) baseStart_3716546 baseEnd_3716546 := by
    simpa [prefixWord, tailWord_3716546, baseEnd_3716546] using wordTrace_append hprefix tailTrace_3716546
  have hstable : (prefixWord ++ tailWord_3716546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716546).length < 2 ^ (prefixWord ++ tailWord_3716546).sum := by decide
  have hdescent : baseEnd_3716546 < baseStart_3716546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716591 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 3]
def baseStart_3716591 : Nat := 118140960795 + 3716591 * 2 ^ 59
def prefixEnd_3716591 : Nat := 4983230072969 + 3 ^ 40 * 3716591 * 2
def baseEnd_3716591 : Nat := 1908397579174373554320215

theorem tailTrace_3716591 : CollatzResearch.WordTrace tailWord_3716591 prefixEnd_3716591 1908397579174373554320215 := by
  unfold tailWord_3716591
  simp only [CollatzResearch.WordTrace]
  refine ⟨135555210078433025053421627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90370140052288683368947751 135555210078433025053421627)
  ·
    refine ⟨203332815117649537580132441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135555210078433025053421627 203332815117649537580132441)
    ·
      refine ⟨152499611338237153185099331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203332815117649537580132441 152499611338237153185099331)
      ·
        refine ⟨228749417007355729777648997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152499611338237153185099331 228749417007355729777648997)
        ·
          refine ⟨42890515688879199333309187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228749417007355729777648997 42890515688879199333309187)
          ·
            refine ⟨64335773533318798999963781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42890515688879199333309187 64335773533318798999963781)
            ·
              refine ⟨12062957537497274812493209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64335773533318798999963781 12062957537497274812493209)
              ·
                refine ⟨9047218153122956109369907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12062957537497274812493209 9047218153122956109369907)
                ·
                  refine ⟨13570827229684434164054861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9047218153122956109369907 13570827229684434164054861)
                  ·
                    refine ⟨5089060211131662811520573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13570827229684434164054861 5089060211131662811520573)
                    ·
                      refine ⟨1908397579174373554320215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5089060211131662811520573 1908397579174373554320215)
                      ·
                        rfl

theorem cell23_3716591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_3716591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716591 prefixEnd_3716591 := by exact prefixLift 3716591
  have htrace : WordTrace (prefixWord ++ tailWord_3716591) baseStart_3716591 baseEnd_3716591 := by
    simpa [prefixWord, tailWord_3716591, baseEnd_3716591] using wordTrace_append hprefix tailTrace_3716591
  have hstable : (prefixWord ++ tailWord_3716591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716591).length < 2 ^ (prefixWord ++ tailWord_3716591).sum := by decide
  have hdescent : baseEnd_3716591 < baseStart_3716591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716592 : List Nat := [2, 1, 1, 1, 3, 5, 2, 3, 1, 2, 2]
def baseStart_3716592 : Nat := 118140960795 + 3716592 * 2 ^ 59
def prefixEnd_3716592 : Nat := 4983230072969 + 3 ^ 40 * 3716592 * 2
def baseEnd_3716592 : Nat := 1908398092655028050407711

theorem tailTrace_3716592 : CollatzResearch.WordTrace tailWord_3716592 prefixEnd_3716592 1908398092655028050407711 := by
  unfold tailWord_3716592
  simp only [CollatzResearch.WordTrace]
  refine ⟨67777623275714701112104015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90370164367619601482805353 67777623275714701112104015)
  ·
    refine ⟨101666434913572051668156023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67777623275714701112104015 101666434913572051668156023)
    ·
      refine ⟨152499652370358077502234035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101666434913572051668156023 152499652370358077502234035)
      ·
        refine ⟨228749478555537116253351053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152499652370358077502234035 228749478555537116253351053)
        ·
          refine ⟨85781054458326418595006645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228749478555537116253351053 85781054458326418595006645)
          ·
            refine ⟨8041973855468101743281873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85781054458326418595006645 8041973855468101743281873)
            ·
              refine ⟨6031480391601076307461405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8041973855468101743281873 6031480391601076307461405)
              ·
                refine ⟨2261805146850403615298027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6031480391601076307461405 2261805146850403615298027)
                ·
                  refine ⟨3392707720275605422947041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2261805146850403615298027 3392707720275605422947041)
                  ·
                    refine ⟨2544530790206704067210281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3392707720275605422947041 2544530790206704067210281)
                    ·
                      refine ⟨1908398092655028050407711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544530790206704067210281 1908398092655028050407711)
                      ·
                        rfl

theorem cell23_3716592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 1, 2, 2].length) (baseStart_3716592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716592 prefixEnd_3716592 := by exact prefixLift 3716592
  have htrace : WordTrace (prefixWord ++ tailWord_3716592) baseStart_3716592 baseEnd_3716592 := by
    simpa [prefixWord, tailWord_3716592, baseEnd_3716592] using wordTrace_append hprefix tailTrace_3716592
  have hstable : (prefixWord ++ tailWord_3716592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716592).length < 2 ^ (prefixWord ++ tailWord_3716592).sum := by decide
  have hdescent : baseEnd_3716592 < baseStart_3716592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716625 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 2, 1, 3]
def baseStart_3716625 : Nat := 118140960795 + 3716625 * 2 ^ 59
def prefixEnd_3716625 : Nat := 4983230072969 + 3 ^ 40 * 3716625 * 2
def baseEnd_3716625 : Nat := 1908415037516626421295059

theorem tailTrace_3716625 : CollatzResearch.WordTrace tailWord_3716625 prefixEnd_3716625 1908415037516626421295059 := by
  unfold tailWord_3716625
  simp only [CollatzResearch.WordTrace]
  refine ⟨135556450160309848860159329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90370966773539899240106219 135556450160309848860159329)
  ·
    refine ⟨101667337620232386645119497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135556450160309848860159329 101667337620232386645119497)
    ·
      refine ⟨76250503215174289983839623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101667337620232386645119497 76250503215174289983839623)
      ·
        refine ⟨114375754822761434975759435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76250503215174289983839623 114375754822761434975759435)
        ·
          refine ⟨171563632234142152463639153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114375754822761434975759435 171563632234142152463639153)
          ·
            refine ⟨128672724175606614347729365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171563632234142152463639153 128672724175606614347729365)
            ·
              refine ⟨3015766972865780023774907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128672724175606614347729365 3015766972865780023774907)
              ·
                refine ⟨4523650459298670035662361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015766972865780023774907 4523650459298670035662361)
                ·
                  refine ⟨3392737844474002526746771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4523650459298670035662361 3392737844474002526746771)
                  ·
                    refine ⟨5089106766711003790120157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3392737844474002526746771 5089106766711003790120157)
                    ·
                      refine ⟨1908415037516626421295059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5089106766711003790120157 1908415037516626421295059)
                      ·
                        rfl

theorem cell23_3716625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_3716625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716625 prefixEnd_3716625 := by exact prefixLift 3716625
  have htrace : WordTrace (prefixWord ++ tailWord_3716625) baseStart_3716625 baseEnd_3716625 := by
    simpa [prefixWord, tailWord_3716625, baseEnd_3716625] using wordTrace_append hprefix tailTrace_3716625
  have hstable : (prefixWord ++ tailWord_3716625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716625).length < 2 ^ (prefixWord ++ tailWord_3716625).sum := by decide
  have hdescent : baseEnd_3716625 < baseStart_3716625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716665 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 4, 2, 2]
def baseStart_3716665 : Nat := 118140960795 + 3716665 * 2 ^ 59
def prefixEnd_3716665 : Nat := 4983230072969 + 3 ^ 40 * 3716665 * 2
def baseEnd_3716665 : Nat := 1908435576742806264794875

theorem tailTrace_3716665 : CollatzResearch.WordTrace tailWord_3716665 prefixEnd_3716665 1908435576742806264794875 := by
  unfold tailWord_3716665
  simp only [CollatzResearch.WordTrace]
  refine ⟨135557909080164935691615449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90371939386776623794410299 135557909080164935691615449)
  ·
    refine ⟨101668431810123701768711587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135557909080164935691615449 101668431810123701768711587)
    ·
      refine ⟨152502647715185552653067381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101668431810123701768711587 152502647715185552653067381)
      ·
        refine ⟨14297123223298645561225067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152502647715185552653067381 14297123223298645561225067)
        ·
          refine ⟨21445684834947968341837601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14297123223298645561225067 21445684834947968341837601)
          ·
            refine ⟨16084263626210976256378201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21445684834947968341837601 16084263626210976256378201)
            ·
              refine ⟨12063197719658232192283651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16084263626210976256378201 12063197719658232192283651)
              ·
                refine ⟨18094796579487348288425477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12063197719658232192283651 18094796579487348288425477)
                ·
                  refine ⟨3392774358653877804079777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18094796579487348288425477 3392774358653877804079777)
                  ·
                    refine ⟨2544580768990408353059833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3392774358653877804079777 2544580768990408353059833)
                    ·
                      refine ⟨1908435576742806264794875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544580768990408353059833 1908435576742806264794875)
                      ·
                        rfl

theorem cell23_3716665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_3716665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716665 prefixEnd_3716665 := by exact prefixLift 3716665
  have htrace : WordTrace (prefixWord ++ tailWord_3716665) baseStart_3716665 baseEnd_3716665 := by
    simpa [prefixWord, tailWord_3716665, baseEnd_3716665] using wordTrace_append hprefix tailTrace_3716665
  have hstable : (prefixWord ++ tailWord_3716665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716665).length < 2 ^ (prefixWord ++ tailWord_3716665).sum := by decide
  have hdescent : baseEnd_3716665 < baseStart_3716665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716671 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 7]
def baseStart_3716671 : Nat := 118140960795 + 3716671 * 2 ^ 59
def prefixEnd_3716671 : Nat := 4983230072969 + 3 ^ 40 * 3716671 * 2
def baseEnd_3716671 : Nat := 212048739736303693479983

theorem tailTrace_3716671 : CollatzResearch.WordTrace tailWord_3716671 prefixEnd_3716671 212048739736303693479983 := by
  unfold tailWord_3716671
  simp only [CollatzResearch.WordTrace]
  refine ⟨135558127918143198716333867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90372085278762132477555911 135558127918143198716333867)
  ·
    refine ⟨203337191877214798074500801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135558127918143198716333867 203337191877214798074500801)
    ·
      refine ⟨152502893907911098555875601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203337191877214798074500801 152502893907911098555875601)
      ·
        refine ⟨114377170430933323916906701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152502893907911098555875601 114377170430933323916906701)
        ·
          refine ⟨42891438911599996468840013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114377170430933323916906701 42891438911599996468840013)
          ·
            refine ⟨16084289591849998675815005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42891438911599996468840013 16084289591849998675815005)
            ·
              refine ⟨6031608596943749503430627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16084289591849998675815005 6031608596943749503430627)
              ·
                refine ⟨9047412895415624255145941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031608596943749503430627 9047412895415624255145941)
                ·
                  refine ⟨212048739736303693479983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9047412895415624255145941 212048739736303693479983)
                  ·
                    rfl

theorem cell23_3716671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 7].length) (baseStart_3716671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716671 prefixEnd_3716671 := by exact prefixLift 3716671
  have htrace : WordTrace (prefixWord ++ tailWord_3716671) baseStart_3716671 baseEnd_3716671 := by
    simpa [prefixWord, tailWord_3716671, baseEnd_3716671] using wordTrace_append hprefix tailTrace_3716671
  have hstable : (prefixWord ++ tailWord_3716671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716671).length < 2 ^ (prefixWord ++ tailWord_3716671).sum := by decide
  have hdescent : baseEnd_3716671 < baseStart_3716671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716681 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 3]
def baseStart_3716681 : Nat := 118140960795 + 3716681 * 2 ^ 59
def prefixEnd_3716681 : Nat := 4983230072969 + 3 ^ 40 * 3716681 * 2
def baseEnd_3716681 : Nat := 1908443792433278202194801

theorem tailTrace_3716681 : CollatzResearch.WordTrace tailWord_3716681 prefixEnd_3716681 1908443792433278202194801 := by
  unfold tailWord_3716681
  simp only [CollatzResearch.WordTrace]
  refine ⟨135558492648106970424197897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90372328432071313616131931 135558492648106970424197897)
  ·
    refine ⟨101668869486080227818148423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135558492648106970424197897 101668869486080227818148423)
    ·
      refine ⟨152503304229120341727222635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101668869486080227818148423 152503304229120341727222635)
      ·
        refine ⟨228754956343680512590833953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152503304229120341727222635 228754956343680512590833953)
        ·
          refine ⟨171566217257760384443125465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228754956343680512590833953 171566217257760384443125465)
          ·
            refine ⟨128674662943320288332344099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171566217257760384443125465 128674662943320288332344099)
            ·
              refine ⟨193011994414980432498516149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128674662943320288332344099 193011994414980432498516149)
              ·
                refine ⟨18094874476404415546735889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193011994414980432498516149 18094874476404415546735889)
                ·
                  refine ⟨13571155857303311660051917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18094874476404415546735889 13571155857303311660051917)
                  ·
                    refine ⟨5089183446488741872519469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13571155857303311660051917 5089183446488741872519469)
                    ·
                      refine ⟨1908443792433278202194801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5089183446488741872519469 1908443792433278202194801)
                      ·
                        rfl

theorem cell23_3716681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_3716681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716681 prefixEnd_3716681 := by exact prefixLift 3716681
  have htrace : WordTrace (prefixWord ++ tailWord_3716681) baseStart_3716681 baseEnd_3716681 := by
    simpa [prefixWord, tailWord_3716681, baseEnd_3716681] using wordTrace_append hprefix tailTrace_3716681
  have hstable : (prefixWord ++ tailWord_3716681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716681).length < 2 ^ (prefixWord ++ tailWord_3716681).sum := by decide
  have hdescent : baseEnd_3716681 < baseStart_3716681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716711 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_3716711 : Nat := 118140960795 + 3716711 * 2 ^ 59
def prefixEnd_3716711 : Nat := 4983230072969 + 3 ^ 40 * 3716711 * 2
def baseEnd_3716711 : Nat := 1908459196852913084819663

theorem tailTrace_3716711 : CollatzResearch.WordTrace tailWord_3716711 prefixEnd_3716711 1908459196852913084819663 := by
  unfold tailWord_3716711
  simp only [CollatzResearch.WordTrace]
  refine ⟨135559586837998285547789987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90373057891998857031859991 135559586837998285547789987)
  ·
    refine ⟨203339380256997428321684981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135559586837998285547789987 203339380256997428321684981)
    ·
      refine ⟨19063066899093508905157967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203339380256997428321684981 19063066899093508905157967)
      ·
        refine ⟨28594600348640263357736951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19063066899093508905157967 28594600348640263357736951)
        ·
          refine ⟨42891900522960395036605427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28594600348640263357736951 42891900522960395036605427)
          ·
            refine ⟨64337850784440592554908141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42891900522960395036605427 64337850784440592554908141)
            ·
              refine ⟨24126694044165222208090553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64337850784440592554908141 24126694044165222208090553)
              ·
                refine ⟨18095020533123916656067915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24126694044165222208090553 18095020533123916656067915)
                ·
                  refine ⟨27142530799685874984101873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18095020533123916656067915 27142530799685874984101873)
                  ·
                    refine ⟨20356898099764406238076405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27142530799685874984101873 20356898099764406238076405)
                    ·
                      refine ⟨1908459196852913084819663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20356898099764406238076405 1908459196852913084819663)
                      ·
                        rfl

theorem cell23_3716711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_3716711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716711 prefixEnd_3716711 := by exact prefixLift 3716711
  have htrace : WordTrace (prefixWord ++ tailWord_3716711) baseStart_3716711 baseEnd_3716711 := by
    simpa [prefixWord, tailWord_3716711, baseEnd_3716711] using wordTrace_append hprefix tailTrace_3716711
  have hstable : (prefixWord ++ tailWord_3716711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716711).length < 2 ^ (prefixWord ++ tailWord_3716711).sum := by decide
  have hdescent : baseEnd_3716711 < baseStart_3716711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716722 : List Nat := [3, 2, 1, 2, 3, 3, 2, 2, 5]
def baseStart_3716722 : Nat := 118140960795 + 3716722 * 2 ^ 59
def prefixEnd_3716722 : Nat := 4983230072969 + 3 ^ 40 * 3716722 * 2
def baseEnd_3716722 : Nat := 212051649460012504642457

theorem tailTrace_3716722 : CollatzResearch.WordTrace tailWord_3716722 prefixEnd_3716722 212051649460012504642457 := by
  unfold tailWord_3716722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33889997010239608606610105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90373325360638956284293613 33889997010239608606610105)
  ·
    refine ⟨25417497757679706454957579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33889997010239608606610105 25417497757679706454957579)
    ·
      refine ⟨38126246636519559682436369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25417497757679706454957579 38126246636519559682436369)
      ·
        refine ⟨28594684977389669761827277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38126246636519559682436369 28594684977389669761827277)
        ·
          refine ⟨10723006866521126160685229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28594684977389669761827277 10723006866521126160685229)
          ·
            refine ⟨4021127574945422310256961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10723006866521126160685229 4021127574945422310256961)
            ·
              refine ⟨3015845681209066732692721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021127574945422310256961 3015845681209066732692721)
              ·
                refine ⟨2261884260906800049519541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3015845681209066732692721 2261884260906800049519541)
                ·
                  refine ⟨212051649460012504642457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2261884260906800049519541 212051649460012504642457)
                  ·
                    rfl

theorem cell23_3716722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_3716722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716722 prefixEnd_3716722 := by exact prefixLift 3716722
  have htrace : WordTrace (prefixWord ++ tailWord_3716722) baseStart_3716722 baseEnd_3716722 := by
    simpa [prefixWord, tailWord_3716722, baseEnd_3716722] using wordTrace_append hprefix tailTrace_3716722
  have hstable : (prefixWord ++ tailWord_3716722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716722).length < 2 ^ (prefixWord ++ tailWord_3716722).sum := by decide
  have hdescent : baseEnd_3716722 < baseStart_3716722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716725 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3716725 : Nat := 118140960795 + 3716725 * 2 ^ 59
def prefixEnd_3716725 : Nat := 4983230072969 + 3 ^ 40 * 3716725 * 2
def baseEnd_3716725 : Nat := 1908466385582076030044599

theorem tailTrace_3716725 : CollatzResearch.WordTrace tailWord_3716725 prefixEnd_3716725 1908466385582076030044599 := by
  unfold tailWord_3716725
  simp only [CollatzResearch.WordTrace]
  refine ⟨135560097459947565938799629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90373398306631710625866419 135560097459947565938799629)
  ·
    refine ⟨50835036547480337227049861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135560097459947565938799629 50835036547480337227049861)
    ·
      refine ⟨9531569352652563230071849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50835036547480337227049861 9531569352652563230071849)
      ·
        refine ⟨7148677014489422422553887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9531569352652563230071849 7148677014489422422553887)
        ·
          refine ⟨10723015521734133633830831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148677014489422422553887 10723015521734133633830831)
          ·
            refine ⟨16084523282601200450746247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723015521734133633830831 16084523282601200450746247)
            ·
              refine ⟨24126784923901800676119371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16084523282601200450746247 24126784923901800676119371)
              ·
                refine ⟨36190177385852701014179057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24126784923901800676119371 36190177385852701014179057)
                ·
                  refine ⟨27142633039389525760634293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36190177385852701014179057 27142633039389525760634293)
                  ·
                    refine ⟨2544621847442768040059465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27142633039389525760634293 2544621847442768040059465)
                    ·
                      refine ⟨1908466385582076030044599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544621847442768040059465 1908466385582076030044599)
                      ·
                        rfl

theorem cell23_3716725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3716725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716725 prefixEnd_3716725 := by exact prefixLift 3716725
  have htrace : WordTrace (prefixWord ++ tailWord_3716725) baseStart_3716725 baseEnd_3716725 := by
    simpa [prefixWord, tailWord_3716725, baseEnd_3716725] using wordTrace_append hprefix tailTrace_3716725
  have hstable : (prefixWord ++ tailWord_3716725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716725).length < 2 ^ (prefixWord ++ tailWord_3716725).sum := by decide
  have hdescent : baseEnd_3716725 < baseStart_3716725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716748 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_3716748 : Nat := 118140960795 + 3716748 * 2 ^ 59
def prefixEnd_3716748 : Nat := 4983230072969 + 3 ^ 40 * 3716748 * 2
def baseEnd_3716748 : Nat := 636159398545709813352331

theorem tailTrace_3716748 : CollatzResearch.WordTrace tailWord_3716748 prefixEnd_3716748 636159398545709813352331 := by
  unfold tailWord_3716748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67780468169432120433443449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90373957559242827244591265 67780468169432120433443449)
  ·
    refine ⟨50835351127074090325082587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67780468169432120433443449 50835351127074090325082587)
    ·
      refine ⟨76253026690611135487623881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50835351127074090325082587 76253026690611135487623881)
      ·
        refine ⟨57189770017958351615717911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76253026690611135487623881 57189770017958351615717911)
        ·
          refine ⟨85784655026937527423576867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57189770017958351615717911 85784655026937527423576867)
          ·
            refine ⟨128676982540406291135365301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85784655026937527423576867 128676982540406291135365301)
            ·
              refine ⟨12063467113163089793940497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128676982540406291135365301 12063467113163089793940497)
              ·
                refine ⟨9047600334872317345455373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12063467113163089793940497 9047600334872317345455373)
                ·
                  refine ⟨3392850125577119004545765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9047600334872317345455373 3392850125577119004545765)
                  ·
                    refine ⟨636159398545709813352331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3392850125577119004545765 636159398545709813352331)
                    ·
                      rfl

theorem cell23_3716748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_3716748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716748 prefixEnd_3716748 := by exact prefixLift 3716748
  have htrace : WordTrace (prefixWord ++ tailWord_3716748) baseStart_3716748 baseEnd_3716748 := by
    simpa [prefixWord, tailWord_3716748, baseEnd_3716748] using wordTrace_append hprefix tailTrace_3716748
  have hstable : (prefixWord ++ tailWord_3716748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716748).length < 2 ^ (prefixWord ++ tailWord_3716748).sum := by decide
  have hdescent : baseEnd_3716748 < baseStart_3716748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716811 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4]
def baseStart_3716811 : Nat := 118140960795 + 3716811 * 2 ^ 59
def prefixEnd_3716811 : Nat := 4983230072969 + 3 ^ 40 * 3716811 * 2
def baseEnd_3716811 : Nat := 1908510544918362693569203

theorem tailTrace_3716811 : CollatzResearch.WordTrace tailWord_3716811 prefixEnd_3716811 1908510544918362693569203 := by
  unfold tailWord_3716811
  simp only [CollatzResearch.WordTrace]
  refine ⟨135563234137636002626430287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90375489425090668417620191 135563234137636002626430287)
  ·
    refine ⟨203344851206454003939645431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135563234137636002626430287 203344851206454003939645431)
    ·
      refine ⟨305017276809681005909468147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203344851206454003939645431 305017276809681005909468147)
      ·
        refine ⟨457525915214521508864202221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305017276809681005909468147 457525915214521508864202221)
        ·
          refine ⟨171572218205445565824075833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457525915214521508864202221 171572218205445565824075833)
          ·
            refine ⟨128679163654084174368056875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171572218205445565824075833 128679163654084174368056875)
            ·
              refine ⟨193018745481126261552085313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128679163654084174368056875 193018745481126261552085313)
              ·
                refine ⟨144764059110844696164063985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193018745481126261552085313 144764059110844696164063985)
                ·
                  refine ⟨108573044333133522123047989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144764059110844696164063985 108573044333133522123047989)
                  ·
                    refine ⟨10178722906231267699035749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108573044333133522123047989 10178722906231267699035749)
                    ·
                      refine ⟨1908510544918362693569203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10178722906231267699035749 1908510544918362693569203)
                      ·
                        rfl

theorem cell23_3716811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 4].length) (baseStart_3716811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716811 prefixEnd_3716811 := by exact prefixLift 3716811
  have htrace : WordTrace (prefixWord ++ tailWord_3716811) baseStart_3716811 baseEnd_3716811 := by
    simpa [prefixWord, tailWord_3716811, baseEnd_3716811] using wordTrace_append hprefix tailTrace_3716811
  have hstable : (prefixWord ++ tailWord_3716811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716811).length < 2 ^ (prefixWord ++ tailWord_3716811).sum := by decide
  have hdescent : baseEnd_3716811 < baseStart_3716811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716851 : List Nat := [1, 1, 1, 2, 2, 3, 3, 10]
def baseStart_3716851 : Nat := 118140960795 + 3716851 * 2 ^ 59
def prefixEnd_3716851 : Nat := 4983230072969 + 3 ^ 40 * 3716851 * 2
def baseEnd_3716851 : Nat := 70686336449797871743297

theorem tailTrace_3716851 : CollatzResearch.WordTrace tailWord_3716851 prefixEnd_3716851 70686336449797871743297 := by
  unfold tailWord_3716851
  simp only [CollatzResearch.WordTrace]
  refine ⟨135564693057491089457886407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90376462038327392971924271 135564693057491089457886407)
  ·
    refine ⟨203347039586236634186829611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135564693057491089457886407 203347039586236634186829611)
    ·
      refine ⟨305020559379354951280244417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203347039586236634186829611 305020559379354951280244417)
      ·
        refine ⟨228765419534516213460183313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305020559379354951280244417 228765419534516213460183313)
        ·
          refine ⟨171574064650887160095137485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228765419534516213460183313 171574064650887160095137485)
          ·
            refine ⟨64340274244082685035676557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171574064650887160095137485 64340274244082685035676557)
            ·
              refine ⟨24127602841531006888378709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64340274244082685035676557 24127602841531006888378709)
              ·
                refine ⟨70686336449797871743297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24127602841531006888378709 70686336449797871743297)
                ·
                  rfl

theorem cell23_3716851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 10].length) (baseStart_3716851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716851 prefixEnd_3716851 := by exact prefixLift 3716851
  have htrace : WordTrace (prefixWord ++ tailWord_3716851) baseStart_3716851 baseEnd_3716851 := by
    simpa [prefixWord, tailWord_3716851, baseEnd_3716851] using wordTrace_append hprefix tailTrace_3716851
  have hstable : (prefixWord ++ tailWord_3716851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716851).length < 2 ^ (prefixWord ++ tailWord_3716851).sum := by decide
  have hdescent : baseEnd_3716851 < baseStart_3716851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716858 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_3716858 : Nat := 118140960795 + 3716858 * 2 ^ 59
def prefixEnd_3716858 : Nat := 4983230072969 + 3 ^ 40 * 3716858 * 2
def baseEnd_3716858 : Nat := 1908534678509124009681487

theorem tailTrace_3716858 : CollatzResearch.WordTrace tailWord_3716858 prefixEnd_3716858 1908534678509124009681487 := by
  unfold tailWord_3716858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33891237092116432413347807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90376632245643819768927485 33891237092116432413347807)
  ·
    refine ⟨50836855638174648620021711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33891237092116432413347807 50836855638174648620021711)
    ·
      refine ⟨76255283457261972930032567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50836855638174648620021711 76255283457261972930032567)
      ·
        refine ⟨114382925185892959395048851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76255283457261972930032567 114382925185892959395048851)
        ·
          refine ⟨171574387778839439092573277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114382925185892959395048851 171574387778839439092573277)
          ·
            refine ⟨64340395417064789659714979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171574387778839439092573277 64340395417064789659714979)
            ·
              refine ⟨96510593125597184489572469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64340395417064789659714979 96510593125597184489572469)
              ·
                refine ⟨9047868105524736045897419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96510593125597184489572469 9047868105524736045897419)
                ·
                  refine ⟨13571802158287104068846129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9047868105524736045897419 13571802158287104068846129)
                  ·
                    refine ⟨10178851618715328051634597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13571802158287104068846129 10178851618715328051634597)
                    ·
                      refine ⟨1908534678509124009681487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10178851618715328051634597 1908534678509124009681487)
                      ·
                        rfl

theorem cell23_3716858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_3716858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716858 prefixEnd_3716858 := by exact prefixLift 3716858
  have htrace : WordTrace (prefixWord ++ tailWord_3716858) baseStart_3716858 baseEnd_3716858 := by
    simpa [prefixWord, tailWord_3716858, baseEnd_3716858] using wordTrace_append hprefix tailTrace_3716858
  have hstable : (prefixWord ++ tailWord_3716858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716858).length < 2 ^ (prefixWord ++ tailWord_3716858).sum := by decide
  have hdescent : baseEnd_3716858 < baseStart_3716858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716862 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3716862 : Nat := 118140960795 + 3716862 * 2 ^ 59
def prefixEnd_3716862 : Nat := 4983230072969 + 3 ^ 40 * 3716862 * 2
def baseEnd_3716862 : Nat := 1908536732431741994031469

theorem tailTrace_3716862 : CollatzResearch.WordTrace tailWord_3716862 prefixEnd_3716862 1908536732431741994031469 := by
  unfold tailWord_3716862
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945636782556404792067105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90376729506967492224357893 16945636782556404792067105)
  ·
    refine ⟨12709227586917303594050329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16945636782556404792067105 12709227586917303594050329)
    ·
      refine ⟨9531920690187977695537747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12709227586917303594050329 9531920690187977695537747)
      ·
        refine ⟨14297881035281966543306621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9531920690187977695537747 14297881035281966543306621)
        ·
          refine ⟨5361705388230737453739983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14297881035281966543306621 5361705388230737453739983)
          ·
            refine ⟨8042558082346106180609975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361705388230737453739983 8042558082346106180609975)
            ·
              refine ⟨12063837123519159270914963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042558082346106180609975 12063837123519159270914963)
              ·
                refine ⟨18095755685278738906372445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12063837123519159270914963 18095755685278738906372445)
                ·
                  refine ⟨6785908381979527089889667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18095755685278738906372445 6785908381979527089889667)
                  ·
                    refine ⟨10178862572969290634834501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6785908381979527089889667 10178862572969290634834501)
                    ·
                      refine ⟨1908536732431741994031469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10178862572969290634834501 1908536732431741994031469)
                      ·
                        rfl

theorem cell23_3716862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3716862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716862 prefixEnd_3716862 := by exact prefixLift 3716862
  have htrace : WordTrace (prefixWord ++ tailWord_3716862) baseStart_3716862 baseEnd_3716862 := by
    simpa [prefixWord, tailWord_3716862, baseEnd_3716862] using wordTrace_append hprefix tailTrace_3716862
  have hstable : (prefixWord ++ tailWord_3716862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716862).length < 2 ^ (prefixWord ++ tailWord_3716862).sum := by decide
  have hdescent : baseEnd_3716862 < baseStart_3716862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716868 : List Nat := [2, 3, 2, 2, 1, 2, 2, 9]
def baseStart_3716868 : Nat := 118140960795 + 3716868 * 2 ^ 59
def prefixEnd_3716868 : Nat := 4983230072969 + 3 ^ 40 * 3716868 * 2
def baseEnd_3716868 : Nat := 70686659752432184094683

theorem tailTrace_3716868 : CollatzResearch.WordTrace tailWord_3716868 prefixEnd_3716868 70686659752432184094683 := by
  unfold tailWord_3716868
  simp only [CollatzResearch.WordTrace]
  refine ⟨67782656549214750680627629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90376875398953000907503505 67782656549214750680627629)
  ·
    refine ⟨25418496205955531505235361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67782656549214750680627629 25418496205955531505235361)
    ·
      refine ⟨19063872154466648628926521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25418496205955531505235361 19063872154466648628926521)
      ·
        refine ⟨14297904115849986471694891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19063872154466648628926521 14297904115849986471694891)
        ·
          refine ⟨21446856173774979707542337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14297904115849986471694891 21446856173774979707542337)
          ·
            refine ⟨16085142130331234780656753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21446856173774979707542337 16085142130331234780656753)
            ·
              refine ⟨12063856597748426085492565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16085142130331234780656753 12063856597748426085492565)
              ·
                refine ⟨70686659752432184094683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12063856597748426085492565 70686659752432184094683)
                ·
                  rfl

theorem cell23_3716868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 9].length) (baseStart_3716868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716868 prefixEnd_3716868 := by exact prefixLift 3716868
  have htrace : WordTrace (prefixWord ++ tailWord_3716868) baseStart_3716868 baseEnd_3716868 := by
    simpa [prefixWord, tailWord_3716868, baseEnd_3716868] using wordTrace_append hprefix tailTrace_3716868
  have hstable : (prefixWord ++ tailWord_3716868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716868).length < 2 ^ (prefixWord ++ tailWord_3716868).sum := by decide
  have hdescent : baseEnd_3716868 < baseStart_3716868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716882 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3716882 : Nat := 118140960795 + 3716882 * 2 ^ 59
def prefixEnd_3716882 : Nat := 4983230072969 + 3 ^ 40 * 3716882 * 2
def baseEnd_3716882 : Nat := 1908547002044831915781377

theorem tailTrace_3716882 : CollatzResearch.WordTrace tailWord_3716882 prefixEnd_3716882 1908547002044831915781377 := by
  unfold tailWord_3716882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33891455930094695438066225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90377215813585854501509933 33891455930094695438066225)
  ·
    refine ⟨25418591947571021578549669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33891455930094695438066225 25418591947571021578549669)
    ·
      refine ⟨4765985990169566545978063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25418591947571021578549669 4765985990169566545978063)
      ·
        refine ⟨7148978985254349818967095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765985990169566545978063 7148978985254349818967095)
        ·
          refine ⟨10723468477881524728450643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148978985254349818967095 10723468477881524728450643)
          ·
            refine ⟨16085202716822287092675965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723468477881524728450643 16085202716822287092675965)
            ·
              refine ⟨6031951018808357659753487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16085202716822287092675965 6031951018808357659753487)
              ·
                refine ⟨9047926528212536489630231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031951018808357659753487 9047926528212536489630231)
                ·
                  refine ⟨13571889792318804734445347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9047926528212536489630231 13571889792318804734445347)
                  ·
                    refine ⟨20357834688478207101668021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13571889792318804734445347 20357834688478207101668021)
                    ·
                      refine ⟨1908547002044831915781377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20357834688478207101668021 1908547002044831915781377)
                      ·
                        rfl

theorem cell23_3716882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3716882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716882 prefixEnd_3716882 := by exact prefixLift 3716882
  have htrace : WordTrace (prefixWord ++ tailWord_3716882) baseStart_3716882 baseEnd_3716882 := by
    simpa [prefixWord, tailWord_3716882, baseEnd_3716882] using wordTrace_append hprefix tailTrace_3716882
  have hstable : (prefixWord ++ tailWord_3716882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716882).length < 2 ^ (prefixWord ++ tailWord_3716882).sum := by decide
  have hdescent : baseEnd_3716882 < baseStart_3716882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716898 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3716898 : Nat := 118140960795 + 3716898 * 2 ^ 59
def prefixEnd_3716898 : Nat := 4983230072969 + 3 ^ 40 * 3716898 * 2
def baseEnd_3716898 : Nat := 636185072578434617727101

theorem tailTrace_3716898 : CollatzResearch.WordTrace tailWord_3716898 prefixEnd_3716898 636185072578434617727101 := by
  unfold tailWord_3716898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33891601822080204121211837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90377604858880544323231565 33891601822080204121211837)
  ·
    refine ⟨12709350683280076545454439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33891601822080204121211837 12709350683280076545454439)
    ·
      refine ⟨19064026024920114818181659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12709350683280076545454439 19064026024920114818181659)
      ·
        refine ⟨28596039037380172227272489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19064026024920114818181659 28596039037380172227272489)
        ·
          refine ⟨21447029278035129170454367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28596039037380172227272489 21447029278035129170454367)
          ·
            refine ⟨32170543917052693755681551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21447029278035129170454367 32170543917052693755681551)
            ·
              refine ⟨48255815875579040633522327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32170543917052693755681551 48255815875579040633522327)
              ·
                refine ⟨72383723813368560950283491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48255815875579040633522327 72383723813368560950283491)
                ·
                  refine ⟨108575585720052841425425237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72383723813368560950283491 108575585720052841425425237)
                  ·
                    refine ⟨636185072578434617727101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 108575585720052841425425237 636185072578434617727101)
                    ·
                      rfl

theorem cell23_3716898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3716898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716898 prefixEnd_3716898 := by exact prefixLift 3716898
  have htrace : WordTrace (prefixWord ++ tailWord_3716898) baseStart_3716898 baseEnd_3716898 := by
    simpa [prefixWord, tailWord_3716898, baseEnd_3716898] using wordTrace_append hprefix tailTrace_3716898
  have hstable : (prefixWord ++ tailWord_3716898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716898).length < 2 ^ (prefixWord ++ tailWord_3716898).sum := by decide
  have hdescent : baseEnd_3716898 < baseStart_3716898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716922 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2]
def baseStart_3716922 : Nat := 118140960795 + 3716922 * 2 ^ 59
def prefixEnd_3716922 : Nat := 4983230072969 + 3 ^ 40 * 3716922 * 2
def baseEnd_3716922 : Nat := 1908567541271011759281193

theorem tailTrace_3716922 : CollatzResearch.WordTrace tailWord_3716922 prefixEnd_3716922 1908567541271011759281193 := by
  unfold tailWord_3716922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33891820660058467145930255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90378188426822579055814013 33891820660058467145930255)
  ·
    refine ⟨50837730990087700718895383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33891820660058467145930255 50837730990087700718895383)
    ·
      refine ⟨76256596485131551078343075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50837730990087700718895383 76256596485131551078343075)
      ·
        refine ⟨114384894727697326617514613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76256596485131551078343075 114384894727697326617514613)
        ·
          refine ⟨10723583880721624370391995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114384894727697326617514613 10723583880721624370391995)
          ·
            refine ⟨16085375821082436555587993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723583880721624370391995 16085375821082436555587993)
            ·
              refine ⟨12064031865811827416690995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16085375821082436555587993 12064031865811827416690995)
              ·
                refine ⟨18096047798717741125036493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064031865811827416690995 18096047798717741125036493)
                ·
                  refine ⟨6786017924519152921888685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18096047798717741125036493 6786017924519152921888685)
                  ·
                    refine ⟨2544756721694682345708257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6786017924519152921888685 2544756721694682345708257)
                    ·
                      refine ⟨1908567541271011759281193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544756721694682345708257 1908567541271011759281193)
                      ·
                        rfl

theorem cell23_3716922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_3716922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716922 prefixEnd_3716922 := by exact prefixLift 3716922
  have htrace : WordTrace (prefixWord ++ tailWord_3716922) baseStart_3716922 baseEnd_3716922 := by
    simpa [prefixWord, tailWord_3716922, baseEnd_3716922] using wordTrace_append hprefix tailTrace_3716922
  have hstable : (prefixWord ++ tailWord_3716922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716922).length < 2 ^ (prefixWord ++ tailWord_3716922).sum := by decide
  have hdescent : baseEnd_3716922 < baseStart_3716922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3716938 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_3716938 : Nat := 118140960795 + 3716938 * 2 ^ 59
def prefixEnd_3716938 : Nat := 4983230072969 + 3 ^ 40 * 3716938 * 2
def baseEnd_3716938 : Nat := 1908575756961483696681119

theorem tailTrace_3716938 : CollatzResearch.WordTrace tailWord_3716938 prefixEnd_3716938 1908575756961483696681119 := by
  unfold tailWord_3716938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33891966552043975829075867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90378577472117268877535645 33891966552043975829075867)
  ·
    refine ⟨50837949828065963743613801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33891966552043975829075867 50837949828065963743613801)
    ·
      refine ⟨38128462371049472807710351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50837949828065963743613801 38128462371049472807710351)
      ·
        refine ⟨57192693556574209211565527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38128462371049472807710351 57192693556574209211565527)
        ·
          refine ⟨85789040334861313817348291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57192693556574209211565527 85789040334861313817348291)
          ·
            refine ⟨128683560502291970726022437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85789040334861313817348291 128683560502291970726022437)
            ·
              refine ⟨24128167594179744511129207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128683560502291970726022437 24128167594179744511129207)
              ·
                refine ⟨36192251391269616766693811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24128167594179744511129207 36192251391269616766693811)
                ·
                  refine ⟨54288377086904425150040717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36192251391269616766693811 54288377086904425150040717)
                  ·
                    refine ⟨20358141407589159431265269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54288377086904425150040717 20358141407589159431265269)
                    ·
                      refine ⟨1908575756961483696681119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20358141407589159431265269 1908575756961483696681119)
                      ·
                        rfl

theorem cell23_3716938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_3716938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3716938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3716938 prefixEnd_3716938 := by exact prefixLift 3716938
  have htrace : WordTrace (prefixWord ++ tailWord_3716938) baseStart_3716938 baseEnd_3716938 := by
    simpa [prefixWord, tailWord_3716938, baseEnd_3716938] using wordTrace_append hprefix tailTrace_3716938
  have hstable : (prefixWord ++ tailWord_3716938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3716938).length < 2 ^ (prefixWord ++ tailWord_3716938).sum := by decide
  have hdescent : baseEnd_3716938 < baseStart_3716938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3716938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717015 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3717015 : Nat := 118140960795 + 3717015 * 2 ^ 59
def prefixEnd_3717015 : Nat := 4983230072969 + 3 ^ 40 * 3717015 * 2
def baseEnd_3717015 : Nat := 1908615294971879895418265

theorem tailTrace_3717015 : CollatzResearch.WordTrace tailWord_3717015 prefixEnd_3717015 1908615294971879895418265 := by
  unfold tailWord_3717015
  simp only [CollatzResearch.WordTrace]
  refine ⟨135570674628896945466856499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90380449752597963644570999 135570674628896945466856499)
  ·
    refine ⟨203356011943345418200284749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135570674628896945466856499 203356011943345418200284749)
    ·
      refine ⟨76258504478754531825106781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203356011943345418200284749 76258504478754531825106781)
      ·
        refine ⟨28596939179532949434415043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76258504478754531825106781 28596939179532949434415043)
        ·
          refine ⟨42895408769299424151622565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28596939179532949434415043 42895408769299424151622565)
          ·
            refine ⟨8042889144243642028429231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42895408769299424151622565 8042889144243642028429231)
            ·
              refine ⟨12064333716365463042643847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8042889144243642028429231 12064333716365463042643847)
              ·
                refine ⟨18096500574548194563965771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064333716365463042643847 18096500574548194563965771)
                ·
                  refine ⟨27144750861822291845948657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18096500574548194563965771 27144750861822291845948657)
                  ·
                    refine ⟨20358563146366718884461493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27144750861822291845948657 20358563146366718884461493)
                    ·
                      refine ⟨1908615294971879895418265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20358563146366718884461493 1908615294971879895418265)
                      ·
                        rfl

theorem cell23_3717015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3717015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717015 prefixEnd_3717015 := by exact prefixLift 3717015
  have htrace : WordTrace (prefixWord ++ tailWord_3717015) baseStart_3717015 baseEnd_3717015 := by
    simpa [prefixWord, tailWord_3717015, baseEnd_3717015] using wordTrace_append hprefix tailTrace_3717015
  have hstable : (prefixWord ++ tailWord_3717015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717015).length < 2 ^ (prefixWord ++ tailWord_3717015).sum := by decide
  have hdescent : baseEnd_3717015 < baseStart_3717015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717149 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3717149 : Nat := 118140960795 + 3717149 * 2 ^ 59
def prefixEnd_3717149 : Nat := 4983230072969 + 3 ^ 40 * 3717149 * 2
def baseEnd_3717149 : Nat := 1908684101379582371142649

theorem tailTrace_3717149 : CollatzResearch.WordTrace tailWord_3717149 prefixEnd_3717149 1908684101379582371142649 := by
  unfold tailWord_3717149
  simp only [CollatzResearch.WordTrace]
  refine ⟨135575562010411486352234501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90383708006940990901489667 135575562010411486352234501)
  ·
    refine ⟨25420417876952153691043969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135575562010411486352234501 25420417876952153691043969)
    ·
      refine ⟨19065313407714115268282977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25420417876952153691043969 19065313407714115268282977)
      ·
        refine ⟨14298985055785586451212233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19065313407714115268282977 14298985055785586451212233)
        ·
          refine ⟨10724238791839189838409175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14298985055785586451212233 10724238791839189838409175)
          ·
            refine ⟨16086358187758784757613763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724238791839189838409175 16086358187758784757613763)
            ·
              refine ⟨24129537281638177136420645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16086358187758784757613763 24129537281638177136420645)
              ·
                refine ⟨4524288240307158213078871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24129537281638177136420645 4524288240307158213078871)
                ·
                  refine ⟨6786432360460737319618307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524288240307158213078871 6786432360460737319618307)
                  ·
                    refine ⟨10179648540691105979427461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6786432360460737319618307 10179648540691105979427461)
                    ·
                      refine ⟨1908684101379582371142649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10179648540691105979427461 1908684101379582371142649)
                      ·
                        rfl

theorem cell23_3717149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3717149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717149 prefixEnd_3717149 := by exact prefixLift 3717149
  have htrace : WordTrace (prefixWord ++ tailWord_3717149) baseStart_3717149 baseEnd_3717149 := by
    simpa [prefixWord, tailWord_3717149, baseEnd_3717149] using wordTrace_append hprefix tailTrace_3717149
  have hstable : (prefixWord ++ tailWord_3717149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717149).length < 2 ^ (prefixWord ++ tailWord_3717149).sum := by decide
  have hdescent : baseEnd_3717149 < baseStart_3717149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717155 : List Nat := [1, 1, 1, 4, 3, 1, 3, 9]
def baseStart_3717155 : Nat := 118140960795 + 3717155 * 2 ^ 59
def prefixEnd_3717155 : Nat := 4983230072969 + 3 ^ 40 * 3717155 * 2
def baseEnd_3717155 : Nat := 70692117861611457321023

theorem tailTrace_3717155 : CollatzResearch.WordTrace tailWord_3717155 prefixEnd_3717155 70692117861611457321023 := by
  unfold tailWord_3717155
  simp only [CollatzResearch.WordTrace]
  refine ⟨135575780848389749376952919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90383853898926499584635279 135575780848389749376952919)
  ·
    refine ⟨203363671272584624065429379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135575780848389749376952919 203363671272584624065429379)
    ·
      refine ⟨305045506908876936098144069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203363671272584624065429379 305045506908876936098144069)
      ·
        refine ⟨57196032545414425518402013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305045506908876936098144069 57196032545414425518402013)
        ·
          refine ⟨21448512204530409569400755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57196032545414425518402013 21448512204530409569400755)
          ·
            refine ⟨32172768306795614354101133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21448512204530409569400755 32172768306795614354101133)
            ·
              refine ⟨12064788115048355382787925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32172768306795614354101133 12064788115048355382787925)
              ·
                refine ⟨70692117861611457321023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12064788115048355382787925 70692117861611457321023)
                ·
                  rfl

theorem cell23_3717155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 9].length) (baseStart_3717155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717155 prefixEnd_3717155 := by exact prefixLift 3717155
  have htrace : WordTrace (prefixWord ++ tailWord_3717155) baseStart_3717155 baseEnd_3717155 := by
    simpa [prefixWord, tailWord_3717155, baseEnd_3717155] using wordTrace_append hprefix tailTrace_3717155
  have hstable : (prefixWord ++ tailWord_3717155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717155).length < 2 ^ (prefixWord ++ tailWord_3717155).sum := by decide
  have hdescent : baseEnd_3717155 < baseStart_3717155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717169 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3717169 : Nat := 118140960795 + 3717169 * 2 ^ 59
def prefixEnd_3717169 : Nat := 4983230072969 + 3 ^ 40 * 3717169 * 2
def baseEnd_3717169 : Nat := 1908694370992672292892557

theorem tailTrace_3717169 : CollatzResearch.WordTrace tailWord_3717169 prefixEnd_3717169 1908694370992672292892557 := by
  unfold tailWord_3717169
  simp only [CollatzResearch.WordTrace]
  refine ⟨135576291470339029767962561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90384194313559353178641707 135576291470339029767962561)
  ·
    refine ⟨101682218602754272325971921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135576291470339029767962561 101682218602754272325971921)
    ·
      refine ⟨76261663952065704244478941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101682218602754272325971921 76261663952065704244478941)
      ·
        refine ⟨28598123982024639091679603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76261663952065704244478941 28598123982024639091679603)
        ·
          refine ⟨42897185973036958637519405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28598123982024639091679603 42897185973036958637519405)
          ·
            refine ⟨16086444739888859489069777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42897185973036958637519405 16086444739888859489069777)
            ·
              refine ⟨12064833554916644616802333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16086444739888859489069777 12064833554916644616802333)
              ·
                refine ⟨4524312583093741731300875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12064833554916644616802333 4524312583093741731300875)
                ·
                  refine ⟨6786468874640612596951313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524312583093741731300875 6786468874640612596951313)
                  ·
                    refine ⟨5089851655980459447713485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6786468874640612596951313 5089851655980459447713485)
                    ·
                      refine ⟨1908694370992672292892557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5089851655980459447713485 1908694370992672292892557)
                      ·
                        rfl

theorem cell23_3717169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3717169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717169 prefixEnd_3717169 := by exact prefixLift 3717169
  have htrace : WordTrace (prefixWord ++ tailWord_3717169) baseStart_3717169 baseEnd_3717169 := by
    simpa [prefixWord, tailWord_3717169, baseEnd_3717169] using wordTrace_append hprefix tailTrace_3717169
  have hstable : (prefixWord ++ tailWord_3717169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717169).length < 2 ^ (prefixWord ++ tailWord_3717169).sum := by decide
  have hdescent : baseEnd_3717169 < baseStart_3717169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717195 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5]
def baseStart_3717195 : Nat := 118140960795 + 3717195 * 2 ^ 59
def prefixEnd_3717195 : Nat := 4983230072969 + 3 ^ 40 * 3717195 * 2
def baseEnd_3717195 : Nat := 1908707721489689191167437

theorem tailTrace_3717195 : CollatzResearch.WordTrace tailWord_3717195 prefixEnd_3717195 1908707721489689191167437 := by
  unfold tailWord_3717195
  simp only [CollatzResearch.WordTrace]
  refine ⟨135577239768244836208409039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90384826512163224138939359 135577239768244836208409039)
  ·
    refine ⟨203365859652367254312613559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135577239768244836208409039 203365859652367254312613559)
    ·
      refine ⟨305048789478550881468920339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203365859652367254312613559 305048789478550881468920339)
      ·
        refine ⟨457573184217826322203380509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305048789478550881468920339 457573184217826322203380509)
        ·
          refine ⟨171589944081684870826267691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457573184217826322203380509 171589944081684870826267691)
          ·
            refine ⟨257384916122527306239401537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171589944081684870826267691 257384916122527306239401537)
            ·
              refine ⟨193038687091895479679551153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257384916122527306239401537 193038687091895479679551153)
              ·
                refine ⟨144779015318921609759663365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193038687091895479679551153 144779015318921609759663365)
                ·
                  refine ⟨27146065372297801829936881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144779015318921609759663365 27146065372297801829936881)
                  ·
                    refine ⟨20359549029223351372452661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27146065372297801829936881 20359549029223351372452661)
                    ·
                      refine ⟨1908707721489689191167437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20359549029223351372452661 1908707721489689191167437)
                      ·
                        rfl

theorem cell23_3717195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_3717195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717195 prefixEnd_3717195 := by exact prefixLift 3717195
  have htrace : WordTrace (prefixWord ++ tailWord_3717195) baseStart_3717195 baseEnd_3717195 := by
    simpa [prefixWord, tailWord_3717195, baseEnd_3717195] using wordTrace_append hprefix tailTrace_3717195
  have hstable : (prefixWord ++ tailWord_3717195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717195).length < 2 ^ (prefixWord ++ tailWord_3717195).sum := by decide
  have hdescent : baseEnd_3717195 < baseStart_3717195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717199 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 3]
def baseStart_3717199 : Nat := 118140960795 + 3717199 * 2 ^ 59
def prefixEnd_3717199 : Nat := 4983230072969 + 3 ^ 40 * 3717199 * 2
def baseEnd_3717199 : Nat := 1908709775412307175517419

theorem tailTrace_3717199 : CollatzResearch.WordTrace tailWord_3717199 prefixEnd_3717199 1908709775412307175517419 := by
  unfold tailWord_3717199
  simp only [CollatzResearch.WordTrace]
  refine ⟨135577385660230344891554651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90384923773486896594369767 135577385660230344891554651)
  ·
    refine ⟨203366078490345517337331977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135577385660230344891554651 203366078490345517337331977)
    ·
      refine ⟨152524558867759138002998983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203366078490345517337331977 152524558867759138002998983)
      ·
        refine ⟨228786838301638707004498475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152524558867759138002998983 228786838301638707004498475)
        ·
          refine ⟨343180257452458060506747713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228786838301638707004498475 343180257452458060506747713)
          ·
            refine ⟨257385193089343545380060785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343180257452458060506747713 257385193089343545380060785)
            ·
              refine ⟨193038894817007659035045589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257385193089343545380060785 193038894817007659035045589)
              ·
                refine ⟨4524349097273617008633881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 193038894817007659035045589 4524349097273617008633881)
                ·
                  refine ⟨3393261822955212756475411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524349097273617008633881 3393261822955212756475411)
                  ·
                    refine ⟨5089892734432819134713117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3393261822955212756475411 5089892734432819134713117)
                    ·
                      refine ⟨1908709775412307175517419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5089892734432819134713117 1908709775412307175517419)
                      ·
                        rfl

theorem cell23_3717199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 3].length) (baseStart_3717199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717199 prefixEnd_3717199 := by exact prefixLift 3717199
  have htrace : WordTrace (prefixWord ++ tailWord_3717199) baseStart_3717199 baseEnd_3717199 := by
    simpa [prefixWord, tailWord_3717199, baseEnd_3717199] using wordTrace_append hprefix tailTrace_3717199
  have hstable : (prefixWord ++ tailWord_3717199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717199).length < 2 ^ (prefixWord ++ tailWord_3717199).sum := by decide
  have hdescent : baseEnd_3717199 < baseStart_3717199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717209 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 3, 3, 2]
def baseStart_3717209 : Nat := 118140960795 + 3717209 * 2 ^ 59
def prefixEnd_3717209 : Nat := 4983230072969 + 3 ^ 40 * 3717209 * 2
def baseEnd_3717209 : Nat := 1908714910218852136392373

theorem tailTrace_3717209 : CollatzResearch.WordTrace tailWord_3717209 prefixEnd_3717209 1908714910218852136392373 := by
  unfold tailWord_3717209
  simp only [CollatzResearch.WordTrace]
  refine ⟨135577750390194116599418681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90385166926796077732945787 135577750390194116599418681)
  ·
    refine ⟨101683312792645587449564011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135577750390194116599418681 101683312792645587449564011)
    ·
      refine ⟨152524969188968381174346017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101683312792645587449564011 152524969188968381174346017)
      ·
        refine ⟨114393726891726285880759513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152524969188968381174346017 114393726891726285880759513)
        ·
          refine ⟨85795295168794714410569635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114393726891726285880759513 85795295168794714410569635)
          ·
            refine ⟨128692942753192071615854453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85795295168794714410569635 128692942753192071615854453)
            ·
              refine ⟨12064963383111756713986355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128692942753192071615854453 12064963383111756713986355)
              ·
                refine ⟨18097445074667635070979533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12064963383111756713986355 18097445074667635070979533)
                ·
                  refine ⟨6786541903000363151617325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18097445074667635070979533 6786541903000363151617325)
                  ·
                    refine ⟨2544953213625136181856497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6786541903000363151617325 2544953213625136181856497)
                    ·
                      refine ⟨1908714910218852136392373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544953213625136181856497 1908714910218852136392373)
                      ·
                        rfl

theorem cell23_3717209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_3717209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717209 prefixEnd_3717209 := by exact prefixLift 3717209
  have htrace : WordTrace (prefixWord ++ tailWord_3717209) baseStart_3717209 baseEnd_3717209 := by
    simpa [prefixWord, tailWord_3717209, baseEnd_3717209] using wordTrace_append hprefix tailTrace_3717209
  have hstable : (prefixWord ++ tailWord_3717209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717209).length < 2 ^ (prefixWord ++ tailWord_3717209).sum := by decide
  have hdescent : baseEnd_3717209 < baseStart_3717209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717215 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 3, 8]
def baseStart_3717215 : Nat := 118140960795 + 3717215 * 2 ^ 59
def prefixEnd_3717215 : Nat := 4983230072969 + 3 ^ 40 * 3717215 * 2
def baseEnd_3717215 : Nat := 636239330367593037639115

theorem tailTrace_3717215 : CollatzResearch.WordTrace tailWord_3717215 prefixEnd_3717215 636239330367593037639115 := by
  unfold tailWord_3717215
  simp only [CollatzResearch.WordTrace]
  refine ⟨135577969228172379624137099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90385312818781586416091399 135577969228172379624137099)
  ·
    refine ⟨203366953842258569436205649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135577969228172379624137099 203366953842258569436205649)
    ·
      refine ⟨152525215381693927077154237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203366953842258569436205649 152525215381693927077154237)
      ·
        refine ⟨57196955768135222653932839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152525215381693927077154237 57196955768135222653932839)
        ·
          refine ⟨85795433652202833980899259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57196955768135222653932839 85795433652202833980899259)
          ·
            refine ⟨128693150478304250971348889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85795433652202833980899259 128693150478304250971348889)
            ·
              refine ⟨96519862858728188228511667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128693150478304250971348889 96519862858728188228511667)
              ·
                refine ⟨144779794288092282342767501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96519862858728188228511667 144779794288092282342767501)
                ·
                  refine ⟨54292422858034605878537813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144779794288092282342767501 54292422858034605878537813)
                  ·
                    refine ⟨636239330367593037639115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54292422858034605878537813 636239330367593037639115)
                    ·
                      rfl

theorem cell23_3717215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_3717215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717215 prefixEnd_3717215 := by exact prefixLift 3717215
  have htrace : WordTrace (prefixWord ++ tailWord_3717215) baseStart_3717215 baseEnd_3717215 := by
    simpa [prefixWord, tailWord_3717215, baseEnd_3717215] using wordTrace_append hprefix tailTrace_3717215
  have hstable : (prefixWord ++ tailWord_3717215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717215).length < 2 ^ (prefixWord ++ tailWord_3717215).sum := by decide
  have hdescent : baseEnd_3717215 < baseStart_3717215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717249 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3717249 : Nat := 118140960795 + 3717249 * 2 ^ 59
def prefixEnd_3717249 : Nat := 4983230072969 + 3 ^ 40 * 3717249 * 2
def baseEnd_3717249 : Nat := 636245149815010659964063

theorem tailTrace_3717249 : CollatzResearch.WordTrace tailWord_3717249 prefixEnd_3717249 636245149815010659964063 := by
  unfold tailWord_3717249
  simp only [CollatzResearch.WordTrace]
  refine ⟨135579209310049203430874801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90386139540032802287249867 135579209310049203430874801)
  ·
    refine ⟨101684406982536902573156101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135579209310049203430874801 101684406982536902573156101)
    ·
      refine ⟨19065826309225669232466769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101684406982536902573156101 19065826309225669232466769)
      ·
        refine ⟨14299369731919251924350077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19065826309225669232466769 14299369731919251924350077)
        ·
          refine ⟨5362263649469719471631279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14299369731919251924350077 5362263649469719471631279)
          ·
            refine ⟨8043395474204579207446919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362263649469719471631279 8043395474204579207446919)
            ·
              refine ⟨12065093211306868811170379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043395474204579207446919 12065093211306868811170379)
              ·
                refine ⟨18097639816960303216755569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12065093211306868811170379 18097639816960303216755569)
                ·
                  refine ⟨13573229862720227412566677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18097639816960303216755569 13573229862720227412566677)
                  ·
                    refine ⟨636245149815010659964063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13573229862720227412566677 636245149815010659964063)
                    ·
                      rfl

theorem cell23_3717249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3717249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717249 prefixEnd_3717249 := by exact prefixLift 3717249
  have htrace : WordTrace (prefixWord ++ tailWord_3717249) baseStart_3717249 baseEnd_3717249 := by
    simpa [prefixWord, tailWord_3717249, baseEnd_3717249] using wordTrace_append hprefix tailTrace_3717249
  have hstable : (prefixWord ++ tailWord_3717249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717249).length < 2 ^ (prefixWord ++ tailWord_3717249).sum := by decide
  have hdescent : baseEnd_3717249 < baseStart_3717249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717256 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3717256 : Nat := 118140960795 + 3717256 * 2 ^ 59
def prefixEnd_3717256 : Nat := 4983230072969 + 3 ^ 40 * 3717256 * 2
def baseEnd_3717256 : Nat := 1908739043809613452504657

theorem tailTrace_3717256 : CollatzResearch.WordTrace tailWord_3717256 prefixEnd_3717256 1908739043809613452504657 := by
  unfold tailWord_3717256
  simp only [CollatzResearch.WordTrace]
  refine ⟨67789732310511921813189811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90386309747349229084253081 67789732310511921813189811)
  ·
    refine ⟨101684598465767882719784717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67789732310511921813189811 101684598465767882719784717)
    ·
      refine ⟨38131724424662956019919269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101684598465767882719784717 38131724424662956019919269)
      ·
        refine ⟨7149698329624304253734863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38131724424662956019919269 7149698329624304253734863)
        ·
          refine ⟨10724547494436456380602295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149698329624304253734863 10724547494436456380602295)
          ·
            refine ⟨16086821241654684570903443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10724547494436456380602295 16086821241654684570903443)
            ·
              refine ⟨24130231862482026856355165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16086821241654684570903443 24130231862482026856355165)
              ·
                refine ⟨9048836948430760071133187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24130231862482026856355165 9048836948430760071133187)
                ·
                  refine ⟨13573255422646140106699781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9048836948430760071133187 13573255422646140106699781)
                  ·
                    refine ⟨2544985391746151270006209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13573255422646140106699781 2544985391746151270006209)
                    ·
                      refine ⟨1908739043809613452504657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2544985391746151270006209 1908739043809613452504657)
                      ·
                        rfl

theorem cell23_3717256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3717256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717256 prefixEnd_3717256 := by exact prefixLift 3717256
  have htrace : WordTrace (prefixWord ++ tailWord_3717256) baseStart_3717256 baseEnd_3717256 := by
    simpa [prefixWord, tailWord_3717256, baseEnd_3717256] using wordTrace_append hprefix tailTrace_3717256
  have hstable : (prefixWord ++ tailWord_3717256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717256).length < 2 ^ (prefixWord ++ tailWord_3717256).sum := by decide
  have hdescent : baseEnd_3717256 < baseStart_3717256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717290 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3717290 : Nat := 118140960795 + 3717290 * 2 ^ 59
def prefixEnd_3717290 : Nat := 4983230072969 + 3 ^ 40 * 3717290 * 2
def baseEnd_3717290 : Nat := 1908756502151866319479501

theorem tailTrace_3717290 : CollatzResearch.WordTrace tailWord_3717290 prefixEnd_3717290 1908756502151866319479501 := by
  unfold tailWord_3717290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33895176175725166858279331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90387136468600444955411549 33895176175725166858279331)
  ·
    refine ⟨50842764263587750287418997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33895176175725166858279331 50842764263587750287418997)
    ·
      refine ⟨4766509149711351589445531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50842764263587750287418997 4766509149711351589445531)
      ·
        refine ⟨7149763724567027384168297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766509149711351589445531 7149763724567027384168297)
        ·
          refine ⟨5362322793425270538126223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7149763724567027384168297 5362322793425270538126223)
          ·
            refine ⟨8043484190137905807189335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362322793425270538126223 8043484190137905807189335)
            ·
              refine ⟨12065226285206858710784003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043484190137905807189335 12065226285206858710784003)
              ·
                refine ⟨18097839427810288066176005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12065226285206858710784003 18097839427810288066176005)
                ·
                  refine ⟨3393344892714429012408001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18097839427810288066176005 3393344892714429012408001)
                  ·
                    refine ⟨2545008669535821759306001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3393344892714429012408001 2545008669535821759306001)
                    ·
                      refine ⟨1908756502151866319479501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545008669535821759306001 1908756502151866319479501)
                      ·
                        rfl

theorem cell23_3717290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3717290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717290 prefixEnd_3717290 := by exact prefixLift 3717290
  have htrace : WordTrace (prefixWord ++ tailWord_3717290) baseStart_3717290 baseEnd_3717290 := by
    simpa [prefixWord, tailWord_3717290, baseEnd_3717290] using wordTrace_append hprefix tailTrace_3717290
  have hstable : (prefixWord ++ tailWord_3717290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717290).length < 2 ^ (prefixWord ++ tailWord_3717290).sum := by decide
  have hdescent : baseEnd_3717290 < baseStart_3717290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717322 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_3717322 : Nat := 118140960795 + 3717322 * 2 ^ 59
def prefixEnd_3717322 : Nat := 4983230072969 + 3 ^ 40 * 3717322 * 2
def baseEnd_3717322 : Nat := 636257644510936731426451

theorem tailTrace_3717322 : CollatzResearch.WordTrace tailWord_3717322 prefixEnd_3717322 636257644510936731426451 := by
  unfold tailWord_3717322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33895467959696184224570555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90387914559189824598854813 33895467959696184224570555)
  ·
    refine ⟨50843201939544276336855833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33895467959696184224570555 50843201939544276336855833)
    ·
      refine ⟨38132401454658207252641875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50843201939544276336855833 38132401454658207252641875)
      ·
        refine ⟨57198602181987310878962813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38132401454658207252641875 57198602181987310878962813)
        ·
          refine ⟨21449475818245241579611055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57198602181987310878962813 21449475818245241579611055)
          ·
            refine ⟨32174213727367862369416583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21449475818245241579611055 32174213727367862369416583)
            ·
              refine ⟨48261320591051793554124875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32174213727367862369416583 48261320591051793554124875)
              ·
                refine ⟨72391980886577690331187313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48261320591051793554124875 72391980886577690331187313)
                ·
                  refine ⟨54293985664933267748390485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72391980886577690331187313 54293985664933267748390485)
                  ·
                    refine ⟨636257644510936731426451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54293985664933267748390485 636257644510936731426451)
                    ·
                      rfl

theorem cell23_3717322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_3717322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717322 prefixEnd_3717322 := by exact prefixLift 3717322
  have htrace : WordTrace (prefixWord ++ tailWord_3717322) baseStart_3717322 baseEnd_3717322 := by
    simpa [prefixWord, tailWord_3717322, baseEnd_3717322] using wordTrace_append hprefix tailTrace_3717322
  have hstable : (prefixWord ++ tailWord_3717322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717322).length < 2 ^ (prefixWord ++ tailWord_3717322).sum := by decide
  have hdescent : baseEnd_3717322 < baseStart_3717322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717329 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 1, 6, 2]
def baseStart_3717329 : Nat := 118140960795 + 3717329 * 2 ^ 59
def prefixEnd_3717329 : Nat := 4983230072969 + 3 ^ 40 * 3717329 * 2
def baseEnd_3717329 : Nat := 1908776527897391666891821

theorem tailTrace_3717329 : CollatzResearch.WordTrace tailWord_3717329 prefixEnd_3717329 1908776527897391666891821 := by
  unfold tailWord_3717329
  simp only [CollatzResearch.WordTrace]
  refine ⟨135582127149759377093787041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90388084766506251395858027 135582127149759377093787041)
  ·
    refine ⟨101686595362319532820340281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135582127149759377093787041 101686595362319532820340281)
    ·
      refine ⟨76264946521739649615255211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101686595362319532820340281 76264946521739649615255211)
      ·
        refine ⟨114397419782609474422882817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76264946521739649615255211 114397419782609474422882817)
        ·
          refine ⟨85798064836957105817162113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114397419782609474422882817 85798064836957105817162113)
          ·
            refine ⟨64348548627717829362871585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85798064836957105817162113 64348548627717829362871585)
            ·
              refine ⟨48261411470788372022153689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64348548627717829362871585 48261411470788372022153689)
              ·
                refine ⟨36196058603091279016615267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48261411470788372022153689 36196058603091279016615267)
                ·
                  refine ⟨54294087904636918524922901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36196058603091279016615267 54294087904636918524922901)
                  ·
                    refine ⟨2545035370529855555855761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54294087904636918524922901 2545035370529855555855761)
                    ·
                      refine ⟨1908776527897391666891821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545035370529855555855761 1908776527897391666891821)
                      ·
                        rfl

theorem cell23_3717329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_3717329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717329 prefixEnd_3717329 := by exact prefixLift 3717329
  have htrace : WordTrace (prefixWord ++ tailWord_3717329) baseStart_3717329 baseEnd_3717329 := by
    simpa [prefixWord, tailWord_3717329, baseEnd_3717329] using wordTrace_append hprefix tailTrace_3717329
  have hstable : (prefixWord ++ tailWord_3717329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717329).length < 2 ^ (prefixWord ++ tailWord_3717329).sum := by decide
  have hdescent : baseEnd_3717329 < baseStart_3717329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717436 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3717436 : Nat := 118140960795 + 3717436 * 2 ^ 59
def prefixEnd_3717436 : Nat := 4983230072969 + 3 ^ 40 * 3717436 * 2
def baseEnd_3717436 : Nat := 1908831470327422748253829

theorem tailTrace_3717436 : CollatzResearch.WordTrace tailWord_3717436 prefixEnd_3717436 1908831470327422748253829 := by
  unfold tailWord_3717436
  simp only [CollatzResearch.WordTrace]
  refine ⟨67793014880185867183966081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90390686506914489578621441 67793014880185867183966081)
  ·
    refine ⟨50844761160139400387974561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67793014880185867183966081 50844761160139400387974561)
    ·
      refine ⟨38133570870104550290980921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50844761160139400387974561 38133570870104550290980921)
      ·
        refine ⟨28600178152578412718235691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38133570870104550290980921 28600178152578412718235691)
        ·
          refine ⟨42900267228867619077353537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28600178152578412718235691 42900267228867619077353537)
          ·
            refine ⟨32175200421650714308015153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42900267228867619077353537 32175200421650714308015153)
            ·
              refine ⟨24131400316238035731011365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32175200421650714308015153 24131400316238035731011365)
              ·
                refine ⟨4524637559294631699564631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24131400316238035731011365 4524637559294631699564631)
                ·
                  refine ⟨6786956338941947549346947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4524637559294631699564631 6786956338941947549346947)
                  ·
                    refine ⟨10180434508412921324020421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6786956338941947549346947 10180434508412921324020421)
                    ·
                      refine ⟨1908831470327422748253829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10180434508412921324020421 1908831470327422748253829)
                      ·
                        rfl

theorem cell23_3717436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3717436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717436 prefixEnd_3717436 := by exact prefixLift 3717436
  have htrace : WordTrace (prefixWord ++ tailWord_3717436) baseStart_3717436 baseEnd_3717436 := by
    simpa [prefixWord, tailWord_3717436, baseEnd_3717436] using wordTrace_append hprefix tailTrace_3717436
  have hstable : (prefixWord ++ tailWord_3717436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717436).length < 2 ^ (prefixWord ++ tailWord_3717436).sum := by decide
  have hdescent : baseEnd_3717436 < baseStart_3717436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717480 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 2, 4]
def baseStart_3717480 : Nat := 118140960795 + 3717480 * 2 ^ 59
def prefixEnd_3717480 : Nat := 4983230072969 + 3 ^ 40 * 3717480 * 2
def baseEnd_3717480 : Nat := 636284687825406858701209

theorem tailTrace_3717480 : CollatzResearch.WordTrace tailWord_3717480 prefixEnd_3717480 636284687825406858701209 := by
  unfold tailWord_3717480
  simp only [CollatzResearch.WordTrace]
  refine ⟨67793817286106164941266947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90391756381474886588355929 67793817286106164941266947)
  ·
    refine ⟨101690725929159247411900421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67793817286106164941266947 101690725929159247411900421)
    ·
      refine ⟨19067011111717358889731329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101690725929159247411900421 19067011111717358889731329)
      ·
        refine ⟨14300258333788019167298497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19067011111717358889731329 14300258333788019167298497)
        ·
          refine ⟨10725193750341014375473873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14300258333788019167298497 10725193750341014375473873)
          ·
            refine ⟨8043895312755760781605405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10725193750341014375473873 8043895312755760781605405)
            ·
              refine ⟨3016460742283410293102027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8043895312755760781605405 3016460742283410293102027)
              ·
                refine ⟨4524691113425115439653041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016460742283410293102027 4524691113425115439653041)
                ·
                  refine ⟨3393518335068836579739781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524691113425115439653041 3393518335068836579739781)
                  ·
                    refine ⟨636284687825406858701209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393518335068836579739781 636284687825406858701209)
                    ·
                      rfl

theorem cell23_3717480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_3717480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717480 prefixEnd_3717480 := by exact prefixLift 3717480
  have htrace : WordTrace (prefixWord ++ tailWord_3717480) baseStart_3717480 baseEnd_3717480 := by
    simpa [prefixWord, tailWord_3717480, baseEnd_3717480] using wordTrace_append hprefix tailTrace_3717480
  have hstable : (prefixWord ++ tailWord_3717480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717480).length < 2 ^ (prefixWord ++ tailWord_3717480).sum := by decide
  have hdescent : baseEnd_3717480 < baseStart_3717480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717493 : List Nat := [1, 3, 4, 1, 2, 3, 2, 7]
def baseStart_3717493 : Nat := 118140960795 + 3717493 * 2 ^ 59
def prefixEnd_3717493 : Nat := 4983230072969 + 3 ^ 40 * 3717493 * 2
def baseEnd_3717493 : Nat := 70698545878693667601521

theorem tailTrace_3717493 : CollatzResearch.WordTrace tailWord_3717493 prefixEnd_3717493 70698545878693667601521 := by
  unfold tailWord_3717493
  simp only [CollatzResearch.WordTrace]
  refine ⟨135588108721165233102757133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90392072480776822068504755 135588108721165233102757133)
  ·
    refine ⟨50845540770436962413533925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135588108721165233102757133 50845540770436962413533925)
    ·
      refine ⟨9533538894456930452537611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50845540770436962413533925 9533538894456930452537611)
      ·
        refine ⟨14300308341685395678806417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9533538894456930452537611 14300308341685395678806417)
        ·
          refine ⟨10725231256264046759104813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14300308341685395678806417 10725231256264046759104813)
          ·
            refine ⟨4021961721099017534664305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10725231256264046759104813 4021961721099017534664305)
            ·
              refine ⟨3016471290824263150998229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021961721099017534664305 3016471290824263150998229)
              ·
                refine ⟨70698545878693667601521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3016471290824263150998229 70698545878693667601521)
                ·
                  rfl

theorem cell23_3717493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 7].length) (baseStart_3717493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717493 prefixEnd_3717493 := by exact prefixLift 3717493
  have htrace : WordTrace (prefixWord ++ tailWord_3717493) baseStart_3717493 baseEnd_3717493 := by
    simpa [prefixWord, tailWord_3717493, baseEnd_3717493] using wordTrace_append hprefix tailTrace_3717493
  have hstable : (prefixWord ++ tailWord_3717493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717493).length < 2 ^ (prefixWord ++ tailWord_3717493).sum := by decide
  have hdescent : baseEnd_3717493 < baseStart_3717493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717499 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5]
def baseStart_3717499 : Nat := 118140960795 + 3717499 * 2 ^ 59
def prefixEnd_3717499 : Nat := 4983230072969 + 3 ^ 40 * 3717499 * 2
def baseEnd_3717499 : Nat := 1908863819608656001766039

theorem tailTrace_3717499 : CollatzResearch.WordTrace tailWord_3717499 prefixEnd_3717499 1908863819608656001766039 := by
  unfold tailWord_3717499
  simp only [CollatzResearch.WordTrace]
  refine ⟨135588327559143496127475551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90392218372762330751650367 135588327559143496127475551)
  ·
    refine ⟨203382491338715244191213327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135588327559143496127475551 203382491338715244191213327)
    ·
      refine ⟨305073737008072866286819991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203382491338715244191213327 305073737008072866286819991)
      ·
        refine ⟨457610605512109299430229987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305073737008072866286819991 457610605512109299430229987)
        ·
          refine ⟨686415908268163949145344981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457610605512109299430229987 686415908268163949145344981)
          ·
            refine ⟨16087872850035092558094023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 686415908268163949145344981 16087872850035092558094023)
            ·
              refine ⟨24131809275052638837141035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16087872850035092558094023 24131809275052638837141035)
              ·
                refine ⟨36197713912578958255711553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24131809275052638837141035 36197713912578958255711553)
                ·
                  refine ⟨27148285434434218691783665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36197713912578958255711553 27148285434434218691783665)
                  ·
                    refine ⟨20361214075825664018837749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27148285434434218691783665 20361214075825664018837749)
                    ·
                      refine ⟨1908863819608656001766039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20361214075825664018837749 1908863819608656001766039)
                      ·
                        rfl

theorem cell23_3717499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_3717499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717499 prefixEnd_3717499 := by exact prefixLift 3717499
  have htrace : WordTrace (prefixWord ++ tailWord_3717499) baseStart_3717499 baseEnd_3717499 := by
    simpa [prefixWord, tailWord_3717499, baseEnd_3717499] using wordTrace_append hprefix tailTrace_3717499
  have hstable : (prefixWord ++ tailWord_3717499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717499).length < 2 ^ (prefixWord ++ tailWord_3717499).sum := by decide
  have hdescent : baseEnd_3717499 < baseStart_3717499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717509 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_3717509 : Nat := 118140960795 + 3717509 * 2 ^ 59
def prefixEnd_3717509 : Nat := 4983230072969 + 3 ^ 40 * 3717509 * 2
def baseEnd_3717509 : Nat := 1908868954415200962640993

theorem tailTrace_3717509 : CollatzResearch.WordTrace tailWord_3717509 prefixEnd_3717509 1908868954415200962640993 := by
  unfold tailWord_3717509
  simp only [CollatzResearch.WordTrace]
  refine ⟨135588692289107267835339581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90392461526071511890226387 135588692289107267835339581)
  ·
    refine ⟨50845759608415225438252343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135588692289107267835339581 50845759608415225438252343)
    ·
      refine ⟨76268639412622838157378515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50845759608415225438252343 76268639412622838157378515)
      ·
        refine ⟨114402959118934257236067773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76268639412622838157378515 114402959118934257236067773)
        ·
          refine ⟨42901109669600346463525415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114402959118934257236067773 42901109669600346463525415)
          ·
            refine ⟨64351664504400519695288123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42901109669600346463525415 64351664504400519695288123)
            ·
              refine ⟨96527496756600779542932185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64351664504400519695288123 96527496756600779542932185)
              ·
                refine ⟨72395622567450584657199139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96527496756600779542932185 72395622567450584657199139)
                ·
                  refine ⟨108593433851175876985798709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72395622567450584657199139 108593433851175876985798709)
                  ·
                    refine ⟨10180634423547738467418629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108593433851175876985798709 10180634423547738467418629)
                    ·
                      refine ⟨1908868954415200962640993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10180634423547738467418629 1908868954415200962640993)
                      ·
                        rfl

theorem cell23_3717509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_3717509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717509 prefixEnd_3717509 := by exact prefixLift 3717509
  have htrace : WordTrace (prefixWord ++ tailWord_3717509) baseStart_3717509 baseEnd_3717509 := by
    simpa [prefixWord, tailWord_3717509, baseEnd_3717509] using wordTrace_append hprefix tailTrace_3717509
  have hstable : (prefixWord ++ tailWord_3717509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717509).length < 2 ^ (prefixWord ++ tailWord_3717509).sum := by decide
  have hdescent : baseEnd_3717509 < baseStart_3717509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717529 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_3717529 : Nat := 118140960795 + 3717529 * 2 ^ 59
def prefixEnd_3717529 : Nat := 4983230072969 + 3 ^ 40 * 3717529 * 2
def baseEnd_3717529 : Nat := 1908879224028290884390901

theorem tailTrace_3717529 : CollatzResearch.WordTrace tailWord_3717529 prefixEnd_3717529 1908879224028290884390901 := by
  unfold tailWord_3717529
  simp only [CollatzResearch.WordTrace]
  refine ⟨135589421749034811251067641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90392947832689874167378427 135589421749034811251067641)
  ·
    refine ⟨101692066311776108438300731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135589421749034811251067641 101692066311776108438300731)
    ·
      refine ⟨152538099467664162657451097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101692066311776108438300731 152538099467664162657451097)
      ·
        refine ⟨114403574600748121993088323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152538099467664162657451097 114403574600748121993088323)
        ·
          refine ⟨171605361901122182989632485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114403574600748121993088323 171605361901122182989632485)
          ·
            refine ⟨32176005356460409310556091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171605361901122182989632485 32176005356460409310556091)
            ·
              refine ⟨48264008034690613965834137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32176005356460409310556091 48264008034690613965834137)
              ·
                refine ⟨36198006026017960474375603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48264008034690613965834137 36198006026017960474375603)
                ·
                  refine ⟨54297009039026940711563405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36198006026017960474375603 54297009039026940711563405)
                  ·
                    refine ⟨20361378389635102766836277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54297009039026940711563405 20361378389635102766836277)
                    ·
                      refine ⟨1908879224028290884390901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20361378389635102766836277 1908879224028290884390901)
                      ·
                        rfl

theorem cell23_3717529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_3717529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717529 prefixEnd_3717529 := by exact prefixLift 3717529
  have htrace : WordTrace (prefixWord ++ tailWord_3717529) baseStart_3717529 baseEnd_3717529 := by
    simpa [prefixWord, tailWord_3717529, baseEnd_3717529] using wordTrace_append hprefix tailTrace_3717529
  have hstable : (prefixWord ++ tailWord_3717529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717529).length < 2 ^ (prefixWord ++ tailWord_3717529).sum := by decide
  have hdescent : baseEnd_3717529 < baseStart_3717529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717537 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3717537 : Nat := 118140960795 + 3717537 * 2 ^ 59
def prefixEnd_3717537 : Nat := 4983230072969 + 3 ^ 40 * 3717537 * 2
def baseEnd_3717537 : Nat := 1908883331873526853090865

theorem tailTrace_3717537 : CollatzResearch.WordTrace tailWord_3717537 prefixEnd_3717537 1908883331873526853090865 := by
  unfold tailWord_3717537
  simp only [CollatzResearch.WordTrace]
  refine ⟨135589713533005828617358865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90393142355337219078239243 135589713533005828617358865)
  ·
    refine ⟨101692285149754371463019149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135589713533005828617358865 101692285149754371463019149)
    ·
      refine ⟨38134606931157889298632181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101692285149754371463019149 38134606931157889298632181)
      ·
        refine ⟨3575119399796052121746767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38134606931157889298632181 3575119399796052121746767)
        ·
          refine ⟨5362679099694078182620151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575119399796052121746767 5362679099694078182620151)
          ·
            refine ⟨8044018649541117273930227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362679099694078182620151 8044018649541117273930227)
            ·
              refine ⟨12066027974311675910895341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8044018649541117273930227 12066027974311675910895341)
              ·
                refine ⟨4524760490366878466585753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12066027974311675910895341 4524760490366878466585753)
                ·
                  refine ⟨3393570367775158849939315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4524760490366878466585753 3393570367775158849939315)
                  ·
                    refine ⟨5090355551662738274908973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3393570367775158849939315 5090355551662738274908973)
                    ·
                      refine ⟨1908883331873526853090865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5090355551662738274908973 1908883331873526853090865)
                      ·
                        rfl

theorem cell23_3717537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3717537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717537 prefixEnd_3717537 := by exact prefixLift 3717537
  have htrace : WordTrace (prefixWord ++ tailWord_3717537) baseStart_3717537 baseEnd_3717537 := by
    simpa [prefixWord, tailWord_3717537, baseEnd_3717537] using wordTrace_append hprefix tailTrace_3717537
  have hstable : (prefixWord ++ tailWord_3717537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717537).length < 2 ^ (prefixWord ++ tailWord_3717537).sum := by decide
  have hdescent : baseEnd_3717537 < baseStart_3717537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717579 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 3, 7]
def baseStart_3717579 : Nat := 118140960795 + 3717579 * 2 ^ 59
def prefixEnd_3717579 : Nat := 4983230072969 + 3 ^ 40 * 3717579 * 2
def baseEnd_3717579 : Nat := 636301632687005229588557

theorem tailTrace_3717579 : CollatzResearch.WordTrace tailWord_3717579 prefixEnd_3717579 636301632687005229588557 := by
  unfold tailWord_3717579
  simp only [CollatzResearch.WordTrace]
  refine ⟨135591245398853669790387791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90394163599235779860258527 135591245398853669790387791)
  ·
    refine ⟨203386868098280504685581687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135591245398853669790387791 203386868098280504685581687)
    ·
      refine ⟨305080302147420757028372531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203386868098280504685581687 305080302147420757028372531)
      ·
        refine ⟨457620453221131135542558797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305080302147420757028372531 457620453221131135542558797)
        ·
          refine ⟨171607669957924175828459549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457620453221131135542558797 171607669957924175828459549)
          ·
            refine ⟨64352876234221565935672331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171607669957924175828459549 64352876234221565935672331)
            ·
              refine ⟨96529314351332348903508497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64352876234221565935672331 96529314351332348903508497)
              ·
                refine ⟨72396985763499261677631373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96529314351332348903508497 72396985763499261677631373)
                ·
                  refine ⟨27148869661312223129111765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72396985763499261677631373 27148869661312223129111765)
                  ·
                    refine ⟨636301632687005229588557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27148869661312223129111765 636301632687005229588557)
                    ·
                      rfl

theorem cell23_3717579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 7].length) (baseStart_3717579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717579 prefixEnd_3717579 := by exact prefixLift 3717579
  have htrace : WordTrace (prefixWord ++ tailWord_3717579) baseStart_3717579 baseEnd_3717579 := by
    simpa [prefixWord, tailWord_3717579, baseEnd_3717579] using wordTrace_append hprefix tailTrace_3717579
  have hstable : (prefixWord ++ tailWord_3717579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717579).length < 2 ^ (prefixWord ++ tailWord_3717579).sum := by decide
  have hdescent : baseEnd_3717579 < baseStart_3717579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717609 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 10]
def baseStart_3717609 : Nat := 118140960795 + 3717609 * 2 ^ 59
def prefixEnd_3717609 : Nat := 4983230072969 + 3 ^ 40 * 3717609 * 2
def baseEnd_3717609 : Nat := 636306767493550190463511

theorem tailTrace_3717609 : CollatzResearch.WordTrace tailWord_3717609 prefixEnd_3717609 636306767493550190463511 := by
  unfold tailWord_3717609
  simp only [CollatzResearch.WordTrace]
  refine ⟨135592339588744984913979881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90394893059163323275986587 135592339588744984913979881)
  ·
    refine ⟨101694254691558738685484911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135592339588744984913979881 101694254691558738685484911)
    ·
      refine ⟨152541382037338108028227367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101694254691558738685484911 152541382037338108028227367)
      ·
        refine ⟨228812073056007162042341051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152541382037338108028227367 228812073056007162042341051)
        ·
          refine ⟨343218109584010743063511577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228812073056007162042341051 343218109584010743063511577)
          ·
            refine ⟨257413582188008057297633683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343218109584010743063511577 257413582188008057297633683)
            ·
              refine ⟨386120373282012085946450525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257413582188008057297633683 386120373282012085946450525)
              ·
                refine ⟨144795139980754532229918947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386120373282012085946450525 144795139980754532229918947)
                ·
                  refine ⟨217192709971131798344878421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144795139980754532229918947 217192709971131798344878421)
                  ·
                    refine ⟨636306767493550190463511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 217192709971131798344878421 636306767493550190463511)
                    ·
                      rfl

theorem cell23_3717609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_3717609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717609 prefixEnd_3717609 := by exact prefixLift 3717609
  have htrace : WordTrace (prefixWord ++ tailWord_3717609) baseStart_3717609 baseEnd_3717609 := by
    simpa [prefixWord, tailWord_3717609, baseEnd_3717609] using wordTrace_append hprefix tailTrace_3717609
  have hstable : (prefixWord ++ tailWord_3717609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717609).length < 2 ^ (prefixWord ++ tailWord_3717609).sum := by decide
  have hdescent : baseEnd_3717609 < baseStart_3717609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717613 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_3717613 : Nat := 118140960795 + 3717613 * 2 ^ 59
def prefixEnd_3717613 : Nat := 4983230072969 + 3 ^ 40 * 3717613 * 2
def baseEnd_3717613 : Nat := 636307452134422851913505

theorem tailTrace_3717613 : CollatzResearch.WordTrace tailWord_3717613 prefixEnd_3717613 636307452134422851913505 := by
  unfold tailWord_3717613
  simp only [CollatzResearch.WordTrace]
  refine ⟨135592485480730493597125493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90394990320486995731416995 135592485480730493597125493)
  ·
    refine ⟨12711795513818483774730515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135592485480730493597125493 12711795513818483774730515)
    ·
      refine ⟨19067693270727725662095773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12711795513818483774730515 19067693270727725662095773)
      ·
        refine ⟨7150384976522897123285915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19067693270727725662095773 7150384976522897123285915)
        ·
          refine ⟨10725577464784345684928873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7150384976522897123285915 10725577464784345684928873)
          ·
            refine ⟨8044183098588259263696655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10725577464784345684928873 8044183098588259263696655)
            ·
              refine ⟨12066274647882388895544983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8044183098588259263696655 12066274647882388895544983)
              ·
                refine ⟨18099411971823583343317475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12066274647882388895544983 18099411971823583343317475)
                ·
                  refine ⟨27149117957735375014976213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18099411971823583343317475 27149117957735375014976213)
                  ·
                    refine ⟨636307452134422851913505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27149117957735375014976213 636307452134422851913505)
                    ·
                      rfl

theorem cell23_3717613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_3717613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717613 prefixEnd_3717613 := by exact prefixLift 3717613
  have htrace : WordTrace (prefixWord ++ tailWord_3717613) baseStart_3717613 baseEnd_3717613 := by
    simpa [prefixWord, tailWord_3717613, baseEnd_3717613] using wordTrace_append hprefix tailTrace_3717613
  have hstable : (prefixWord ++ tailWord_3717613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717613).length < 2 ^ (prefixWord ++ tailWord_3717613).sum := by decide
  have hdescent : baseEnd_3717613 < baseStart_3717613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717616 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_3717616 : Nat := 118140960795 + 3717616 * 2 ^ 59
def prefixEnd_3717616 : Nat := 4983230072969 + 3 ^ 40 * 3717616 * 2
def baseEnd_3717616 : Nat := 1908923896845232044003001

theorem tailTrace_3717616 : CollatzResearch.WordTrace tailWord_3717616 prefixEnd_3717616 1908923896845232044003001 := by
  unfold tailWord_3717616
  simp only [CollatzResearch.WordTrace]
  refine ⟨67796297449859812554742351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90395063266479750072989801 67796297449859812554742351)
  ·
    refine ⟨101694446174789718832113527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67796297449859812554742351 101694446174789718832113527)
    ·
      refine ⟨152541669262184578248170291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101694446174789718832113527 152541669262184578248170291)
      ·
        refine ⟨228812503893276867372255437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152541669262184578248170291 228812503893276867372255437)
        ·
          refine ⟨85804688959978825264595789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228812503893276867372255437 85804688959978825264595789)
          ·
            refine ⟨32176758359992059474223421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85804688959978825264595789 32176758359992059474223421)
            ·
              refine ⟨12066284384997022302833783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32176758359992059474223421 12066284384997022302833783)
              ·
                refine ⟨18099426577495533454250675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12066284384997022302833783 18099426577495533454250675)
                ·
                  refine ⟨27149139866243300181376013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18099426577495533454250675 27149139866243300181376013)
                  ·
                    refine ⟨10180927449841237568016005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27149139866243300181376013 10180927449841237568016005)
                    ·
                      refine ⟨1908923896845232044003001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10180927449841237568016005 1908923896845232044003001)
                      ·
                        rfl

theorem cell23_3717616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_3717616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717616 prefixEnd_3717616 := by exact prefixLift 3717616
  have htrace : WordTrace (prefixWord ++ tailWord_3717616) baseStart_3717616 baseEnd_3717616 := by
    simpa [prefixWord, tailWord_3717616, baseEnd_3717616] using wordTrace_append hprefix tailTrace_3717616
  have hstable : (prefixWord ++ tailWord_3717616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717616).length < 2 ^ (prefixWord ++ tailWord_3717616).sum := by decide
  have hdescent : baseEnd_3717616 < baseStart_3717616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717643 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 3, 4]
def baseStart_3717643 : Nat := 118140960795 + 3717643 * 2 ^ 59
def prefixEnd_3717643 : Nat := 4983230072969 + 3 ^ 40 * 3717643 * 2
def baseEnd_3717643 : Nat := 636312586940967812788459

theorem tailTrace_3717643 : CollatzResearch.WordTrace tailWord_3717643 prefixEnd_3717643 636312586940967812788459 := by
  unfold tailWord_3717643
  simp only [CollatzResearch.WordTrace]
  refine ⟨135593579670621808720717583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90395719780414539147145055 135593579670621808720717583)
  ·
    refine ⟨203390369505932713081076375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135593579670621808720717583 203390369505932713081076375)
    ·
      refine ⟨305085554258899069621614563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203390369505932713081076375 305085554258899069621614563)
      ·
        refine ⟨457628331388348604432421845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305085554258899069621614563 457628331388348604432421845)
        ·
          refine ⟨10725664016914420416384887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 457628331388348604432421845 10725664016914420416384887)
          ·
            refine ⟨16088496025371630624577331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10725664016914420416384887 16088496025371630624577331)
            ·
              refine ⟨24132744038057445936865997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16088496025371630624577331 24132744038057445936865997)
              ·
                refine ⟨9049779014271542226324749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24132744038057445936865997 9049779014271542226324749)
                ·
                  refine ⟨3393667130351828334871781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9049779014271542226324749 3393667130351828334871781)
                  ·
                    refine ⟨636312586940967812788459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393667130351828334871781 636312586940967812788459)
                    ·
                      rfl

theorem cell23_3717643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 4].length) (baseStart_3717643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717643 prefixEnd_3717643 := by exact prefixLift 3717643
  have htrace : WordTrace (prefixWord ++ tailWord_3717643) baseStart_3717643 baseEnd_3717643 := by
    simpa [prefixWord, tailWord_3717643, baseEnd_3717643] using wordTrace_append hprefix tailTrace_3717643
  have hstable : (prefixWord ++ tailWord_3717643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717643).length < 2 ^ (prefixWord ++ tailWord_3717643).sum := by decide
  have hdescent : baseEnd_3717643 < baseStart_3717643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717694 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3717694 : Nat := 118140960795 + 3717694 * 2 ^ 59
def prefixEnd_3717694 : Nat := 4983230072969 + 3 ^ 40 * 3717694 * 2
def baseEnd_3717694 : Nat := 636321316112094246275881

theorem tailTrace_3717694 : CollatzResearch.WordTrace tailWord_3717694 prefixEnd_3717694 636321316112094246275881 := by
  unfold tailWord_3717694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16949429974179630553853017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90396959862291362953882757 16949429974179630553853017)
  ·
    refine ⟨12712072480634722915389763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16949429974179630553853017 12712072480634722915389763)
    ·
      refine ⟨19068108720952084373084645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12712072480634722915389763 19068108720952084373084645)
      ·
        refine ⟨3575270385178515819953371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19068108720952084373084645 3575270385178515819953371)
        ·
          refine ⟨5362905577767773729930057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575270385178515819953371 5362905577767773729930057)
          ·
            refine ⟨4022179183325830297447543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5362905577767773729930057 4022179183325830297447543)
            ·
              refine ⟨6033268774988745446171315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022179183325830297447543 6033268774988745446171315)
              ·
                refine ⟨9049903162483118169256973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033268774988745446171315 9049903162483118169256973)
                ·
                  refine ⟨3393713685931169313471365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9049903162483118169256973 3393713685931169313471365)
                  ·
                    refine ⟨636321316112094246275881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393713685931169313471365 636321316112094246275881)
                    ·
                      rfl

theorem cell23_3717694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3717694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717694 prefixEnd_3717694 := by exact prefixLift 3717694
  have htrace : WordTrace (prefixWord ++ tailWord_3717694) baseStart_3717694 baseEnd_3717694 := by
    simpa [prefixWord, tailWord_3717694, baseEnd_3717694] using wordTrace_append hprefix tailTrace_3717694
  have hstable : (prefixWord ++ tailWord_3717694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717694).length < 2 ^ (prefixWord ++ tailWord_3717694).sum := by decide
  have hdescent : baseEnd_3717694 < baseStart_3717694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717743 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 5]
def baseStart_3717743 : Nat := 118140960795 + 3717743 * 2 ^ 59
def prefixEnd_3717743 : Nat := 4983230072969 + 3 ^ 40 * 3717743 * 2
def baseEnd_3717743 : Nat := 1908989108888353047114917

theorem tailTrace_3717743 : CollatzResearch.WordTrace tailWord_3717743 prefixEnd_3717743 1908989108888353047114917 := by
  unfold tailWord_3717743
  simp only [CollatzResearch.WordTrace]
  refine ⟨135597226970259525799357883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90398151313506350532905255 135597226970259525799357883)
  ·
    refine ⟨203395840455389288699036825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135597226970259525799357883 203395840455389288699036825)
    ·
      refine ⟨152546880341541966524277619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203395840455389288699036825 152546880341541966524277619)
      ·
        refine ⟨228820320512312949786416429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152546880341541966524277619 228820320512312949786416429)
        ·
          refine ⟨85807620192117356169906161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228820320512312949786416429 85807620192117356169906161)
          ·
            refine ⟨64355715144088017127429621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85807620192117356169906161 64355715144088017127429621)
            ·
              refine ⟨6033348294758251605696527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64355715144088017127429621 6033348294758251605696527)
              ·
                refine ⟨9050022442137377408544791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033348294758251605696527 9050022442137377408544791)
                ·
                  refine ⟨13575033663206066112817187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9050022442137377408544791 13575033663206066112817187)
                  ·
                    refine ⟨20362550494809099169225781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13575033663206066112817187 20362550494809099169225781)
                    ·
                      refine ⟨1908989108888353047114917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20362550494809099169225781 1908989108888353047114917)
                      ·
                        rfl

theorem cell23_3717743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_3717743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717743 prefixEnd_3717743 := by exact prefixLift 3717743
  have htrace : WordTrace (prefixWord ++ tailWord_3717743) baseStart_3717743 baseEnd_3717743 := by
    simpa [prefixWord, tailWord_3717743, baseEnd_3717743] using wordTrace_append hprefix tailTrace_3717743
  have hstable : (prefixWord ++ tailWord_3717743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717743).length < 2 ^ (prefixWord ++ tailWord_3717743).sum := by decide
  have hdescent : baseEnd_3717743 < baseStart_3717743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717746 : List Nat := [3, 2, 1, 2, 15]
def baseStart_3717746 : Nat := 118140960795 + 3717746 * 2 ^ 59
def prefixEnd_3717746 : Nat := 4983230072969 + 3 ^ 40 * 3717746 * 2
def baseEnd_3717746 : Nat := 2618642866022382078707

theorem tailTrace_3717746 : CollatzResearch.WordTrace tailWord_3717746 prefixEnd_3717746 2618642866022382078707 := by
  unfold tailWord_3717746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33899334097312164327929273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90398224259499104874478061 33899334097312164327929273)
  ·
    refine ⟨25424500572984123245946955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33899334097312164327929273 25424500572984123245946955)
    ·
      refine ⟨38136750859476184868920433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25424500572984123245946955 38136750859476184868920433)
      ·
        refine ⟨28602563144607138651690325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38136750859476184868920433 28602563144607138651690325)
        ·
          refine ⟨2618642866022382078707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 28602563144607138651690325 2618642866022382078707)
          ·
            rfl

theorem cell23_3717746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 15].length) (baseStart_3717746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717746 prefixEnd_3717746 := by exact prefixLift 3717746
  have htrace : WordTrace (prefixWord ++ tailWord_3717746) baseStart_3717746 baseEnd_3717746 := by
    simpa [prefixWord, tailWord_3717746, baseEnd_3717746] using wordTrace_append hprefix tailTrace_3717746
  have hstable : (prefixWord ++ tailWord_3717746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717746).length < 2 ^ (prefixWord ++ tailWord_3717746).sum := by decide
  have hdescent : baseEnd_3717746 < baseStart_3717746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717807 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 3]
def baseStart_3717807 : Nat := 118140960795 + 3717807 * 2 ^ 59
def prefixEnd_3717807 : Nat := 4983230072969 + 3 ^ 40 * 3717807 * 2
def baseEnd_3717807 : Nat := 1909021971650240796714623

theorem tailTrace_3717807 : CollatzResearch.WordTrace tailWord_3717807 prefixEnd_3717807 1909021971650240796714623 := by
  unfold tailWord_3717807
  simp only [CollatzResearch.WordTrace]
  refine ⟨135599561242027664729687675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90399707494685109819791783 135599561242027664729687675)
  ·
    refine ⟨203399341863041497094531513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135599561242027664729687675 203399341863041497094531513)
    ·
      refine ⟨152549506397281122820898635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203399341863041497094531513 152549506397281122820898635)
      ·
        refine ⟨228824259595921684231347953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152549506397281122820898635 228824259595921684231347953)
        ·
          refine ⟨171618194696941263173510965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228824259595921684231347953 171618194696941263173510965)
          ·
            refine ⟨16089205752838243422516653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171618194696941263173510965 16089205752838243422516653)
            ·
              refine ⟨6033452157314341283443745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16089205752838243422516653 6033452157314341283443745)
              ·
                refine ⟨4525089117985755962582809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033452157314341283443745 4525089117985755962582809)
                ·
                  refine ⟨3393816838489316971937107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4525089117985755962582809 3393816838489316971937107)
                  ·
                    refine ⟨5090725257733975457905661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3393816838489316971937107 5090725257733975457905661)
                    ·
                      refine ⟨1909021971650240796714623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5090725257733975457905661 1909021971650240796714623)
                      ·
                        rfl

theorem cell23_3717807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 3].length) (baseStart_3717807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717807 prefixEnd_3717807 := by exact prefixLift 3717807
  have htrace : WordTrace (prefixWord ++ tailWord_3717807) baseStart_3717807 baseEnd_3717807 := by
    simpa [prefixWord, tailWord_3717807, baseEnd_3717807] using wordTrace_append hprefix tailTrace_3717807
  have hstable : (prefixWord ++ tailWord_3717807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717807).length < 2 ^ (prefixWord ++ tailWord_3717807).sum := by decide
  have hdescent : baseEnd_3717807 < baseStart_3717807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717823 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 2, 6]
def baseStart_3717823 : Nat := 118140960795 + 3717823 * 2 ^ 59
def prefixEnd_3717823 : Nat := 4983230072969 + 3 ^ 40 * 3717823 * 2
def baseEnd_3717823 : Nat := 636343395780237578038183

theorem tailTrace_3717823 : CollatzResearch.WordTrace tailWord_3717823 prefixEnd_3717823 636343395780237578038183 := by
  unfold tailWord_3717823
  simp only [CollatzResearch.WordTrace]
  refine ⟨135600144809969699462270123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90400096539979799641513415 135600144809969699462270123)
  ·
    refine ⟨203400217214954549193405185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135600144809969699462270123 203400217214954549193405185)
    ·
      refine ⟨152550162911215911895053889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203400217214954549193405185 152550162911215911895053889)
      ·
        refine ⟨114412622183411933921290417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152550162911215911895053889 114412622183411933921290417)
        ·
          refine ⟨85809466637558950440967813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114412622183411933921290417 85809466637558950440967813)
          ·
            refine ⟨16089274994542303207681465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85809466637558950440967813 16089274994542303207681465)
            ·
              refine ⟨12066956245906727405761099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16089274994542303207681465 12066956245906727405761099)
              ·
                refine ⟨18100434368860091108641649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12066956245906727405761099 18100434368860091108641649)
                ·
                  refine ⟨13575325776645068331481237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18100434368860091108641649 13575325776645068331481237)
                  ·
                    refine ⟨636343395780237578038183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13575325776645068331481237 636343395780237578038183)
                    ·
                      rfl

theorem cell23_3717823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_3717823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717823 prefixEnd_3717823 := by exact prefixLift 3717823
  have htrace : WordTrace (prefixWord ++ tailWord_3717823) baseStart_3717823 baseEnd_3717823 := by
    simpa [prefixWord, tailWord_3717823, baseEnd_3717823] using wordTrace_append hprefix tailTrace_3717823
  have hstable : (prefixWord ++ tailWord_3717823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717823).length < 2 ^ (prefixWord ++ tailWord_3717823).sum := by decide
  have hdescent : baseEnd_3717823 < baseStart_3717823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717824 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 2, 1, 3]
def baseStart_3717824 : Nat := 118140960795 + 3717824 * 2 ^ 59
def prefixEnd_3717824 : Nat := 4983230072969 + 3 ^ 40 * 3717824 * 2
def baseEnd_3717824 : Nat := 1909030700821367230202045

theorem tailTrace_3717824 : CollatzResearch.WordTrace tailWord_3717824 prefixEnd_3717824 1909030700821367230202045 := by
  unfold tailWord_3717824
  simp only [CollatzResearch.WordTrace]
  refine ⟨67800090641483038316528263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90400120855310717755371017 67800090641483038316528263)
  ·
    refine ⟨101700135962224557474792395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67800090641483038316528263 101700135962224557474792395)
    ·
      refine ⟨152550203943336836212188593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101700135962224557474792395 152550203943336836212188593)
      ·
        refine ⟨114412652957502627159141445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152550203943336836212188593 114412652957502627159141445)
        ·
          refine ⟨21452372429531742592339021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114412652957502627159141445 21452372429531742592339021)
          ·
            refine ⟨8044639661074403472127133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21452372429531742592339021 8044639661074403472127133)
            ·
              refine ⟨3016739872902901302047675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8044639661074403472127133 3016739872902901302047675)
              ·
                refine ⟨4525109809354351953071513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016739872902901302047675 4525109809354351953071513)
                ·
                  refine ⟨3393832357015763964803635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4525109809354351953071513 3393832357015763964803635)
                  ·
                    refine ⟨5090748535523645947205453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3393832357015763964803635 5090748535523645947205453)
                    ·
                      refine ⟨1909030700821367230202045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5090748535523645947205453 1909030700821367230202045)
                      ·
                        rfl

theorem cell23_3717824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_3717824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717824 prefixEnd_3717824 := by exact prefixLift 3717824
  have htrace : WordTrace (prefixWord ++ tailWord_3717824) baseStart_3717824 baseEnd_3717824 := by
    simpa [prefixWord, tailWord_3717824, baseEnd_3717824] using wordTrace_append hprefix tailTrace_3717824
  have hstable : (prefixWord ++ tailWord_3717824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717824).length < 2 ^ (prefixWord ++ tailWord_3717824).sum := by decide
  have hdescent : baseEnd_3717824 < baseStart_3717824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717834 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2]
def baseStart_3717834 : Nat := 118140960795 + 3717834 * 2 ^ 59
def prefixEnd_3717834 : Nat := 4983230072969 + 3 ^ 40 * 3717834 * 2
def baseEnd_3717834 : Nat := 1909035835627912191076999

theorem tailTrace_3717834 : CollatzResearch.WordTrace tailWord_3717834 prefixEnd_3717834 1909035835627912191076999 := by
  unfold tailWord_3717834
  simp only [CollatzResearch.WordTrace]
  refine ⟨33900136503232462085230139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90400364008619898893947037 33900136503232462085230139)
  ·
    refine ⟨50850204754848693127845209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33900136503232462085230139 50850204754848693127845209)
    ·
      refine ⟨38137653566136519845883907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50850204754848693127845209 38137653566136519845883907)
      ·
        refine ⟨57206480349204779768825861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38137653566136519845883907 57206480349204779768825861)
        ·
          refine ⟨10726215065475896206654849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57206480349204779768825861 10726215065475896206654849)
          ·
            refine ⟨8044661299106922154991137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10726215065475896206654849 8044661299106922154991137)
            ·
              refine ⟨6033495974330191616243353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8044661299106922154991137 6033495974330191616243353)
              ·
                refine ⟨4525121980747643712182515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033495974330191616243353 4525121980747643712182515)
                ·
                  refine ⟨6787682971121465568273773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525121980747643712182515 6787682971121465568273773)
                  ·
                    refine ⟨2545381114170549588102665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6787682971121465568273773 2545381114170549588102665)
                    ·
                      refine ⟨1909035835627912191076999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545381114170549588102665 1909035835627912191076999)
                      ·
                        rfl

theorem cell23_3717834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_3717834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717834 prefixEnd_3717834 := by exact prefixLift 3717834
  have htrace : WordTrace (prefixWord ++ tailWord_3717834) baseStart_3717834 baseEnd_3717834 := by
    simpa [prefixWord, tailWord_3717834, baseEnd_3717834] using wordTrace_append hprefix tailTrace_3717834
  have hstable : (prefixWord ++ tailWord_3717834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717834).length < 2 ^ (prefixWord ++ tailWord_3717834).sum := by decide
  have hdescent : baseEnd_3717834 < baseStart_3717834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717847 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 4, 2, 2]
def baseStart_3717847 : Nat := 118140960795 + 3717847 * 2 ^ 59
def prefixEnd_3717847 : Nat := 4983230072969 + 3 ^ 40 * 3717847 * 2
def baseEnd_3717847 : Nat := 1909042510876420640214439

theorem tailTrace_3717847 : CollatzResearch.WordTrace tailWord_3717847 prefixEnd_3717847 1909042510876420640214439 := by
  unfold tailWord_3717847
  simp only [CollatzResearch.WordTrace]
  refine ⟨135601020161882751561143795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90400680107921834374095863 135601020161882751561143795)
  ·
    refine ⟨203401530242824127341715693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135601020161882751561143795 203401530242824127341715693)
    ·
      refine ⟨76275573841059047753143385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203401530242824127341715693 76275573841059047753143385)
      ·
        refine ⟨57206680380794285814857539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76275573841059047753143385 57206680380794285814857539)
        ·
          refine ⟨85810020571191428722286309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57206680380794285814857539 85810020571191428722286309)
          ·
            refine ⟨16089378857098392885428683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85810020571191428722286309 16089378857098392885428683)
            ·
              refine ⟨24134068285647589328143025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16089378857098392885428683 24134068285647589328143025)
              ·
                refine ⟨18100551214235691996107269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24134068285647589328143025 18100551214235691996107269)
                ·
                  refine ⟨3393853352669192249270113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18100551214235691996107269 3393853352669192249270113)
                  ·
                    refine ⟨2545390014501894186952585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3393853352669192249270113 2545390014501894186952585)
                    ·
                      refine ⟨1909042510876420640214439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545390014501894186952585 1909042510876420640214439)
                      ·
                        rfl

theorem cell23_3717847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_3717847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717847 prefixEnd_3717847 := by exact prefixLift 3717847
  have htrace : WordTrace (prefixWord ++ tailWord_3717847) baseStart_3717847 baseEnd_3717847 := by
    simpa [prefixWord, tailWord_3717847, baseEnd_3717847] using wordTrace_append hprefix tailTrace_3717847
  have hstable : (prefixWord ++ tailWord_3717847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717847).length < 2 ^ (prefixWord ++ tailWord_3717847).sum := by decide
  have hdescent : baseEnd_3717847 < baseStart_3717847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717870 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_3717870 : Nat := 118140960795 + 3717870 * 2 ^ 59
def prefixEnd_3717870 : Nat := 4983230072969 + 3 ^ 40 * 3717870 * 2
def baseEnd_3717870 : Nat := 212117146770163783358537

theorem tailTrace_3717870 : CollatzResearch.WordTrace tailWord_3717870 prefixEnd_3717870 212117146770163783358537 := by
  unfold tailWord_3717870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950232380099928311153883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90401239360532950992820709 16950232380099928311153883)
  ·
    refine ⟨25425348570149892466730825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16950232380099928311153883 25425348570149892466730825)
    ·
      refine ⟨19069011427612419350048119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25425348570149892466730825 19069011427612419350048119)
      ·
        refine ⟨28603517141418629025072179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19069011427612419350048119 28603517141418629025072179)
        ·
          refine ⟨42905275712127943537608269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28603517141418629025072179 42905275712127943537608269)
          ·
            refine ⟨16089478392047978826603101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42905275712127943537608269 16089478392047978826603101)
            ·
              refine ⟨6033554397017992059976163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16089478392047978826603101 6033554397017992059976163)
              ·
                refine ⟨9050331595526988089964245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6033554397017992059976163 9050331595526988089964245)
                ·
                  refine ⟨212117146770163783358537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9050331595526988089964245 212117146770163783358537)
                  ·
                    rfl

theorem cell23_3717870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_3717870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717870 prefixEnd_3717870 := by exact prefixLift 3717870
  have htrace : WordTrace (prefixWord ++ tailWord_3717870) baseStart_3717870 baseEnd_3717870 := by
    simpa [prefixWord, tailWord_3717870, baseEnd_3717870] using wordTrace_append hprefix tailTrace_3717870
  have hstable : (prefixWord ++ tailWord_3717870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717870).length < 2 ^ (prefixWord ++ tailWord_3717870).sum := by decide
  have hdescent : baseEnd_3717870 < baseStart_3717870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717923 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5]
def baseStart_3717923 : Nat := 118140960795 + 3717923 * 2 ^ 59
def prefixEnd_3717923 : Nat := 4983230072969 + 3 ^ 40 * 3717923 * 2
def baseEnd_3717923 : Nat := 1909081535406162342864089

theorem tailTrace_3717923 : CollatzResearch.WordTrace tailWord_3717923 prefixEnd_3717923 1909081535406162342864089 := by
  unfold tailWord_3717923
  simp only [CollatzResearch.WordTrace]
  refine ⟨135603792109607416540910423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90402528073071611027273615 135603792109607416540910423)
  ·
    refine ⟨203405688164411124811365635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135603792109607416540910423 203405688164411124811365635)
    ·
      refine ⟨305108532246616687217048453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203405688164411124811365635 305108532246616687217048453)
      ·
        refine ⟨57207849796240628853196585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305108532246616687217048453 57207849796240628853196585)
        ·
          refine ⟨42905887347180471639897439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57207849796240628853196585 42905887347180471639897439)
          ·
            refine ⟨64358831020770707459846159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42905887347180471639897439 64358831020770707459846159)
            ·
              refine ⟨96538246531156061189769239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64358831020770707459846159 96538246531156061189769239)
              ·
                refine ⟨144807369796734091784653859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96538246531156061189769239 144807369796734091784653859)
                ·
                  refine ⟨217211054695101137676980789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144807369796734091784653859 217211054695101137676980789)
                  ·
                    refine ⟨20363536377665731657216949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 217211054695101137676980789 20363536377665731657216949)
                    ·
                      refine ⟨1909081535406162342864089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20363536377665731657216949 1909081535406162342864089)
                      ·
                        rfl

theorem cell23_3717923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_3717923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717923 prefixEnd_3717923 := by exact prefixLift 3717923
  have htrace : WordTrace (prefixWord ++ tailWord_3717923) baseStart_3717923 baseEnd_3717923 := by
    simpa [prefixWord, tailWord_3717923, baseEnd_3717923] using wordTrace_append hprefix tailTrace_3717923
  have hstable : (prefixWord ++ tailWord_3717923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717923).length < 2 ^ (prefixWord ++ tailWord_3717923).sum := by decide
  have hdescent : baseEnd_3717923 < baseStart_3717923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717937 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 2, 4, 2]
def baseStart_3717937 : Nat := 118140960795 + 3717937 * 2 ^ 59
def prefixEnd_3717937 : Nat := 4983230072969 + 3 ^ 40 * 3717937 * 2
def baseEnd_3717937 : Nat := 1909088724135325288089025

theorem tailTrace_3717937 : CollatzResearch.WordTrace tailWord_3717937 prefixEnd_3717937 1909088724135325288089025 := by
  unfold tailWord_3717937
  simp only [CollatzResearch.WordTrace]
  refine ⟨135604302731556696931920065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90402868487704464621280043 135604302731556696931920065)
  ·
    refine ⟨101703227048667522698940049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135604302731556696931920065 101703227048667522698940049)
    ·
      refine ⟨76277420286500642024205037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101703227048667522698940049 76277420286500642024205037)
      ·
        refine ⟨28604032607437740759076889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76277420286500642024205037 28604032607437740759076889)
        ·
          refine ⟨21453024455578305569307667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28604032607437740759076889 21453024455578305569307667)
          ·
            refine ⟨32179536683367458353961501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21453024455578305569307667 32179536683367458353961501)
            ·
              refine ⟨12067326256262796882735563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32179536683367458353961501 12067326256262796882735563)
              ·
                refine ⟨18100989384394195324103345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12067326256262796882735563 18100989384394195324103345)
                ·
                  refine ⟨13575742038295646493077509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18100989384394195324103345 13575742038295646493077509)
                  ·
                    refine ⟨2545451632180433717452033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13575742038295646493077509 2545451632180433717452033)
                    ·
                      refine ⟨1909088724135325288089025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545451632180433717452033 1909088724135325288089025)
                      ·
                        rfl

theorem cell23_3717937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_3717937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717937 prefixEnd_3717937 := by exact prefixLift 3717937
  have htrace : WordTrace (prefixWord ++ tailWord_3717937) baseStart_3717937 baseEnd_3717937 := by
    simpa [prefixWord, tailWord_3717937, baseEnd_3717937] using wordTrace_append hprefix tailTrace_3717937
  have hstable : (prefixWord ++ tailWord_3717937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717937).length < 2 ^ (prefixWord ++ tailWord_3717937).sum := by decide
  have hdescent : baseEnd_3717937 < baseStart_3717937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717963 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6]
def baseStart_3717963 : Nat := 118140960795 + 3717963 * 2 ^ 59
def prefixEnd_3717963 : Nat := 4983230072969 + 3 ^ 40 * 3717963 * 2
def baseEnd_3717963 : Nat := 1909102074632342186363905

theorem tailTrace_3717963 : CollatzResearch.WordTrace tailWord_3717963 prefixEnd_3717963 1909102074632342186363905 := by
  unfold tailWord_3717963
  simp only [CollatzResearch.WordTrace]
  refine ⟨135605251029462503372366543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90403500686308335581577695 135605251029462503372366543)
  ·
    refine ⟨203407876544193755058549815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135605251029462503372366543 203407876544193755058549815)
    ·
      refine ⟨305111814816290632587824723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203407876544193755058549815 305111814816290632587824723)
      ·
        refine ⟨457667722224435948881737085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305111814816290632587824723 457667722224435948881737085)
        ·
          refine ⟨171625395834163480830651407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457667722224435948881737085 171625395834163480830651407)
          ·
            refine ⟨257438093751245221245977111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171625395834163480830651407 257438093751245221245977111)
            ·
              refine ⟨386157140626867831868965667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257438093751245221245977111 386157140626867831868965667)
              ·
                refine ⟨579235710940301747803448501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386157140626867831868965667 579235710940301747803448501)
                ·
                  refine ⟨54303347900653288856573297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 579235710940301747803448501 54303347900653288856573297)
                  ·
                    refine ⟨40727510925489966642429973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54303347900653288856573297 40727510925489966642429973)
                    ·
                      refine ⟨1909102074632342186363905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40727510925489966642429973 1909102074632342186363905)
                      ·
                        rfl

theorem cell23_3717963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_3717963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717963 prefixEnd_3717963 := by exact prefixLift 3717963
  have htrace : WordTrace (prefixWord ++ tailWord_3717963) baseStart_3717963 baseEnd_3717963 := by
    simpa [prefixWord, tailWord_3717963, baseEnd_3717963] using wordTrace_append hprefix tailTrace_3717963
  have hstable : (prefixWord ++ tailWord_3717963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717963).length < 2 ^ (prefixWord ++ tailWord_3717963).sum := by decide
  have hdescent : baseEnd_3717963 < baseStart_3717963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717964 : List Nat := [2, 2, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_3717964 : Nat := 118140960795 + 3717964 * 2 ^ 59
def prefixEnd_3717964 : Nat := 4983230072969 + 3 ^ 40 * 3717964 * 2
def baseEnd_3717964 : Nat := 636367529370998894150467

theorem tailTrace_3717964 : CollatzResearch.WordTrace tailWord_3717964 prefixEnd_3717964 636367529370998894150467 := by
  unfold tailWord_3717964
  simp only [CollatzResearch.WordTrace]
  refine ⟨67802643751229440271576473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90403525001639253695435297 67802643751229440271576473)
  ·
    refine ⟨50851982813422080203682355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67802643751229440271576473 50851982813422080203682355)
    ·
      refine ⟨76277974220133120305523533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50851982813422080203682355 76277974220133120305523533)
      ·
        refine ⟨28604240332549920114571325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76277974220133120305523533 28604240332549920114571325)
        ·
          refine ⟨10726590124706220042964247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28604240332549920114571325 10726590124706220042964247)
          ·
            refine ⟨16089885187059330064446371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10726590124706220042964247 16089885187059330064446371)
            ·
              refine ⟨24134827780588995096669557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16089885187059330064446371 24134827780588995096669557)
              ·
                refine ⟨2262640104430218290312771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24134827780588995096669557 2262640104430218290312771)
                ·
                  refine ⟨3393960156645327435469157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262640104430218290312771 3393960156645327435469157)
                  ·
                    refine ⟨636367529370998894150467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3393960156645327435469157 636367529370998894150467)
                    ·
                      rfl

theorem cell23_3717964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_3717964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717964 prefixEnd_3717964 := by exact prefixLift 3717964
  have htrace : WordTrace (prefixWord ++ tailWord_3717964) baseStart_3717964 baseEnd_3717964 := by
    simpa [prefixWord, tailWord_3717964, baseEnd_3717964] using wordTrace_append hprefix tailTrace_3717964
  have hstable : (prefixWord ++ tailWord_3717964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717964).length < 2 ^ (prefixWord ++ tailWord_3717964).sum := by decide
  have hdescent : baseEnd_3717964 < baseStart_3717964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3717977 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 6]
def baseStart_3717977 : Nat := 118140960795 + 3717977 * 2 ^ 59
def prefixEnd_3717977 : Nat := 4983230072969 + 3 ^ 40 * 3717977 * 2
def baseEnd_3717977 : Nat := 212123251484611681287649

theorem tailTrace_3717977 : CollatzResearch.WordTrace tailWord_3717977 prefixEnd_3717977 212123251484611681287649 := by
  unfold tailWord_3717977
  simp only [CollatzResearch.WordTrace]
  refine ⟨135605761651411783763376185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90403841100941189175584123 135605761651411783763376185)
  ·
    refine ⟨101704321238558837822532139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135605761651411783763376185 101704321238558837822532139)
    ·
      refine ⟨152556481857838256733798209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101704321238558837822532139 152556481857838256733798209)
      ·
        refine ⟨114417361393378692550348657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152556481857838256733798209 114417361393378692550348657)
        ·
          refine ⟨85813021045034019412761493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114417361393378692550348657 85813021045034019412761493)
          ·
            refine ⟨4022485361485969659973195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85813021045034019412761493 4022485361485969659973195)
            ·
              refine ⟨6033728042228954489959793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022485361485969659973195 6033728042228954489959793)
              ·
                refine ⟨4525296031671715867469845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6033728042228954489959793 4525296031671715867469845)
                ·
                  refine ⟨212123251484611681287649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4525296031671715867469845 212123251484611681287649)
                  ·
                    rfl

theorem cell23_3717977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 6].length) (baseStart_3717977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3717977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3717977 prefixEnd_3717977 := by exact prefixLift 3717977
  have htrace : WordTrace (prefixWord ++ tailWord_3717977) baseStart_3717977 baseEnd_3717977 := by
    simpa [prefixWord, tailWord_3717977, baseEnd_3717977] using wordTrace_append hprefix tailTrace_3717977
  have hstable : (prefixWord ++ tailWord_3717977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3717977).length < 2 ^ (prefixWord ++ tailWord_3717977).sum := by decide
  have hdescent : baseEnd_3717977 < baseStart_3717977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3717977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718020 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3718020 : Nat := 118140960795 + 3718020 * 2 ^ 59
def prefixEnd_3718020 : Nat := 4983230072969 + 3 ^ 40 * 3718020 * 2
def baseEnd_3718020 : Nat := 636377114343216154450381

theorem tailTrace_3718020 : CollatzResearch.WordTrace tailWord_3718020 prefixEnd_3718020 636377114343216154450381 := by
  unfold tailWord_3718020
  simp only [CollatzResearch.WordTrace]
  refine ⟨67803664995128001053595757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90404886660170668071461009 67803664995128001053595757)
  ·
    refine ⟨25426374373173000395098409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67803664995128001053595757 25426374373173000395098409)
    ·
      refine ⟨19069780779879750296323807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25426374373173000395098409 19069780779879750296323807)
      ·
        refine ⟨28604671169819625444485711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19069780779879750296323807 28604671169819625444485711)
        ·
          refine ⟨42907006754729438166728567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28604671169819625444485711 42907006754729438166728567)
          ·
            refine ⟨64360510132094157250092851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42907006754729438166728567 64360510132094157250092851)
            ·
              refine ⟨96540765198141235875139277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64360510132094157250092851 96540765198141235875139277)
              ·
                refine ⟨36202786949302963453177229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96540765198141235875139277 36202786949302963453177229)
                ·
                  refine ⟨13576045105988611294941461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36202786949302963453177229 13576045105988611294941461)
                  ·
                    refine ⟨636377114343216154450381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13576045105988611294941461 636377114343216154450381)
                    ·
                      rfl

theorem cell23_3718020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3718020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718020 prefixEnd_3718020 := by exact prefixLift 3718020
  have htrace : WordTrace (prefixWord ++ tailWord_3718020) baseStart_3718020 baseEnd_3718020 := by
    simpa [prefixWord, tailWord_3718020, baseEnd_3718020] using wordTrace_append hprefix tailTrace_3718020
  have hstable : (prefixWord ++ tailWord_3718020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718020).length < 2 ^ (prefixWord ++ tailWord_3718020).sum := by decide
  have hdescent : baseEnd_3718020 < baseStart_3718020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718021 : List Nat := [1, 3, 1, 1, 3, 3, 3, 3, 1, 1, 3]
def baseStart_3718021 : Nat := 118140960795 + 3718021 * 2 ^ 59
def prefixEnd_3718021 : Nat := 4983230072969 + 3 ^ 40 * 3718021 * 2
def baseEnd_3718021 : Nat := 1909131856510302959438639

theorem tailTrace_3718021 : CollatzResearch.WordTrace tailWord_3718021 prefixEnd_3718021 1909131856510302959438639 := by
  unfold tailWord_3718021
  simp only [CollatzResearch.WordTrace]
  refine ⟨135607366463252379277977917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90404910975501586185318611 135607366463252379277977917)
  ·
    refine ⟨50852762423719642229241719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135607366463252379277977917 50852762423719642229241719)
    ·
      refine ⟨76279143635579463343862579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50852762423719642229241719 76279143635579463343862579)
      ·
        refine ⟨114418715453369195015793869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76279143635579463343862579 114418715453369195015793869)
        ·
          refine ⟨42907018295013448130922701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114418715453369195015793869 42907018295013448130922701)
          ·
            refine ⟨16090131860630043049096013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42907018295013448130922701 16090131860630043049096013)
            ·
              refine ⟨6033799447736266143411005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16090131860630043049096013 6033799447736266143411005)
              ·
                refine ⟨2262674792901099803779127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6033799447736266143411005 2262674792901099803779127)
                ·
                  refine ⟨3394012189351649705668691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262674792901099803779127 3394012189351649705668691)
                  ·
                    refine ⟨5091018284027474558503037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3394012189351649705668691 5091018284027474558503037)
                    ·
                      refine ⟨1909131856510302959438639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5091018284027474558503037 1909131856510302959438639)
                      ·
                        rfl

theorem cell23_3718021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_3718021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718021 prefixEnd_3718021 := by exact prefixLift 3718021
  have htrace : WordTrace (prefixWord ++ tailWord_3718021) baseStart_3718021 baseEnd_3718021 := by
    simpa [prefixWord, tailWord_3718021, baseEnd_3718021] using wordTrace_append hprefix tailTrace_3718021
  have hstable : (prefixWord ++ tailWord_3718021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718021).length < 2 ^ (prefixWord ++ tailWord_3718021).sum := by decide
  have hdescent : baseEnd_3718021 < baseStart_3718021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718027 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 4]
def baseStart_3718027 : Nat := 118140960795 + 3718027 * 2 ^ 59
def prefixEnd_3718027 : Nat := 4983230072969 + 3 ^ 40 * 3718027 * 2
def baseEnd_3718027 : Nat := 1909134937394229935963611

theorem tailTrace_3718027 : CollatzResearch.WordTrace tailWord_3718027 prefixEnd_3718027 1909134937394229935963611 := by
  unfold tailWord_3718027
  simp only [CollatzResearch.WordTrace]
  refine ⟨135607585301230642302696335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90405056867487094868464223 135607585301230642302696335)
  ·
    refine ⟨203411377951845963454044503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135607585301230642302696335 203411377951845963454044503)
    ·
      refine ⟨305117066927768945181066755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203411377951845963454044503 305117066927768945181066755)
      ·
        refine ⟨457675600391653417771600133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305117066927768945181066755 457675600391653417771600133)
        ·
          refine ⟨85814175073435015832175025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457675600391653417771600133 85814175073435015832175025)
          ·
            refine ⟨64360631305076261874131269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85814175073435015832175025 64360631305076261874131269)
            ·
              refine ⟨12067618369701799101399613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64360631305076261874131269 12067618369701799101399613)
              ·
                refine ⟨4525356888638174663024855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12067618369701799101399613 4525356888638174663024855)
                ·
                  refine ⟨6788035332957261994537283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525356888638174663024855 6788035332957261994537283)
                  ·
                    refine ⟨10182052999435892991805925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788035332957261994537283 10182052999435892991805925)
                    ·
                      refine ⟨1909134937394229935963611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10182052999435892991805925 1909134937394229935963611)
                      ·
                        rfl

theorem cell23_3718027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 4].length) (baseStart_3718027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718027 prefixEnd_3718027 := by exact prefixLift 3718027
  have htrace : WordTrace (prefixWord ++ tailWord_3718027) baseStart_3718027 baseEnd_3718027 := by
    simpa [prefixWord, tailWord_3718027, baseEnd_3718027] using wordTrace_append hprefix tailTrace_3718027
  have hstable : (prefixWord ++ tailWord_3718027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718027).length < 2 ^ (prefixWord ++ tailWord_3718027).sum := by decide
  have hdescent : baseEnd_3718027 < baseStart_3718027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718037 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_3718037 : Nat := 118140960795 + 3718037 * 2 ^ 59
def prefixEnd_3718037 : Nat := 4983230072969 + 3 ^ 40 * 3718037 * 2
def baseEnd_3718037 : Nat := 636380024066924965612855

theorem tailTrace_3718037 : CollatzResearch.WordTrace tailWord_3718037 prefixEnd_3718037 636380024066924965612855 := by
  unfold tailWord_3718037
  simp only [CollatzResearch.WordTrace]
  refine ⟨135607950031194414010560365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90405300020796276007040243 135607950031194414010560365)
  ·
    refine ⟨50852981261697905253960137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135607950031194414010560365 50852981261697905253960137)
    ·
      refine ⟨38139735946273428940470103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50852981261697905253960137 38139735946273428940470103)
      ·
        refine ⟨57209603919410143410705155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38139735946273428940470103 57209603919410143410705155)
        ·
          refine ⟨85814405879115215116057733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57209603919410143410705155 85814405879115215116057733)
          ·
            refine ⟨16090201102334102834260825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85814405879115215116057733 16090201102334102834260825)
            ·
              refine ⟨12067650826750577125695619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16090201102334102834260825 12067650826750577125695619)
              ·
                refine ⟨18101476240125865688543429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12067650826750577125695619 18101476240125865688543429)
                ·
                  refine ⟨3394026795023599816601893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18101476240125865688543429 3394026795023599816601893)
                  ·
                    refine ⟨636380024066924965612855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3394026795023599816601893 636380024066924965612855)
                    ·
                      rfl

theorem cell23_3718037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_3718037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718037 prefixEnd_3718037 := by exact prefixLift 3718037
  have htrace : WordTrace (prefixWord ++ tailWord_3718037) baseStart_3718037 baseEnd_3718037 := by
    simpa [prefixWord, tailWord_3718037, baseEnd_3718037] using wordTrace_append hprefix tailTrace_3718037
  have hstable : (prefixWord ++ tailWord_3718037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718037).length < 2 ^ (prefixWord ++ tailWord_3718037).sum := by decide
  have hdescent : baseEnd_3718037 < baseStart_3718037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718047 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3718047 : Nat := 118140960795 + 3718047 * 2 ^ 59
def prefixEnd_3718047 : Nat := 4983230072969 + 3 ^ 40 * 3718047 * 2
def baseEnd_3718047 : Nat := 1909145207007319857713519

theorem tailTrace_3718047 : CollatzResearch.WordTrace tailWord_3718047 prefixEnd_3718047 1909145207007319857713519 := by
  unfold tailWord_3718047
  simp only [CollatzResearch.WordTrace]
  refine ⟨135608314761158185718424395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90405543174105457145616263 135608314761158185718424395)
  ·
    refine ⟨203412472141737278577636593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135608314761158185718424395 203412472141737278577636593)
    ·
      refine ⟨152559354106302958933227445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203412472141737278577636593 152559354106302958933227445)
      ·
        refine ⟨14302439447465902399990073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152559354106302958933227445 14302439447465902399990073)
        ·
          refine ⟨10726829585599426799992555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14302439447465902399990073 10726829585599426799992555)
          ·
            refine ⟨16090244378399140199988833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10726829585599426799992555 16090244378399140199988833)
            ·
              refine ⟨12067683283799355149991625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16090244378399140199988833 12067683283799355149991625)
              ·
                refine ⟨9050762462849516362493719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12067683283799355149991625 9050762462849516362493719)
                ·
                  refine ⟨13576143694274274543740579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9050762462849516362493719 13576143694274274543740579)
                  ·
                    refine ⟨20364215541411411815610869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13576143694274274543740579 20364215541411411815610869)
                    ·
                      refine ⟨1909145207007319857713519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20364215541411411815610869 1909145207007319857713519)
                      ·
                        rfl

theorem cell23_3718047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3718047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718047 prefixEnd_3718047 := by exact prefixLift 3718047
  have htrace : WordTrace (prefixWord ++ tailWord_3718047) baseStart_3718047 baseEnd_3718047 := by
    simpa [prefixWord, tailWord_3718047, baseEnd_3718047] using wordTrace_append hprefix tailTrace_3718047
  have hstable : (prefixWord ++ tailWord_3718047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718047).length < 2 ^ (prefixWord ++ tailWord_3718047).sum := by decide
  have hdescent : baseEnd_3718047 < baseStart_3718047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718061 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3718061 : Nat := 118140960795 + 3718061 * 2 ^ 59
def prefixEnd_3718061 : Nat := 4983230072969 + 3 ^ 40 * 3718061 * 2
def baseEnd_3718061 : Nat := 1909152395736482802938455

theorem tailTrace_3718061 : CollatzResearch.WordTrace tailWord_3718061 prefixEnd_3718061 1909152395736482802938455 := by
  unfold tailWord_3718061
  simp only [CollatzResearch.WordTrace]
  refine ⟨135608825383107466109434037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90405883588738310739622691 135608825383107466109434037)
  ·
    refine ⟨12713327379666324947759441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135608825383107466109434037 12713327379666324947759441)
    ·
      refine ⟨9534995534749743710819581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12713327379666324947759441 9534995534749743710819581)
      ·
        refine ⟨3575623325531153891557343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9534995534749743710819581 3575623325531153891557343)
        ·
          refine ⟨5363434988296730837336015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575623325531153891557343 5363434988296730837336015)
          ·
            refine ⟨8045152482445096256004023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363434988296730837336015 8045152482445096256004023)
            ·
              refine ⟨12067728723667644384006035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045152482445096256004023 12067728723667644384006035)
              ·
                refine ⟨18101593085501466576009053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12067728723667644384006035 18101593085501466576009053)
                ·
                  refine ⟨6788097407063049966003395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18101593085501466576009053 6788097407063049966003395)
                  ·
                    refine ⟨10182146110594574949005093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6788097407063049966003395 10182146110594574949005093)
                    ·
                      refine ⟨1909152395736482802938455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10182146110594574949005093 1909152395736482802938455)
                      ·
                        rfl

theorem cell23_3718061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3718061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718061 prefixEnd_3718061 := by exact prefixLift 3718061
  have htrace : WordTrace (prefixWord ++ tailWord_3718061) baseStart_3718061 baseEnd_3718061 := by
    simpa [prefixWord, tailWord_3718061, baseEnd_3718061] using wordTrace_append hprefix tailTrace_3718061
  have hstable : (prefixWord ++ tailWord_3718061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718061).length < 2 ^ (prefixWord ++ tailWord_3718061).sum := by decide
  have hdescent : baseEnd_3718061 < baseStart_3718061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718078 : List Nat := [4, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_3718078 : Nat := 118140960795 + 3718078 * 2 ^ 59
def prefixEnd_3718078 : Nat := 4983230072969 + 3 ^ 40 * 3718078 * 2
def baseEnd_3718078 : Nat := 1909161124907609236425877

theorem tailTrace_3718078 : CollatzResearch.WordTrace tailWord_3718078 prefixEnd_3718078 1909161124907609236425877 := by
  unfold tailWord_3718078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951180678005734751600361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90406296949363918675201925 16951180678005734751600361)
  ·
    refine ⟨12713385508504301063700271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16951180678005734751600361 12713385508504301063700271)
    ·
      refine ⟨19070078262756451595550407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12713385508504301063700271 19070078262756451595550407)
      ·
        refine ⟨28605117394134677393325611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19070078262756451595550407 28605117394134677393325611)
        ·
          refine ⟨42907676091202016089988417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28605117394134677393325611 42907676091202016089988417)
          ·
            refine ⟨32180757068401512067491313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42907676091202016089988417 32180757068401512067491313)
            ·
              refine ⟨24135567801301134050618485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32180757068401512067491313 24135567801301134050618485)
              ·
                refine ⟨2262709481371981317245483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24135567801301134050618485 2262709481371981317245483)
                ·
                  refine ⟨3394064222057971975868225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262709481371981317245483 3394064222057971975868225)
                  ·
                    refine ⟨2545548166543478981901169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3394064222057971975868225 2545548166543478981901169)
                    ·
                      refine ⟨1909161124907609236425877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545548166543478981901169 1909161124907609236425877)
                      ·
                        rfl

theorem cell23_3718078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_3718078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718078 prefixEnd_3718078 := by exact prefixLift 3718078
  have htrace : WordTrace (prefixWord ++ tailWord_3718078) baseStart_3718078 baseEnd_3718078 := by
    simpa [prefixWord, tailWord_3718078, baseEnd_3718078] using wordTrace_append hprefix tailTrace_3718078
  have hstable : (prefixWord ++ tailWord_3718078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718078).length < 2 ^ (prefixWord ++ tailWord_3718078).sum := by decide
  have hdescent : baseEnd_3718078 < baseStart_3718078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718084 : List Nat := [2, 3, 3, 3, 2, 10]
def baseStart_3718084 : Nat := 118140960795 + 3718084 * 2 ^ 59
def prefixEnd_3718084 : Nat := 4983230072969 + 3 ^ 40 * 3718084 * 2
def baseEnd_3718084 : Nat := 7856642822187391822843

theorem tailTrace_3718084 : CollatzResearch.WordTrace tailWord_3718084 prefixEnd_3718084 7856642822187391822843 := by
  unfold tailWord_3718084
  simp only [CollatzResearch.WordTrace]
  refine ⟨67804832131012070518760653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90406442841349427358347537 67804832131012070518760653)
  ·
    refine ⟨25426812049129526444535245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67804832131012070518760653 25426812049129526444535245)
    ·
      refine ⟨9535054518423572416700717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25426812049129526444535245 9535054518423572416700717)
      ·
        refine ⟨3575645444408839656262769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9535054518423572416700717 3575645444408839656262769)
        ·
          refine ⟨2681734083306629742197077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575645444408839656262769 2681734083306629742197077)
          ·
            refine ⟨7856642822187391822843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2681734083306629742197077 7856642822187391822843)
            ·
              rfl

theorem cell23_3718084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 10].length) (baseStart_3718084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718084 prefixEnd_3718084 := by exact prefixLift 3718084
  have htrace : WordTrace (prefixWord ++ tailWord_3718084) baseStart_3718084 baseEnd_3718084 := by
    simpa [prefixWord, tailWord_3718084, baseEnd_3718084] using wordTrace_append hprefix tailTrace_3718084
  have hstable : (prefixWord ++ tailWord_3718084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718084).length < 2 ^ (prefixWord ++ tailWord_3718084).sum := by decide
  have hdescent : baseEnd_3718084 < baseStart_3718084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718095 : List Nat := [1, 1, 2, 1, 1, 8, 2, 2, 1, 2, 2]
def baseStart_3718095 : Nat := 118140960795 + 3718095 * 2 ^ 59
def prefixEnd_3718095 : Nat := 4983230072969 + 3 ^ 40 * 3718095 * 2
def baseEnd_3718095 : Nat := 1909169854078735669913299

theorem tailTrace_3718095 : CollatzResearch.WordTrace tailWord_3718095 prefixEnd_3718095 1909169854078735669913299 := by
  unfold tailWord_3718095
  simp only [CollatzResearch.WordTrace]
  refine ⟨135610065464984289916171739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90406710309989526610781159 135610065464984289916171739)
  ·
    refine ⟨203415098197476434874257609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135610065464984289916171739 203415098197476434874257609)
    ·
      refine ⟨152561323648107326155693207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203415098197476434874257609 152561323648107326155693207)
      ·
        refine ⟨228841985472160989233539811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152561323648107326155693207 228841985472160989233539811)
        ·
          refine ⟨343262978208241483850309717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228841985472160989233539811 343262978208241483850309717)
          ·
            refine ⟨4022613025877829888870817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 343262978208241483850309717 4022613025877829888870817)
            ·
              refine ⟨3016959769408372416653113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4022613025877829888870817 3016959769408372416653113)
              ·
                refine ⟨2262719827056279312489835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016959769408372416653113 2262719827056279312489835)
                ·
                  refine ⟨3394079740584418968734753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2262719827056279312489835 3394079740584418968734753)
                  ·
                    refine ⟨2545559805438314226551065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3394079740584418968734753 2545559805438314226551065)
                    ·
                      refine ⟨1909169854078735669913299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545559805438314226551065 1909169854078735669913299)
                      ·
                        rfl

theorem cell23_3718095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 1, 2, 2].length) (baseStart_3718095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718095 prefixEnd_3718095 := by exact prefixLift 3718095
  have htrace : WordTrace (prefixWord ++ tailWord_3718095) baseStart_3718095 baseEnd_3718095 := by
    simpa [prefixWord, tailWord_3718095, baseEnd_3718095] using wordTrace_append hprefix tailTrace_3718095
  have hstable : (prefixWord ++ tailWord_3718095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718095).length < 2 ^ (prefixWord ++ tailWord_3718095).sum := by decide
  have hdescent : baseEnd_3718095 < baseStart_3718095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718104 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 3, 3, 2]
def baseStart_3718104 : Nat := 118140960795 + 3718104 * 2 ^ 59
def prefixEnd_3718104 : Nat := 4983230072969 + 3 ^ 40 * 3718104 * 2
def baseEnd_3718104 : Nat := 1909174475404626134700757

theorem tailTrace_3718104 : CollatzResearch.WordTrace tailWord_3718104 prefixEnd_3718104 1909174475404626134700757 := by
  unfold tailWord_3718104
  simp only [CollatzResearch.WordTrace]
  refine ⟨67805196860975842226624683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90406929147967789635499577 67805196860975842226624683)
  ·
    refine ⟨101707795291463763339937025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67805196860975842226624683 101707795291463763339937025)
    ·
      refine ⟨76280846468597822504952769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101707795291463763339937025 76280846468597822504952769)
      ·
        refine ⟨57210634851448366878714577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76280846468597822504952769 57210634851448366878714577)
        ·
          refine ⟨42907976138586275159035933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57210634851448366878714577 42907976138586275159035933)
          ·
            refine ⟨16090491051969853184638475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42907976138586275159035933 16090491051969853184638475)
            ·
              refine ⟨24135736577954779776957713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16090491051969853184638475 24135736577954779776957713)
              ·
                refine ⟨18101802433466084832718285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24135736577954779776957713 18101802433466084832718285)
                ·
                  refine ⟨6788175912549781812269357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18101802433466084832718285 6788175912549781812269357)
                  ·
                    refine ⟨2545565967206168179601009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6788175912549781812269357 2545565967206168179601009)
                    ·
                      refine ⟨1909174475404626134700757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545565967206168179601009 1909174475404626134700757)
                      ·
                        rfl

theorem cell23_3718104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_3718104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718104 prefixEnd_3718104 := by exact prefixLift 3718104
  have htrace : WordTrace (prefixWord ++ tailWord_3718104) baseStart_3718104 baseEnd_3718104 := by
    simpa [prefixWord, tailWord_3718104, baseEnd_3718104] using wordTrace_append hprefix tailTrace_3718104
  have hstable : (prefixWord ++ tailWord_3718104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718104).length < 2 ^ (prefixWord ++ tailWord_3718104).sum := by decide
  have hdescent : baseEnd_3718104 < baseStart_3718104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718132 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3718132 : Nat := 118140960795 + 3718132 * 2 ^ 59
def prefixEnd_3718132 : Nat := 4983230072969 + 3 ^ 40 * 3718132 * 2
def baseEnd_3718132 : Nat := 1909188852862952025150629

theorem tailTrace_3718132 : CollatzResearch.WordTrace tailWord_3718132 prefixEnd_3718132 1909188852862952025150629 := by
  unfold tailWord_3718132
  simp only [CollatzResearch.WordTrace]
  refine ⟨67805707482925122617634325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90407609977233496823512433 67805707482925122617634325)
  ·
    refine ⟨3178392538262115122701609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67805707482925122617634325 3178392538262115122701609)
    ·
      refine ⟨2383794403696586342026207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3178392538262115122701609 2383794403696586342026207)
      ·
        refine ⟨3575691605544879513039311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383794403696586342026207 3575691605544879513039311)
        ·
          refine ⟨5363537408317319269558967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575691605544879513039311 5363537408317319269558967)
          ·
            refine ⟨8045306112475978904338451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363537408317319269558967 8045306112475978904338451)
            ·
              refine ⟨12067959168713968356507677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045306112475978904338451 12067959168713968356507677)
              ·
                refine ⟨4525484688267738133690379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12067959168713968356507677 4525484688267738133690379)
                ·
                  refine ⟨6788227032401607200535569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525484688267738133690379 6788227032401607200535569)
                  ·
                    refine ⟨5091170274301205400401677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6788227032401607200535569 5091170274301205400401677)
                    ·
                      refine ⟨1909188852862952025150629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5091170274301205400401677 1909188852862952025150629)
                      ·
                        rfl

theorem cell23_3718132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3718132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718132 prefixEnd_3718132 := by exact prefixLift 3718132
  have htrace : WordTrace (prefixWord ++ tailWord_3718132) baseStart_3718132 baseEnd_3718132 := by
    simpa [prefixWord, tailWord_3718132, baseEnd_3718132] using wordTrace_append hprefix tailTrace_3718132
  have hstable : (prefixWord ++ tailWord_3718132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718132).length < 2 ^ (prefixWord ++ tailWord_3718132).sum := by decide
  have hdescent : baseEnd_3718132 < baseStart_3718132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718151 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_3718151 : Nat := 118140960795 + 3718151 * 2 ^ 59
def prefixEnd_3718151 : Nat := 4983230072969 + 3 ^ 40 * 3718151 * 2
def baseEnd_3718151 : Nat := 1909198608995387450813041

theorem tailTrace_3718151 : CollatzResearch.WordTrace tailWord_3718151 prefixEnd_3718151 1909198608995387450813041 := by
  unfold tailWord_3718151
  simp only [CollatzResearch.WordTrace]
  refine ⟨135612107952781411480210307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90408071968520940986806871 135612107952781411480210307)
  ·
    refine ⟨203418161929172117220315461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135612107952781411480210307 203418161929172117220315461)
    ·
      refine ⟨38140905361719771978809149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203418161929172117220315461 38140905361719771978809149)
      ·
        refine ⟨14302839510644914492053431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38140905361719771978809149 14302839510644914492053431)
        ·
          refine ⟨21454259265967371738080147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14302839510644914492053431 21454259265967371738080147)
          ·
            refine ⟨32181388898951057607120221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21454259265967371738080147 32181388898951057607120221)
            ·
              refine ⟨12068020837106646602670083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32181388898951057607120221 12068020837106646602670083)
              ·
                refine ⟨18102031255659969904005125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12068020837106646602670083 18102031255659969904005125)
                ·
                  refine ⟨3394130860436244357000961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18102031255659969904005125 3394130860436244357000961)
                  ·
                    refine ⟨2545598145327183267750721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3394130860436244357000961 2545598145327183267750721)
                    ·
                      refine ⟨1909198608995387450813041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545598145327183267750721 1909198608995387450813041)
                      ·
                        rfl

theorem cell23_3718151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_3718151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718151 prefixEnd_3718151 := by exact prefixLift 3718151
  have htrace : WordTrace (prefixWord ++ tailWord_3718151) baseStart_3718151 baseEnd_3718151 := by
    simpa [prefixWord, tailWord_3718151, baseEnd_3718151] using wordTrace_append hprefix tailTrace_3718151
  have hstable : (prefixWord ++ tailWord_3718151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718151).length < 2 ^ (prefixWord ++ tailWord_3718151).sum := by decide
  have hdescent : baseEnd_3718151 < baseStart_3718151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718160 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_3718160 : Nat := 118140960795 + 3718160 * 2 ^ 59
def prefixEnd_3718160 : Nat := 4983230072969 + 3 ^ 40 * 3718160 * 2
def baseEnd_3718160 : Nat := 1909203230321277915600499

theorem tailTrace_3718160 : CollatzResearch.WordTrace tailWord_3718160 prefixEnd_3718160 1909203230321277915600499 := by
  unfold tailWord_3718160
  simp only [CollatzResearch.WordTrace]
  refine ⟨67806218104874403008643967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90408290806499204011525289 67806218104874403008643967)
  ·
    refine ⟨101709327157311604512965951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67806218104874403008643967 101709327157311604512965951)
    ·
      refine ⟨152563990735967406769448927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101709327157311604512965951 152563990735967406769448927)
      ·
        refine ⟨228845986103951110154173391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152563990735967406769448927 228845986103951110154173391)
        ·
          refine ⟨343268979155926665231260087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228845986103951110154173391 343268979155926665231260087)
          ·
            refine ⟨514903468733889997846890131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343268979155926665231260087 514903468733889997846890131)
            ·
              refine ⟨772355203100834996770335197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514903468733889997846890131 772355203100834996770335197)
              ·
                refine ⟨289633201162813123788875699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 772355203100834996770335197 289633201162813123788875699)
                ·
                  refine ⟨434449801744219685683313549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289633201162813123788875699 434449801744219685683313549)
                  ·
                    refine ⟨162918675654082382131242581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 434449801744219685683313549 162918675654082382131242581)
                    ·
                      refine ⟨1909203230321277915600499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 162918675654082382131242581 1909203230321277915600499)
                      ·
                        rfl

theorem cell23_3718160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_3718160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718160 prefixEnd_3718160 := by exact prefixLift 3718160
  have htrace : WordTrace (prefixWord ++ tailWord_3718160) baseStart_3718160 baseEnd_3718160 := by
    simpa [prefixWord, tailWord_3718160, baseEnd_3718160] using wordTrace_append hprefix tailTrace_3718160
  have hstable : (prefixWord ++ tailWord_3718160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718160).length < 2 ^ (prefixWord ++ tailWord_3718160).sum := by decide
  have hdescent : baseEnd_3718160 < baseStart_3718160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718162 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3718162 : Nat := 118140960795 + 3718162 * 2 ^ 59
def prefixEnd_3718162 : Nat := 4983230072969 + 3 ^ 40 * 3718162 * 2
def baseEnd_3718162 : Nat := 1909204257282586907775491

theorem tailTrace_3718162 : CollatzResearch.WordTrace tailWord_3718162 prefixEnd_3718162 1909204257282586907775491 := by
  unfold tailWord_3718162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33903127288935390089715185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90408339437161040239240493 33903127288935390089715185)
  ·
    refine ⟨25427345466701542567286389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33903127288935390089715185 25427345466701542567286389)
    ·
      refine ⟨2383813637503269615683099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25427345466701542567286389 2383813637503269615683099)
      ·
        refine ⟨3575720456254904423524649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383813637503269615683099 3575720456254904423524649)
        ·
          refine ⟨2681790342191178317643487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575720456254904423524649 2681790342191178317643487)
          ·
            refine ⟨4022685513286767476465231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681790342191178317643487 4022685513286767476465231)
            ·
              refine ⟨6034028269930151214697847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022685513286767476465231 6034028269930151214697847)
              ·
                refine ⟨9051042404895226822046771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6034028269930151214697847 9051042404895226822046771)
                ·
                  refine ⟨13576563607342840233070157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9051042404895226822046771 13576563607342840233070157)
                  ·
                    refine ⟨5091211352753565087401309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13576563607342840233070157 5091211352753565087401309)
                    ·
                      refine ⟨1909204257282586907775491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5091211352753565087401309 1909204257282586907775491)
                      ·
                        rfl

theorem cell23_3718162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3718162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718162 prefixEnd_3718162 := by exact prefixLift 3718162
  have htrace : WordTrace (prefixWord ++ tailWord_3718162) baseStart_3718162 baseEnd_3718162 := by
    simpa [prefixWord, tailWord_3718162, baseEnd_3718162] using wordTrace_append hprefix tailTrace_3718162
  have hstable : (prefixWord ++ tailWord_3718162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718162).length < 2 ^ (prefixWord ++ tailWord_3718162).sum := by decide
  have hdescent : baseEnd_3718162 < baseStart_3718162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718187 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 2, 5]
def baseStart_3718187 : Nat := 118140960795 + 3718187 * 2 ^ 59
def prefixEnd_3718187 : Nat := 4983230072969 + 3 ^ 40 * 3718187 * 2
def baseEnd_3718187 : Nat := 636405698099649769987625

theorem tailTrace_3718187 : CollatzResearch.WordTrace tailWord_3718187 prefixEnd_3718187 636405698099649769987625 := by
  unfold tailWord_3718187
  simp only [CollatzResearch.WordTrace]
  refine ⟨135613420980650989628520815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90408947320433993085680543 135613420980650989628520815)
  ·
    refine ⟨203420131470976484442781223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135613420980650989628520815 203420131470976484442781223)
    ·
      refine ⟨305130197206464726664171835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203420131470976484442781223 305130197206464726664171835)
      ·
        refine ⟨457695295809697089996257753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305130197206464726664171835 457695295809697089996257753)
        ·
          refine ⟨343271471857272817497193315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457695295809697089996257753 343271471857272817497193315)
          ·
            refine ⟨514907207785909226245789973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343271471857272817497193315 514907207785909226245789973)
            ·
              refine ⟨24136275364964494980271405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 514907207785909226245789973 24136275364964494980271405)
              ·
                refine ⟨9051103261861685617601777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24136275364964494980271405 9051103261861685617601777)
                ·
                  refine ⟨6788327446396264213201333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9051103261861685617601777 6788327446396264213201333)
                  ·
                    refine ⟨636405698099649769987625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6788327446396264213201333 636405698099649769987625)
                    ·
                      rfl

theorem cell23_3718187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 5].length) (baseStart_3718187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718187 prefixEnd_3718187 := by exact prefixLift 3718187
  have htrace : WordTrace (prefixWord ++ tailWord_3718187) baseStart_3718187 baseEnd_3718187 := by
    simpa [prefixWord, tailWord_3718187, baseEnd_3718187] using wordTrace_append hprefix tailTrace_3718187
  have hstable : (prefixWord ++ tailWord_3718187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718187).length < 2 ^ (prefixWord ++ tailWord_3718187).sum := by decide
  have hdescent : baseEnd_3718187 < baseStart_3718187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718197 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3718197 : Nat := 118140960795 + 3718197 * 2 ^ 59
def prefixEnd_3718197 : Nat := 4983230072969 + 3 ^ 40 * 3718197 * 2
def baseEnd_3718197 : Nat := 1909222229105494270837829

theorem tailTrace_3718197 : CollatzResearch.WordTrace tailWord_3718197 prefixEnd_3718197 1909222229105494270837829 := by
  unfold tailWord_3718197
  simp only [CollatzResearch.WordTrace]
  refine ⟨135613785710614761336384845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90409190473743174224256563 135613785710614761336384845)
  ·
    refine ⟨50855169641480535501144317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135613785710614761336384845 50855169641480535501144317)
    ·
      refine ⟨19070688615555200812929119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50855169641480535501144317 19070688615555200812929119)
      ·
        refine ⟨28606032923332801219393679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19070688615555200812929119 28606032923332801219393679)
        ·
          refine ⟨42909049384999201829090519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28606032923332801219393679 42909049384999201829090519)
          ·
            refine ⟨64363574077498802743635779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42909049384999201829090519 64363574077498802743635779)
            ·
              refine ⟨96545361116248204115453669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64363574077498802743635779 96545361116248204115453669)
              ·
                refine ⟨18102255209296538271647563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96545361116248204115453669 18102255209296538271647563)
                ·
                  refine ⟨27153382813944807407471345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18102255209296538271647563 27153382813944807407471345)
                  ·
                    refine ⟨20365037110458605555603509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27153382813944807407471345 20365037110458605555603509)
                    ·
                      refine ⟨1909222229105494270837829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20365037110458605555603509 1909222229105494270837829)
                      ·
                        rfl

theorem cell23_3718197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3718197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718197 prefixEnd_3718197 := by exact prefixLift 3718197
  have htrace : WordTrace (prefixWord ++ tailWord_3718197) baseStart_3718197 baseEnd_3718197 := by
    simpa [prefixWord, tailWord_3718197, baseEnd_3718197] using wordTrace_append hprefix tailTrace_3718197
  have hstable : (prefixWord ++ tailWord_3718197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718197).length < 2 ^ (prefixWord ++ tailWord_3718197).sum := by decide
  have hdescent : baseEnd_3718197 < baseStart_3718197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718204 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_3718204 : Nat := 118140960795 + 3718204 * 2 ^ 59
def prefixEnd_3718204 : Nat := 4983230072969 + 3 ^ 40 * 3718204 * 2
def baseEnd_3718204 : Nat := 636408607823358581150099

theorem tailTrace_3718204 : CollatzResearch.WordTrace tailWord_3718204 prefixEnd_3718204 636408607823358581150099 := by
  unfold tailWord_3718204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67807020510794700765944833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90409360681059601021259777 67807020510794700765944833)
  ·
    refine ⟨50855265383096025574458625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67807020510794700765944833 50855265383096025574458625)
    ·
      refine ⟨38141449037322019180843969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50855265383096025574458625 38141449037322019180843969)
      ·
        refine ⟨28606086777991514385632977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38141449037322019180843969 28606086777991514385632977)
        ·
          refine ⟨21454565083493635789224733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28606086777991514385632977 21454565083493635789224733)
          ·
            refine ⟨8045461906310113420959275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21454565083493635789224733 8045461906310113420959275)
            ·
              refine ⟨12068192859465170131438913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045461906310113420959275 12068192859465170131438913)
              ·
                refine ⟨9051144644598877598579185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12068192859465170131438913 9051144644598877598579185)
                ·
                  refine ⟨6788358483449158198934389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9051144644598877598579185 6788358483449158198934389)
                  ·
                    refine ⟨636408607823358581150099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6788358483449158198934389 636408607823358581150099)
                    ·
                      rfl

theorem cell23_3718204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_3718204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718204 prefixEnd_3718204 := by exact prefixLift 3718204
  have htrace : WordTrace (prefixWord ++ tailWord_3718204) baseStart_3718204 baseEnd_3718204 := by
    simpa [prefixWord, tailWord_3718204, baseEnd_3718204] using wordTrace_append hprefix tailTrace_3718204
  have hstable : (prefixWord ++ tailWord_3718204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718204).length < 2 ^ (prefixWord ++ tailWord_3718204).sum := by decide
  have hdescent : baseEnd_3718204 < baseStart_3718204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718224 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 2, 4, 2]
def baseStart_3718224 : Nat := 118140960795 + 3718224 * 2 ^ 59
def prefixEnd_3718224 : Nat := 4983230072969 + 3 ^ 40 * 3718224 * 2
def baseEnd_3718224 : Nat := 1909236093083165665200205

theorem tailTrace_3718224 : CollatzResearch.WordTrace tailWord_3718224 prefixEnd_3718224 1909236093083165665200205 := by
  unfold tailWord_3718224
  simp only [CollatzResearch.WordTrace]
  refine ⟨67807385240758472473808863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90409846987677963298411817 67807385240758472473808863)
  ·
    refine ⟨101711077861137708710713295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67807385240758472473808863 101711077861137708710713295)
    ·
      refine ⟨152566616791706563066069943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101711077861137708710713295 152566616791706563066069943)
      ·
        refine ⟨228849925187559844599104915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152566616791706563066069943 228849925187559844599104915)
        ·
          refine ⟨343274887781339766898657373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228849925187559844599104915 343274887781339766898657373)
          ·
            refine ⟨128728082918002412586996515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343274887781339766898657373 128728082918002412586996515)
            ·
              refine ⟨193092124377003618880494773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128728082918002412586996515 193092124377003618880494773)
              ·
                refine ⟨18102386660344089270046385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193092124377003618880494773 18102386660344089270046385)
                ·
                  refine ⟨13576789995258066952534789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18102386660344089270046385 13576789995258066952534789)
                  ·
                    refine ⟨2545648124110887553600273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13576789995258066952534789 2545648124110887553600273)
                    ·
                      refine ⟨1909236093083165665200205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545648124110887553600273 1909236093083165665200205)
                      ·
                        rfl

theorem cell23_3718224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 4, 2].length) (baseStart_3718224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718224 prefixEnd_3718224 := by exact prefixLift 3718224
  have htrace : WordTrace (prefixWord ++ tailWord_3718224) baseStart_3718224 baseEnd_3718224 := by
    simpa [prefixWord, tailWord_3718224, baseEnd_3718224] using wordTrace_append hprefix tailTrace_3718224
  have hstable : (prefixWord ++ tailWord_3718224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718224).length < 2 ^ (prefixWord ++ tailWord_3718224).sum := by decide
  have hdescent : baseEnd_3718224 < baseStart_3718224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718238 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3718238 : Nat := 118140960795 + 3718238 * 2 ^ 59
def prefixEnd_3718238 : Nat := 4983230072969 + 3 ^ 40 * 3718238 * 2
def baseEnd_3718238 : Nat := 636414427270776203475047

theorem tailTrace_3718238 : CollatzResearch.WordTrace tailWord_3718238 prefixEnd_3718238 636414427270776203475047 := by
  unfold tailWord_3718238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951910137933278167328421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90410187402310816892418245 16951910137933278167328421)
  ·
    refine ⟨3178483150862489656374079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16951910137933278167328421 3178483150862489656374079)
    ·
      refine ⟨4767724726293734484561119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3178483150862489656374079 4767724726293734484561119)
      ·
        refine ⟨7151587089440601726841679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4767724726293734484561119 7151587089440601726841679)
        ·
          refine ⟨10727380634160902590262519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7151587089440601726841679 10727380634160902590262519)
          ·
            refine ⟨16091070951241353885393779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10727380634160902590262519 16091070951241353885393779)
            ·
              refine ⟨24136606426862030828090669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16091070951241353885393779 24136606426862030828090669)
              ·
                refine ⟨9051227410073261560534001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24136606426862030828090669 9051227410073261560534001)
                ·
                  refine ⟨6788420557554946170400501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9051227410073261560534001 6788420557554946170400501)
                  ·
                    refine ⟨636414427270776203475047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6788420557554946170400501 636414427270776203475047)
                    ·
                      rfl

theorem cell23_3718238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3718238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718238 prefixEnd_3718238 := by exact prefixLift 3718238
  have htrace : WordTrace (prefixWord ++ tailWord_3718238) baseStart_3718238 baseEnd_3718238 := by
    simpa [prefixWord, tailWord_3718238, baseEnd_3718238] using wordTrace_append hprefix tailTrace_3718238
  have hstable : (prefixWord ++ tailWord_3718238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718238).length < 2 ^ (prefixWord ++ tailWord_3718238).sum := by decide
  have hdescent : baseEnd_3718238 < baseStart_3718238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718301 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 1, 5, 2]
def baseStart_3718301 : Nat := 118140960795 + 3718301 * 2 ^ 59
def prefixEnd_3718301 : Nat := 4983230072969 + 3 ^ 40 * 3718301 * 2
def baseEnd_3718301 : Nat := 1909275631093561863937351

theorem tailTrace_3718301 : CollatzResearch.WordTrace tailWord_3718301 prefixEnd_3718301 1909275631093561863937351 := by
  unfold tailWord_3718301
  simp only [CollatzResearch.WordTrace]
  refine ⟨135617578902237987098170757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90411719268158658065447171 135617578902237987098170757)
  ·
    refine ⟨25428296044169622580907017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135617578902237987098170757 25428296044169622580907017)
    ·
      refine ⟨19071222033127216935680263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25428296044169622580907017 19071222033127216935680263)
      ·
        refine ⟨28606833049690825403520395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19071222033127216935680263 28606833049690825403520395)
        ·
          refine ⟨42910249574536238105280593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28606833049690825403520395 42910249574536238105280593)
          ·
            refine ⟨32182687180902178578960445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42910249574536238105280593 32182687180902178578960445)
            ·
              refine ⟨12068507692838316967110167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32182687180902178578960445 12068507692838316967110167)
              ·
                refine ⟨18102761539257475450665251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12068507692838316967110167 18102761539257475450665251)
                ·
                  refine ⟨27154142308886213175997877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18102761539257475450665251 27154142308886213175997877)
                  ·
                    refine ⟨2545700841458082485249801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27154142308886213175997877 2545700841458082485249801)
                    ·
                      refine ⟨1909275631093561863937351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545700841458082485249801 1909275631093561863937351)
                      ·
                        rfl

theorem cell23_3718301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_3718301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718301 prefixEnd_3718301 := by exact prefixLift 3718301
  have htrace : WordTrace (prefixWord ++ tailWord_3718301) baseStart_3718301 baseEnd_3718301 := by
    simpa [prefixWord, tailWord_3718301, baseEnd_3718301] using wordTrace_append hprefix tailTrace_3718301
  have hstable : (prefixWord ++ tailWord_3718301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718301).length < 2 ^ (prefixWord ++ tailWord_3718301).sum := by decide
  have hdescent : baseEnd_3718301 < baseStart_3718301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718354 : List Nat := [3, 2, 2, 2, 1, 1, 3, 9]
def baseStart_3718354 : Nat := 118140960795 + 3718354 * 2 ^ 59
def prefixEnd_3718354 : Nat := 4983230072969 + 3 ^ 40 * 3718354 * 2
def baseEnd_3718354 : Nat := 70714920206231487280541

theorem tailTrace_3718354 : CollatzResearch.WordTrace tailWord_3718354 prefixEnd_3718354 70714920206231487280541 := by
  unfold tailWord_3718354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33904877992761494287462529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90413007980697318099900077 33904877992761494287462529)
  ·
    refine ⟨25428658494571120715596897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33904877992761494287462529 25428658494571120715596897)
    ·
      refine ⟨19071493870928340536697673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25428658494571120715596897 19071493870928340536697673)
      ·
        refine ⟨14303620403196255402523255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19071493870928340536697673 14303620403196255402523255)
        ·
          refine ⟨21455430604794383103784883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14303620403196255402523255 21455430604794383103784883)
          ·
            refine ⟨32183145907191574655677325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21455430604794383103784883 32183145907191574655677325)
            ·
              refine ⟨12068679715196840495878997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32183145907191574655677325 12068679715196840495878997)
              ·
                refine ⟨70714920206231487280541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12068679715196840495878997 70714920206231487280541)
                ·
                  rfl

theorem cell23_3718354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 9].length) (baseStart_3718354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718354 prefixEnd_3718354 := by exact prefixLift 3718354
  have htrace : WordTrace (prefixWord ++ tailWord_3718354) baseStart_3718354 baseEnd_3718354 := by
    simpa [prefixWord, tailWord_3718354, baseEnd_3718354] using wordTrace_append hprefix tailTrace_3718354
  have hstable : (prefixWord ++ tailWord_3718354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718354).length < 2 ^ (prefixWord ++ tailWord_3718354).sum := by decide
  have hdescent : baseEnd_3718354 < baseStart_3718354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718391 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 5, 3, 2]
def baseStart_3718391 : Nat := 118140960795 + 3718391 * 2 ^ 59
def prefixEnd_3718391 : Nat := 4983230072969 + 3 ^ 40 * 3718391 * 2
def baseEnd_3718391 : Nat := 1909321844352466511811937

theorem tailTrace_3718391 : CollatzResearch.WordTrace tailWord_3718391 prefixEnd_3718391 1909321844352466511811937 := by
  unfold tailWord_3718391
  simp only [CollatzResearch.WordTrace]
  refine ⟨135620861471911932468947027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90413907647941288312631351 135620861471911932468947027)
  ·
    refine ⟨203431292207867898703420541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135620861471911932468947027 203431292207867898703420541)
    ·
      refine ⟨76286734577950462013782703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203431292207867898703420541 76286734577950462013782703)
      ·
        refine ⟨114430101866925693020674055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76286734577950462013782703 114430101866925693020674055)
        ·
          refine ⟨171645152800388539531011083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114430101866925693020674055 171645152800388539531011083)
          ·
            refine ⟨257467729200582809296516625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171645152800388539531011083 257467729200582809296516625)
            ·
              refine ⟨193100796900437106972387469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257467729200582809296516625 193100796900437106972387469)
              ·
                refine ⟨72412798837663915114645301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193100796900437106972387469 72412798837663915114645301)
                ·
                  refine ⟨6788699891030992041997997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72412798837663915114645301 6788699891030992041997997)
                  ·
                    refine ⟨2545762459136622015749249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6788699891030992041997997 2545762459136622015749249)
                    ·
                      refine ⟨1909321844352466511811937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545762459136622015749249 1909321844352466511811937)
                      ·
                        rfl

theorem cell23_3718391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_3718391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718391 prefixEnd_3718391 := by exact prefixLift 3718391
  have htrace : WordTrace (prefixWord ++ tailWord_3718391) baseStart_3718391 baseEnd_3718391 := by
    simpa [prefixWord, tailWord_3718391, baseEnd_3718391] using wordTrace_append hprefix tailTrace_3718391
  have hstable : (prefixWord ++ tailWord_3718391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718391).length < 2 ^ (prefixWord ++ tailWord_3718391).sum := by decide
  have hdescent : baseEnd_3718391 < baseStart_3718391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718402 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_3718402 : Nat := 118140960795 + 3718402 * 2 ^ 59
def prefixEnd_3718402 : Nat := 4983230072969 + 3 ^ 40 * 3718402 * 2
def baseEnd_3718402 : Nat := 1909327492639665968774387

theorem tailTrace_3718402 : CollatzResearch.WordTrace tailWord_3718402 prefixEnd_3718402 1909327492639665968774387 := by
  unfold tailWord_3718402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905315668718020336899365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90414175116581387565064973 33905315668718020336899365)
  ·
    refine ⟨6357246687884628813168631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33905315668718020336899365 6357246687884628813168631)
    ·
      refine ⟨9535870031826943219752947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6357246687884628813168631 9535870031826943219752947)
      ·
        refine ⟨14303805047740414829629421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535870031826943219752947 14303805047740414829629421)
        ·
          refine ⟨5363926892902655561111033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14303805047740414829629421 5363926892902655561111033)
          ·
            refine ⟨4022945169676991670833275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5363926892902655561111033 4022945169676991670833275)
            ·
              refine ⟨6034417754515487506249913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4022945169676991670833275 6034417754515487506249913)
              ·
                refine ⟨4525813315886615629687435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6034417754515487506249913 4525813315886615629687435)
                ·
                  refine ⟨6788719973829923444531153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4525813315886615629687435 6788719973829923444531153)
                  ·
                    refine ⟨5091539980372442583398365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6788719973829923444531153 5091539980372442583398365)
                    ·
                      refine ⟨1909327492639665968774387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5091539980372442583398365 1909327492639665968774387)
                      ·
                        rfl

theorem cell23_3718402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_3718402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718402 prefixEnd_3718402 := by exact prefixLift 3718402
  have htrace : WordTrace (prefixWord ++ tailWord_3718402) baseStart_3718402 baseEnd_3718402 := by
    simpa [prefixWord, tailWord_3718402, baseEnd_3718402] using wordTrace_append hprefix tailTrace_3718402
  have hstable : (prefixWord ++ tailWord_3718402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718402).length < 2 ^ (prefixWord ++ tailWord_3718402).sum := by decide
  have hdescent : baseEnd_3718402 < baseStart_3718402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718444 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 7]
def baseStart_3718444 : Nat := 118140960795 + 3718444 * 2 ^ 59
def prefixEnd_3718444 : Nat := 4983230072969 + 3 ^ 40 * 3718444 * 2
def baseEnd_3718444 : Nat := 212149895425239422716577

theorem tailTrace_3718444 : CollatzResearch.WordTrace tailWord_3718444 prefixEnd_3718444 212149895425239422716577 := by
  unfold tailWord_3718444
  simp only [CollatzResearch.WordTrace]
  refine ⟨67811397270359961260313193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90415196360479948347084257 67811397270359961260313193)
  ·
    refine ⟨50858547952769970945234895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67811397270359961260313193 50858547952769970945234895)
    ·
      refine ⟨76287821929154956417852343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50858547952769970945234895 76287821929154956417852343)
      ·
        refine ⟨114431732893732434626778515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76287821929154956417852343 114431732893732434626778515)
        ·
          refine ⟨171647599340598651940167773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114431732893732434626778515 171647599340598651940167773)
          ·
            refine ⟨64367849752724494477562915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171647599340598651940167773 64367849752724494477562915)
            ·
              refine ⟨96551774629086741716344373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64367849752724494477562915 96551774629086741716344373)
              ·
                refine ⟨9051728871476882035907285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96551774629086741716344373 9051728871476882035907285)
                ·
                  refine ⟨212149895425239422716577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9051728871476882035907285 212149895425239422716577)
                  ·
                    rfl

theorem cell23_3718444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_3718444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718444 prefixEnd_3718444 := by exact prefixLift 3718444
  have htrace : WordTrace (prefixWord ++ tailWord_3718444) baseStart_3718444 baseEnd_3718444 := by
    simpa [prefixWord, tailWord_3718444, baseEnd_3718444] using wordTrace_append hprefix tailTrace_3718444
  have hstable : (prefixWord ++ tailWord_3718444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718444).length < 2 ^ (prefixWord ++ tailWord_3718444).sum := by decide
  have hdescent : baseEnd_3718444 < baseStart_3718444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718451 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4]
def baseStart_3718451 : Nat := 118140960795 + 3718451 * 2 ^ 59
def prefixEnd_3718451 : Nat := 4983230072969 + 3 ^ 40 * 3718451 * 2
def baseEnd_3718451 : Nat := 1909352653191736277061661

theorem tailTrace_3718451 : CollatzResearch.WordTrace tailWord_3718451 prefixEnd_3718451 1909352653191736277061661 := by
  unfold tailWord_3718451
  simp only [CollatzResearch.WordTrace]
  refine ⟨135623049851694562716131207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90415366567796375144087471 135623049851694562716131207)
  ·
    refine ⟨203434574777541844074196811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135623049851694562716131207 203434574777541844074196811)
    ·
      refine ⟨305151862166312766111295217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203434574777541844074196811 305151862166312766111295217)
      ·
        refine ⟨228863896624734574583471413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305151862166312766111295217 228863896624734574583471413)
        ·
          refine ⟨21455990308568866367200445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228863896624734574583471413 21455990308568866367200445)
          ·
            refine ⟨8045996365713324887700167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21455990308568866367200445 8045996365713324887700167)
            ·
              refine ⟨12068994548569987331550251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045996365713324887700167 12068994548569987331550251)
              ·
                refine ⟨18103491822854980997325377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12068994548569987331550251 18103491822854980997325377)
                ·
                  refine ⟨13577618867141235747994033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18103491822854980997325377 13577618867141235747994033)
                  ·
                    refine ⟨10183214150355926810995525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13577618867141235747994033 10183214150355926810995525)
                    ·
                      refine ⟨1909352653191736277061661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10183214150355926810995525 1909352653191736277061661)
                      ·
                        rfl

theorem cell23_3718451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_3718451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718451 prefixEnd_3718451 := by exact prefixLift 3718451
  have htrace : WordTrace (prefixWord ++ tailWord_3718451) baseStart_3718451 baseEnd_3718451 := by
    simpa [prefixWord, tailWord_3718451, baseEnd_3718451] using wordTrace_append hprefix tailTrace_3718451
  have hstable : (prefixWord ++ tailWord_3718451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718451).length < 2 ^ (prefixWord ++ tailWord_3718451).sum := by decide
  have hdescent : baseEnd_3718451 < baseStart_3718451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718478 : List Nat := [4, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_3718478 : Nat := 118140960795 + 3718478 * 2 ^ 59
def prefixEnd_3718478 : Nat := 4983230072969 + 3 ^ 40 * 3718478 * 2
def baseEnd_3718478 : Nat := 212151835241045296824893

theorem tailTrace_3718478 : CollatzResearch.WordTrace tailWord_3718478 prefixEnd_3718478 212151835241045296824893 := by
  unfold tailWord_3718478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16953004327824593290920511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90416023081731164218242725 16953004327824593290920511)
  ·
    refine ⟨25429506491736889936380767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16953004327824593290920511 25429506491736889936380767)
    ·
      refine ⟨38144259737605334904571151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25429506491736889936380767 38144259737605334904571151)
      ·
        refine ⟨57216389606408002356856727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38144259737605334904571151 57216389606408002356856727)
        ·
          refine ⟨85824584409612003535285091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57216389606408002356856727 85824584409612003535285091)
          ·
            refine ⟨128736876614418005302927637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85824584409612003535285091 128736876614418005302927637)
            ·
              refine ⟨6034541091300843998574733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128736876614418005302927637 6034541091300843998574733)
              ·
                refine ⟨2262952909237816499465525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6034541091300843998574733 2262952909237816499465525)
                ·
                  refine ⟨212151835241045296824893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2262952909237816499465525 212151835241045296824893)
                  ·
                    rfl

theorem cell23_3718478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_3718478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718478 prefixEnd_3718478 := by exact prefixLift 3718478
  have htrace : WordTrace (prefixWord ++ tailWord_3718478) baseStart_3718478 baseEnd_3718478 := by
    simpa [prefixWord, tailWord_3718478, baseEnd_3718478] using wordTrace_append hprefix tailTrace_3718478
  have hstable : (prefixWord ++ tailWord_3718478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718478).length < 2 ^ (prefixWord ++ tailWord_3718478).sum := by decide
  have hdescent : baseEnd_3718478 < baseStart_3718478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718551 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 6]
def baseStart_3718551 : Nat := 118140960795 + 3718551 * 2 ^ 59
def prefixEnd_3718551 : Nat := 4983230072969 + 3 ^ 40 * 3718551 * 2
def baseEnd_3718551 : Nat := 212156000139687320645689

theorem tailTrace_3718551 : CollatzResearch.WordTrace tailWord_3718551 prefixEnd_3718551 212156000139687320645689 := by
  unfold tailWord_3718551
  simp only [CollatzResearch.WordTrace]
  refine ⟨135626697151332279794771507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90417798100888186529847671 135626697151332279794771507)
  ·
    refine ⟨203440045726998419692157261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135626697151332279794771507 203440045726998419692157261)
    ·
      refine ⟨76290017147624407384558973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203440045726998419692157261 76290017147624407384558973)
      ·
        refine ⟨28608756430359152769209615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76290017147624407384558973 28608756430359152769209615)
        ·
          refine ⟨42913134645538729153814423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28608756430359152769209615 42913134645538729153814423)
          ·
            refine ⟨64369701968308093730721635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42913134645538729153814423 64369701968308093730721635)
            ·
              refine ⟨96554552952462140596082453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64369701968308093730721635 96554552952462140596082453)
              ·
                refine ⟨4525994669646662840441365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96554552952462140596082453 4525994669646662840441365)
                ·
                  refine ⟨212156000139687320645689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4525994669646662840441365 212156000139687320645689)
                  ·
                    rfl

theorem cell23_3718551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 6].length) (baseStart_3718551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718551 prefixEnd_3718551 := by exact prefixLift 3718551
  have htrace : WordTrace (prefixWord ++ tailWord_3718551) baseStart_3718551 baseEnd_3718551 := by
    simpa [prefixWord, tailWord_3718551, baseEnd_3718551] using wordTrace_append hprefix tailTrace_3718551
  have hstable : (prefixWord ++ tailWord_3718551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718551).length < 2 ^ (prefixWord ++ tailWord_3718551).sum := by decide
  have hdescent : baseEnd_3718551 < baseStart_3718551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718618 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4]
def baseStart_3718618 : Nat := 118140960795 + 3718618 * 2 ^ 59
def prefixEnd_3718618 : Nat := 4983230072969 + 3 ^ 40 * 3718618 * 2
def baseEnd_3718618 : Nat := 1909438404461037123673393

theorem tailTrace_3718618 : CollatzResearch.WordTrace tailWord_3718618 prefixEnd_3718618 1909438404461037123673393 := by
  unfold tailWord_3718618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33907285210522387559365127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90419427228059700158307005 33907285210522387559365127)
  ·
    refine ⟨50860927815783581339047691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33907285210522387559365127 50860927815783581339047691)
    ·
      refine ⟨76291391723675372008571537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50860927815783581339047691 76291391723675372008571537)
      ·
        refine ⟨57218543792756529006428653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76291391723675372008571537 57218543792756529006428653)
        ·
          refine ⟨21456953922283698377410745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57218543792756529006428653 21456953922283698377410745)
          ·
            refine ⟨16092715441712773783058059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21456953922283698377410745 16092715441712773783058059)
            ·
              refine ⟨24139073162569160674587089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16092715441712773783058059 24139073162569160674587089)
              ·
                refine ⟨18104304871926870505940317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24139073162569160674587089 18104304871926870505940317)
                ·
                  refine ⟨6789114326972576439727619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18104304871926870505940317 6789114326972576439727619)
                  ·
                    refine ⟨10183671490458864659591429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6789114326972576439727619 10183671490458864659591429)
                    ·
                      refine ⟨1909438404461037123673393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10183671490458864659591429 1909438404461037123673393)
                      ·
                        rfl

theorem cell23_3718618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_3718618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718618 prefixEnd_3718618 := by exact prefixLift 3718618
  have htrace : WordTrace (prefixWord ++ tailWord_3718618) baseStart_3718618 baseEnd_3718618 := by
    simpa [prefixWord, tailWord_3718618, baseEnd_3718618] using wordTrace_append hprefix tailTrace_3718618
  have hstable : (prefixWord ++ tailWord_3718618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718618).length < 2 ^ (prefixWord ++ tailWord_3718618).sum := by decide
  have hdescent : baseEnd_3718618 < baseStart_3718618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718645 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3718645 : Nat := 118140960795 + 3718645 * 2 ^ 59
def prefixEnd_3718645 : Nat := 4983230072969 + 3 ^ 40 * 3718645 * 2
def baseEnd_3718645 : Nat := 636484089479569506011923

theorem tailTrace_3718645 : CollatzResearch.WordTrace tailWord_3718645 prefixEnd_3718645 636484089479569506011923 := by
  unfold tailWord_3718645
  simp only [CollatzResearch.WordTrace]
  refine ⟨135630125612991733848693389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90420083741994489232462259 135630125612991733848693389)
  ·
    refine ⟨50861297104871900193260021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135630125612991733848693389 50861297104871900193260021)
    ·
      refine ⟨4768246603581740643118127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50861297104871900193260021 4768246603581740643118127)
      ·
        refine ⟨7152369905372610964677191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4768246603581740643118127 7152369905372610964677191)
        ·
          refine ⟨10728554858058916447015787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7152369905372610964677191 10728554858058916447015787)
          ·
            refine ⟨16092832287088374670523681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10728554858058916447015787 16092832287088374670523681)
            ·
              refine ⟨12069624215316281002892761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16092832287088374670523681 12069624215316281002892761)
              ·
                refine ⟨9052218161487210752169571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12069624215316281002892761 9052218161487210752169571)
                ·
                  refine ⟨13578327242230816128254357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9052218161487210752169571 13578327242230816128254357)
                  ·
                    refine ⟨636484089479569506011923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13578327242230816128254357 636484089479569506011923)
                    ·
                      rfl

theorem cell23_3718645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3718645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718645 prefixEnd_3718645 := by exact prefixLift 3718645
  have htrace : WordTrace (prefixWord ++ tailWord_3718645) baseStart_3718645 baseEnd_3718645 := by
    simpa [prefixWord, tailWord_3718645, baseEnd_3718645] using wordTrace_append hprefix tailTrace_3718645
  have hstable : (prefixWord ++ tailWord_3718645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718645).length < 2 ^ (prefixWord ++ tailWord_3718645).sum := by decide
  have hdescent : baseEnd_3718645 < baseStart_3718645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718648 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_3718648 : Nat := 118140960795 + 3718648 * 2 ^ 59
def prefixEnd_3718648 : Nat := 4983230072969 + 3 ^ 40 * 3718648 * 2
def baseEnd_3718648 : Nat := 1909453808880672006298255

theorem tailTrace_3718648 : CollatzResearch.WordTrace tailWord_3718648 prefixEnd_3718648 1909453808880672006298255 := by
  unfold tailWord_3718648
  simp only [CollatzResearch.WordTrace]
  refine ⟨67815117515990432680526299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90420156687987243574035065 67815117515990432680526299)
  ·
    refine ⟨101722676273985649020789449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67815117515990432680526299 101722676273985649020789449)
    ·
      refine ⟨76292007205489236765592087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101722676273985649020789449 76292007205489236765592087)
      ·
        refine ⟨114438010808233855148388131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76292007205489236765592087 114438010808233855148388131)
        ·
          refine ⟨171657016212350782722582197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114438010808233855148388131 171657016212350782722582197)
          ·
            refine ⟨16092845269907885880242081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171657016212350782722582197 16092845269907885880242081)
            ·
              refine ⟨12069633952430914410181561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16092845269907885880242081 12069633952430914410181561)
              ·
                refine ⟨9052225464323185807636171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12069633952430914410181561 9052225464323185807636171)
                ·
                  refine ⟨13578338196484778711454257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9052225464323185807636171 13578338196484778711454257)
                  ·
                    refine ⟨10183753647363584033590693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13578338196484778711454257 10183753647363584033590693)
                    ·
                      refine ⟨1909453808880672006298255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10183753647363584033590693 1909453808880672006298255)
                      ·
                        rfl

theorem cell23_3718648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_3718648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718648 prefixEnd_3718648 := by exact prefixLift 3718648
  have htrace : WordTrace (prefixWord ++ tailWord_3718648) baseStart_3718648 baseEnd_3718648 := by
    simpa [prefixWord, tailWord_3718648, baseEnd_3718648] using wordTrace_append hprefix tailTrace_3718648
  have hstable : (prefixWord ++ tailWord_3718648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718648).length < 2 ^ (prefixWord ++ tailWord_3718648).sum := by decide
  have hdescent : baseEnd_3718648 < baseStart_3718648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718661 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_3718661 : Nat := 118140960795 + 3718661 * 2 ^ 59
def prefixEnd_3718661 : Nat := 4983230072969 + 3 ^ 40 * 3718661 * 2
def baseEnd_3718661 : Nat := 1909460484129180455435695

theorem tailTrace_3718661 : CollatzResearch.WordTrace tailWord_3718661 prefixEnd_3718661 1909460484129180455435695 := by
  unfold tailWord_3718661
  simp only [CollatzResearch.WordTrace]
  refine ⟨135630709180933768581275837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90420472787289179054183891 135630709180933768581275837)
  ·
    refine ⟨50861515942850163217978439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135630709180933768581275837 50861515942850163217978439)
    ·
      refine ⟨76292273914275244826967659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50861515942850163217978439 76292273914275244826967659)
      ·
        refine ⟨114438410871412867240451489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76292273914275244826967659 114438410871412867240451489)
        ·
          refine ⟨85828808153559650430338617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114438410871412867240451489 85828808153559650430338617)
          ·
            refine ⟨64371606115169737822753963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85828808153559650430338617 64371606115169737822753963)
            ·
              refine ⟨96557409172754606734130945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64371606115169737822753963 96557409172754606734130945)
              ·
                refine ⟨72418056879565955050598209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96557409172754606734130945 72418056879565955050598209)
                ·
                  refine ⟨54313542659674466287948657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72418056879565955050598209 54313542659674466287948657)
                  ·
                    refine ⟨40735156994755849715961493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54313542659674466287948657 40735156994755849715961493)
                    ·
                      refine ⟨1909460484129180455435695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40735156994755849715961493 1909460484129180455435695)
                      ·
                        rfl

theorem cell23_3718661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_3718661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718661 prefixEnd_3718661 := by exact prefixLift 3718661
  have htrace : WordTrace (prefixWord ++ tailWord_3718661) baseStart_3718661 baseEnd_3718661 := by
    simpa [prefixWord, tailWord_3718661, baseEnd_3718661] using wordTrace_append hprefix tailTrace_3718661
  have hstable : (prefixWord ++ tailWord_3718661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718661).length < 2 ^ (prefixWord ++ tailWord_3718661).sum := by decide
  have hdescent : baseEnd_3718661 < baseStart_3718661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718681 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_3718681 : Nat := 118140960795 + 3718681 * 2 ^ 59
def prefixEnd_3718681 : Nat := 4983230072969 + 3 ^ 40 * 3718681 * 2
def baseEnd_3718681 : Nat := 1909470753742270377185603

theorem tailTrace_3718681 : CollatzResearch.WordTrace tailWord_3718681 prefixEnd_3718681 1909470753742270377185603 := by
  unfold tailWord_3718681
  simp only [CollatzResearch.WordTrace]
  refine ⟨135631438640861311997003897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90420959093907541331335931 135631438640861311997003897)
  ·
    refine ⟨101723578980645983997752923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135631438640861311997003897 101723578980645983997752923)
    ·
      refine ⟨152585368470968975996629385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101723578980645983997752923 152585368470968975996629385)
      ·
        refine ⟨114439026353226731997472039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152585368470968975996629385 114439026353226731997472039)
        ·
          refine ⟨171658539529840097996208059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114439026353226731997472039 171658539529840097996208059)
          ·
            refine ⟨257487809294760146994312089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171658539529840097996208059 257487809294760146994312089)
            ·
              refine ⟨193115856971070110245734067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257487809294760146994312089 193115856971070110245734067)
              ·
                refine ⟨289673785456605165368601101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193115856971070110245734067 289673785456605165368601101)
                ·
                  refine ⟨108627669546226937013225413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 289673785456605165368601101 108627669546226937013225413)
                  ·
                    refine ⟨20367688039917550689979765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108627669546226937013225413 20367688039917550689979765)
                    ·
                      refine ⟨1909470753742270377185603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20367688039917550689979765 1909470753742270377185603)
                      ·
                        rfl

theorem cell23_3718681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_3718681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718681 prefixEnd_3718681 := by exact prefixLift 3718681
  have htrace : WordTrace (prefixWord ++ tailWord_3718681) baseStart_3718681 baseEnd_3718681 := by
    simpa [prefixWord, tailWord_3718681, baseEnd_3718681] using wordTrace_append hprefix tailTrace_3718681
  have hstable : (prefixWord ++ tailWord_3718681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718681).length < 2 ^ (prefixWord ++ tailWord_3718681).sum := by decide
  have hdescent : baseEnd_3718681 < baseStart_3718681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718698 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3718698 : Nat := 118140960795 + 3718698 * 2 ^ 59
def prefixEnd_3718698 : Nat := 4983230072969 + 3 ^ 40 * 3718698 * 2
def baseEnd_3718698 : Nat := 1909479482913396810673025

theorem tailTrace_3718698 : CollatzResearch.WordTrace tailWord_3718698 prefixEnd_3718698 1909479482913396810673025 := by
  unfold tailWord_3718698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33908014670449930975093187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90421372454533149266915165 33908014670449930975093187)
  ·
    refine ⟨50862022005674896462639781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33908014670449930975093187 50862022005674896462639781)
    ·
      refine ⟨9536629126064043086744959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50862022005674896462639781 9536629126064043086744959)
      ·
        refine ⟨14304943689096064630117439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536629126064043086744959 14304943689096064630117439)
        ·
          refine ⟨21457415533644096945176159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14304943689096064630117439 21457415533644096945176159)
          ·
            refine ⟨32186123300466145417764239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21457415533644096945176159 32186123300466145417764239)
            ·
              refine ⟨48279184950699218126646359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32186123300466145417764239 48279184950699218126646359)
              ·
                refine ⟨72418777426048827189969539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48279184950699218126646359 72418777426048827189969539)
                ·
                  refine ⟨108628166139073240784954309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72418777426048827189969539 108628166139073240784954309)
                  ·
                    refine ⟨20367781151076232647178933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108628166139073240784954309 20367781151076232647178933)
                    ·
                      refine ⟨1909479482913396810673025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20367781151076232647178933 1909479482913396810673025)
                      ·
                        rfl

theorem cell23_3718698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3718698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718698 prefixEnd_3718698 := by exact prefixLift 3718698
  have htrace : WordTrace (prefixWord ++ tailWord_3718698) baseStart_3718698 baseEnd_3718698 := by
    simpa [prefixWord, tailWord_3718698, baseEnd_3718698] using wordTrace_append hprefix tailTrace_3718698
  have hstable : (prefixWord ++ tailWord_3718698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718698).length < 2 ^ (prefixWord ++ tailWord_3718698).sum := by decide
  have hdescent : baseEnd_3718698 < baseStart_3718698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718702 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3718702 : Nat := 118140960795 + 3718702 * 2 ^ 59
def prefixEnd_3718702 : Nat := 4983230072969 + 3 ^ 40 * 3718702 * 2
def baseEnd_3718702 : Nat := 1909481536836014795023007

theorem tailTrace_3718702 : CollatzResearch.WordTrace tailWord_3718702 prefixEnd_3718702 1909481536836014795023007 := by
  unfold tailWord_3718702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954025571723154072939795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90421469715856821722345573 16954025571723154072939795)
  ·
    refine ⟨25431038357584731109409693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16954025571723154072939795 25431038357584731109409693)
    ·
      refine ⟨9536639384094274166028635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25431038357584731109409693 9536639384094274166028635)
      ·
        refine ⟨14304959076141411249042953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536639384094274166028635 14304959076141411249042953)
        ·
          refine ⟨10728719307106058436782215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14304959076141411249042953 10728719307106058436782215)
          ·
            refine ⟨16093078960659087655173323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10728719307106058436782215 16093078960659087655173323)
            ·
              refine ⟨24139618440988631482759985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16093078960659087655173323 24139618440988631482759985)
              ·
                refine ⟨18104713830741473612069989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24139618440988631482759985 18104713830741473612069989)
                ·
                  refine ⟨3394633843264026302263123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18104713830741473612069989 3394633843264026302263123)
                  ·
                    refine ⟨5091950764896039453394685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3394633843264026302263123 5091950764896039453394685)
                    ·
                      refine ⟨1909481536836014795023007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5091950764896039453394685 1909481536836014795023007)
                      ·
                        rfl

theorem cell23_3718702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3718702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718702 prefixEnd_3718702 := by exact prefixLift 3718702
  have htrace : WordTrace (prefixWord ++ tailWord_3718702) baseStart_3718702 baseEnd_3718702 := by
    simpa [prefixWord, tailWord_3718702, baseEnd_3718702] using wordTrace_append hprefix tailTrace_3718702
  have hstable : (prefixWord ++ tailWord_3718702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718702).length < 2 ^ (prefixWord ++ tailWord_3718702).sum := by decide
  have hdescent : baseEnd_3718702 < baseStart_3718702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718712 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 1, 3, 2]
def baseStart_3718712 : Nat := 118140960795 + 3718712 * 2 ^ 59
def prefixEnd_3718712 : Nat := 4983230072969 + 3 ^ 40 * 3718712 * 2
def baseEnd_3718712 : Nat := 1909486671642559755897961

theorem tailTrace_3718712 : CollatzResearch.WordTrace tailWord_3718712 prefixEnd_3718712 1909486671642559755897961 := by
  unfold tailWord_3718712
  simp only [CollatzResearch.WordTrace]
  refine ⟨67816284651874502145691195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90421712869166002860921593 67816284651874502145691195)
  ·
    refine ⟨101724426977811753218536793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67816284651874502145691195 101724426977811753218536793)
    ·
      refine ⟨76293320233358814913902595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101724426977811753218536793 76293320233358814913902595)
      ·
        refine ⟨114439980350038222370853893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76293320233358814913902595 114439980350038222370853893)
        ·
          refine ⟨21457496315632166694535105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114439980350038222370853893 21457496315632166694535105)
          ·
            refine ⟨16093122236724125020901329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21457496315632166694535105 16093122236724125020901329)
            ·
              refine ⟨12069841677543093765675997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16093122236724125020901329 12069841677543093765675997)
              ·
                refine ⟨4526190629078660162128499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12069841677543093765675997 4526190629078660162128499)
                ·
                  refine ⟨6789285943617990243192749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4526190629078660162128499 6789285943617990243192749)
                  ·
                    refine ⟨2545982228856746341197281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6789285943617990243192749 2545982228856746341197281)
                    ·
                      refine ⟨1909486671642559755897961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2545982228856746341197281 1909486671642559755897961)
                      ·
                        rfl

theorem cell23_3718712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_3718712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718712 prefixEnd_3718712 := by exact prefixLift 3718712
  have htrace : WordTrace (prefixWord ++ tailWord_3718712) baseStart_3718712 baseEnd_3718712 := by
    simpa [prefixWord, tailWord_3718712, baseEnd_3718712] using wordTrace_append hprefix tailTrace_3718712
  have hstable : (prefixWord ++ tailWord_3718712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718712).length < 2 ^ (prefixWord ++ tailWord_3718712).sum := by decide
  have hdescent : baseEnd_3718712 < baseStart_3718712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718778 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_3718778 : Nat := 118140960795 + 3718778 * 2 ^ 59
def prefixEnd_3718778 : Nat := 4983230072969 + 3 ^ 40 * 3718778 * 2
def baseEnd_3718778 : Nat := 636506853788585499224219

theorem tailTrace_3718778 : CollatzResearch.WordTrace tailWord_3718778 prefixEnd_3718778 636506853788585499224219 := by
  unfold tailWord_3718778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33908744130377474390821247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90423317681006598375523325 33908744130377474390821247)
  ·
    refine ⟨50863116195566211586231871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33908744130377474390821247 50863116195566211586231871)
    ·
      refine ⟨76294674293349317379347807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50863116195566211586231871 76294674293349317379347807)
      ·
        refine ⟨114442011440023976069021711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76294674293349317379347807 114442011440023976069021711)
        ·
          refine ⟨171663017160035964103532567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114442011440023976069021711 171663017160035964103532567)
          ·
            refine ⟨257494525740053946155298851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171663017160035964103532567 257494525740053946155298851)
            ·
              refine ⟨386241788610080919232948277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257494525740053946155298851 386241788610080919232948277)
              ·
                refine ⟨36210167682195086178088901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 386241788610080919232948277 36210167682195086178088901)
                ·
                  refine ⟨6789406440411578658391669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36210167682195086178088901 6789406440411578658391669)
                  ·
                    refine ⟨636506853788585499224219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6789406440411578658391669 636506853788585499224219)
                    ·
                      rfl

theorem cell23_3718778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_3718778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718778 prefixEnd_3718778 := by exact prefixLift 3718778
  have htrace : WordTrace (prefixWord ++ tailWord_3718778) baseStart_3718778 baseEnd_3718778 := by
    simpa [prefixWord, tailWord_3718778, baseEnd_3718778] using wordTrace_append hprefix tailTrace_3718778
  have hstable : (prefixWord ++ tailWord_3718778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718778).length < 2 ^ (prefixWord ++ tailWord_3718778).sum := by decide
  have hdescent : baseEnd_3718778 < baseStart_3718778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718828 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_3718828 : Nat := 118140960795 + 3718828 * 2 ^ 59
def prefixEnd_3718828 : Nat := 4983230072969 + 3 ^ 40 * 3718828 * 2
def baseEnd_3718828 : Nat := 1909546235398481302047427

theorem tailTrace_3718828 : CollatzResearch.WordTrace tailWord_3718828 prefixEnd_3718828 1909546235398481302047427 := by
  unfold tailWord_3718828
  simp only [CollatzResearch.WordTrace]
  refine ⟨67818400085664378051302569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90424533447552504068403425 67818400085664378051302569)
  ·
    refine ⟨50863800064248283538476927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67818400085664378051302569 50863800064248283538476927)
    ·
      refine ⟨76295700096372425307715391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50863800064248283538476927 76295700096372425307715391)
      ·
        refine ⟨114443550144558637961573087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76295700096372425307715391 114443550144558637961573087)
        ·
          refine ⟨171665325216837956942359631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114443550144558637961573087 171665325216837956942359631)
          ·
            refine ⟨257497987825256935413539447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171665325216837956942359631 257497987825256935413539447)
            ·
              refine ⟨386246981737885403120309171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257497987825256935413539447 386246981737885403120309171)
              ·
                refine ⟨579370472606828104680463757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386246981737885403120309171 579370472606828104680463757)
                ·
                  refine ⟨217263927227560539255173909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579370472606828104680463757 217263927227560539255173909)
                  ·
                    refine ⟨10184246588791900277586277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 217263927227560539255173909 10184246588791900277586277)
                    ·
                      refine ⟨1909546235398481302047427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10184246588791900277586277 1909546235398481302047427)
                      ·
                        rfl

theorem cell23_3718828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_3718828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718828 prefixEnd_3718828 := by exact prefixLift 3718828
  have htrace : WordTrace (prefixWord ++ tailWord_3718828) baseStart_3718828 baseEnd_3718828 := by
    simpa [prefixWord, tailWord_3718828, baseEnd_3718828] using wordTrace_append hprefix tailTrace_3718828
  have hstable : (prefixWord ++ tailWord_3718828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718828).length < 2 ^ (prefixWord ++ tailWord_3718828).sum := by decide
  have hdescent : baseEnd_3718828 < baseStart_3718828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718835 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 3]
def baseStart_3718835 : Nat := 118140960795 + 3718835 * 2 ^ 59
def prefixEnd_3718835 : Nat := 4983230072969 + 3 ^ 40 * 3718835 * 2
def baseEnd_3718835 : Nat := 1909549829763062774659895

theorem tailTrace_3718835 : CollatzResearch.WordTrace tailWord_3718835 prefixEnd_3718835 1909549829763062774659895 := by
  unfold tailWord_3718835
  simp only [CollatzResearch.WordTrace]
  refine ⟨135637055482303396298109959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90424703654868930865406639 135637055482303396298109959)
  ·
    refine ⟨203455583223455094447164939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135637055482303396298109959 203455583223455094447164939)
    ·
      refine ⟨305183374835182641670747409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203455583223455094447164939 305183374835182641670747409)
      ·
        refine ⟨228887531126386981253060557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305183374835182641670747409 228887531126386981253060557)
        ·
          refine ⟨85832824172395117969897709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228887531126386981253060557 85832824172395117969897709)
          ·
            refine ⟨32187309064648169238711641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85832824172395117969897709 32187309064648169238711641)
            ·
              refine ⟨24140481798486126929033731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32187309064648169238711641 24140481798486126929033731)
              ·
                refine ⟨36210722697729190393550597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24140481798486126929033731 36210722697729190393550597)
                ·
                  refine ⟨6789510505824223198790737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36210722697729190393550597 6789510505824223198790737)
                  ·
                    refine ⟨5092132879368167399093053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6789510505824223198790737 5092132879368167399093053)
                    ·
                      refine ⟨1909549829763062774659895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5092132879368167399093053 1909549829763062774659895)
                      ·
                        rfl

theorem cell23_3718835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_3718835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718835 prefixEnd_3718835 := by exact prefixLift 3718835
  have htrace : WordTrace (prefixWord ++ tailWord_3718835) baseStart_3718835 baseEnd_3718835 := by
    simpa [prefixWord, tailWord_3718835, baseEnd_3718835] using wordTrace_append hprefix tailTrace_3718835
  have hstable : (prefixWord ++ tailWord_3718835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718835).length < 2 ^ (prefixWord ++ tailWord_3718835).sum := by decide
  have hdescent : baseEnd_3718835 < baseStart_3718835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718842 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_3718842 : Nat := 118140960795 + 3718842 * 2 ^ 59
def prefixEnd_3718842 : Nat := 4983230072969 + 3 ^ 40 * 3718842 * 2
def baseEnd_3718842 : Nat := 636517808042548082424121

theorem tailTrace_3718842 : CollatzResearch.WordTrace tailWord_3718842 prefixEnd_3718842 636517808042548082424121 := by
  unfold tailWord_3718842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33909327698319509123403695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90424873862185357662409853 33909327698319509123403695)
  ·
    refine ⟨50863991547479263685105543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33909327698319509123403695 50863991547479263685105543)
    ·
      refine ⟨76295987321218895527658315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50863991547479263685105543 76295987321218895527658315)
      ·
        refine ⟨114443980981828343291487473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76295987321218895527658315 114443980981828343291487473)
        ·
          refine ⟨85832985736371257468615605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114443980981828343291487473 85832985736371257468615605)
          ·
            refine ⟨8046842412784805387682713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85832985736371257468615605 8046842412784805387682713)
            ·
              refine ⟨6035131809588604040762035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8046842412784805387682713 6035131809588604040762035)
              ·
                refine ⟨9052697714382906061143053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035131809588604040762035 9052697714382906061143053)
                ·
                  refine ⟨3394761642893589772928645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9052697714382906061143053 3394761642893589772928645)
                  ·
                    refine ⟨636517808042548082424121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3394761642893589772928645 636517808042548082424121)
                    ·
                      rfl

theorem cell23_3718842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_3718842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718842 prefixEnd_3718842 := by exact prefixLift 3718842
  have htrace : WordTrace (prefixWord ++ tailWord_3718842) baseStart_3718842 baseEnd_3718842 := by
    simpa [prefixWord, tailWord_3718842, baseEnd_3718842] using wordTrace_append hprefix tailTrace_3718842
  have hstable : (prefixWord ++ tailWord_3718842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718842).length < 2 ^ (prefixWord ++ tailWord_3718842).sum := by decide
  have hdescent : baseEnd_3718842 < baseStart_3718842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718892 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 4, 3, 2]
def baseStart_3718892 : Nat := 118140960795 + 3718892 * 2 ^ 59
def prefixEnd_3718892 : Nat := 4983230072969 + 3 ^ 40 * 3718892 * 2
def baseEnd_3718892 : Nat := 1909579098160369051647133

theorem tailTrace_3718892 : CollatzResearch.WordTrace tailWord_3718892 prefixEnd_3718892 1909579098160369051647133 := by
  unfold tailWord_3718892
  simp only [CollatzResearch.WordTrace]
  refine ⟨67819567221548447516467465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90426089628731263355289953 67819567221548447516467465)
  ·
    refine ⟨50864675416161335637350599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67819567221548447516467465 50864675416161335637350599)
    ·
      refine ⟨76297013124242003456025899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50864675416161335637350599 76297013124242003456025899)
      ·
        refine ⟨114445519686363005184038849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76297013124242003456025899 114445519686363005184038849)
        ·
          refine ⟨85834139764772253888029137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114445519686363005184038849 85834139764772253888029137)
          ·
            refine ⟨64375604823579190416021853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85834139764772253888029137 64375604823579190416021853)
            ·
              refine ⟨24140851808842196406008195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64375604823579190416021853 24140851808842196406008195)
              ·
                refine ⟨36211277713263294609012293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24140851808842196406008195 36211277713263294609012293)
                ·
                  refine ⟨6789614571236867739189805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36211277713263294609012293 6789614571236867739189805)
                  ·
                    refine ⟨2546105464213825402196177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6789614571236867739189805 2546105464213825402196177)
                    ·
                      refine ⟨1909579098160369051647133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546105464213825402196177 1909579098160369051647133)
                      ·
                        rfl

theorem cell23_3718892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_3718892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718892 prefixEnd_3718892 := by exact prefixLift 3718892
  have htrace : WordTrace (prefixWord ++ tailWord_3718892) baseStart_3718892 baseEnd_3718892 := by
    simpa [prefixWord, tailWord_3718892, baseEnd_3718892] using wordTrace_append hprefix tailTrace_3718892
  have hstable : (prefixWord ++ tailWord_3718892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718892).length < 2 ^ (prefixWord ++ tailWord_3718892).sum := by decide
  have hdescent : baseEnd_3718892 < baseStart_3718892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718899 : List Nat := [1, 1, 1, 2, 2, 3, 2, 6, 1, 1, 3]
def baseStart_3718899 : Nat := 118140960795 + 3718899 * 2 ^ 59
def prefixEnd_3718899 : Nat := 4983230072969 + 3 ^ 40 * 3718899 * 2
def baseEnd_3718899 : Nat := 1909582692524950524259601

theorem tailTrace_3718899 : CollatzResearch.WordTrace tailWord_3718899 prefixEnd_3718899 1909582692524950524259601 := by
  unfold tailWord_3718899
  simp only [CollatzResearch.WordTrace]
  refine ⟨135639389754071535228439751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90426259836047690152293167 135639389754071535228439751)
  ·
    refine ⟨203459084631107302842659627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135639389754071535228439751 203459084631107302842659627)
    ·
      refine ⟨305188626946660954263989441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203459084631107302842659627 305188626946660954263989441)
      ·
        refine ⟨228891470209995715697992081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305188626946660954263989441 228891470209995715697992081)
        ·
          refine ⟨171668602657496786773494061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228891470209995715697992081 171668602657496786773494061)
          ·
            refine ⟨64375725996561295040060273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171668602657496786773494061 64375725996561295040060273)
            ·
              refine ⟨48281794497420971280045205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64375725996561295040060273 48281794497420971280045205)
              ·
                refine ⟨2263209117066608028752119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48281794497420971280045205 2263209117066608028752119)
                ·
                  refine ⟨3394813675599912043128179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263209117066608028752119 3394813675599912043128179)
                  ·
                    refine ⟨5092220513399868064692269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3394813675599912043128179 5092220513399868064692269)
                    ·
                      refine ⟨1909582692524950524259601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5092220513399868064692269 1909582692524950524259601)
                      ·
                        rfl

theorem cell23_3718899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 1, 3].length) (baseStart_3718899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718899 prefixEnd_3718899 := by exact prefixLift 3718899
  have htrace : WordTrace (prefixWord ++ tailWord_3718899) baseStart_3718899 baseEnd_3718899 := by
    simpa [prefixWord, tailWord_3718899, baseEnd_3718899] using wordTrace_append hprefix tailTrace_3718899
  have hstable : (prefixWord ++ tailWord_3718899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718899).length < 2 ^ (prefixWord ++ tailWord_3718899).sum := by decide
  have hdescent : baseEnd_3718899 < baseStart_3718899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718922 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3718922 : Nat := 118140960795 + 3718922 * 2 ^ 59
def prefixEnd_3718922 : Nat := 4983230072969 + 3 ^ 40 * 3718922 * 2
def baseEnd_3718922 : Nat := 1909594502580003934271995

theorem tailTrace_3718922 : CollatzResearch.WordTrace tailWord_3718922 prefixEnd_3718922 1909594502580003934271995 := by
  unfold tailWord_3718922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33910057158247052539131755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90426819088658806771018013 33910057158247052539131755)
  ·
    refine ⟨50865085737370578808697633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33910057158247052539131755 50865085737370578808697633)
    ·
      refine ⟨38148814303027934106523225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50865085737370578808697633 38148814303027934106523225)
      ·
        refine ⟨28611610727270950579892419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38148814303027934106523225 28611610727270950579892419)
        ·
          refine ⟨42917416090906425869838629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28611610727270950579892419 42917416090906425869838629)
          ·
            refine ⟨8047015517044954850594743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42917416090906425869838629 8047015517044954850594743)
            ·
              refine ⟨12070523275567432275892115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8047015517044954850594743 12070523275567432275892115)
              ·
                refine ⟨18105784913351148413838173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12070523275567432275892115 18105784913351148413838173)
                ·
                  refine ⟨6789669342506680655189315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18105784913351148413838173 6789669342506680655189315)
                  ·
                    refine ⟨10184504013760020982783973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6789669342506680655189315 10184504013760020982783973)
                    ·
                      refine ⟨1909594502580003934271995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10184504013760020982783973 1909594502580003934271995)
                      ·
                        rfl

theorem cell23_3718922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3718922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718922 prefixEnd_3718922 := by exact prefixLift 3718922
  have htrace : WordTrace (prefixWord ++ tailWord_3718922) baseStart_3718922 baseEnd_3718922 := by
    simpa [prefixWord, tailWord_3718922, baseEnd_3718922] using wordTrace_append hprefix tailTrace_3718922
  have hstable : (prefixWord ++ tailWord_3718922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718922).length < 2 ^ (prefixWord ++ tailWord_3718922).sum := by decide
  have hdescent : baseEnd_3718922 < baseStart_3718922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718949 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_3718949 : Nat := 118140960795 + 3718949 * 2 ^ 59
def prefixEnd_3718949 : Nat := 4983230072969 + 3 ^ 40 * 3718949 * 2
def baseEnd_3718949 : Nat := 636536122185891776211457

theorem tailTrace_3718949 : CollatzResearch.WordTrace tailWord_3718949 prefixEnd_3718949 636536122185891776211457 := by
  unfold tailWord_3718949
  simp only [CollatzResearch.WordTrace]
  refine ⟨135641213403890393767759901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90427475602593595845173267 135641213403890393767759901)
  ·
    refine ⟨50865455026458897662909963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135641213403890393767759901 50865455026458897662909963)
    ·
      refine ⟨76298182539688346494364945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50865455026458897662909963 76298182539688346494364945)
      ·
        refine ⟨57223636904766259870773709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76298182539688346494364945 57223636904766259870773709)
        ·
          refine ⟨21458863839287347451540141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57223636904766259870773709 21458863839287347451540141)
          ·
            refine ⟨8047073939732755294327553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21458863839287347451540141 8047073939732755294327553)
            ·
              refine ⟨6035305454799566470745665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8047073939732755294327553 6035305454799566470745665)
              ·
                refine ⟨4526479091099674853059249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6035305454799566470745665 4526479091099674853059249)
                ·
                  refine ⟨3394859318324756139794437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4526479091099674853059249 3394859318324756139794437)
                  ·
                    refine ⟨636536122185891776211457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3394859318324756139794437 636536122185891776211457)
                    ·
                      rfl

theorem cell23_3718949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_3718949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718949 prefixEnd_3718949 := by exact prefixLift 3718949
  have htrace : WordTrace (prefixWord ++ tailWord_3718949) baseStart_3718949 baseEnd_3718949 := by
    simpa [prefixWord, tailWord_3718949, baseEnd_3718949] using wordTrace_append hprefix tailTrace_3718949
  have hstable : (prefixWord ++ tailWord_3718949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718949).length < 2 ^ (prefixWord ++ tailWord_3718949).sum := by decide
  have hdescent : baseEnd_3718949 < baseStart_3718949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718962 : List Nat := [3, 2, 1, 1, 3, 4, 1, 8]
def baseStart_3718962 : Nat := 118140960795 + 3718962 * 2 ^ 59
def prefixEnd_3718962 : Nat := 4983230072969 + 3 ^ 40 * 3718962 * 2
def baseEnd_3718962 : Nat := 70726483029858658435993

theorem tailTrace_3718962 : CollatzResearch.WordTrace tailWord_3718962 prefixEnd_3718962 70726483029858658435993 := by
  unfold tailWord_3718962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33910421888210824246995785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90427791701895531325322093 33910421888210824246995785)
  ·
    refine ⟨25432816416158118185246839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33910421888210824246995785 25432816416158118185246839)
    ·
      refine ⟨38149224624237177277870259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25432816416158118185246839 38149224624237177277870259)
      ·
        refine ⟨57223836936355765916805389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38149224624237177277870259 57223836936355765916805389)
        ·
          refine ⟨21458938851133412218802021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57223836936355765916805389 21458938851133412218802021)
          ·
            refine ⟨4023551034587514791025379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21458938851133412218802021 4023551034587514791025379)
            ·
              refine ⟨6035326551881272186538069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023551034587514791025379 6035326551881272186538069)
              ·
                refine ⟨70726483029858658435993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6035326551881272186538069 70726483029858658435993)
                ·
                  rfl

theorem cell23_3718962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 8].length) (baseStart_3718962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718962 prefixEnd_3718962 := by exact prefixLift 3718962
  have htrace : WordTrace (prefixWord ++ tailWord_3718962) baseStart_3718962 baseEnd_3718962 := by
    simpa [prefixWord, tailWord_3718962, baseEnd_3718962] using wordTrace_append hprefix tailTrace_3718962
  have hstable : (prefixWord ++ tailWord_3718962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718962).length < 2 ^ (prefixWord ++ tailWord_3718962).sum := by decide
  have hdescent : baseEnd_3718962 < baseStart_3718962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718966 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3718966 : Nat := 118140960795 + 3718966 * 2 ^ 59
def prefixEnd_3718966 : Nat := 4983230072969 + 3 ^ 40 * 3718966 * 2
def baseEnd_3718966 : Nat := 636539031909600587373931

theorem tailTrace_3718966 : CollatzResearch.WordTrace tailWord_3718966 prefixEnd_3718966 636539031909600587373931 := by
  unfold tailWord_3718966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8477614590301800354445547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90427888963219203780752501 8477614590301800354445547)
  ·
    refine ⟨12716421885452700531668321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8477614590301800354445547 12716421885452700531668321)
    ·
      refine ⟨9537316414089525398751241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12716421885452700531668321 9537316414089525398751241)
      ·
        refine ⟨7152987310567144049063431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9537316414089525398751241 7152987310567144049063431)
        ·
          refine ⟨10729480965850716073595147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7152987310567144049063431 10729480965850716073595147)
          ·
            refine ⟨16094221448776074110392721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10729480965850716073595147 16094221448776074110392721)
            ·
              refine ⟨12070666086582055582794541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16094221448776074110392721 12070666086582055582794541)
              ·
                refine ⟨4526499782468270843547953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12070666086582055582794541 4526499782468270843547953)
                ·
                  refine ⟨3394874836851203132660965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4526499782468270843547953 3394874836851203132660965)
                  ·
                    refine ⟨636539031909600587373931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3394874836851203132660965 636539031909600587373931)
                    ·
                      rfl

theorem cell23_3718966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3718966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718966 prefixEnd_3718966 := by exact prefixLift 3718966
  have htrace : WordTrace (prefixWord ++ tailWord_3718966) baseStart_3718966 baseEnd_3718966 := by
    simpa [prefixWord, tailWord_3718966, baseEnd_3718966] using wordTrace_append hprefix tailTrace_3718966
  have hstable : (prefixWord ++ tailWord_3718966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718966).length < 2 ^ (prefixWord ++ tailWord_3718966).sum := by decide
  have hdescent : baseEnd_3718966 < baseStart_3718966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718972 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3718972 : Nat := 118140960795 + 3718972 * 2 ^ 59
def prefixEnd_3718972 : Nat := 4983230072969 + 3 ^ 40 * 3718972 * 2
def baseEnd_3718972 : Nat := 1909620176612728738646765

theorem tailTrace_3718972 : CollatzResearch.WordTrace tailWord_3718972 prefixEnd_3718972 1909620176612728738646765 := by
  unfold tailWord_3718972
  simp only [CollatzResearch.WordTrace]
  refine ⟨67821026141403534347923585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90428034855204712463898113 67821026141403534347923585)
  ·
    refine ⟨50865769606052650760942689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67821026141403534347923585 50865769606052650760942689)
    ·
      refine ⟨38149327204539488070707017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50865769606052650760942689 38149327204539488070707017)
      ·
        refine ⟨28611995403404616053030263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38149327204539488070707017 28611995403404616053030263)
        ·
          refine ⟨42917993105106924079545395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28611995403404616053030263 42917993105106924079545395)
          ·
            refine ⟨64376989657660386119318093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42917993105106924079545395 64376989657660386119318093)
            ·
              refine ⟨24141371121622644794744285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64376989657660386119318093 24141371121622644794744285)
              ·
                refine ⟨9053014170608491798029107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24141371121622644794744285 9053014170608491798029107)
                ·
                  refine ⟨13579521255912737697043661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9053014170608491798029107 13579521255912737697043661)
                  ·
                    refine ⟨5092320470967276636391373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13579521255912737697043661 5092320470967276636391373)
                    ·
                      refine ⟨1909620176612728738646765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5092320470967276636391373 1909620176612728738646765)
                      ·
                        rfl

theorem cell23_3718972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3718972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718972 prefixEnd_3718972 := by exact prefixLift 3718972
  have htrace : WordTrace (prefixWord ++ tailWord_3718972) baseStart_3718972 baseEnd_3718972 := by
    simpa [prefixWord, tailWord_3718972, baseEnd_3718972] using wordTrace_append hprefix tailTrace_3718972
  have hstable : (prefixWord ++ tailWord_3718972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718972).length < 2 ^ (prefixWord ++ tailWord_3718972).sum := by decide
  have hdescent : baseEnd_3718972 < baseStart_3718972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3718985 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_3718985 : Nat := 118140960795 + 3718985 * 2 ^ 59
def prefixEnd_3718985 : Nat := 4983230072969 + 3 ^ 40 * 3718985 * 2
def baseEnd_3718985 : Nat := 1909626851861237187784205

theorem tailTrace_3718985 : CollatzResearch.WordTrace tailWord_3718985 prefixEnd_3718985 1909626851861237187784205 := by
  unfold tailWord_3718985
  simp only [CollatzResearch.WordTrace]
  refine ⟨135642526431759971916070409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90428350954506647944046939 135642526431759971916070409)
  ·
    refine ⟨101731894823819978937052807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135642526431759971916070409 101731894823819978937052807)
    ·
      refine ⟨152597842235729968405579211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101731894823819978937052807 152597842235729968405579211)
      ·
        refine ⟨228896763353594952608368817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152597842235729968405579211 228896763353594952608368817)
        ·
          refine ⟨171672572515196214456276613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228896763353594952608368817 171672572515196214456276613)
          ·
            refine ⟨32188607346599290210551865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171672572515196214456276613 32188607346599290210551865)
            ·
              refine ⟨24141455509949467657913899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32188607346599290210551865 24141455509949467657913899)
              ·
                refine ⟨36212183264924201486870849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24141455509949467657913899 36212183264924201486870849)
                ·
                  refine ⟨27159137448693151115153137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36212183264924201486870849 27159137448693151115153137)
                  ·
                    refine ⟨20369353086519863336364853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27159137448693151115153137 20369353086519863336364853)
                    ·
                      refine ⟨1909626851861237187784205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20369353086519863336364853 1909626851861237187784205)
                      ·
                        rfl

theorem cell23_3718985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_3718985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3718985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3718985 prefixEnd_3718985 := by exact prefixLift 3718985
  have htrace : WordTrace (prefixWord ++ tailWord_3718985) baseStart_3718985 baseEnd_3718985 := by
    simpa [prefixWord, tailWord_3718985, baseEnd_3718985] using wordTrace_append hprefix tailTrace_3718985
  have hstable : (prefixWord ++ tailWord_3718985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3718985).length < 2 ^ (prefixWord ++ tailWord_3718985).sum := by decide
  have hdescent : baseEnd_3718985 < baseStart_3718985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3718985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719069 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 7]
def baseStart_3719069 : Nat := 118140960795 + 3719069 * 2 ^ 59
def prefixEnd_3719069 : Nat := 4983230072969 + 3 ^ 40 * 3719069 * 2
def baseEnd_3719069 : Nat := 212185553804023873237091

theorem tailTrace_3719069 : CollatzResearch.WordTrace tailWord_3719069 prefixEnd_3719069 212185553804023873237091 := by
  unfold tailWord_3719069
  simp only [CollatzResearch.WordTrace]
  refine ⟨135645590163455654262128261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90430393442303769508085507 135645590163455654262128261)
  ·
    refine ⟨25433548155647935174149049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135645590163455654262128261 25433548155647935174149049)
    ·
      refine ⟨19075161116735951380611787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25433548155647935174149049 19075161116735951380611787)
      ·
        refine ⟨28612741675103927070917681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19075161116735951380611787 28612741675103927070917681)
        ·
          refine ⟨21459556256327945303188261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28612741675103927070917681 21459556256327945303188261)
          ·
            refine ⟨4023666798061489744347799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21459556256327945303188261 4023666798061489744347799)
            ·
              refine ⟨6035500197092234616521699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023666798061489744347799 6035500197092234616521699)
              ·
                refine ⟨9053250295638351924782549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035500197092234616521699 9053250295638351924782549)
                ·
                  refine ⟨212185553804023873237091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9053250295638351924782549 212185553804023873237091)
                  ·
                    rfl

theorem cell23_3719069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_3719069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719069 prefixEnd_3719069 := by exact prefixLift 3719069
  have htrace : WordTrace (prefixWord ++ tailWord_3719069) baseStart_3719069 baseEnd_3719069 := by
    simpa [prefixWord, tailWord_3719069, baseEnd_3719069] using wordTrace_append hprefix tailTrace_3719069
  have hstable : (prefixWord ++ tailWord_3719069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719069).length < 2 ^ (prefixWord ++ tailWord_3719069).sum := by decide
  have hdescent : baseEnd_3719069 < baseStart_3719069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719119 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 2, 4, 2]
def baseStart_3719119 : Nat := 118140960795 + 3719119 * 2 ^ 59
def prefixEnd_3719119 : Nat := 4983230072969 + 3 ^ 40 * 3719119 * 2
def baseEnd_3719119 : Nat := 1909695658268939663508589

theorem tailTrace_3719119 : CollatzResearch.WordTrace tailWord_3719119 prefixEnd_3719119 1909695658268939663508589 := by
  unfold tailWord_3719119
  simp only [CollatzResearch.WordTrace]
  refine ⟨135647413813274512801448411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90431609208849675200965607 135647413813274512801448411)
  ·
    refine ⟨203471120719911769202172617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135647413813274512801448411 203471120719911769202172617)
    ·
      refine ⟨152603340539933826901629463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203471120719911769202172617 152603340539933826901629463)
      ·
        refine ⟨228905010809900740352444195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152603340539933826901629463 228905010809900740352444195)
        ·
          refine ⟨343357516214851110528666293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228905010809900740352444195 343357516214851110528666293)
          ·
            refine ⟨32189767145142291612062465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343357516214851110528666293 32189767145142291612062465)
            ·
              refine ⟨24142325358856718709046849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32189767145142291612062465 24142325358856718709046849)
              ·
                refine ⟨18106744019142539031785137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24142325358856718709046849 18106744019142539031785137)
                ·
                  refine ⟨13580058014356904273838853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18106744019142539031785137 13580058014356904273838853)
                  ·
                    refine ⟨2546260877691919551344785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13580058014356904273838853 2546260877691919551344785)
                    ·
                      refine ⟨1909695658268939663508589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546260877691919551344785 1909695658268939663508589)
                      ·
                        rfl

theorem cell23_3719119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4, 2].length) (baseStart_3719119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719119 prefixEnd_3719119 := by exact prefixLift 3719119
  have htrace : WordTrace (prefixWord ++ tailWord_3719119) baseStart_3719119 baseEnd_3719119 := by
    simpa [prefixWord, tailWord_3719119, baseEnd_3719119] using wordTrace_append hprefix tailTrace_3719119
  have hstable : (prefixWord ++ tailWord_3719119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719119).length < 2 ^ (prefixWord ++ tailWord_3719119).sum := by decide
  have hdescent : baseEnd_3719119 < baseStart_3719119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719153 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 2, 1, 4]
def baseStart_3719153 : Nat := 118140960795 + 3719153 * 2 ^ 59
def prefixEnd_3719153 : Nat := 4983230072969 + 3 ^ 40 * 3719153 * 2
def baseEnd_3719153 : Nat := 1909713116611192530483433

theorem tailTrace_3719153 : CollatzResearch.WordTrace tailWord_3719153 prefixEnd_3719153 1909713116611192530483433 := by
  unfold tailWord_3719153
  simp only [CollatzResearch.WordTrace]
  refine ⟨135648653895151336608186113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90432435930100891072124075 135648653895151336608186113)
  ·
    refine ⟨101736490421363502456139585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135648653895151336608186113 101736490421363502456139585)
    ·
      refine ⟨76302367816022626842104689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101736490421363502456139585 76302367816022626842104689)
      ·
        refine ⟨57226775862016970131578517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76302367816022626842104689 57226775862016970131578517)
        ·
          refine ⟨2682505118532045474917743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57226775862016970131578517 2682505118532045474917743)
          ·
            refine ⟨4023757677798068212376615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682505118532045474917743 4023757677798068212376615)
            ·
              refine ⟨6035636516697102318564923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4023757677798068212376615 6035636516697102318564923)
              ·
                refine ⟨9053454775045653477847385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6035636516697102318564923 9053454775045653477847385)
                ·
                  refine ⟨6790091081284240108385539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9053454775045653477847385 6790091081284240108385539)
                  ·
                    refine ⟨10185136621926360162578309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6790091081284240108385539 10185136621926360162578309)
                    ·
                      refine ⟨1909713116611192530483433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10185136621926360162578309 1909713116611192530483433)
                      ·
                        rfl

theorem cell23_3719153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_3719153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719153 prefixEnd_3719153 := by exact prefixLift 3719153
  have htrace : WordTrace (prefixWord ++ tailWord_3719153) baseStart_3719153 baseEnd_3719153 := by
    simpa [prefixWord, tailWord_3719153, baseEnd_3719153] using wordTrace_append hprefix tailTrace_3719153
  have hstable : (prefixWord ++ tailWord_3719153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719153).length < 2 ^ (prefixWord ++ tailWord_3719153).sum := by decide
  have hdescent : baseEnd_3719153 < baseStart_3719153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719196 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_3719196 : Nat := 118140960795 + 3719196 * 2 ^ 59
def prefixEnd_3719196 : Nat := 4983230072969 + 3 ^ 40 * 3719196 * 2
def baseEnd_3719196 : Nat := 1909735196279335862245735

theorem tailTrace_3719196 : CollatzResearch.WordTrace tailWord_3719196 prefixEnd_3719196 1909735196279335862245735 := by
  unfold tailWord_3719196
  simp only [CollatzResearch.WordTrace]
  refine ⟨67825111116997777476000721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90433481489330369968000961 67825111116997777476000721)
  ·
    refine ⟨50868833337748333107000541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67825111116997777476000721 50868833337748333107000541)
    ·
      refine ⟨19075812501655624915125203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50868833337748333107000541 19075812501655624915125203)
      ·
        refine ⟨28613718752483437372687805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19075812501655624915125203 28613718752483437372687805)
        ·
          refine ⟨10730144532181289014757927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28613718752483437372687805 10730144532181289014757927)
          ·
            refine ⟨16095216798271933522136891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10730144532181289014757927 16095216798271933522136891)
            ·
              refine ⟨24142825197407900283205337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095216798271933522136891 24142825197407900283205337)
              ·
                refine ⟨18107118898055925212404003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24142825197407900283205337 18107118898055925212404003)
                ·
                  refine ⟨27160678347083887818606005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18107118898055925212404003 27160678347083887818606005)
                  ·
                    refine ⟨2546313595039114482994313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27160678347083887818606005 2546313595039114482994313)
                    ·
                      refine ⟨1909735196279335862245735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546313595039114482994313 1909735196279335862245735)
                      ·
                        rfl

theorem cell23_3719196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_3719196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719196 prefixEnd_3719196 := by exact prefixLift 3719196
  have htrace : WordTrace (prefixWord ++ tailWord_3719196) baseStart_3719196 baseEnd_3719196 := by
    simpa [prefixWord, tailWord_3719196, baseEnd_3719196] using wordTrace_append hprefix tailTrace_3719196
  have hstable : (prefixWord ++ tailWord_3719196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719196).length < 2 ^ (prefixWord ++ tailWord_3719196).sum := by decide
  have hdescent : baseEnd_3719196 < baseStart_3719196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719219 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 4, 4]
def baseStart_3719219 : Nat := 118140960795 + 3719219 * 2 ^ 59
def prefixEnd_3719219 : Nat := 4983230072969 + 3 ^ 40 * 3719219 * 2
def baseEnd_3719219 : Nat := 636582335444796424086043

theorem tailTrace_3719219 : CollatzResearch.WordTrace tailWord_3719219 prefixEnd_3719219 636582335444796424086043 := by
  unfold tailWord_3719219
  simp only [CollatzResearch.WordTrace]
  refine ⟨135651061112912229880088711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90434040741941486586725807 135651061112912229880088711)
  ·
    refine ⟨203476591669368344820133067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135651061112912229880088711 203476591669368344820133067)
    ·
      refine ⟨305214887504052517230199601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203476591669368344820133067 305214887504052517230199601)
      ·
        refine ⟨228911165628039387922649701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305214887504052517230199601 228911165628039387922649701)
        ·
          refine ⟨42920843555257385235496819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228911165628039387922649701 42920843555257385235496819)
          ·
            refine ⟨64381265332886077853245229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42920843555257385235496819 64381265332886077853245229)
            ·
              refine ⟨24142974499832279194966961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64381265332886077853245229 24142974499832279194966961)
              ·
                refine ⟨18107230874874209396225221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24142974499832279194966961 18107230874874209396225221)
                ·
                  refine ⟨3395105789038914261792229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18107230874874209396225221 3395105789038914261792229)
                  ·
                    refine ⟨636582335444796424086043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395105789038914261792229 636582335444796424086043)
                    ·
                      rfl

theorem cell23_3719219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 4].length) (baseStart_3719219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719219 prefixEnd_3719219 := by exact prefixLift 3719219
  have htrace : WordTrace (prefixWord ++ tailWord_3719219) baseStart_3719219 baseEnd_3719219 := by
    simpa [prefixWord, tailWord_3719219, baseEnd_3719219] using wordTrace_append hprefix tailTrace_3719219
  have hstable : (prefixWord ++ tailWord_3719219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719219).length < 2 ^ (prefixWord ++ tailWord_3719219).sum := by decide
  have hdescent : baseEnd_3719219 < baseStart_3719219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719230 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_3719230 : Nat := 118140960795 + 3719230 * 2 ^ 59
def prefixEnd_3719230 : Nat := 4983230072969 + 3 ^ 40 * 3719230 * 2
def baseEnd_3719230 : Nat := 1909752654621588729220579

theorem tailTrace_3719230 : CollatzResearch.WordTrace tailWord_3719230 prefixEnd_3719230 1909752654621588729220579 := by
  unfold tailWord_3719230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16956432789484047344842393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90434308210581585839159429 16956432789484047344842393)
  ·
    refine ⟨12717324592113035508631795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16956432789484047344842393 12717324592113035508631795)
    ·
      refine ⟨19075986888169553262947693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12717324592113035508631795 19075986888169553262947693)
      ·
        refine ⟨7153495083063582473605385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19075986888169553262947693 7153495083063582473605385)
        ·
          refine ⟨5365121312297686855204039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7153495083063582473605385 5365121312297686855204039)
          ·
            refine ⟨8047681968446530282806059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5365121312297686855204039 8047681968446530282806059)
            ·
              refine ⟨12071522952669795424209089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8047681968446530282806059 12071522952669795424209089)
              ·
                refine ⟨9053642214502346568156817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12071522952669795424209089 9053642214502346568156817)
                ·
                  refine ⟨6790231660876759926117613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9053642214502346568156817 6790231660876759926117613)
                  ·
                    refine ⟨2546336872828784972294105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6790231660876759926117613 2546336872828784972294105)
                    ·
                      refine ⟨1909752654621588729220579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546336872828784972294105 1909752654621588729220579)
                      ·
                        rfl

theorem cell23_3719230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_3719230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719230 prefixEnd_3719230 := by exact prefixLift 3719230
  have htrace : WordTrace (prefixWord ++ tailWord_3719230) baseStart_3719230 baseEnd_3719230 := by
    simpa [prefixWord, tailWord_3719230, baseEnd_3719230] using wordTrace_append hprefix tailTrace_3719230
  have hstable : (prefixWord ++ tailWord_3719230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719230).length < 2 ^ (prefixWord ++ tailWord_3719230).sum := by decide
  have hdescent : baseEnd_3719230 < baseStart_3719230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719232 : List Nat := [2, 1, 1, 2, 2, 4, 11]
def baseStart_3719232 : Nat := 118140960795 + 3719232 * 2 ^ 59
def prefixEnd_3719232 : Nat := 4983230072969 + 3 ^ 40 * 3719232 * 2
def baseEnd_3719232 : Nat := 23577205945467873103649

theorem tailTrace_3719232 : CollatzResearch.WordTrace tailWord_3719232 prefixEnd_3719232 23577205945467873103649 := by
  unfold tailWord_3719232
  simp only [CollatzResearch.WordTrace]
  refine ⟨67825767630932566550155975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90434356841243422066874633 67825767630932566550155975)
  ·
    refine ⟨101738651446398849825233963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67825767630932566550155975 101738651446398849825233963)
    ·
      refine ⟨152607977169598274737850945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101738651446398849825233963 152607977169598274737850945)
      ·
        refine ⟨114455982877198706053388209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152607977169598274737850945 114455982877198706053388209)
        ·
          refine ⟨85841987157899029540041157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114455982877198706053388209 85841987157899029540041157)
          ·
            refine ⟨16095372592106068038757717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85841987157899029540041157 16095372592106068038757717)
            ·
              refine ⟨23577205945467873103649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16095372592106068038757717 23577205945467873103649)
              ·
                rfl

theorem cell23_3719232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 11].length) (baseStart_3719232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719232 prefixEnd_3719232 := by exact prefixLift 3719232
  have htrace : WordTrace (prefixWord ++ tailWord_3719232) baseStart_3719232 baseEnd_3719232 := by
    simpa [prefixWord, tailWord_3719232, baseEnd_3719232] using wordTrace_append hprefix tailTrace_3719232
  have hstable : (prefixWord ++ tailWord_3719232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719232).length < 2 ^ (prefixWord ++ tailWord_3719232).sum := by decide
  have hdescent : baseEnd_3719232 < baseStart_3719232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719253 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_3719253 : Nat := 118140960795 + 3719253 * 2 ^ 59
def prefixEnd_3719253 : Nat := 4983230072969 + 3 ^ 40 * 3719253 * 2
def baseEnd_3719253 : Nat := 636588154892214046410991

theorem tailTrace_3719253 : CollatzResearch.WordTrace tailWord_3719253 prefixEnd_3719253 636588154892214046410991 := by
  unfold tailWord_3719253
  simp only [CollatzResearch.WordTrace]
  refine ⟨135652301194789053686826413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90434867463192702457884275 135652301194789053686826413)
  ·
    refine ⟨50869612948045895132559905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135652301194789053686826413 50869612948045895132559905)
    ·
      refine ⟨38152209711034421349419929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50869612948045895132559905 38152209711034421349419929)
      ·
        refine ⟨28614157283275816012064947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38152209711034421349419929 28614157283275816012064947)
        ·
          refine ⟨42921235924913724018097421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28614157283275816012064947 42921235924913724018097421)
          ·
            refine ⟨16095463471842646506786533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42921235924913724018097421 16095463471842646506786533)
            ·
              refine ⟨3017899400970496220022475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16095463471842646506786533 3017899400970496220022475)
              ·
                refine ⟨4526849101455744330033713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017899400970496220022475 4526849101455744330033713)
                ·
                  refine ⟨3395136826091808247525285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4526849101455744330033713 3395136826091808247525285)
                  ·
                    refine ⟨636588154892214046410991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395136826091808247525285 636588154892214046410991)
                    ·
                      rfl

theorem cell23_3719253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_3719253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719253 prefixEnd_3719253 := by exact prefixLift 3719253
  have htrace : WordTrace (prefixWord ++ tailWord_3719253) baseStart_3719253 baseEnd_3719253 := by
    simpa [prefixWord, tailWord_3719253, baseEnd_3719253] using wordTrace_append hprefix tailTrace_3719253
  have hstable : (prefixWord ++ tailWord_3719253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719253).length < 2 ^ (prefixWord ++ tailWord_3719253).sum := by decide
  have hdescent : baseEnd_3719253 < baseStart_3719253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719276 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_3719276 : Nat := 118140960795 + 3719276 * 2 ^ 59
def prefixEnd_3719276 : Nat := 4983230072969 + 3 ^ 40 * 3719276 * 2
def baseEnd_3719276 : Nat := 1909776274731695549245367

theorem tailTrace_3719276 : CollatzResearch.WordTrace tailWord_3719276 prefixEnd_3719276 1909776274731695549245367 := by
  unfold tailWord_3719276
  simp only [CollatzResearch.WordTrace]
  refine ⟨67826570036852864307456841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90435426715803819076609121 67826570036852864307456841)
  ·
    refine ⟨50869927527639648230592631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67826570036852864307456841 50869927527639648230592631)
    ·
      refine ⟨76304891291459472345888947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50869927527639648230592631 76304891291459472345888947)
      ·
        refine ⟨114457336937189208518833421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76304891291459472345888947 114457336937189208518833421)
        ·
          refine ⟨42921501351445953194562533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114457336937189208518833421 42921501351445953194562533)
          ·
            refine ⟨8047781503396116223980475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42921501351445953194562533 8047781503396116223980475)
            ·
              refine ⟨12071672255094174335970713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8047781503396116223980475 12071672255094174335970713)
              ·
                refine ⟨9053754191320630751978035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12071672255094174335970713 9053754191320630751978035)
                ·
                  refine ⟨13580631286980946127967053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9053754191320630751978035 13580631286980946127967053)
                  ·
                    refine ⟨5092736732617854797987645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13580631286980946127967053 5092736732617854797987645)
                    ·
                      refine ⟨1909776274731695549245367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5092736732617854797987645 1909776274731695549245367)
                      ·
                        rfl

theorem cell23_3719276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_3719276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719276 prefixEnd_3719276 := by exact prefixLift 3719276
  have htrace : WordTrace (prefixWord ++ tailWord_3719276) baseStart_3719276 baseEnd_3719276 := by
    simpa [prefixWord, tailWord_3719276, baseEnd_3719276] using wordTrace_append hprefix tailTrace_3719276
  have hstable : (prefixWord ++ tailWord_3719276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719276).length < 2 ^ (prefixWord ++ tailWord_3719276).sum := by decide
  have hdescent : baseEnd_3719276 < baseStart_3719276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719293 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_3719293 : Nat := 118140960795 + 3719293 * 2 ^ 59
def prefixEnd_3719293 : Nat := 4983230072969 + 3 ^ 40 * 3719293 * 2
def baseEnd_3719293 : Nat := 1909785003902821982732789

theorem tailTrace_3719293 : CollatzResearch.WordTrace tailWord_3719293 prefixEnd_3719293 1909785003902821982732789 := by
  unfold tailWord_3719293
  simp only [CollatzResearch.WordTrace]
  refine ⟨135653760114644140518282533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90435840076429427012188355 135653760114644140518282533)
  ·
    refine ⟨25435080021495776347177975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135653760114644140518282533 25435080021495776347177975)
    ·
      refine ⟨38152620032243664520766963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25435080021495776347177975 38152620032243664520766963)
      ·
        refine ⟨57228930048365496781150445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38152620032243664520766963 57228930048365496781150445)
        ·
          refine ⟨21460848768137061292931417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57228930048365496781150445 21460848768137061292931417)
          ·
            refine ⟨16095636576102795969698563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21460848768137061292931417 16095636576102795969698563)
            ·
              refine ⟨24143454864154193954547845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095636576102795969698563 24143454864154193954547845)
              ·
                refine ⟨4526897787028911366477721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24143454864154193954547845 4526897787028911366477721)
                ·
                  refine ⟨3395173340271683524858291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4526897787028911366477721 3395173340271683524858291)
                  ·
                    refine ⟨5092760010407525287287437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3395173340271683524858291 5092760010407525287287437)
                    ·
                      refine ⟨1909785003902821982732789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5092760010407525287287437 1909785003902821982732789)
                      ·
                        rfl

theorem cell23_3719293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_3719293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719293 prefixEnd_3719293 := by exact prefixLift 3719293
  have htrace : WordTrace (prefixWord ++ tailWord_3719293) baseStart_3719293 baseEnd_3719293 := by
    simpa [prefixWord, tailWord_3719293, baseEnd_3719293] using wordTrace_append hprefix tailTrace_3719293
  have hstable : (prefixWord ++ tailWord_3719293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719293).length < 2 ^ (prefixWord ++ tailWord_3719293).sum := by decide
  have hdescent : baseEnd_3719293 < baseStart_3719293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719299 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4]
def baseStart_3719299 : Nat := 118140960795 + 3719299 * 2 ^ 59
def prefixEnd_3719299 : Nat := 4983230072969 + 3 ^ 40 * 3719299 * 2
def baseEnd_3719299 : Nat := 1909788084786748959257761

theorem tailTrace_3719299 : CollatzResearch.WordTrace tailWord_3719299 prefixEnd_3719299 1909788084786748959257761 := by
  unfold tailWord_3719299
  simp only [CollatzResearch.WordTrace]
  refine ⟨135653978952622403543000951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90435985968414935695333967 135653978952622403543000951)
  ·
    refine ⟨203480968428933605314501427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135653978952622403543000951 203480968428933605314501427)
    ·
      refine ⟨305221452643400407971752141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203480968428933605314501427 305221452643400407971752141)
      ·
        refine ⟨114458044741275152989407053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305221452643400407971752141 114458044741275152989407053)
        ·
          refine ⟨42921766777978182371027645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114458044741275152989407053 42921766777978182371027645)
          ·
            refine ⟨16095662541741818389135367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42921766777978182371027645 16095662541741818389135367)
            ·
              refine ⟨24143493812612727583703051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16095662541741818389135367 24143493812612727583703051)
              ·
                refine ⟨36215240718919091375554577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24143493812612727583703051 36215240718919091375554577)
                ·
                  refine ⟨27161430539189318531665933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36215240718919091375554577 27161430539189318531665933)
                  ·
                    refine ⟨10185536452195994449374725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27161430539189318531665933 10185536452195994449374725)
                    ·
                      refine ⟨1909788084786748959257761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10185536452195994449374725 1909788084786748959257761)
                      ·
                        rfl

theorem cell23_3719299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_3719299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719299 prefixEnd_3719299 := by exact prefixLift 3719299
  have htrace : WordTrace (prefixWord ++ tailWord_3719299) baseStart_3719299 baseEnd_3719299 := by
    simpa [prefixWord, tailWord_3719299, baseEnd_3719299] using wordTrace_append hprefix tailTrace_3719299
  have hstable : (prefixWord ++ tailWord_3719299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719299).length < 2 ^ (prefixWord ++ tailWord_3719299).sum := by decide
  have hdescent : baseEnd_3719299 < baseStart_3719299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719333 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 4, 2, 2]
def baseStart_3719333 : Nat := 118140960795 + 3719333 * 2 ^ 59
def prefixEnd_3719333 : Nat := 4983230072969 + 3 ^ 40 * 3719333 * 2
def baseEnd_3719333 : Nat := 1909805543129001826232605

theorem tailTrace_3719333 : CollatzResearch.WordTrace tailWord_3719333 prefixEnd_3719333 1909805543129001826232605 := by
  unfold tailWord_3719333
  simp only [CollatzResearch.WordTrace]
  refine ⟨135655219034499227349738653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90436812689666151566492435 135655219034499227349738653)
  ·
    refine ⟨50870707137937210256151995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135655219034499227349738653 50870707137937210256151995)
    ·
      refine ⟨76306060706905815384227993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50870707137937210256151995 76306060706905815384227993)
      ·
        refine ⟨57229545530179361538170995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76306060706905815384227993 57229545530179361538170995)
        ·
          refine ⟨85844318295269042307256493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57229545530179361538170995 85844318295269042307256493)
          ·
            refine ⟨32191619360725890865221185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85844318295269042307256493 32191619360725890865221185)
            ·
              refine ⟨24143714520544418148915889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32191619360725890865221185 24143714520544418148915889)
              ·
                refine ⟨18107785890408313611686917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24143714520544418148915889 18107785890408313611686917)
                ·
                  refine ⟨3395209854451558802191297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18107785890408313611686917 3395209854451558802191297)
                  ·
                    refine ⟨2546407390838669101643473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3395209854451558802191297 2546407390838669101643473)
                    ·
                      refine ⟨1909805543129001826232605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546407390838669101643473 1909805543129001826232605)
                      ·
                        rfl

theorem cell23_3719333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_3719333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719333 prefixEnd_3719333 := by exact prefixLift 3719333
  have htrace : WordTrace (prefixWord ++ tailWord_3719333) baseStart_3719333 baseEnd_3719333 := by
    simpa [prefixWord, tailWord_3719333, baseEnd_3719333] using wordTrace_append hprefix tailTrace_3719333
  have hstable : (prefixWord ++ tailWord_3719333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719333).length < 2 ^ (prefixWord ++ tailWord_3719333).sum := by decide
  have hdescent : baseEnd_3719333 < baseStart_3719333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719369 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 6, 5]
def baseStart_3719369 : Nat := 118140960795 + 3719369 * 2 ^ 59
def prefixEnd_3719369 : Nat := 4983230072969 + 3 ^ 40 * 3719369 * 2
def baseEnd_3719369 : Nat := 636608009477521228460813

theorem tailTrace_3719369 : CollatzResearch.WordTrace tailWord_3719369 prefixEnd_3719369 636608009477521228460813 := by
  unfold tailWord_3719369
  simp only [CollatzResearch.WordTrace]
  refine ⟨135656532062368805498049161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90437688041579203665366107 135656532062368805498049161)
  ·
    refine ⟨101742399046776604123536871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135656532062368805498049161 101742399046776604123536871)
    ·
      refine ⟨152613598570164906185305307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101742399046776604123536871 152613598570164906185305307)
      ·
        refine ⟨228920397855247359277957961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152613598570164906185305307 228920397855247359277957961)
        ·
          refine ⟨171690298391435519458468471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228920397855247359277957961 171690298391435519458468471)
          ·
            refine ⟨257535447587153279187702707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171690298391435519458468471 257535447587153279187702707)
            ·
              refine ⟨386303171380729918781554061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257535447587153279187702707 386303171380729918781554061)
              ·
                refine ⟨144863689267773719543082773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386303171380729918781554061 144863689267773719543082773)
                ·
                  refine ⟨6790485434426893103582005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144863689267773719543082773 6790485434426893103582005)
                  ·
                    refine ⟨636608009477521228460813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6790485434426893103582005 636608009477521228460813)
                    ·
                      rfl

theorem cell23_3719369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_3719369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719369 prefixEnd_3719369 := by exact prefixLift 3719369
  have htrace : WordTrace (prefixWord ++ tailWord_3719369) baseStart_3719369 baseEnd_3719369 := by
    simpa [prefixWord, tailWord_3719369, baseEnd_3719369] using wordTrace_append hprefix tailTrace_3719369
  have hstable : (prefixWord ++ tailWord_3719369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719369).length < 2 ^ (prefixWord ++ tailWord_3719369).sum := by decide
  have hdescent : baseEnd_3719369 < baseStart_3719369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719429 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 10]
def baseStart_3719429 : Nat := 118140960795 + 3719429 * 2 ^ 59
def prefixEnd_3719429 : Nat := 4983230072969 + 3 ^ 40 * 3719429 * 2
def baseEnd_3719429 : Nat := 212206093030203716736907

theorem tailTrace_3719429 : CollatzResearch.WordTrace tailWord_3719429 prefixEnd_3719429 212206093030203716736907 := by
  unfold tailWord_3719429
  simp only [CollatzResearch.WordTrace]
  refine ⟨135658720442151435745233341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90439146961434290496822227 135658720442151435745233341)
  ·
    refine ⟨50872020165806788404462503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135658720442151435745233341 50872020165806788404462503)
    ·
      refine ⟨76308030248710182606693755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50872020165806788404462503 76308030248710182606693755)
      ·
        refine ⟨114462045373065273910040633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76308030248710182606693755 114462045373065273910040633)
        ·
          refine ⟨85846534029798955432530475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114462045373065273910040633 85846534029798955432530475)
          ·
            refine ⟨128769801044698433148795713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85846534029798955432530475 128769801044698433148795713)
            ·
              refine ⟨96577350783523824861596785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128769801044698433148795713 96577350783523824861596785)
              ·
                refine ⟨72433013087642868646197589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96577350783523824861596785 72433013087642868646197589)
                ·
                  refine ⟨212206093030203716736907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 72433013087642868646197589 212206093030203716736907)
                  ·
                    rfl

theorem cell23_3719429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_3719429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719429 prefixEnd_3719429 := by exact prefixLift 3719429
  have htrace : WordTrace (prefixWord ++ tailWord_3719429) baseStart_3719429 baseEnd_3719429 := by
    simpa [prefixWord, tailWord_3719429, baseEnd_3719429] using wordTrace_append hprefix tailTrace_3719429
  have hstable : (prefixWord ++ tailWord_3719429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719429).length < 2 ^ (prefixWord ++ tailWord_3719429).sum := by decide
  have hdescent : baseEnd_3719429 < baseStart_3719429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719523 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 4, 4]
def baseStart_3719523 : Nat := 118140960795 + 3719523 * 2 ^ 59
def prefixEnd_3719523 : Nat := 4983230072969 + 3 ^ 40 * 3719523 * 2
def baseEnd_3719523 : Nat := 636634368151118694285577

theorem tailTrace_3719523 : CollatzResearch.WordTrace tailWord_3719523 prefixEnd_3719523 636634368151118694285577 := by
  unfold tailWord_3719523
  simp only [CollatzResearch.WordTrace]
  refine ⟨135662148903810889799155223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90441432602540593199436815 135662148903810889799155223)
  ·
    refine ⟨203493223355716334698732835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135662148903810889799155223 203493223355716334698732835)
    ·
      refine ⟨305239835033574502048099253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203493223355716334698732835 305239835033574502048099253)
      ·
        refine ⟨28616234534397609567009305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305239835033574502048099253 28616234534397609567009305)
        ·
          refine ⟨21462175900798207175256979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28616234534397609567009305 21462175900798207175256979)
          ·
            refine ⟨32193263851197310762885469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21462175900798207175256979 32193263851197310762885469)
            ·
              refine ⟨12072473944198991536082051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32193263851197310762885469 12072473944198991536082051)
              ·
                refine ⟨18108710916298487304123077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12072473944198991536082051 18108710916298487304123077)
                ·
                  refine ⟨3395383296805966369523077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18108710916298487304123077 3395383296805966369523077)
                  ·
                    refine ⟨636634368151118694285577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3395383296805966369523077 636634368151118694285577)
                    ·
                      rfl

theorem cell23_3719523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 4].length) (baseStart_3719523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719523 prefixEnd_3719523 := by exact prefixLift 3719523
  have htrace : WordTrace (prefixWord ++ tailWord_3719523) baseStart_3719523 baseEnd_3719523 := by
    simpa [prefixWord, tailWord_3719523, baseEnd_3719523] using wordTrace_append hprefix tailTrace_3719523
  have hstable : (prefixWord ++ tailWord_3719523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719523).length < 2 ^ (prefixWord ++ tailWord_3719523).sum := by decide
  have hdescent : baseEnd_3719523 < baseStart_3719523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719533 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3719533 : Nat := 118140960795 + 3719533 * 2 ^ 59
def prefixEnd_3719533 : Nat := 4983230072969 + 3 ^ 40 * 3719533 * 2
def baseEnd_3719533 : Nat := 1909908239259901043731685

theorem tailTrace_3719533 : CollatzResearch.WordTrace tailWord_3719533 prefixEnd_3719533 1909908239259901043731685 := by
  unfold tailWord_3719533
  simp only [CollatzResearch.WordTrace]
  refine ⟨135662513633774661507019253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90441675755849774338012835 135662513633774661507019253)
  ·
    refine ⟨12718360653166374516283055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135662513633774661507019253 12718360653166374516283055)
    ·
      refine ⟨19077540979749561774424583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12718360653166374516283055 19077540979749561774424583)
      ·
        refine ⟨28616311469624342661636875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19077540979749561774424583 28616311469624342661636875)
        ·
          refine ⟨42924467204436513992455313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28616311469624342661636875 42924467204436513992455313)
          ·
            refine ⟨32193350403327385494341485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42924467204436513992455313 32193350403327385494341485)
            ·
              refine ⟨12072506401247769560378057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32193350403327385494341485 12072506401247769560378057)
              ·
                refine ⟨9054379800935827170283543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12072506401247769560378057 9054379800935827170283543)
                ·
                  refine ⟨13581569701403740755425315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9054379800935827170283543 13581569701403740755425315)
                  ·
                    refine ⟨20372354552105611133137973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13581569701403740755425315 20372354552105611133137973)
                    ·
                      refine ⟨1909908239259901043731685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20372354552105611133137973 1909908239259901043731685)
                      ·
                        rfl

theorem cell23_3719533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3719533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719533 prefixEnd_3719533 := by exact prefixLift 3719533
  have htrace : WordTrace (prefixWord ++ tailWord_3719533) baseStart_3719533 baseEnd_3719533 := by
    simpa [prefixWord, tailWord_3719533, baseEnd_3719533] using wordTrace_append hprefix tailTrace_3719533
  have hstable : (prefixWord ++ tailWord_3719533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719533).length < 2 ^ (prefixWord ++ tailWord_3719533).sum := by decide
  have hdescent : baseEnd_3719533 < baseStart_3719533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719553 : List Nat := [1, 2, 4, 3, 1, 2, 1, 9]
def baseStart_3719553 : Nat := 118140960795 + 3719553 * 2 ^ 59
def prefixEnd_3719553 : Nat := 4983230072969 + 3 ^ 40 * 3719553 * 2
def baseEnd_3719553 : Nat := 70737722550851517240059

theorem tailTrace_3719553 : CollatzResearch.WordTrace tailWord_3719553 prefixEnd_3719553 70737722550851517240059 := by
  unfold tailWord_3719553
  simp only [CollatzResearch.WordTrace]
  refine ⟨135663243093702204922747313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90442162062468136615164875 135663243093702204922747313)
  ·
    refine ⟨101747432320276653692060485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135663243093702204922747313 101747432320276653692060485)
    ·
      refine ⟨19077643560051872567261341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101747432320276653692060485 19077643560051872567261341)
      ·
        refine ⟨7154116335019452212723003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19077643560051872567261341 7154116335019452212723003)
        ·
          refine ⟨10731174502529178319084505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7154116335019452212723003 10731174502529178319084505)
          ·
            refine ⟨8048380876896883739313379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10731174502529178319084505 8048380876896883739313379)
            ·
              refine ⟨12072571315345325608970069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8048380876896883739313379 12072571315345325608970069)
              ·
                refine ⟨70737722550851517240059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12072571315345325608970069 70737722550851517240059)
                ·
                  rfl

theorem cell23_3719553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 9].length) (baseStart_3719553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719553 prefixEnd_3719553 := by exact prefixLift 3719553
  have htrace : WordTrace (prefixWord ++ tailWord_3719553) baseStart_3719553 baseEnd_3719553 := by
    simpa [prefixWord, tailWord_3719553, baseEnd_3719553] using wordTrace_append hprefix tailTrace_3719553
  have hstable : (prefixWord ++ tailWord_3719553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719553).length < 2 ^ (prefixWord ++ tailWord_3719553).sum := by decide
  have hdescent : baseEnd_3719553 < baseStart_3719553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719564 : List Nat := [2, 2, 1, 2, 1, 4, 3, 3, 1, 2, 2]
def baseStart_3719564 : Nat := 118140960795 + 3719564 * 2 ^ 59
def prefixEnd_3719564 : Nat := 4983230072969 + 3 ^ 40 * 3719564 * 2
def baseEnd_3719564 : Nat := 1909924157160190422444043

theorem tailTrace_3719564 : CollatzResearch.WordTrace tailWord_3719564 prefixEnd_3719564 1909924157160190422444043 := by
  unfold tailWord_3719564
  simp only [CollatzResearch.WordTrace]
  refine ⟨67831822148331176900698873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90442429531108235867598497 67831822148331176900698873)
  ·
    refine ⟨50873866611248382675524155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67831822148331176900698873 50873866611248382675524155)
    ·
      refine ⟨76310799916872574013286233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50873866611248382675524155 76310799916872574013286233)
      ·
        refine ⟨57233099937654430509964675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76310799916872574013286233 57233099937654430509964675)
        ·
          refine ⟨85849649906481645764947013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57233099937654430509964675 85849649906481645764947013)
          ·
            refine ⟨16096809357465308580927565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85849649906481645764947013 16096809357465308580927565)
            ·
              refine ⟨6036303509049490717847837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16096809357465308580927565 6036303509049490717847837)
              ·
                refine ⟨2263613815893559019192939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6036303509049490717847837 2263613815893559019192939)
                ·
                  refine ⟨3395420723840338528789409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2263613815893559019192939 3395420723840338528789409)
                  ·
                    refine ⟨2546565542880253896592057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3395420723840338528789409 2546565542880253896592057)
                    ·
                      refine ⟨1909924157160190422444043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546565542880253896592057 1909924157160190422444043)
                      ·
                        rfl

theorem cell23_3719564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_3719564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719564 prefixEnd_3719564 := by exact prefixLift 3719564
  have htrace : WordTrace (prefixWord ++ tailWord_3719564) baseStart_3719564 baseEnd_3719564 := by
    simpa [prefixWord, tailWord_3719564, baseEnd_3719564] using wordTrace_append hprefix tailTrace_3719564
  have hstable : (prefixWord ++ tailWord_3719564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719564).length < 2 ^ (prefixWord ++ tailWord_3719564).sum := by decide
  have hdescent : baseEnd_3719564 < baseStart_3719564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719581 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 3, 2, 2]
def baseStart_3719581 : Nat := 118140960795 + 3719581 * 2 ^ 59
def prefixEnd_3719581 : Nat := 4983230072969 + 3 ^ 40 * 3719581 * 2
def baseEnd_3719581 : Nat := 1909932886331316855931465

theorem tailTrace_3719581 : CollatzResearch.WordTrace tailWord_3719581 prefixEnd_3719581 1909932886331316855931465 := by
  unfold tailWord_3719581
  simp only [CollatzResearch.WordTrace]
  refine ⟨135664264337600765704766597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90442842891733843803177731 135664264337600765704766597)
  ·
    refine ⟨25437049563300143569643737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135664264337600765704766597 25437049563300143569643737)
    ·
      refine ⟨19077787172475107677232803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25437049563300143569643737 19077787172475107677232803)
      ·
        refine ⟨28616680758712661515849205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19077787172475107677232803 28616680758712661515849205)
        ·
          refine ⟨2682813821129312017110863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28616680758712661515849205 2682813821129312017110863)
          ·
            refine ⟨4024220731693968025666295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682813821129312017110863 4024220731693968025666295)
            ·
              refine ⟨6036331097540952038499443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024220731693968025666295 6036331097540952038499443)
              ·
                refine ⟨9054496646311428057749165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036331097540952038499443 9054496646311428057749165)
                ·
                  refine ⟨3395436242366785521655937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9054496646311428057749165 3395436242366785521655937)
                  ·
                    refine ⟨2546577181775089141241953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3395436242366785521655937 2546577181775089141241953)
                    ·
                      refine ⟨1909932886331316855931465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546577181775089141241953 1909932886331316855931465)
                      ·
                        rfl

theorem cell23_3719581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_3719581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719581 prefixEnd_3719581 := by exact prefixLift 3719581
  have htrace : WordTrace (prefixWord ++ tailWord_3719581) baseStart_3719581 baseEnd_3719581 := by
    simpa [prefixWord, tailWord_3719581, baseEnd_3719581] using wordTrace_append hprefix tailTrace_3719581
  have hstable : (prefixWord ++ tailWord_3719581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719581).length < 2 ^ (prefixWord ++ tailWord_3719581).sum := by decide
  have hdescent : baseEnd_3719581 < baseStart_3719581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719596 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_3719596 : Nat := 118140960795 + 3719596 * 2 ^ 59
def prefixEnd_3719596 : Nat := 4983230072969 + 3 ^ 40 * 3719596 * 2
def baseEnd_3719596 : Nat := 636646862847044765747965

theorem tailTrace_3719596 : CollatzResearch.WordTrace tailWord_3719596 prefixEnd_3719596 636646862847044765747965 := by
  unfold tailWord_3719596
  simp only [CollatzResearch.WordTrace]
  refine ⟨67832405716273211633281321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90443207621697615511041761 67832405716273211633281321)
  ·
    refine ⟨50874304287204908724960991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67832405716273211633281321 50874304287204908724960991)
    ·
      refine ⟨76311456430807363087441487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50874304287204908724960991 76311456430807363087441487)
      ·
        refine ⟨114467184646211044631162231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76311456430807363087441487 114467184646211044631162231)
        ·
          refine ⟨171700776969316566946743347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114467184646211044631162231 171700776969316566946743347)
          ·
            refine ⟨257551165453974850420115021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171700776969316566946743347 257551165453974850420115021)
            ·
              refine ⟨96581687045240568907543133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257551165453974850420115021 96581687045240568907543133)
              ·
                refine ⟨36218132641965213340328675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96581687045240568907543133 36218132641965213340328675)
                ·
                  refine ⟨54327198962947820010493013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36218132641965213340328675 54327198962947820010493013)
                  ·
                    refine ⟨636646862847044765747965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54327198962947820010493013 636646862847044765747965)
                    ·
                      rfl

theorem cell23_3719596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_3719596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719596 prefixEnd_3719596 := by exact prefixLift 3719596
  have htrace : WordTrace (prefixWord ++ tailWord_3719596) baseStart_3719596 baseEnd_3719596 := by
    simpa [prefixWord, tailWord_3719596, baseEnd_3719596] using wordTrace_append hprefix tailTrace_3719596
  have hstable : (prefixWord ++ tailWord_3719596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719596).length < 2 ^ (prefixWord ++ tailWord_3719596).sum := by decide
  have hdescent : baseEnd_3719596 < baseStart_3719596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719607 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 1, 3, 2]
def baseStart_3719607 : Nat := 118140960795 + 3719607 * 2 ^ 59
def prefixEnd_3719607 : Nat := 4983230072969 + 3 ^ 40 * 3719607 * 2
def baseEnd_3719607 : Nat := 1909946236828333754206345

theorem tailTrace_3719607 : CollatzResearch.WordTrace tailWord_3719607 prefixEnd_3719607 1909946236828333754206345 := by
  unfold tailWord_3719607
  simp only [CollatzResearch.WordTrace]
  refine ⟨135665212635506572145213075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90443475090337714763475383 135665212635506572145213075)
  ·
    refine ⟨203497818953259858217819613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135665212635506572145213075 203497818953259858217819613)
    ·
      refine ⟨76311682107472446831682355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203497818953259858217819613 76311682107472446831682355)
      ·
        refine ⟨114467523161208670247523533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76311682107472446831682355 114467523161208670247523533)
        ·
          refine ⟨42925321185453251342821325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114467523161208670247523533 42925321185453251342821325)
          ·
            refine ⟨16096995444544969253557997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42925321185453251342821325 16096995444544969253557997)
            ·
              refine ⟨6036373291704363470084249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16096995444544969253557997 6036373291704363470084249)
              ·
                refine ⟨4527279968778272602563187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6036373291704363470084249 4527279968778272602563187)
                ·
                  refine ⟨6790919953167408903844781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4527279968778272602563187 6790919953167408903844781)
                  ·
                    refine ⟨2546594982437778338941793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6790919953167408903844781 2546594982437778338941793)
                    ·
                      refine ⟨1909946236828333754206345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2546594982437778338941793 1909946236828333754206345)
                      ·
                        rfl

theorem cell23_3719607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_3719607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719607 prefixEnd_3719607 := by exact prefixLift 3719607
  have htrace : WordTrace (prefixWord ++ tailWord_3719607) baseStart_3719607 baseEnd_3719607 := by
    simpa [prefixWord, tailWord_3719607, baseEnd_3719607] using wordTrace_append hprefix tailTrace_3719607
  have hstable : (prefixWord ++ tailWord_3719607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719607).length < 2 ^ (prefixWord ++ tailWord_3719607).sum := by decide
  have hdescent : baseEnd_3719607 < baseStart_3719607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3719623 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_3719623 : Nat := 118140960795 + 3719623 * 2 ^ 59
def prefixEnd_3719623 : Nat := 4983230072969 + 3 ^ 40 * 3719623 * 2
def baseEnd_3719623 : Nat := 1909954452518805691606271

theorem tailTrace_3719623 : CollatzResearch.WordTrace tailWord_3719623 prefixEnd_3719623 1909954452518805691606271 := by
  unfold tailWord_3719623
  simp only [CollatzResearch.WordTrace]
  refine ⟨135665796203448606877795523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90443864135632404585197015 135665796203448606877795523)
  ·
    refine ⟨203498694305172910316693285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135665796203448606877795523 203498694305172910316693285)
    ·
      refine ⟨38156005182219920684379991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203498694305172910316693285 38156005182219920684379991)
      ·
        refine ⟨57234007773329881026569987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38156005182219920684379991 57234007773329881026569987)
        ·
          refine ⟨85851011659994821539854981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57234007773329881026569987 85851011659994821539854981)
          ·
            refine ⟨16097064686249029038722809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85851011659994821539854981 16097064686249029038722809)
            ·
              refine ⟨12072798514686771779042107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16097064686249029038722809 12072798514686771779042107)
              ·
                refine ⟨18109197772030157668563161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12072798514686771779042107 18109197772030157668563161)
                ·
                  refine ⟨13581898329022618251422371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18109197772030157668563161 13581898329022618251422371)
                  ·
                    refine ⟨20372847493533927377133557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13581898329022618251422371 20372847493533927377133557)
                    ·
                      refine ⟨1909954452518805691606271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20372847493533927377133557 1909954452518805691606271)
                      ·
                        rfl

theorem cell23_3719623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_3719623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3719623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3719623 prefixEnd_3719623 := by exact prefixLift 3719623
  have htrace : WordTrace (prefixWord ++ tailWord_3719623) baseStart_3719623 baseEnd_3719623 := by
    simpa [prefixWord, tailWord_3719623, baseEnd_3719623] using wordTrace_append hprefix tailTrace_3719623
  have hstable : (prefixWord ++ tailWord_3719623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3719623).length < 2 ^ (prefixWord ++ tailWord_3719623).sum := by decide
  have hdescent : baseEnd_3719623 < baseStart_3719623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3719623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
