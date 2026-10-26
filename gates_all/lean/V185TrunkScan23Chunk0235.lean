import V185TrunkScan23Chunk0234

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1390657 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1390657 : Nat := 118140960795 + 1390657 * 2 ^ 59
def prefixEnd_1390657 : Nat := 4983230072969 + 3 ^ 40 * 1390657 * 2
def baseEnd_1390657 : Nat := 714075466539670781791991

theorem tailTrace_1390657 : CollatzResearch.WordTrace tailWord_1390657 prefixEnd_1390657 714075466539670781791991 := by
  unfold tailWord_1390657
  simp only [CollatzResearch.WordTrace]
  refine ⟨50721427722894669151946225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33814285148596446101297483 50721427722894669151946225)
  ·
    refine ⟨38041070792171001863959669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50721427722894669151946225 38041070792171001863959669)
    ·
      refine ⟨3566350386766031424746219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38041070792171001863959669 3566350386766031424746219)
      ·
        refine ⟨5349525580149047137119329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566350386766031424746219 5349525580149047137119329)
        ·
          refine ⟨4012144185111785352839497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5349525580149047137119329 4012144185111785352839497)
          ·
            refine ⟨3009108138833839014629623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012144185111785352839497 3009108138833839014629623)
            ·
              refine ⟨4513662208250758521944435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009108138833839014629623 4513662208250758521944435)
              ·
                refine ⟨6770493312376137782916653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4513662208250758521944435 6770493312376137782916653)
                ·
                  refine ⟨2538934992141051668593745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6770493312376137782916653 2538934992141051668593745)
                  ·
                    refine ⟨1904201244105788751445309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2538934992141051668593745 1904201244105788751445309)
                    ·
                      refine ⟨714075466539670781791991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904201244105788751445309 714075466539670781791991)
                      ·
                        rfl

theorem cell23_1390657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1390657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390657 prefixEnd_1390657 := by exact prefixLift 1390657
  have htrace : WordTrace (prefixWord ++ tailWord_1390657) baseStart_1390657 baseEnd_1390657 := by
    simpa [prefixWord, tailWord_1390657, baseEnd_1390657] using wordTrace_append hprefix tailTrace_1390657
  have hstable : (prefixWord ++ tailWord_1390657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390657).length < 2 ^ (prefixWord ++ tailWord_1390657).sum := by decide
  have hdescent : baseEnd_1390657 < baseStart_1390657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390670 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_1390670 : Nat := 118140960795 + 1390670 * 2 ^ 59
def prefixEnd_1390670 : Nat := 4983230072969 + 3 ^ 40 * 1390670 * 2
def baseEnd_1390670 : Nat := 714082141788179230929431

theorem tailTrace_1390670 : CollatzResearch.WordTrace tailWord_1390670 prefixEnd_1390670 714082141788179230929431 := by
  unfold tailWord_1390670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340237733980946546521183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33814601247898381581446309 6340237733980946546521183)
  ·
    refine ⟨9510356600971419819781775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6340237733980946546521183 9510356600971419819781775)
    ·
      refine ⟨14265534901457129729672663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9510356600971419819781775 14265534901457129729672663)
      ·
        refine ⟨21398302352185694594508995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14265534901457129729672663 21398302352185694594508995)
        ·
          refine ⟨32097453528278541891763493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21398302352185694594508995 32097453528278541891763493)
          ·
            refine ⟨6018272536552226604705655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32097453528278541891763493 6018272536552226604705655)
            ·
              refine ⟨9027408804828339907058483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018272536552226604705655 9027408804828339907058483)
              ·
                refine ⟨13541113207242509860587725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9027408804828339907058483 13541113207242509860587725)
                ·
                  refine ⟨5077917452715941197720397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13541113207242509860587725 5077917452715941197720397)
                  ·
                    refine ⟨1904219044768477949145149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5077917452715941197720397 1904219044768477949145149)
                    ·
                      refine ⟨714082141788179230929431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904219044768477949145149 714082141788179230929431)
                      ·
                        rfl

theorem cell23_1390670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_1390670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390670 prefixEnd_1390670 := by exact prefixLift 1390670
  have htrace : WordTrace (prefixWord ++ tailWord_1390670) baseStart_1390670 baseEnd_1390670 := by
    simpa [prefixWord, tailWord_1390670, baseEnd_1390670] using wordTrace_append hprefix tailTrace_1390670
  have hstable : (prefixWord ++ tailWord_1390670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390670).length < 2 ^ (prefixWord ++ tailWord_1390670).sum := by decide
  have hdescent : baseEnd_1390670 < baseStart_1390670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390674 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_1390674 : Nat := 118140960795 + 1390674 * 2 ^ 59
def prefixEnd_1390674 : Nat := 4983230072969 + 3 ^ 40 * 1390674 * 2
def baseEnd_1390674 : Nat := 714084195710797215279413

theorem tailTrace_1390674 : CollatzResearch.WordTrace tailWord_1390674 prefixEnd_1390674 714084195710797215279413 := by
  unfold tailWord_1390674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680511940958270263828769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33814698509222054036876717 12680511940958270263828769)
  ·
    refine ⟨9510383955718702697871577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12680511940958270263828769 9510383955718702697871577)
    ·
      refine ⟨7132787966789027023403683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9510383955718702697871577 7132787966789027023403683)
      ·
        refine ⟨10699181950183540535105525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7132787966789027023403683 10699181950183540535105525)
        ·
          refine ⟨1003048307829706925166143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10699181950183540535105525 1003048307829706925166143)
          ·
            refine ⟨1504572461744560387749215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003048307829706925166143 1504572461744560387749215)
            ·
              refine ⟨2256858692616840581623823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504572461744560387749215 2256858692616840581623823)
              ·
                refine ⟨3385288038925260872435735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256858692616840581623823 3385288038925260872435735)
                ·
                  refine ⟨5077932058387891308653603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385288038925260872435735 5077932058387891308653603)
                  ·
                    refine ⟨7616898087581836962980405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5077932058387891308653603 7616898087581836962980405)
                    ·
                      refine ⟨714084195710797215279413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7616898087581836962980405 714084195710797215279413)
                      ·
                        rfl

theorem cell23_1390674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_1390674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390674 prefixEnd_1390674 := by exact prefixLift 1390674
  have htrace : WordTrace (prefixWord ++ tailWord_1390674) baseStart_1390674 baseEnd_1390674 := by
    simpa [prefixWord, tailWord_1390674, baseEnd_1390674] using wordTrace_append hprefix tailTrace_1390674
  have hstable : (prefixWord ++ tailWord_1390674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390674).length < 2 ^ (prefixWord ++ tailWord_1390674).sum := by decide
  have hdescent : baseEnd_1390674 < baseStart_1390674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390688 : List Nat := [2, 1, 1, 3, 2, 5, 2, 2, 1, 2, 2]
def baseStart_1390688 : Nat := 118140960795 + 1390688 * 2 ^ 59
def prefixEnd_1390688 : Nat := 4983230072969 + 3 ^ 40 * 1390688 * 2
def baseEnd_1390688 : Nat := 714091384439960160504349

theorem tailTrace_1390688 : CollatzResearch.WordTrace tailWord_1390688 prefixEnd_1390688 714091384439960160504349 := by
  unfold tailWord_1390688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25361279192891180723162359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33815038923854907630883145 25361279192891180723162359)
  ·
    refine ⟨38041918789336771084743539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25361279192891180723162359 38041918789336771084743539)
    ·
      refine ⟨57062878184005156627115309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38041918789336771084743539 57062878184005156627115309)
      ·
        refine ⟨21398579319001933735168241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57062878184005156627115309 21398579319001933735168241)
        ·
          refine ⟨16048934489251450301376181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21398579319001933735168241 16048934489251450301376181)
          ·
            refine ⟨1504587608367323465754017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16048934489251450301376181 1504587608367323465754017)
            ·
              refine ⟨1128440706275492599315513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504587608367323465754017 1128440706275492599315513)
              ·
                refine ⟨846330529706619449486635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128440706275492599315513 846330529706619449486635)
                ·
                  refine ⟨1269495794559929174229953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846330529706619449486635 1269495794559929174229953)
                  ·
                    refine ⟨952121845919946880672465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269495794559929174229953 952121845919946880672465)
                    ·
                      refine ⟨714091384439960160504349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952121845919946880672465 714091384439960160504349)
                      ·
                        rfl

theorem cell23_1390688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_1390688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390688 prefixEnd_1390688 := by exact prefixLift 1390688
  have htrace : WordTrace (prefixWord ++ tailWord_1390688) baseStart_1390688 baseEnd_1390688 := by
    simpa [prefixWord, tailWord_1390688, baseEnd_1390688] using wordTrace_append hprefix tailTrace_1390688
  have hstable : (prefixWord ++ tailWord_1390688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390688).length < 2 ^ (prefixWord ++ tailWord_1390688).sum := by decide
  have hdescent : baseEnd_1390688 < baseStart_1390688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390703 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 1, 8]
def baseStart_1390703 : Nat := 118140960795 + 1390703 * 2 ^ 59
def prefixEnd_1390703 : Nat := 4983230072969 + 3 ^ 40 * 1390703 * 2
def baseEnd_1390703 : Nat := 238033028883259200605593

theorem tailTrace_1390703 : CollatzResearch.WordTrace tailWord_1390703 prefixEnd_1390703 238033028883259200605593 := by
  unfold tailWord_1390703
  simp only [CollatzResearch.WordTrace]
  refine ⟨50723105480728019008120763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33815403653818679338747175 50723105480728019008120763)
  ·
    refine ⟨76084658221092028512181145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50723105480728019008120763 76084658221092028512181145)
    ·
      refine ⟨57063493665819021384135859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76084658221092028512181145 57063493665819021384135859)
      ·
        refine ⟨85595240498728532076203789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57063493665819021384135859 85595240498728532076203789)
        ·
          refine ⟨32098215187023199528576421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85595240498728532076203789 32098215187023199528576421)
          ·
            refine ⟨6018415347566849911608079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32098215187023199528576421 6018415347566849911608079)
            ·
              refine ⟨9027623021350274867412119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018415347566849911608079 9027623021350274867412119)
              ·
                refine ⟨13541434532025412301118179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9027623021350274867412119 13541434532025412301118179)
                ·
                  refine ⟨20312151798038118451677269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13541434532025412301118179 20312151798038118451677269)
                  ·
                    refine ⟨238033028883259200605593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20312151798038118451677269 238033028883259200605593)
                    ·
                      rfl

theorem cell23_1390703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_1390703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390703 prefixEnd_1390703 := by exact prefixLift 1390703
  have htrace : WordTrace (prefixWord ++ tailWord_1390703) baseStart_1390703 baseEnd_1390703 := by
    simpa [prefixWord, tailWord_1390703, baseEnd_1390703] using wordTrace_append hprefix tailTrace_1390703
  have hstable : (prefixWord ++ tailWord_1390703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390703).length < 2 ^ (prefixWord ++ tailWord_1390703).sum := by decide
  have hdescent : baseEnd_1390703 < baseStart_1390703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390727 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_1390727 : Nat := 118140960795 + 1390727 * 2 ^ 59
def prefixEnd_1390727 : Nat := 4983230072969 + 3 ^ 40 * 1390727 * 2
def baseEnd_1390727 : Nat := 714111410185485507916669

theorem tailTrace_1390727 : CollatzResearch.WordTrace tailWord_1390727 prefixEnd_1390727 714111410185485507916669 := by
  unfold tailWord_1390727
  simp only [CollatzResearch.WordTrace]
  refine ⟨50723980832641071106994435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33815987221760714071329623 50723980832641071106994435)
  ·
    refine ⟨76085971248961606660491653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50723980832641071106994435 76085971248961606660491653)
    ·
      refine ⟨14266119609180301248842185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76085971248961606660491653 14266119609180301248842185)
      ·
        refine ⟨10699589706885225936631639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14266119609180301248842185 10699589706885225936631639)
        ·
          refine ⟨16049384560327838904947459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10699589706885225936631639 16049384560327838904947459)
          ·
            refine ⟨24074076840491758357421189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16049384560327838904947459 24074076840491758357421189)
            ·
              refine ⟨4513889407592204692016473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24074076840491758357421189 4513889407592204692016473)
              ·
                refine ⟨3385417055694153519012355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4513889407592204692016473 3385417055694153519012355)
                ·
                  refine ⟨5078125583541230278518533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3385417055694153519012355 5078125583541230278518533)
                  ·
                    refine ⟨952148546913980677222225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5078125583541230278518533 952148546913980677222225)
                    ·
                      refine ⟨714111410185485507916669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952148546913980677222225 714111410185485507916669)
                      ·
                        rfl

theorem cell23_1390727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_1390727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390727 prefixEnd_1390727 := by exact prefixLift 1390727
  have htrace : WordTrace (prefixWord ++ tailWord_1390727) baseStart_1390727 baseEnd_1390727 := by
    simpa [prefixWord, tailWord_1390727, baseEnd_1390727] using wordTrace_append hprefix tailTrace_1390727
  have hstable : (prefixWord ++ tailWord_1390727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390727).length < 2 ^ (prefixWord ++ tailWord_1390727).sum := by decide
  have hdescent : baseEnd_1390727 < baseStart_1390727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390784 : List Nat := [2, 1, 1, 2, 5, 3, 1, 3, 5]
def baseStart_1390784 : Nat := 118140960795 + 1390784 * 2 ^ 59
def prefixEnd_1390784 : Nat := 4983230072969 + 3 ^ 40 * 1390784 * 2
def baseEnd_1390784 : Nat := 79348964286976864989323

theorem tailTrace_1390784 : CollatzResearch.WordTrace tailWord_1390784 prefixEnd_1390784 79348964286976864989323 := by
  unfold tailWord_1390784
  simp only [CollatzResearch.WordTrace]
  refine ⟨25363029896717284920909703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33817373195623046561212937 25363029896717284920909703)
  ·
    refine ⟨38044544845075927381364555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25363029896717284920909703 38044544845075927381364555)
    ·
      refine ⟨57066817267613891072046833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38044544845075927381364555 57066817267613891072046833)
      ·
        refine ⟨42800112950710418304035125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57066817267613891072046833 42800112950710418304035125)
        ·
          refine ⟨4012510589129101716003293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42800112950710418304035125 4012510589129101716003293)
          ·
            refine ⟨1504691470923413143501235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4012510589129101716003293 1504691470923413143501235)
            ·
              refine ⟨2257037206385119715251853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504691470923413143501235 2257037206385119715251853)
              ·
                refine ⟨846388952394419893219445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257037206385119715251853 846388952394419893219445)
                ·
                  refine ⟨79348964286976864989323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 846388952394419893219445 79348964286976864989323)
                  ·
                    rfl

theorem cell23_1390784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 5].length) (baseStart_1390784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390784 prefixEnd_1390784 := by exact prefixLift 1390784
  have htrace : WordTrace (prefixWord ++ tailWord_1390784) baseStart_1390784 baseEnd_1390784 := by
    simpa [prefixWord, tailWord_1390784, baseEnd_1390784] using wordTrace_append hprefix tailTrace_1390784
  have hstable : (prefixWord ++ tailWord_1390784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390784).length < 2 ^ (prefixWord ++ tailWord_1390784).sum := by decide
  have hdescent : baseEnd_1390784 < baseStart_1390784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390812 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1390812 : Nat := 118140960795 + 1390812 * 2 ^ 59
def prefixEnd_1390812 : Nat := 4983230072969 + 3 ^ 40 * 1390812 * 2
def baseEnd_1390812 : Nat := 714155056041117675353779

theorem tailTrace_1390812 : CollatzResearch.WordTrace tailWord_1390812 prefixEnd_1390812 714155056041117675353779 := by
  unfold tailWord_1390812
  simp only [CollatzResearch.WordTrace]
  refine ⟨25363540518666565311919345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33818054024888753749225793 25363540518666565311919345)
  ·
    refine ⟨19022655388999923983939509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25363540518666565311919345 19022655388999923983939509)
    ·
      refine ⟨1783373942718742873494329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19022655388999923983939509 1783373942718742873494329)
      ·
        refine ⟨1337530457039057155120747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1783373942718742873494329 1337530457039057155120747)
        ·
          refine ⟨2006295685558585732681121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337530457039057155120747 2006295685558585732681121)
          ·
            refine ⟨1504721764168939299510841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2006295685558585732681121 1504721764168939299510841)
            ·
              refine ⟨1128541323126704474633131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504721764168939299510841 1128541323126704474633131)
              ·
                refine ⟨1692811984690056711949697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128541323126704474633131 1692811984690056711949697)
                ·
                  refine ⟨1269608988517542533962273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1692811984690056711949697 1269608988517542533962273)
                  ·
                    refine ⟨952206741388156900471705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269608988517542533962273 952206741388156900471705)
                    ·
                      refine ⟨714155056041117675353779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952206741388156900471705 714155056041117675353779)
                      ·
                        rfl

theorem cell23_1390812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1390812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390812 prefixEnd_1390812 := by exact prefixLift 1390812
  have htrace : WordTrace (prefixWord ++ tailWord_1390812) baseStart_1390812 baseEnd_1390812 := by
    simpa [prefixWord, tailWord_1390812, baseEnd_1390812] using wordTrace_append hprefix tailTrace_1390812
  have hstable : (prefixWord ++ tailWord_1390812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390812).length < 2 ^ (prefixWord ++ tailWord_1390812).sum := by decide
  have hdescent : baseEnd_1390812 < baseStart_1390812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390817 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_1390817 : Nat := 118140960795 + 1390817 * 2 ^ 59
def prefixEnd_1390817 : Nat := 4983230072969 + 3 ^ 40 * 1390817 * 2
def baseEnd_1390817 : Nat := 714157623444390155791255

theorem tailTrace_1390817 : CollatzResearch.WordTrace tailWord_1390817 prefixEnd_1390817 714157623444390155791255 := by
  unfold tailWord_1390817
  simp only [CollatzResearch.WordTrace]
  refine ⟨50727263402315016477770705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33818175601543344318513803 50727263402315016477770705)
  ·
    refine ⟨38045447551736262358328029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50727263402315016477770705 38045447551736262358328029)
    ·
      refine ⟨14267042831901098384373011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38045447551736262358328029 14267042831901098384373011)
      ·
        refine ⟨21400564247851647576559517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14267042831901098384373011 21400564247851647576559517)
        ·
          refine ⟨8025211592944367841209819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21400564247851647576559517 8025211592944367841209819)
          ·
            refine ⟨12037817389416551761814729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025211592944367841209819 12037817389416551761814729)
            ·
              refine ⟨9028363042062413821361047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12037817389416551761814729 9028363042062413821361047)
              ·
                refine ⟨13542544563093620732041571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028363042062413821361047 13542544563093620732041571)
                ·
                  refine ⟨20313816844640431098062357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13542544563093620732041571 20313816844640431098062357)
                  ·
                    refine ⟨952210164592520207721673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20313816844640431098062357 952210164592520207721673)
                    ·
                      refine ⟨714157623444390155791255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952210164592520207721673 714157623444390155791255)
                      ·
                        rfl

theorem cell23_1390817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_1390817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390817 prefixEnd_1390817 := by exact prefixLift 1390817
  have htrace : WordTrace (prefixWord ++ tailWord_1390817) baseStart_1390817 baseEnd_1390817 := by
    simpa [prefixWord, tailWord_1390817, baseEnd_1390817] using wordTrace_append hprefix tailTrace_1390817
  have hstable : (prefixWord ++ tailWord_1390817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390817).length < 2 ^ (prefixWord ++ tailWord_1390817).sum := by decide
  have hdescent : baseEnd_1390817 < baseStart_1390817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390830 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1390830 : Nat := 118140960795 + 1390830 * 2 ^ 59
def prefixEnd_1390830 : Nat := 4983230072969 + 3 ^ 40 * 1390830 * 2
def baseEnd_1390830 : Nat := 714164298692898604928695

theorem tailTrace_1390830 : CollatzResearch.WordTrace tailWord_1390830 prefixEnd_1390830 714164298692898604928695 := by
  unfold tailWord_1390830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340967193908489962249243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33818491700845279798662629 6340967193908489962249243)
  ·
    refine ⟨9511450790862734943373865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6340967193908489962249243 9511450790862734943373865)
    ·
      refine ⟨7133588093147051207530399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9511450790862734943373865 7133588093147051207530399)
      ·
        refine ⟨10700382139720576811295599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7133588093147051207530399 10700382139720576811295599)
        ·
          refine ⟨16050573209580865216943399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10700382139720576811295599 16050573209580865216943399)
          ·
            refine ⟨24075859814371297825415099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16050573209580865216943399 24075859814371297825415099)
            ·
              refine ⟨36113789721556946738122649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24075859814371297825415099 36113789721556946738122649)
              ·
                refine ⟨27085342291167710053591987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36113789721556946738122649 27085342291167710053591987)
                ·
                  refine ⟨40628013436751565080387981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27085342291167710053591987 40628013436751565080387981)
                  ·
                    refine ⟨15235505038781836905145493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40628013436751565080387981 15235505038781836905145493)
                    ·
                      refine ⟨714164298692898604928695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15235505038781836905145493 714164298692898604928695)
                      ·
                        rfl

theorem cell23_1390830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1390830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390830 prefixEnd_1390830 := by exact prefixLift 1390830
  have htrace : WordTrace (prefixWord ++ tailWord_1390830) baseStart_1390830 baseEnd_1390830 := by
    simpa [prefixWord, tailWord_1390830, baseEnd_1390830] using wordTrace_append hprefix tailTrace_1390830
  have hstable : (prefixWord ++ tailWord_1390830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390830).length < 2 ^ (prefixWord ++ tailWord_1390830).sum := by decide
  have hdescent : baseEnd_1390830 < baseStart_1390830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390834 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1390834 : Nat := 118140960795 + 1390834 * 2 ^ 59
def prefixEnd_1390834 : Nat := 4983230072969 + 3 ^ 40 * 1390834 * 2
def baseEnd_1390834 : Nat := 714166352615516589278677

theorem tailTrace_1390834 : CollatzResearch.WordTrace tailWord_1390834 prefixEnd_1390834 714166352615516589278677 := by
  unfold tailWord_1390834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12681970860813357095284889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33818588962168952254093037 12681970860813357095284889)
  ·
    refine ⟨9511478145610017821463667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12681970860813357095284889 9511478145610017821463667)
    ·
      refine ⟨14267217218415026732195501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9511478145610017821463667 14267217218415026732195501)
      ·
        refine ⟨5350206456905635024573313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14267217218415026732195501 5350206456905635024573313)
        ·
          refine ⟨4012654842679226268429985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5350206456905635024573313 4012654842679226268429985)
          ·
            refine ⟨3009491132009419701322489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012654842679226268429985 3009491132009419701322489)
            ·
              refine ⟨2257118349007064775991867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009491132009419701322489 2257118349007064775991867)
              ·
                refine ⟨3385677523510597163987801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257118349007064775991867 3385677523510597163987801)
                ·
                  refine ⟨2539258142632947872990851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3385677523510597163987801 2539258142632947872990851)
                  ·
                    refine ⟨3808887213949421809486277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2539258142632947872990851 3808887213949421809486277)
                    ·
                      refine ⟨714166352615516589278677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3808887213949421809486277 714166352615516589278677)
                      ·
                        rfl

theorem cell23_1390834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1390834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390834 prefixEnd_1390834 := by exact prefixLift 1390834
  have htrace : WordTrace (prefixWord ++ tailWord_1390834) baseStart_1390834 baseEnd_1390834 := by
    simpa [prefixWord, tailWord_1390834, baseEnd_1390834] using wordTrace_append hprefix tailTrace_1390834
  have hstable : (prefixWord ++ tailWord_1390834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390834).length < 2 ^ (prefixWord ++ tailWord_1390834).sum := by decide
  have hdescent : baseEnd_1390834 < baseStart_1390834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390857 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 6]
def baseStart_1390857 : Nat := 118140960795 + 1390857 * 2 ^ 59
def prefixEnd_1390857 : Nat := 4983230072969 + 3 ^ 40 * 1390857 * 2
def baseEnd_1390857 : Nat := 79353129185618888810119

theorem tailTrace_1390857 : CollatzResearch.WordTrace tailWord_1390857 prefixEnd_1390857 79353129185618888810119 := by
  unfold tailWord_1390857
  simp only [CollatzResearch.WordTrace]
  refine ⟨50728722322170103309226825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33819148214780068872817883 50728722322170103309226825)
  ·
    refine ⟨38046541741627577481920119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50728722322170103309226825 38046541741627577481920119)
    ·
      refine ⟨57069812612441366222880179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38046541741627577481920119 57069812612441366222880179)
      ·
        refine ⟨85604718918662049334320269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57069812612441366222880179 85604718918662049334320269)
        ·
          refine ⟨32101769594498268500370101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85604718918662049334320269 32101769594498268500370101)
          ·
            refine ⟨3009540899484212671909697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32101769594498268500370101 3009540899484212671909697)
            ·
              refine ⟨2257155674613159503932273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009540899484212671909697 2257155674613159503932273)
              ·
                refine ⟨1692866755959869627949205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2257155674613159503932273 1692866755959869627949205)
                ·
                  refine ⟨79353129185618888810119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1692866755959869627949205 79353129185618888810119)
                  ·
                    rfl

theorem cell23_1390857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 6].length) (baseStart_1390857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390857 prefixEnd_1390857 := by exact prefixLift 1390857
  have htrace : WordTrace (prefixWord ++ tailWord_1390857) baseStart_1390857 baseEnd_1390857 := by
    simpa [prefixWord, tailWord_1390857, baseEnd_1390857] using wordTrace_append hprefix tailTrace_1390857
  have hstable : (prefixWord ++ tailWord_1390857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390857).length < 2 ^ (prefixWord ++ tailWord_1390857).sum := by decide
  have hdescent : baseEnd_1390857 < baseStart_1390857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390860 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1390860 : Nat := 118140960795 + 1390860 * 2 ^ 59
def prefixEnd_1390860 : Nat := 4983230072969 + 3 ^ 40 * 1390860 * 2
def baseEnd_1390860 : Nat := 714179703112533487553557

theorem tailTrace_1390860 : CollatzResearch.WordTrace tailWord_1390860 prefixEnd_1390860 714179703112533487553557 := by
  unfold tailWord_1390860
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364415870579617410793017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33819221160772823214390689 25364415870579617410793017)
  ·
    refine ⟨19023311902934713058094763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25364415870579617410793017 19023311902934713058094763)
    ·
      refine ⟨28534967854402069587142145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19023311902934713058094763 28534967854402069587142145)
      ·
        refine ⟨21401225890801552190356609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28534967854402069587142145 21401225890801552190356609)
        ·
          refine ⟨16050919418101164142767457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21401225890801552190356609 16050919418101164142767457)
          ·
            refine ⟨12038189563575873107075593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16050919418101164142767457 12038189563575873107075593)
            ·
              refine ⟨9028642172681904830306695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12038189563575873107075593 9028642172681904830306695)
              ·
                refine ⟨13542963259022857245460043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028642172681904830306695 13542963259022857245460043)
                ·
                  refine ⟨20314444888534285868190065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13542963259022857245460043 20314444888534285868190065)
                  ·
                    refine ⟨15235833666400714401142549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20314444888534285868190065 15235833666400714401142549)
                    ·
                      refine ⟨714179703112533487553557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15235833666400714401142549 714179703112533487553557)
                      ·
                        rfl

theorem cell23_1390860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1390860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390860 prefixEnd_1390860 := by exact prefixLift 1390860
  have htrace : WordTrace (prefixWord ++ tailWord_1390860) baseStart_1390860 baseEnd_1390860 := by
    simpa [prefixWord, tailWord_1390860, baseEnd_1390860] using wordTrace_append hprefix tailTrace_1390860
  have hstable : (prefixWord ++ tailWord_1390860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390860).length < 2 ^ (prefixWord ++ tailWord_1390860).sum := by decide
  have hdescent : baseEnd_1390860 < baseStart_1390860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390867 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 3]
def baseStart_1390867 : Nat := 118140960795 + 1390867 * 2 ^ 59
def prefixEnd_1390867 : Nat := 4983230072969 + 3 ^ 40 * 1390867 * 2
def baseEnd_1390867 : Nat := 714183297477114960166025

theorem tailTrace_1390867 : CollatzResearch.WordTrace tailWord_1390867 prefixEnd_1390867 714183297477114960166025 := by
  unfold tailWord_1390867
  simp only [CollatzResearch.WordTrace]
  refine ⟨50729087052133875017090855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33819391368089250011393903 50729087052133875017090855)
  ·
    refine ⟨76093630578200812525636283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50729087052133875017090855 76093630578200812525636283)
    ·
      refine ⟨114140445867301218788454425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76093630578200812525636283 114140445867301218788454425)
      ·
        refine ⟨85605334400475914091340819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114140445867301218788454425 85605334400475914091340819)
        ·
          refine ⟨128408001600713871137011229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85605334400475914091340819 128408001600713871137011229)
          ·
            refine ⟨48153000600267701676379211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128408001600713871137011229 48153000600267701676379211)
            ·
              refine ⟨72229500900401552514568817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48153000600267701676379211 72229500900401552514568817)
              ·
                refine ⟨54172125675301164385926613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72229500900401552514568817 54172125675301164385926613)
                ·
                  refine ⟨1269659195514871040295155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 54172125675301164385926613 1269659195514871040295155)
                  ·
                    refine ⟨1904488793272306560442733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1269659195514871040295155 1904488793272306560442733)
                    ·
                      refine ⟨714183297477114960166025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904488793272306560442733 714183297477114960166025)
                      ·
                        rfl

theorem cell23_1390867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 3].length) (baseStart_1390867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390867 prefixEnd_1390867 := by exact prefixLift 1390867
  have htrace : WordTrace (prefixWord ++ tailWord_1390867) baseStart_1390867 baseEnd_1390867 := by
    simpa [prefixWord, tailWord_1390867, baseEnd_1390867] using wordTrace_append hprefix tailTrace_1390867
  have hstable : (prefixWord ++ tailWord_1390867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390867).length < 2 ^ (prefixWord ++ tailWord_1390867).sum := by decide
  have hdescent : baseEnd_1390867 < baseStart_1390867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390884 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1390884 : Nat := 118140960795 + 1390884 * 2 ^ 59
def prefixEnd_1390884 : Nat := 4983230072969 + 3 ^ 40 * 1390884 * 2
def baseEnd_1390884 : Nat := 714192026648241393653447

theorem tailTrace_1390884 : CollatzResearch.WordTrace tailWord_1390884 prefixEnd_1390884 714192026648241393653447 := by
  unfold tailWord_1390884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364853546536143460229853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33819804728714857946973137 25364853546536143460229853)
  ·
    refine ⟨9511820079951053797586195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25364853546536143460229853 9511820079951053797586195)
    ·
      refine ⟨14267730119926580696379293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9511820079951053797586195 14267730119926580696379293)
      ·
        refine ⟨5350398794972467761142235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14267730119926580696379293 5350398794972467761142235)
        ·
          refine ⟨8025598192458701641713353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350398794972467761142235 8025598192458701641713353)
          ·
            refine ⟨6019198644344026231285015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8025598192458701641713353 6019198644344026231285015)
            ·
              refine ⟨9028797966516039346927523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019198644344026231285015 9028797966516039346927523)
              ·
                refine ⟨13543196949774059020391285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028797966516039346927523 13543196949774059020391285)
                ·
                  refine ⟨1269674714041318033161683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13543196949774059020391285 1269674714041318033161683)
                  ·
                    refine ⟨1904512071061977049742525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1269674714041318033161683 1904512071061977049742525)
                    ·
                      refine ⟨714192026648241393653447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904512071061977049742525 714192026648241393653447)
                      ·
                        rfl

theorem cell23_1390884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1390884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390884 prefixEnd_1390884 := by exact prefixLift 1390884
  have htrace : WordTrace (prefixWord ++ tailWord_1390884) baseStart_1390884 baseEnd_1390884 := by
    simpa [prefixWord, tailWord_1390884, baseEnd_1390884] using wordTrace_append hprefix tailTrace_1390884
  have hstable : (prefixWord ++ tailWord_1390884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390884).length < 2 ^ (prefixWord ++ tailWord_1390884).sum := by decide
  have hdescent : baseEnd_1390884 < baseStart_1390884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390888 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_1390888 : Nat := 118140960795 + 1390888 * 2 ^ 59
def prefixEnd_1390888 : Nat := 4983230072969 + 3 ^ 40 * 1390888 * 2
def baseEnd_1390888 : Nat := 714194080570859378003429

theorem tailTrace_1390888 : CollatzResearch.WordTrace tailWord_1390888 prefixEnd_1390888 714194080570859378003429 := by
  unfold tailWord_1390888
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364926492528897801802659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33819901990038530402403545 25364926492528897801802659)
  ·
    refine ⟨38047389738793346702703989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25364926492528897801802659 38047389738793346702703989)
    ·
      refine ⟨3566942788011876253378499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38047389738793346702703989 3566942788011876253378499)
      ·
        refine ⟨5350414182017814380067749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566942788011876253378499 5350414182017814380067749)
        ·
          refine ⟨1003202659128340196262703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5350414182017814380067749 1003202659128340196262703)
          ·
            refine ⟨1504803988692510294394055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003202659128340196262703 1504803988692510294394055)
            ·
              refine ⟨2257205983038765441591083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504803988692510294394055 2257205983038765441591083)
              ·
                refine ⟨3385808974558148162386625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257205983038765441591083 3385808974558148162386625)
                ·
                  refine ⟨2539356730918611121789969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3385808974558148162386625 2539356730918611121789969)
                  ·
                    refine ⟨1904517548188958341342477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539356730918611121789969 1904517548188958341342477)
                    ·
                      refine ⟨714194080570859378003429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904517548188958341342477 714194080570859378003429)
                      ·
                        rfl

theorem cell23_1390888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_1390888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390888 prefixEnd_1390888 := by exact prefixLift 1390888
  have htrace : WordTrace (prefixWord ++ tailWord_1390888) baseStart_1390888 baseEnd_1390888 := by
    simpa [prefixWord, tailWord_1390888, baseEnd_1390888] using wordTrace_append hprefix tailTrace_1390888
  have hstable : (prefixWord ++ tailWord_1390888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390888).length < 2 ^ (prefixWord ++ tailWord_1390888).sum := by decide
  have hdescent : baseEnd_1390888 < baseStart_1390888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390904 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 1, 5]
def baseStart_1390904 : Nat := 118140960795 + 1390904 * 2 ^ 59
def prefixEnd_1390904 : Nat := 4983230072969 + 3 ^ 40 * 1390904 * 2
def baseEnd_1390904 : Nat := 238067432087110438467785

theorem tailTrace_1390904 : CollatzResearch.WordTrace tailWord_1390904 prefixEnd_1390904 238067432087110438467785 := by
  unfold tailWord_1390904
  simp only [CollatzResearch.WordTrace]
  refine ⟨25365218276499915168093883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33820291035333220224125177 25365218276499915168093883)
  ·
    refine ⟨38047827414749872752140825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25365218276499915168093883 38047827414749872752140825)
    ·
      refine ⟨28535870561062404564105619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38047827414749872752140825 28535870561062404564105619)
      ·
        refine ⟨42803805841593606846158429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28535870561062404564105619 42803805841593606846158429)
        ·
          refine ⟨16051427190597602567309411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42803805841593606846158429 16051427190597602567309411)
          ·
            refine ⟨24077140785896403850964117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16051427190597602567309411 24077140785896403850964117)
            ·
              refine ⟨1128615974338893930513943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24077140785896403850964117 1128615974338893930513943)
              ·
                refine ⟨1692923961508340895770915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128615974338893930513943 1692923961508340895770915)
                ·
                  refine ⟨2539385942262511343656373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692923961508340895770915 2539385942262511343656373)
                  ·
                    refine ⟨238067432087110438467785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2539385942262511343656373 238067432087110438467785)
                    ·
                      rfl

theorem cell23_1390904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_1390904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390904 prefixEnd_1390904 := by exact prefixLift 1390904
  have htrace : WordTrace (prefixWord ++ tailWord_1390904) baseStart_1390904 baseEnd_1390904 := by
    simpa [prefixWord, tailWord_1390904, baseEnd_1390904] using wordTrace_append hprefix tailTrace_1390904
  have hstable : (prefixWord ++ tailWord_1390904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390904).length < 2 ^ (prefixWord ++ tailWord_1390904).sum := by decide
  have hdescent : baseEnd_1390904 < baseStart_1390904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1390927 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 3]
def baseStart_1390927 : Nat := 118140960795 + 1390927 * 2 ^ 59
def prefixEnd_1390927 : Nat := 4983230072969 + 3 ^ 40 * 1390927 * 2
def baseEnd_1390927 : Nat := 714214106316384725415749

theorem tailTrace_1390927 : CollatzResearch.WordTrace tailWord_1390927 prefixEnd_1390927 714214106316384725415749 := by
  unfold tailWord_1390927
  simp only [CollatzResearch.WordTrace]
  refine ⟨50731275431916505264275035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33820850287944336842850023 50731275431916505264275035)
  ·
    refine ⟨76096913147874757896412553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50731275431916505264275035 76096913147874757896412553)
    ·
      refine ⟨57072684860906068422309415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76096913147874757896412553 57072684860906068422309415)
      ·
        refine ⟨85609027291359102633464123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57072684860906068422309415 85609027291359102633464123)
        ·
          refine ⟨128413540937038653950196185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85609027291359102633464123 128413540937038653950196185)
          ·
            refine ⟨96310155702778990462647139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128413540937038653950196185 96310155702778990462647139)
            ·
              refine ⟨144465233554168485693970709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96310155702778990462647139 144465233554168485693970709)
              ·
                refine ⟨6771807822851647766904877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144465233554168485693970709 6771807822851647766904877)
                ·
                  refine ⟨2539427933569367912589329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6771807822851647766904877 2539427933569367912589329)
                  ·
                    refine ⟨1904570950177025934441997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2539427933569367912589329 1904570950177025934441997)
                    ·
                      refine ⟨714214106316384725415749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904570950177025934441997 714214106316384725415749)
                      ·
                        rfl

theorem cell23_1390927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_1390927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1390927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1390927 prefixEnd_1390927 := by exact prefixLift 1390927
  have htrace : WordTrace (prefixWord ++ tailWord_1390927) baseStart_1390927 baseEnd_1390927 := by
    simpa [prefixWord, tailWord_1390927, baseEnd_1390927] using wordTrace_append hprefix tailTrace_1390927
  have hstable : (prefixWord ++ tailWord_1390927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1390927).length < 2 ^ (prefixWord ++ tailWord_1390927).sum := by decide
  have hdescent : baseEnd_1390927 < baseStart_1390927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1390927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391017 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 3]
def baseStart_1391017 : Nat := 118140960795 + 1391017 * 2 ^ 59
def prefixEnd_1391017 : Nat := 4983230072969 + 3 ^ 40 * 1391017 * 2
def baseEnd_1391017 : Nat := 714260319575289373290335

theorem tailTrace_1391017 : CollatzResearch.WordTrace tailWord_1391017 prefixEnd_1391017 714260319575289373290335 := by
  unfold tailWord_1391017
  simp only [CollatzResearch.WordTrace]
  refine ⟨50734558001590450635051305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33823038667726967090034203 50734558001590450635051305)
  ·
    refine ⟨38050918501192837976288479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50734558001590450635051305 38050918501192837976288479)
    ·
      refine ⟨57076377751789256964432719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38050918501192837976288479 57076377751789256964432719)
      ·
        refine ⟨85614566627683885446649079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57076377751789256964432719 85614566627683885446649079)
        ·
          refine ⟨128421849941525828169973619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85614566627683885446649079 128421849941525828169973619)
          ·
            refine ⟨192632774912288742254960429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128421849941525828169973619 192632774912288742254960429)
            ·
              refine ⟨72237290592108278345610161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192632774912288742254960429 72237290592108278345610161)
              ·
                refine ⟨54177967944081208759207621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72237290592108278345610161 54177967944081208759207621)
                ·
                  refine ⟨10158368989515226642351429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54177967944081208759207621 10158368989515226642351429)
                  ·
                    refine ⟨1904694185534104995440893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10158368989515226642351429 1904694185534104995440893)
                    ·
                      refine ⟨714260319575289373290335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904694185534104995440893 714260319575289373290335)
                      ·
                        rfl

theorem cell23_1391017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_1391017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391017 prefixEnd_1391017 := by exact prefixLift 1391017
  have htrace : WordTrace (prefixWord ++ tailWord_1391017) baseStart_1391017 baseEnd_1391017 := by
    simpa [prefixWord, tailWord_1391017, baseEnd_1391017] using wordTrace_append hprefix tailTrace_1391017
  have hstable : (prefixWord ++ tailWord_1391017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391017).length < 2 ^ (prefixWord ++ tailWord_1391017).sum := by decide
  have hdescent : baseEnd_1391017 < baseStart_1391017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391048 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_1391048 : Nat := 118140960795 + 1391048 * 2 ^ 59
def prefixEnd_1391048 : Nat := 4983230072969 + 3 ^ 40 * 1391048 * 2
def baseEnd_1391048 : Nat := 714276237475578752002693

theorem tailTrace_1391048 : CollatzResearch.WordTrace tailWord_1391048 prefixEnd_1391048 714276237475578752002693 := by
  unfold tailWord_1391048
  simp only [CollatzResearch.WordTrace]
  refine ⟨25367844332239071464714899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33823792442985428619619865 25367844332239071464714899)
  ·
    refine ⟨38051766498358607197072349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25367844332239071464714899 38051766498358607197072349)
    ·
      refine ⟨14269412436884477698902131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38051766498358607197072349 14269412436884477698902131)
      ·
        refine ⟨21404118655326716548353197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14269412436884477698902131 21404118655326716548353197)
        ·
          refine ⟨8026544495747518705632449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21404118655326716548353197 8026544495747518705632449)
          ·
            refine ⟨6019908371810639029224337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8026544495747518705632449 6019908371810639029224337)
            ·
              refine ⟨4514931278857979271918253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6019908371810639029224337 4514931278857979271918253)
              ·
                refine ⟨1693099229571742226969345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4514931278857979271918253 1693099229571742226969345)
                ·
                  refine ⟨1269824422178806670227009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693099229571742226969345 1269824422178806670227009)
                  ·
                    refine ⟨952368316634105002670257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269824422178806670227009 952368316634105002670257)
                    ·
                      refine ⟨714276237475578752002693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952368316634105002670257 714276237475578752002693)
                      ·
                        rfl

theorem cell23_1391048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_1391048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391048 prefixEnd_1391048 := by exact prefixLift 1391048
  have htrace : WordTrace (prefixWord ++ tailWord_1391048) baseStart_1391048 baseEnd_1391048 := by
    simpa [prefixWord, tailWord_1391048, baseEnd_1391048] using wordTrace_append hprefix tailTrace_1391048
  have hstable : (prefixWord ++ tailWord_1391048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391048).length < 2 ^ (prefixWord ++ tailWord_1391048).sum := by decide
  have hdescent : baseEnd_1391048 < baseStart_1391048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391071 : List Nat := [1, 1, 2, 3, 3, 3, 2, 3, 5]
def baseStart_1391071 : Nat := 118140960795 + 1391071 * 2 ^ 59
def prefixEnd_1391071 : Nat := 4983230072969 + 3 ^ 40 * 1391071 * 2
def baseEnd_1391071 : Nat := 79365338614514684668343

theorem tailTrace_1391071 : CollatzResearch.WordTrace tailWord_1391071 prefixEnd_1391071 79365338614514684668343 := by
  unfold tailWord_1391071
  simp only [CollatzResearch.WordTrace]
  refine ⟨50736527543394817857517067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33824351695596545238344711 50736527543394817857517067)
  ·
    refine ⟨76104791315092226786275601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50736527543394817857517067 76104791315092226786275601)
    ·
      refine ⟨57078593486319170089706701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76104791315092226786275601 57078593486319170089706701)
      ·
        refine ⟨21404472557369688783640013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57078593486319170089706701 21404472557369688783640013)
        ·
          refine ⟨8026677209013633293865005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21404472557369688783640013 8026677209013633293865005)
          ·
            refine ⟨3010003953380112485199377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8026677209013633293865005 3010003953380112485199377)
            ·
              refine ⟨2257502965035084363899533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010003953380112485199377 2257502965035084363899533)
              ·
                refine ⟨846563611888156636462325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257502965035084363899533 846563611888156636462325)
                ·
                  refine ⟨79365338614514684668343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 846563611888156636462325 79365338614514684668343)
                  ·
                    rfl

theorem cell23_1391071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 5].length) (baseStart_1391071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391071 prefixEnd_1391071 := by exact prefixLift 1391071
  have htrace : WordTrace (prefixWord ++ tailWord_1391071) baseStart_1391071 baseEnd_1391071 := by
    simpa [prefixWord, tailWord_1391071, baseEnd_1391071] using wordTrace_append hprefix tailTrace_1391071
  have hstable : (prefixWord ++ tailWord_1391071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391071).length < 2 ^ (prefixWord ++ tailWord_1391071).sum := by decide
  have hdescent : baseEnd_1391071 < baseStart_1391071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391094 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1391094 : Nat := 118140960795 + 1391094 * 2 ^ 59
def prefixEnd_1391094 : Nat := 4983230072969 + 3 ^ 40 * 1391094 * 2
def baseEnd_1391094 : Nat := 714299857585685572027481

theorem tailTrace_1391094 : CollatzResearch.WordTrace tailWord_1391094 prefixEnd_1391094 714299857585685572027481 := by
  unfold tailWord_1391094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3171085401394468299100271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33824910948207661857069557 3171085401394468299100271)
  ·
    refine ⟨4756628102091702448650407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3171085401394468299100271 4756628102091702448650407)
    ·
      refine ⟨7134942153137553672975611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756628102091702448650407 7134942153137553672975611)
      ·
        refine ⟨10702413229706330509463417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7134942153137553672975611 10702413229706330509463417)
        ·
          refine ⟨8026809922279747882097563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10702413229706330509463417 8026809922279747882097563)
          ·
            refine ⟨12040214883419621823146345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8026809922279747882097563 12040214883419621823146345)
            ·
              refine ⟨9030161162564716367359759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12040214883419621823146345 9030161162564716367359759)
              ·
                refine ⟨13545241743847074551039639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9030161162564716367359759 13545241743847074551039639)
                ·
                  refine ⟨20317862615770611826559459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13545241743847074551039639 20317862615770611826559459)
                  ·
                    refine ⟨30476793923655917739839189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20317862615770611826559459 30476793923655917739839189)
                    ·
                      refine ⟨714299857585685572027481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30476793923655917739839189 714299857585685572027481)
                      ·
                        rfl

theorem cell23_1391094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1391094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391094 prefixEnd_1391094 := by exact prefixLift 1391094
  have htrace : WordTrace (prefixWord ++ tailWord_1391094) baseStart_1391094 baseEnd_1391094 := by
    simpa [prefixWord, tailWord_1391094, baseEnd_1391094] using wordTrace_append hprefix tailTrace_1391094
  have hstable : (prefixWord ++ tailWord_1391094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391094).length < 2 ^ (prefixWord ++ tailWord_1391094).sum := by decide
  have hdescent : baseEnd_1391094 < baseStart_1391094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391147 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8]
def baseStart_1391147 : Nat := 118140960795 + 1391147 * 2 ^ 59
def prefixEnd_1391147 : Nat := 4983230072969 + 3 ^ 40 * 1391147 * 2
def baseEnd_1391147 : Nat := 714327072060373864664737

theorem tailTrace_1391147 : CollatzResearch.WordTrace tailWord_1391147 prefixEnd_1391147 714327072060373864664737 := by
  unfold tailWord_1391147
  simp only [CollatzResearch.WordTrace]
  refine ⟨50739299491119482837283695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33826199660746321891522463 50739299491119482837283695)
  ·
    refine ⟨76108949236679224255925543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50739299491119482837283695 76108949236679224255925543)
    ·
      refine ⟨114163423855018836383888315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76108949236679224255925543 114163423855018836383888315)
      ·
        refine ⟨171245135782528254575832473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114163423855018836383888315 171245135782528254575832473)
        ·
          refine ⟨128433851836896190931874355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171245135782528254575832473 128433851836896190931874355)
          ·
            refine ⟨192650777755344286397811533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128433851836896190931874355 192650777755344286397811533)
            ·
              refine ⟨72244041658254107399179325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192650777755344286397811533 72244041658254107399179325)
              ·
                refine ⟨27091515621845290274692247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72244041658254107399179325 27091515621845290274692247)
                ·
                  refine ⟨40637273432767935412038371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27091515621845290274692247 40637273432767935412038371)
                  ·
                    refine ⟨60955910149151903118057557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40637273432767935412038371 60955910149151903118057557)
                    ·
                      refine ⟨714327072060373864664737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 60955910149151903118057557 714327072060373864664737)
                      ·
                        rfl

theorem cell23_1391147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_1391147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391147 prefixEnd_1391147 := by exact prefixLift 1391147
  have htrace : WordTrace (prefixWord ++ tailWord_1391147) baseStart_1391147 baseEnd_1391147 := by
    simpa [prefixWord, tailWord_1391147, baseEnd_1391147] using wordTrace_append hprefix tailTrace_1391147
  have hstable : (prefixWord ++ tailWord_1391147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391147).length < 2 ^ (prefixWord ++ tailWord_1391147).sum := by decide
  have hdescent : baseEnd_1391147 < baseStart_1391147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391171 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 3]
def baseStart_1391171 : Nat := 118140960795 + 1391171 * 2 ^ 59
def prefixEnd_1391171 : Nat := 4983230072969 + 3 ^ 40 * 1391171 * 2
def baseEnd_1391171 : Nat := 714339395596081770764627

theorem tailTrace_1391171 : CollatzResearch.WordTrace tailWord_1391171 prefixEnd_1391171 714339395596081770764627 := by
  unfold tailWord_1391171
  simp only [CollatzResearch.WordTrace]
  refine ⟨50740174843032534936157367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33826783228688356624104911 50740174843032534936157367)
  ·
    refine ⟨76110262264548802404236051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50740174843032534936157367 76110262264548802404236051)
    ·
      refine ⟨114165393396823203606354077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76110262264548802404236051 114165393396823203606354077)
      ·
        refine ⟨42812022523808701352382779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114165393396823203606354077 42812022523808701352382779)
        ·
          refine ⟨64218033785713052028574169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42812022523808701352382779 64218033785713052028574169)
          ·
            refine ⟨48163525339284789021430627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64218033785713052028574169 48163525339284789021430627)
            ·
              refine ⟨72245288008927183532145941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48163525339284789021430627 72245288008927183532145941)
              ·
                refine ⟨3386497875418461728069341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72245288008927183532145941 3386497875418461728069341)
                ·
                  refine ⟨1269936703281923148026003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3386497875418461728069341 1269936703281923148026003)
                  ·
                    refine ⟨1904905054922884722039005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1269936703281923148026003 1904905054922884722039005)
                    ·
                      refine ⟨714339395596081770764627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1904905054922884722039005 714339395596081770764627)
                      ·
                        rfl

theorem cell23_1391171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_1391171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391171 prefixEnd_1391171 := by exact prefixLift 1391171
  have htrace : WordTrace (prefixWord ++ tailWord_1391171) baseStart_1391171 baseEnd_1391171 := by
    simpa [prefixWord, tailWord_1391171, baseEnd_1391171] using wordTrace_append hprefix tailTrace_1391171
  have hstable : (prefixWord ++ tailWord_1391171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391171).length < 2 ^ (prefixWord ++ tailWord_1391171).sum := by decide
  have hdescent : baseEnd_1391171 < baseStart_1391171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391172 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1391172 : Nat := 118140960795 + 1391172 * 2 ^ 59
def prefixEnd_1391172 : Nat := 4983230072969 + 3 ^ 40 * 1391172 * 2
def baseEnd_1391172 : Nat := 714339909076736266852123

theorem tailTrace_1391172 : CollatzResearch.WordTrace tailWord_1391172 prefixEnd_1391172 714339909076736266852123 := by
  unfold tailWord_1391172
  simp only [CollatzResearch.WordTrace]
  refine ⟨25370105658014456053471885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33826807544019274737962513 25370105658014456053471885)
  ·
    refine ⟨9513789621755421020051957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25370105658014456053471885 9513789621755421020051957)
    ·
      refine ⟨891917777039570720629871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9513789621755421020051957 891917777039570720629871)
      ·
        refine ⟨1337876665559356080944807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891917777039570720629871 1337876665559356080944807)
        ·
          refine ⟨2006814998339034121417211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337876665559356080944807 2006814998339034121417211)
          ·
            refine ⟨3010222497508551182125817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006814998339034121417211 3010222497508551182125817)
            ·
              refine ⟨2257666873131413386594363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010222497508551182125817 2257666873131413386594363)
              ·
                refine ⟨3386500309697120079891545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257666873131413386594363 3386500309697120079891545)
                ·
                  refine ⟨2539875232272840059918659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3386500309697120079891545 2539875232272840059918659)
                  ·
                    refine ⟨3809812848409260089877989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2539875232272840059918659 3809812848409260089877989)
                    ·
                      refine ⟨714339909076736266852123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3809812848409260089877989 714339909076736266852123)
                      ·
                        rfl

theorem cell23_1391172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1391172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391172 prefixEnd_1391172 := by exact prefixLift 1391172
  have htrace : WordTrace (prefixWord ++ tailWord_1391172) baseStart_1391172 baseEnd_1391172 := by
    simpa [prefixWord, tailWord_1391172, baseEnd_1391172] using wordTrace_append hprefix tailTrace_1391172
  have hstable : (prefixWord ++ tailWord_1391172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391172).length < 2 ^ (prefixWord ++ tailWord_1391172).sum := by decide
  have hdescent : baseEnd_1391172 < baseStart_1391172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391204 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_1391204 : Nat := 118140960795 + 1391204 * 2 ^ 59
def prefixEnd_1391204 : Nat := 4983230072969 + 3 ^ 40 * 1391204 * 2
def baseEnd_1391204 : Nat := 238118780152560047217325

theorem tailTrace_1391204 : CollatzResearch.WordTrace tailWord_1391204 prefixEnd_1391204 238118780152560047217325 := by
  unfold tailWord_1391204
  simp only [CollatzResearch.WordTrace]
  refine ⟨25370689225956490786054333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33827585634608654381405777 25370689225956490786054333)
  ·
    refine ⟨9514008459733684044770375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25370689225956490786054333 9514008459733684044770375)
    ·
      refine ⟨14271012689600526067155563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9514008459733684044770375 14271012689600526067155563)
      ·
        refine ⟨21406519034400789100733345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14271012689600526067155563 21406519034400789100733345)
        ·
          refine ⟨16054889275800591825550009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21406519034400789100733345 16054889275800591825550009)
          ·
            refine ⟨12041166956850443869162507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16054889275800591825550009 12041166956850443869162507)
            ·
              refine ⟨18061750435275665803743761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12041166956850443869162507 18061750435275665803743761)
              ·
                refine ⟨13546312826456749352807821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18061750435275665803743761 13546312826456749352807821)
                ·
                  refine ⟨5079867309921281007302933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13546312826456749352807821 5079867309921281007302933)
                  ·
                    refine ⟨238118780152560047217325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5079867309921281007302933 238118780152560047217325)
                    ·
                      rfl

theorem cell23_1391204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_1391204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391204 prefixEnd_1391204 := by exact prefixLift 1391204
  have htrace : WordTrace (prefixWord ++ tailWord_1391204) baseStart_1391204 baseEnd_1391204 := by
    simpa [prefixWord, tailWord_1391204, baseEnd_1391204] using wordTrace_append hprefix tailTrace_1391204
  have hstable : (prefixWord ++ tailWord_1391204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391204).length < 2 ^ (prefixWord ++ tailWord_1391204).sum := by decide
  have hdescent : baseEnd_1391204 < baseStart_1391204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391224 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1391224 : Nat := 118140960795 + 1391224 * 2 ^ 59
def prefixEnd_1391224 : Nat := 4983230072969 + 3 ^ 40 * 1391224 * 2
def baseEnd_1391224 : Nat := 714366610070770063401883

theorem tailTrace_1391224 : CollatzResearch.WordTrace tailWord_1391224 prefixEnd_1391224 714366610070770063401883 := by
  unfold tailWord_1391224
  simp only [CollatzResearch.WordTrace]
  refine ⟨25371053955920262493918363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33828071941227016658557817 25371053955920262493918363)
  ·
    refine ⟨38056580933880393740877545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25371053955920262493918363 38056580933880393740877545)
    ·
      refine ⟨28542435700410295305658159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38056580933880393740877545 28542435700410295305658159)
      ·
        refine ⟨42813653550615442958487239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28542435700410295305658159 42813653550615442958487239)
        ·
          refine ⟨64220480325923164437730859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42813653550615442958487239 64220480325923164437730859)
          ·
            refine ⟨96330720488884746656596289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64220480325923164437730859 96330720488884746656596289)
            ·
              refine ⟨72248040366663559992447217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96330720488884746656596289 72248040366663559992447217)
              ·
                refine ⟨54186030274997669994335413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72248040366663559992447217 54186030274997669994335413)
                ·
                  refine ⟨5079940338281031561968945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54186030274997669994335413 5079940338281031561968945)
                  ·
                    refine ⟨3809955253710773671476709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5079940338281031561968945 3809955253710773671476709)
                    ·
                      refine ⟨714366610070770063401883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3809955253710773671476709 714366610070770063401883)
                      ·
                        rfl

theorem cell23_1391224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1391224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391224 prefixEnd_1391224 := by exact prefixLift 1391224
  have htrace : WordTrace (prefixWord ++ tailWord_1391224) baseStart_1391224 baseEnd_1391224 := by
    simpa [prefixWord, tailWord_1391224, baseEnd_1391224] using wordTrace_append hprefix tailTrace_1391224
  have hstable : (prefixWord ++ tailWord_1391224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391224).length < 2 ^ (prefixWord ++ tailWord_1391224).sum := by decide
  have hdescent : baseEnd_1391224 < baseStart_1391224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391228 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_1391228 : Nat := 118140960795 + 1391228 * 2 ^ 59
def prefixEnd_1391228 : Nat := 4983230072969 + 3 ^ 40 * 1391228 * 2
def baseEnd_1391228 : Nat := 714368663993388047751865

theorem tailTrace_1391228 : CollatzResearch.WordTrace tailWord_1391228 prefixEnd_1391228 714368663993388047751865 := by
  unfold tailWord_1391228
  simp only [CollatzResearch.WordTrace]
  refine ⟨25371126901913016835491169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33828169202550689113988225 25371126901913016835491169)
  ·
    refine ⟨19028345176434762626618377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25371126901913016835491169 19028345176434762626618377)
    ·
      refine ⟨14271258882326071969963783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19028345176434762626618377 14271258882326071969963783)
      ·
        refine ⟨21406888323489107954945675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14271258882326071969963783 21406888323489107954945675)
        ·
          refine ⟨32110332485233661932418513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21406888323489107954945675 32110332485233661932418513)
          ·
            refine ⟨24082749363925246449313885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32110332485233661932418513 24082749363925246449313885)
            ·
              refine ⟨9031031011471967418492707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24082749363925246449313885 9031031011471967418492707)
              ·
                refine ⟨13546546517207951127739061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9031031011471967418492707 13546546517207951127739061)
                ·
                  refine ⟨1269988735988245418225537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13546546517207951127739061 1269988735988245418225537)
                  ·
                    refine ⟨952491551991184063669153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269988735988245418225537 952491551991184063669153)
                    ·
                      refine ⟨714368663993388047751865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952491551991184063669153 714368663993388047751865)
                      ·
                        rfl

theorem cell23_1391228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_1391228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391228 prefixEnd_1391228 := by exact prefixLift 1391228
  have htrace : WordTrace (prefixWord ++ tailWord_1391228) baseStart_1391228 baseEnd_1391228 := by
    simpa [prefixWord, tailWord_1391228, baseEnd_1391228] using wordTrace_append hprefix tailTrace_1391228
  have hstable : (prefixWord ++ tailWord_1391228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391228).length < 2 ^ (prefixWord ++ tailWord_1391228).sum := by decide
  have hdescent : baseEnd_1391228 < baseStart_1391228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391242 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_1391242 : Nat := 118140960795 + 1391242 * 2 ^ 59
def prefixEnd_1391242 : Nat := 4983230072969 + 3 ^ 40 * 1391242 * 2
def baseEnd_1391242 : Nat := 238125284240850330992267

theorem tailTrace_1391242 : CollatzResearch.WordTrace tailWord_1391242 prefixEnd_1391242 238125284240850330992267 := by
  unfold tailWord_1391242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12685691106443828515497995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33828509617183542707994653 12685691106443828515497995)
  ·
    refine ⟨19028536659665742773246993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12685691106443828515497995 19028536659665742773246993)
    ·
      refine ⟨14271402494749307079935245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19028536659665742773246993 14271402494749307079935245)
      ·
        refine ⟨5351775935530990154975717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14271402494749307079935245 5351775935530990154975717)
        ·
          refine ⟨1003457987912060654057947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5351775935530990154975717 1003457987912060654057947)
          ·
            refine ⟨1505186981868090981086921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003457987912060654057947 1505186981868090981086921)
            ·
              refine ⟨1128890236401068235815191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505186981868090981086921 1128890236401068235815191)
              ·
                refine ⟨1693335354601602353722787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128890236401068235815191 1693335354601602353722787)
                ·
                  refine ⟨2540003031902403530584181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693335354601602353722787 2540003031902403530584181)
                  ·
                    refine ⟨238125284240850330992267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2540003031902403530584181 238125284240850330992267)
                    ·
                      rfl

theorem cell23_1391242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_1391242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391242 prefixEnd_1391242 := by exact prefixLift 1391242
  have htrace : WordTrace (prefixWord ++ tailWord_1391242) baseStart_1391242 baseEnd_1391242 := by
    simpa [prefixWord, tailWord_1391242, baseEnd_1391242] using wordTrace_append hprefix tailTrace_1391242
  have hstable : (prefixWord ++ tailWord_1391242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391242).length < 2 ^ (prefixWord ++ tailWord_1391242).sum := by decide
  have hdescent : baseEnd_1391242 < baseStart_1391242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391261 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1391261 : Nat := 118140960795 + 1391261 * 2 ^ 59
def prefixEnd_1391261 : Nat := 4983230072969 + 3 ^ 40 * 1391261 * 2
def baseEnd_1391261 : Nat := 714385608854986418639213

theorem tailTrace_1391261 : CollatzResearch.WordTrace tailWord_1391261 prefixEnd_1391261 714385608854986418639213 := by
  unfold tailWord_1391261
  simp only [CollatzResearch.WordTrace]
  refine ⟨50743457412706480306933637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33828971608470986871289091 50743457412706480306933637)
  ·
    refine ⟨9514398264882465057550057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50743457412706480306933637 9514398264882465057550057)
    ·
      refine ⟨7135798698661848793162543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9514398264882465057550057 7135798698661848793162543)
      ·
        refine ⟨10703698047992773189743815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7135798698661848793162543 10703698047992773189743815)
        ·
          refine ⟨16055547071989159784615723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10703698047992773189743815 16055547071989159784615723)
          ·
            refine ⟨24083320607983739676923585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16055547071989159784615723 24083320607983739676923585)
            ·
              refine ⟨18062490455987804757692689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24083320607983739676923585 18062490455987804757692689)
              ·
                refine ⟨13546867841990853568269517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18062490455987804757692689 13546867841990853568269517)
                ·
                  refine ⟨5080075440746570088101069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13546867841990853568269517 5080075440746570088101069)
                  ·
                    refine ⟨1905028290279963783037901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5080075440746570088101069 1905028290279963783037901)
                    ·
                      refine ⟨714385608854986418639213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905028290279963783037901 714385608854986418639213)
                      ·
                        rfl

theorem cell23_1391261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1391261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391261 prefixEnd_1391261 := by exact prefixLift 1391261
  have htrace : WordTrace (prefixWord ++ tailWord_1391261) baseStart_1391261 baseEnd_1391261 := by
    simpa [prefixWord, tailWord_1391261, baseEnd_1391261] using wordTrace_append hprefix tailTrace_1391261
  have hstable : (prefixWord ++ tailWord_1391261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391261).length < 2 ^ (prefixWord ++ tailWord_1391261).sum := by decide
  have hdescent : baseEnd_1391261 < baseStart_1391261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391262 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_1391262 : Nat := 118140960795 + 1391262 * 2 ^ 59
def prefixEnd_1391262 : Nat := 4983230072969 + 3 ^ 40 * 1391262 * 2
def baseEnd_1391262 : Nat := 714386122335640914726709

theorem tailTrace_1391262 : CollatzResearch.WordTrace tailWord_1391262 prefixEnd_1391262 714386122335640914726709 := by
  unfold tailWord_1391262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342936735712857184715005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33828995923801904985146693 6342936735712857184715005)
  ·
    refine ⟨2378601275892321444268127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6342936735712857184715005 2378601275892321444268127)
    ·
      refine ⟨3567901913838482166402191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2378601275892321444268127 3567901913838482166402191)
      ·
        refine ⟨5351852870757723249603287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567901913838482166402191 5351852870757723249603287)
        ·
          refine ⟨8027779306136584874404931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351852870757723249603287 8027779306136584874404931)
          ·
            refine ⟨12041668959204877311607397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027779306136584874404931 12041668959204877311607397)
            ·
              refine ⟨2257812929850914495926387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12041668959204877311607397 2257812929850914495926387)
              ·
                refine ⟨3386719394776371743889581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257812929850914495926387 3386719394776371743889581)
                ·
                  refine ⟨1270019773041139403958593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3386719394776371743889581 1270019773041139403958593)
                  ·
                    refine ⟨952514829780854552968945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1270019773041139403958593 952514829780854552968945)
                    ·
                      refine ⟨714386122335640914726709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952514829780854552968945 714386122335640914726709)
                      ·
                        rfl

theorem cell23_1391262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_1391262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391262 prefixEnd_1391262 := by exact prefixLift 1391262
  have htrace : WordTrace (prefixWord ++ tailWord_1391262) baseStart_1391262 baseEnd_1391262 := by
    simpa [prefixWord, tailWord_1391262, baseEnd_1391262] using wordTrace_append hprefix tailTrace_1391262
  have hstable : (prefixWord ++ tailWord_1391262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391262).length < 2 ^ (prefixWord ++ tailWord_1391262).sum := by decide
  have hdescent : baseEnd_1391262 < baseStart_1391262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391302 : List Nat := [6, 1, 2, 1, 3, 1, 9]
def baseStart_1391302 : Nat := 118140960795 + 1391302 * 2 ^ 59
def prefixEnd_1391302 : Nat := 4983230072969 + 3 ^ 40 * 1391302 * 2
def baseEnd_1391302 : Nat := 8819835327923713064525

theorem tailTrace_1391302 : CollatzResearch.WordTrace tailWord_1391302 prefixEnd_1391302 8819835327923713064525 := by
  unfold tailWord_1391302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1585779775173685759661755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33829968537038629539450773 1585779775173685759661755)
  ·
    refine ⟨2378669662760528639492633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1585779775173685759661755 2378669662760528639492633)
    ·
      refine ⟨1784002247070396479619475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2378669662760528639492633 1784002247070396479619475)
      ·
        refine ⟨2676003370605594719429213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784002247070396479619475 2676003370605594719429213)
        ·
          refine ⟨1003501263977098019785955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2676003370605594719429213 1003501263977098019785955)
          ·
            refine ⟨1505251895965647029678933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003501263977098019785955 1505251895965647029678933)
            ·
              refine ⟨8819835327923713064525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1505251895965647029678933 8819835327923713064525)
              ·
                rfl

theorem cell23_1391302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 9].length) (baseStart_1391302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391302 prefixEnd_1391302 := by exact prefixLift 1391302
  have htrace : WordTrace (prefixWord ++ tailWord_1391302) baseStart_1391302 baseEnd_1391302 := by
    simpa [prefixWord, tailWord_1391302, baseEnd_1391302] using wordTrace_append hprefix tailTrace_1391302
  have hstable : (prefixWord ++ tailWord_1391302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391302).length < 2 ^ (prefixWord ++ tailWord_1391302).sum := by decide
  have hdescent : baseEnd_1391302 < baseStart_1391302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391321 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 3]
def baseStart_1391321 : Nat := 118140960795 + 1391321 * 2 ^ 59
def prefixEnd_1391321 : Nat := 4983230072969 + 3 ^ 40 * 1391321 * 2
def baseEnd_1391321 : Nat := 714416417694256183888937

theorem tailTrace_1391321 : CollatzResearch.WordTrace tailWord_1391321 prefixEnd_1391321 714416417694256183888937 := by
  unfold tailWord_1391321
  simp only [CollatzResearch.WordTrace]
  refine ⟨50745645792489110554117817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33830430528326073702745211 50745645792489110554117817)
  ·
    refine ⟨38059234344366832915588363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50745645792489110554117817 38059234344366832915588363)
    ·
      refine ⟨57088851516550249373382545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38059234344366832915588363 57088851516550249373382545)
      ·
        refine ⟨42816638637412687030036909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57088851516550249373382545 42816638637412687030036909)
        ·
          refine ⟨16056239489029757636263841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42816638637412687030036909 16056239489029757636263841)
          ·
            refine ⟨12042179616772318227197881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16056239489029757636263841 12042179616772318227197881)
            ·
              refine ⟨9031634712579238670398411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12042179616772318227197881 9031634712579238670398411)
              ·
                refine ⟨13547452068868858005597617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9031634712579238670398411 13547452068868858005597617)
                ·
                  refine ⟨10160589051651643504198213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13547452068868858005597617 10160589051651643504198213)
                  ·
                    refine ⟨1905110447184683157037165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10160589051651643504198213 1905110447184683157037165)
                    ·
                      refine ⟨714416417694256183888937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905110447184683157037165 714416417694256183888937)
                      ·
                        rfl

theorem cell23_1391321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_1391321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391321 prefixEnd_1391321 := by exact prefixLift 1391321
  have htrace : WordTrace (prefixWord ++ tailWord_1391321) baseStart_1391321 baseEnd_1391321 := by
    simpa [prefixWord, tailWord_1391321, baseEnd_1391321] using wordTrace_append hprefix tailTrace_1391321
  have hstable : (prefixWord ++ tailWord_1391321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391321).length < 2 ^ (prefixWord ++ tailWord_1391321).sum := by decide
  have hdescent : baseEnd_1391321 < baseStart_1391321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391341 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 9]
def baseStart_1391341 : Nat := 118140960795 + 1391341 * 2 ^ 59
def prefixEnd_1391341 : Nat := 4983230072969 + 3 ^ 40 * 1391341 * 2
def baseEnd_1391341 : Nat := 79380743034149567293205

theorem tailTrace_1391341 : CollatzResearch.WordTrace tailWord_1391341 prefixEnd_1391341 79380743034149567293205 := by
  unfold tailWord_1391341
  simp only [CollatzResearch.WordTrace]
  refine ⟨50746375252416653969845877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33830916834944435979897251 50746375252416653969845877)
  ·
    refine ⟨4757472679914061309673051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50746375252416653969845877 4757472679914061309673051)
    ·
      refine ⟨7136209019871091964509577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757472679914061309673051 7136209019871091964509577)
      ·
        refine ⟨5352156764903318973382183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7136209019871091964509577 5352156764903318973382183)
        ·
          refine ⟨8028235147354978460073275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5352156764903318973382183 8028235147354978460073275)
          ·
            refine ⟨12042352721032467690109913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8028235147354978460073275 12042352721032467690109913)
            ·
              refine ⟨9031764540774350767582435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12042352721032467690109913 9031764540774350767582435)
              ·
                refine ⟨13547646811161526151373653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9031764540774350767582435 13547646811161526151373653)
                ·
                  refine ⟨79380743034149567293205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13547646811161526151373653 79380743034149567293205)
                  ·
                    rfl

theorem cell23_1391341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_1391341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391341 prefixEnd_1391341 := by exact prefixLift 1391341
  have htrace : WordTrace (prefixWord ++ tailWord_1391341) baseStart_1391341 baseEnd_1391341 := by
    simpa [prefixWord, tailWord_1391341, baseEnd_1391341] using wordTrace_append hprefix tailTrace_1391341
  have hstable : (prefixWord ++ tailWord_1391341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391341).length < 2 ^ (prefixWord ++ tailWord_1391341).sum := by decide
  have hdescent : baseEnd_1391341 < baseStart_1391341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391351 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_1391351 : Nat := 118140960795 + 1391351 * 2 ^ 59
def prefixEnd_1391351 : Nat := 4983230072969 + 3 ^ 40 * 1391351 * 2
def baseEnd_1391351 : Nat := 714431822113891066513799

theorem tailTrace_1391351 : CollatzResearch.WordTrace tailWord_1391351 prefixEnd_1391351 714431822113891066513799 := by
  unfold tailWord_1391351
  simp only [CollatzResearch.WordTrace]
  refine ⟨50746739982380425677709907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33831159988253617118473271 50746739982380425677709907)
  ·
    refine ⟨76120109973570638516564861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50746739982380425677709907 76120109973570638516564861)
    ·
      refine ⟨28545041240088989443711823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76120109973570638516564861 28545041240088989443711823)
      ·
        refine ⟨42817561860133484165567735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28545041240088989443711823 42817561860133484165567735)
        ·
          refine ⟨64226342790200226248351603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42817561860133484165567735 64226342790200226248351603)
          ·
            refine ⟨96339514185300339372527405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64226342790200226248351603 96339514185300339372527405)
            ·
              refine ⟨36127317819487627264697777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96339514185300339372527405 36127317819487627264697777)
              ·
                refine ⟨27095488364615720448523333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36127317819487627264697777 27095488364615720448523333)
                ·
                  refine ⟨5080404068365447584098125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27095488364615720448523333 5080404068365447584098125)
                  ·
                    refine ⟨1905151525637042844036797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5080404068365447584098125 1905151525637042844036797)
                    ·
                      refine ⟨714431822113891066513799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905151525637042844036797 714431822113891066513799)
                      ·
                        rfl

theorem cell23_1391351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_1391351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391351 prefixEnd_1391351 := by exact prefixLift 1391351
  have htrace : WordTrace (prefixWord ++ tailWord_1391351) baseStart_1391351 baseEnd_1391351 := by
    simpa [prefixWord, tailWord_1391351, baseEnd_1391351] using wordTrace_append hprefix tailTrace_1391351
  have hstable : (prefixWord ++ tailWord_1391351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391351).length < 2 ^ (prefixWord ++ tailWord_1391351).sum := by decide
  have hdescent : baseEnd_1391351 < baseStart_1391351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391381 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1391381 : Nat := 118140960795 + 1391381 * 2 ^ 59
def prefixEnd_1391381 : Nat := 4983230072969 + 3 ^ 40 * 1391381 * 2
def baseEnd_1391381 : Nat := 714447226533525949138661

theorem tailTrace_1391381 : CollatzResearch.WordTrace tailWord_1391381 prefixEnd_1391381 714447226533525949138661 := by
  unfold tailWord_1391381
  simp only [CollatzResearch.WordTrace]
  refine ⟨50747834172271740801301997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33831889448181160534201331 50747834172271740801301997)
  ·
    refine ⟨19030437814601902800488249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50747834172271740801301997 19030437814601902800488249)
    ·
      refine ⟨14272828360951427100366187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19030437814601902800488249 14272828360951427100366187)
      ·
        refine ⟨21409242541427140650549281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14272828360951427100366187 21409242541427140650549281)
        ·
          refine ⟨16056931906070355487911961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21409242541427140650549281 16056931906070355487911961)
          ·
            refine ⟨12042698929552766615933971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16056931906070355487911961 12042698929552766615933971)
            ·
              refine ⟨18064048394329149923900957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12042698929552766615933971 18064048394329149923900957)
              ·
                refine ⟨6774018147873431221462859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18064048394329149923900957 6774018147873431221462859)
                ·
                  refine ⟨10161027221810146832194289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6774018147873431221462859 10161027221810146832194289)
                  ·
                    refine ⟨7620770416357610124145717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10161027221810146832194289 7620770416357610124145717)
                    ·
                      refine ⟨714447226533525949138661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7620770416357610124145717 714447226533525949138661)
                      ·
                        rfl

theorem cell23_1391381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1391381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391381 prefixEnd_1391381 := by exact prefixLift 1391381
  have htrace : WordTrace (prefixWord ++ tailWord_1391381) baseStart_1391381 baseEnd_1391381 := by
    simpa [prefixWord, tailWord_1391381, baseEnd_1391381] using wordTrace_append hprefix tailTrace_1391381
  have hstable : (prefixWord ++ tailWord_1391381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391381).length < 2 ^ (prefixWord ++ tailWord_1391381).sum := by decide
  have hdescent : baseEnd_1391381 < baseStart_1391381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391485 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_1391485 : Nat := 118140960795 + 1391485 * 2 ^ 59
def prefixEnd_1391485 : Nat := 4983230072969 + 3 ^ 40 * 1391485 * 2
def baseEnd_1391485 : Nat := 714500628521593542238183

theorem tailTrace_1391485 : CollatzResearch.WordTrace tailWord_1391485 prefixEnd_1391485 714500628521593542238183 := by
  unfold tailWord_1391485
  simp only [CollatzResearch.WordTrace]
  refine ⟨50751627363894966563087909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33834418242596644375391939 50751627363894966563087909)
  ·
    refine ⟨9515930130730306230578983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50751627363894966563087909 9515930130730306230578983)
    ·
      refine ⟨14273895196095459345868475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9515930130730306230578983 14273895196095459345868475)
      ·
        refine ⟨21410842794143189018802713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14273895196095459345868475 21410842794143189018802713)
        ·
          refine ⟨16058132095607391764102035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21410842794143189018802713 16058132095607391764102035)
          ·
            refine ⟨24087198143411087646153053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16058132095607391764102035 24087198143411087646153053)
            ·
              refine ⟨9032699303779157867307395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24087198143411087646153053 9032699303779157867307395)
              ·
                refine ⟨13549048955668736800961093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9032699303779157867307395 13549048955668736800961093)
                ·
                  refine ⟨2540446679187888150180205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13549048955668736800961093 2540446679187888150180205)
                  ·
                    refine ⟨952667504695458056317577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540446679187888150180205 952667504695458056317577)
                    ·
                      refine ⟨714500628521593542238183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952667504695458056317577 714500628521593542238183)
                      ·
                        rfl

theorem cell23_1391485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_1391485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391485 prefixEnd_1391485 := by exact prefixLift 1391485
  have htrace : WordTrace (prefixWord ++ tailWord_1391485) baseStart_1391485 baseEnd_1391485 := by
    simpa [prefixWord, tailWord_1391485, baseEnd_1391485] using wordTrace_append hprefix tailTrace_1391485
  have hstable : (prefixWord ++ tailWord_1391485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391485).length < 2 ^ (prefixWord ++ tailWord_1391485).sum := by decide
  have hdescent : baseEnd_1391485 < baseStart_1391485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391486 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1391486 : Nat := 118140960795 + 1391486 * 2 ^ 59
def prefixEnd_1391486 : Nat := 4983230072969 + 3 ^ 40 * 1391486 * 2
def baseEnd_1391486 : Nat := 238167047334082679441893

theorem tailTrace_1391486 : CollatzResearch.WordTrace tailWord_1391486 prefixEnd_1391486 238167047334082679441893 := by
  unfold tailWord_1391486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343957979611417966734289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33834442557927562489249541 6343957979611417966734289)
  ·
    refine ⟨4757968484708563475050717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6343957979611417966734289 4757968484708563475050717)
    ·
      refine ⟨1784238181765711303144019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4757968484708563475050717 1784238181765711303144019)
      ·
        refine ⟨2676357272648566954716029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784238181765711303144019 2676357272648566954716029)
        ·
          refine ⟨1003633977243212608018511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2676357272648566954716029 1003633977243212608018511)
          ·
            refine ⟨1505450965864818912027767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003633977243212608018511 1505450965864818912027767)
            ·
              refine ⟨2258176448797228368041651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505450965864818912027767 2258176448797228368041651)
              ·
                refine ⟨3387264673195842552062477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258176448797228368041651 3387264673195842552062477)
                ·
                  refine ⟨1270224252448440957023429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3387264673195842552062477 1270224252448440957023429)
                  ·
                    refine ⟨238167047334082679441893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1270224252448440957023429 238167047334082679441893)
                    ·
                      rfl

theorem cell23_1391486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1391486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391486 prefixEnd_1391486 := by exact prefixLift 1391486
  have htrace : WordTrace (prefixWord ++ tailWord_1391486) baseStart_1391486 baseEnd_1391486 := by
    simpa [prefixWord, tailWord_1391486, baseEnd_1391486] using wordTrace_append hprefix tailTrace_1391486
  have hstable : (prefixWord ++ tailWord_1391486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391486).length < 2 ^ (prefixWord ++ tailWord_1391486).sum := by decide
  have hdescent : baseEnd_1391486 < baseStart_1391486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391586 : List Nat := [3, 3, 3, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1391586 : Nat := 118140960795 + 1391586 * 2 ^ 59
def prefixEnd_1391586 : Nat := 4983230072969 + 3 ^ 40 * 1391586 * 2
def baseEnd_1391586 : Nat := 714552490067697647075219

theorem tailTrace_1391586 : CollatzResearch.WordTrace tailWord_1391586 prefixEnd_1391586 714552490067697647075219 := by
  unfold tailWord_1391586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12688827784132265203128653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33836874091019373875009741 12688827784132265203128653)
  ·
    refine ⟨4758310419049599451173245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12688827784132265203128653 4758310419049599451173245)
    ·
      refine ⟨1784366407143599794189967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4758310419049599451173245 1784366407143599794189967)
      ·
        refine ⟨2676549610715399691284951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784366407143599794189967 2676549610715399691284951)
        ·
          refine ⟨4014824416073099536927427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676549610715399691284951 4014824416073099536927427)
          ·
            refine ⟨6022236624109649305391141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014824416073099536927427 6022236624109649305391141)
            ·
              refine ⟨1129169367020559244760839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6022236624109649305391141 1129169367020559244760839)
              ·
                refine ⟨1693754050530838867141259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129169367020559244760839 1693754050530838867141259)
                ·
                  refine ⟨2540631075796258300711889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693754050530838867141259 2540631075796258300711889)
                  ·
                    refine ⟨1905473306847193725533917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2540631075796258300711889 1905473306847193725533917)
                    ·
                      refine ⟨714552490067697647075219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905473306847193725533917 714552490067697647075219)
                      ·
                        rfl

theorem cell23_1391586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1391586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391586 prefixEnd_1391586 := by exact prefixLift 1391586
  have htrace : WordTrace (prefixWord ++ tailWord_1391586) baseStart_1391586 baseEnd_1391586 := by
    simpa [prefixWord, tailWord_1391586, baseEnd_1391586] using wordTrace_append hprefix tailTrace_1391586
  have hstable : (prefixWord ++ tailWord_1391586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391586).length < 2 ^ (prefixWord ++ tailWord_1391586).sum := by decide
  have hdescent : baseEnd_1391586 < baseStart_1391586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391588 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_1391588 : Nat := 118140960795 + 1391588 * 2 ^ 59
def prefixEnd_1391588 : Nat := 4983230072969 + 3 ^ 40 * 1391588 * 2
def baseEnd_1391588 : Nat := 714553517029006639250209

theorem tailTrace_1391588 : CollatzResearch.WordTrace tailWord_1391588 prefixEnd_1391588 714553517029006639250209 := by
  unfold tailWord_1391588
  simp only [CollatzResearch.WordTrace]
  refine ⟨25377692041260907577043709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33836922721681210102724945 25377692041260907577043709)
  ·
    refine ⟨9516634515472840341391391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25377692041260907577043709 9516634515472840341391391)
    ·
      refine ⟨14274951773209260512087087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9516634515472840341391391 14274951773209260512087087)
      ·
        refine ⟨21412427659813890768130631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14274951773209260512087087 21412427659813890768130631)
        ·
          refine ⟨32118641489720836152195947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21412427659813890768130631 32118641489720836152195947)
          ·
            refine ⟨48177962234581254228293921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32118641489720836152195947 48177962234581254228293921)
            ·
              refine ⟨36133471675935940671220441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48177962234581254228293921 36133471675935940671220441)
              ·
                refine ⟨27100103756951955503415331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36133471675935940671220441 27100103756951955503415331)
                ·
                  refine ⟨40650155635427933255122997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27100103756951955503415331 40650155635427933255122997)
                  ·
                    refine ⟨3810952090821368742667781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40650155635427933255122997 3810952090821368742667781)
                    ·
                      refine ⟨714553517029006639250209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3810952090821368742667781 714553517029006639250209)
                      ·
                        rfl

theorem cell23_1391588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_1391588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391588 prefixEnd_1391588 := by exact prefixLift 1391588
  have htrace : WordTrace (prefixWord ++ tailWord_1391588) baseStart_1391588 baseEnd_1391588 := by
    simpa [prefixWord, tailWord_1391588, baseEnd_1391588] using wordTrace_append hprefix tailTrace_1391588
  have hstable : (prefixWord ++ tailWord_1391588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391588).length < 2 ^ (prefixWord ++ tailWord_1391588).sum := by decide
  have hdescent : baseEnd_1391588 < baseStart_1391588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391599 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 3]
def baseStart_1391599 : Nat := 118140960795 + 1391599 * 2 ^ 59
def prefixEnd_1391599 : Nat := 4983230072969 + 3 ^ 40 * 1391599 * 2
def baseEnd_1391599 : Nat := 714559165316206096212659

theorem tailTrace_1391599 : CollatzResearch.WordTrace tailWord_1391599 prefixEnd_1391599 714559165316206096212659 := by
  unfold tailWord_1391599
  simp only [CollatzResearch.WordTrace]
  refine ⟨50755785285481964032737851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33837190190321309355158567 50755785285481964032737851)
  ·
    refine ⟨76133677928222946049106777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50755785285481964032737851 76133677928222946049106777)
    ·
      refine ⟨57100258446167209536830083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76133677928222946049106777 57100258446167209536830083)
      ·
        refine ⟨85650387669250814305245125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57100258446167209536830083 85650387669250814305245125)
        ·
          refine ⟨16059447687984527682233461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85650387669250814305245125 16059447687984527682233461)
          ·
            refine ⟨1505573220748549470209387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16059447687984527682233461 1505573220748549470209387)
            ·
              refine ⟨2258359831122824205314081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505573220748549470209387 2258359831122824205314081)
              ·
                refine ⟨1693769873342118153985561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258359831122824205314081 1693769873342118153985561)
                ·
                  refine ⟨1270327405006588615489171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693769873342118153985561 1270327405006588615489171)
                  ·
                    refine ⟨1905491107509882923233757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1270327405006588615489171 1905491107509882923233757)
                    ·
                      refine ⟨714559165316206096212659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905491107509882923233757 714559165316206096212659)
                      ·
                        rfl

theorem cell23_1391599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 3].length) (baseStart_1391599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391599 prefixEnd_1391599 := by exact prefixLift 1391599
  have htrace : WordTrace (prefixWord ++ tailWord_1391599) baseStart_1391599 baseEnd_1391599 := by
    simpa [prefixWord, tailWord_1391599, baseEnd_1391599] using wordTrace_append hprefix tailTrace_1391599
  have hstable : (prefixWord ++ tailWord_1391599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391599).length < 2 ^ (prefixWord ++ tailWord_1391599).sum := by decide
  have hdescent : baseEnd_1391599 < baseStart_1391599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391608 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1391608 : Nat := 118140960795 + 1391608 * 2 ^ 59
def prefixEnd_1391608 : Nat := 4983230072969 + 3 ^ 40 * 1391608 * 2
def baseEnd_1391608 : Nat := 714563786642096561000117

theorem tailTrace_1391608 : CollatzResearch.WordTrace tailWord_1391608 prefixEnd_1391608 714563786642096561000117 := by
  unfold tailWord_1391608
  simp only [CollatzResearch.WordTrace]
  refine ⟨25378056771224679284907739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33837409028299572379876985 25378056771224679284907739)
  ·
    refine ⟨38067085156837018927361609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25378056771224679284907739 38067085156837018927361609)
    ·
      refine ⟨28550313867627764195521207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38067085156837018927361609 28550313867627764195521207)
      ·
        refine ⟨42825470801441646293281811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28550313867627764195521207 42825470801441646293281811)
        ·
          refine ⟨64238206202162469439922717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42825470801441646293281811 64238206202162469439922717)
          ·
            refine ⟨24089327325810926039971019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64238206202162469439922717 24089327325810926039971019)
            ·
              refine ⟨36133990988716389059956529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24089327325810926039971019 36133990988716389059956529)
              ·
                refine ⟨27100493241537291794967397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36133990988716389059956529 27100493241537291794967397)
                ·
                  refine ⟨5081342482788242211556387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27100493241537291794967397 5081342482788242211556387)
                  ·
                    refine ⟨7622013724182363317334581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5081342482788242211556387 7622013724182363317334581)
                    ·
                      refine ⟨714563786642096561000117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7622013724182363317334581 714563786642096561000117)
                      ·
                        rfl

theorem cell23_1391608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1391608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391608 prefixEnd_1391608 := by exact prefixLift 1391608
  have htrace : WordTrace (prefixWord ++ tailWord_1391608) baseStart_1391608 baseEnd_1391608 := by
    simpa [prefixWord, tailWord_1391608, baseEnd_1391608] using wordTrace_append hprefix tailTrace_1391608
  have hstable : (prefixWord ++ tailWord_1391608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391608).length < 2 ^ (prefixWord ++ tailWord_1391608).sum := by decide
  have hdescent : baseEnd_1391608 < baseStart_1391608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391634 : List Nat := [3, 2, 5, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1391634 : Nat := 118140960795 + 1391634 * 2 ^ 59
def prefixEnd_1391634 : Nat := 4983230072969 + 3 ^ 40 * 1391634 * 2
def baseEnd_1391634 : Nat := 714577137139113459274999

theorem tailTrace_1391634 : CollatzResearch.WordTrace tailWord_1391634 prefixEnd_1391634 714577137139113459274999 := by
  unfold tailWord_1391634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12689265460088791252565489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33838041226903443340174637 12689265460088791252565489)
  ·
    refine ⟨9516949095066593439424117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12689265460088791252565489 9516949095066593439424117)
    ·
      refine ⟨892213977662493134946011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9516949095066593439424117 892213977662493134946011)
      ·
        refine ⟨1338320966493739702419017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892213977662493134946011 1338320966493739702419017)
        ·
          refine ⟨1003740724870304776814263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338320966493739702419017 1003740724870304776814263)
          ·
            refine ⟨1505611087305457165221395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003740724870304776814263 1505611087305457165221395)
            ·
              refine ⟨2258416630958185747832093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505611087305457165221395 2258416630958185747832093)
              ·
                refine ⟨846906236609319655437035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2258416630958185747832093 846906236609319655437035)
                ·
                  refine ⟨1270359354913979483155553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846906236609319655437035 1270359354913979483155553)
                  ·
                    refine ⟨952769516185484612366665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1270359354913979483155553 952769516185484612366665)
                    ·
                      refine ⟨714577137139113459274999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952769516185484612366665 714577137139113459274999)
                      ·
                        rfl

theorem cell23_1391634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1391634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391634 prefixEnd_1391634 := by exact prefixLift 1391634
  have htrace : WordTrace (prefixWord ++ tailWord_1391634) baseStart_1391634 baseEnd_1391634 := by
    simpa [prefixWord, tailWord_1391634, baseEnd_1391634] using wordTrace_append hprefix tailTrace_1391634
  have hstable : (prefixWord ++ tailWord_1391634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391634).length < 2 ^ (prefixWord ++ tailWord_1391634).sum := by decide
  have hdescent : baseEnd_1391634 < baseStart_1391634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391639 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1391639 : Nat := 118140960795 + 1391639 * 2 ^ 59
def prefixEnd_1391639 : Nat := 4983230072969 + 3 ^ 40 * 1391639 * 2
def baseEnd_1391639 : Nat := 714579704542385939712475

theorem tailTrace_1391639 : CollatzResearch.WordTrace tailWord_1391639 prefixEnd_1391639 714579704542385939712475 := by
  unfold tailWord_1391639
  simp only [CollatzResearch.WordTrace]
  refine ⟨50757244205337050864193971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33838162803558033909462647 50757244205337050864193971)
  ·
    refine ⟨76135866308005576296290957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50757244205337050864193971 76135866308005576296290957)
    ·
      refine ⟨28550949865502091111109109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76135866308005576296290957 28550949865502091111109109)
      ·
        refine ⟨2676651549890821041666479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28550949865502091111109109 2676651549890821041666479)
        ·
          refine ⟨4014977324836231562499719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676651549890821041666479 4014977324836231562499719)
          ·
            refine ⟨6022465987254347343749579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014977324836231562499719 6022465987254347343749579)
            ·
              refine ⟨9033698980881521015624369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6022465987254347343749579 9033698980881521015624369)
              ·
                refine ⟨6775274235661140761718277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9033698980881521015624369 6775274235661140761718277)
                ·
                  refine ⟨1270363919186463892822177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6775274235661140761718277 1270363919186463892822177)
                  ·
                    refine ⟨952772939389847919616633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1270363919186463892822177 952772939389847919616633)
                    ·
                      refine ⟨714579704542385939712475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952772939389847919616633 714579704542385939712475)
                      ·
                        rfl

theorem cell23_1391639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1391639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391639 prefixEnd_1391639 := by exact prefixLift 1391639
  have htrace : WordTrace (prefixWord ++ tailWord_1391639) baseStart_1391639 baseEnd_1391639 := by
    simpa [prefixWord, tailWord_1391639, baseEnd_1391639] using wordTrace_append hprefix tailTrace_1391639
  have hstable : (prefixWord ++ tailWord_1391639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391639).length < 2 ^ (prefixWord ++ tailWord_1391639).sum := by decide
  have hdescent : baseEnd_1391639 < baseStart_1391639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391673 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1391673 : Nat := 118140960795 + 1391673 * 2 ^ 59
def prefixEnd_1391673 : Nat := 4983230072969 + 3 ^ 40 * 1391673 * 2
def baseEnd_1391673 : Nat := 714597162884638806687319

theorem tailTrace_1391673 : CollatzResearch.WordTrace tailWord_1391673 prefixEnd_1391673 714597162884638806687319 := by
  unfold tailWord_1391673
  simp only [CollatzResearch.WordTrace]
  refine ⟨50758484287213874670931673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33838989524809249780621115 50758484287213874670931673)
  ·
    refine ⟨38068863215410406003198755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50758484287213874670931673 38068863215410406003198755)
    ·
      refine ⟨57103294823115609004798133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38068863215410406003198755 57103294823115609004798133)
      ·
        refine ⟨5353433889667088344199825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57103294823115609004798133 5353433889667088344199825)
        ·
          refine ⟨4015075417250316258149869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5353433889667088344199825 4015075417250316258149869)
          ·
            refine ⟨1505653281468868596806201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4015075417250316258149869 1505653281468868596806201)
            ·
              refine ⟨1129239961101651447604651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505653281468868596806201 1129239961101651447604651)
              ·
                refine ⟨1693859941652477171406977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129239961101651447604651 1693859941652477171406977)
                ·
                  refine ⟨1270394956239357878555233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693859941652477171406977 1270394956239357878555233)
                  ·
                    refine ⟨952796217179518408916425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1270394956239357878555233 952796217179518408916425)
                    ·
                      refine ⟨714597162884638806687319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952796217179518408916425 714597162884638806687319)
                      ·
                        rfl

theorem cell23_1391673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1391673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391673 prefixEnd_1391673 := by exact prefixLift 1391673
  have htrace : WordTrace (prefixWord ++ tailWord_1391673) baseStart_1391673 baseEnd_1391673 := by
    simpa [prefixWord, tailWord_1391673, baseEnd_1391673] using wordTrace_append hprefix tailTrace_1391673
  have hstable : (prefixWord ++ tailWord_1391673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391673).length < 2 ^ (prefixWord ++ tailWord_1391673).sum := by decide
  have hdescent : baseEnd_1391673 < baseStart_1391673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391705 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 7, 4]
def baseStart_1391705 : Nat := 118140960795 + 1391705 * 2 ^ 59
def prefixEnd_1391705 : Nat := 4983230072969 + 3 ^ 40 * 1391705 * 2
def baseEnd_1391705 : Nat := 238204531421860893829057

theorem tailTrace_1391705 : CollatzResearch.WordTrace tailWord_1391705 prefixEnd_1391705 238204531421860893829057 := by
  unfold tailWord_1391705
  simp only [CollatzResearch.WordTrace]
  refine ⟨50759651423097944136096569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33839767615398629424064379 50759651423097944136096569)
  ·
    refine ⟨38069738567323458102072427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50759651423097944136096569 38069738567323458102072427)
    ·
      refine ⟨57104607850985187153108641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38069738567323458102072427 57104607850985187153108641)
      ·
        refine ⟨42828455888238890364831481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57104607850985187153108641 42828455888238890364831481)
        ·
          refine ⟨32121341916179167773623611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42828455888238890364831481 32121341916179167773623611)
          ·
            refine ⟨48182012874268751660435417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32121341916179167773623611 48182012874268751660435417)
            ·
              refine ⟨36136509655701563745326563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48182012874268751660435417 36136509655701563745326563)
              ·
                refine ⟨54204764483552345617989845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36136509655701563745326563 54204764483552345617989845)
                ·
                  refine ⟨1270424167583258100421637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 54204764483552345617989845 1270424167583258100421637)
                  ·
                    refine ⟨238204531421860893829057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1270424167583258100421637 238204531421860893829057)
                    ·
                      rfl

theorem cell23_1391705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_1391705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391705 prefixEnd_1391705 := by exact prefixLift 1391705
  have htrace : WordTrace (prefixWord ++ tailWord_1391705) baseStart_1391705 baseEnd_1391705 := by
    simpa [prefixWord, tailWord_1391705, baseEnd_1391705] using wordTrace_append hprefix tailTrace_1391705
  have hstable : (prefixWord ++ tailWord_1391705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391705).length < 2 ^ (prefixWord ++ tailWord_1391705).sum := by decide
  have hdescent : baseEnd_1391705 < baseStart_1391705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391712 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 2, 4, 2]
def baseStart_1391712 : Nat := 118140960795 + 1391712 * 2 ^ 59
def prefixEnd_1391712 : Nat := 4983230072969 + 3 ^ 40 * 1391712 * 2
def baseEnd_1391712 : Nat := 714617188630164154099639

theorem tailTrace_1391712 : CollatzResearch.WordTrace tailWord_1391712 prefixEnd_1391712 714617188630164154099639 := by
  unfold tailWord_1391712
  simp only [CollatzResearch.WordTrace]
  refine ⟨25379953367036292165800695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33839937822715056221067593 25379953367036292165800695)
  ·
    refine ⟨38069930050554438248701043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25379953367036292165800695 38069930050554438248701043)
    ·
      refine ⟨57104895075831657373051565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38069930050554438248701043 57104895075831657373051565)
      ·
        refine ⟨21414335653436871514894337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57104895075831657373051565 21414335653436871514894337)
        ·
          refine ⟨16060751740077653636170753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21414335653436871514894337 16060751740077653636170753)
          ·
            refine ⟨12045563805058240227128065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16060751740077653636170753 12045563805058240227128065)
            ·
              refine ⟨9034172853793680170346049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12045563805058240227128065 9034172853793680170346049)
              ·
                refine ⟨6775629640345260127759537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9034172853793680170346049 6775629640345260127759537)
                ·
                  refine ⟨5081722230258945095819653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6775629640345260127759537 5081722230258945095819653)
                  ·
                    refine ⟨952822918173552205466185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5081722230258945095819653 952822918173552205466185)
                    ·
                      refine ⟨714617188630164154099639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952822918173552205466185 714617188630164154099639)
                      ·
                        rfl

theorem cell23_1391712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_1391712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391712 prefixEnd_1391712 := by exact prefixLift 1391712
  have htrace : WordTrace (prefixWord ++ tailWord_1391712) baseStart_1391712 baseEnd_1391712 := by
    simpa [prefixWord, tailWord_1391712, baseEnd_1391712] using wordTrace_append hprefix tailTrace_1391712
  have hstable : (prefixWord ++ tailWord_1391712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391712).length < 2 ^ (prefixWord ++ tailWord_1391712).sum := by decide
  have hdescent : baseEnd_1391712 < baseStart_1391712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391715 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1391715 : Nat := 118140960795 + 1391715 * 2 ^ 59
def prefixEnd_1391715 : Nat := 4983230072969 + 3 ^ 40 * 1391715 * 2
def baseEnd_1391715 : Nat := 714618729072127642362125

theorem tailTrace_1391715 : CollatzResearch.WordTrace tailWord_1391715 prefixEnd_1391715 714618729072127642362125 := by
  unfold tailWord_1391715
  simp only [CollatzResearch.WordTrace]
  refine ⟨50760016153061715843960599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33840010768707810562640399 50760016153061715843960599)
  ·
    refine ⟨76140024229592573765940899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50760016153061715843960599 76140024229592573765940899)
    ·
      refine ⟨114210036344388860648911349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76140024229592573765940899 114210036344388860648911349)
      ·
        refine ⟨10707190907286455685835439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114210036344388860648911349 10707190907286455685835439)
        ·
          refine ⟨16060786360929683528753159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10707190907286455685835439 16060786360929683528753159)
          ·
            refine ⟨24091179541394525293129739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16060786360929683528753159 24091179541394525293129739)
            ·
              refine ⟨36136769312091787939694609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24091179541394525293129739 36136769312091787939694609)
              ·
                refine ⟨27102576984068840954770957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36136769312091787939694609 27102576984068840954770957)
                ·
                  refine ⟨10163466369025815358039109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27102576984068840954770957 10163466369025815358039109)
                  ·
                    refine ⟨1905649944192340379632333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10163466369025815358039109 1905649944192340379632333)
                    ·
                      refine ⟨714618729072127642362125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905649944192340379632333 714618729072127642362125)
                      ·
                        rfl

theorem cell23_1391715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1391715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391715 prefixEnd_1391715 := by exact prefixLift 1391715
  have htrace : WordTrace (prefixWord ++ tailWord_1391715) baseStart_1391715 baseEnd_1391715 := by
    simpa [prefixWord, tailWord_1391715, baseEnd_1391715] using wordTrace_append hprefix tailTrace_1391715
  have hstable : (prefixWord ++ tailWord_1391715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391715).length < 2 ^ (prefixWord ++ tailWord_1391715).sum := by decide
  have hdescent : baseEnd_1391715 < baseStart_1391715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391735 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 6]
def baseStart_1391735 : Nat := 118140960795 + 1391735 * 2 ^ 59
def prefixEnd_1391735 : Nat := 4983230072969 + 3 ^ 40 * 1391735 * 2
def baseEnd_1391735 : Nat := 79403222076135284901337

theorem tailTrace_1391735 : CollatzResearch.WordTrace tailWord_1391735 prefixEnd_1391735 79403222076135284901337 := by
  unfold tailWord_1391735
  simp only [CollatzResearch.WordTrace]
  refine ⟨50760745612989259259688659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33840497075326172839792439 50760745612989259259688659)
  ·
    refine ⟨76141118419483888889532989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50760745612989259259688659 76141118419483888889532989)
    ·
      refine ⟨28552919407306458333574871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76141118419483888889532989 28552919407306458333574871)
      ·
        refine ⟨42829379110959687500362307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28552919407306458333574871 42829379110959687500362307)
        ·
          refine ⟨64244068666439531250543461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42829379110959687500362307 64244068666439531250543461)
          ·
            refine ⟨12045762874957412109476899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64244068666439531250543461 12045762874957412109476899)
            ·
              refine ⟨18068644312436118164215349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12045762874957412109476899 18068644312436118164215349)
              ·
                refine ⟨1693935404290886077895189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18068644312436118164215349 1693935404290886077895189)
                ·
                  refine ⟨79403222076135284901337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1693935404290886077895189 79403222076135284901337)
                  ·
                    rfl

theorem cell23_1391735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 6].length) (baseStart_1391735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391735 prefixEnd_1391735 := by exact prefixLift 1391735
  have htrace : WordTrace (prefixWord ++ tailWord_1391735) baseStart_1391735 baseEnd_1391735 := by
    simpa [prefixWord, tailWord_1391735, baseEnd_1391735] using wordTrace_append hprefix tailTrace_1391735
  have hstable : (prefixWord ++ tailWord_1391735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391735).length < 2 ^ (prefixWord ++ tailWord_1391735).sum := by decide
  have hdescent : baseEnd_1391735 < baseStart_1391735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391765 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1391765 : Nat := 118140960795 + 1391765 * 2 ^ 59
def prefixEnd_1391765 : Nat := 4983230072969 + 3 ^ 40 * 1391765 * 2
def baseEnd_1391765 : Nat := 238214801034950815578965

theorem tailTrace_1391765 : CollatzResearch.WordTrace tailWord_1391765 prefixEnd_1391765 238214801034950815578965 := by
  unfold tailWord_1391765
  simp only [CollatzResearch.WordTrace]
  refine ⟨50761839802880574383280749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33841226535253716255520499 50761839802880574383280749)
  ·
    refine ⟨19035689926080215393730281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50761839802880574383280749 19035689926080215393730281)
    ·
      refine ⟨14276767444560161545297711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19035689926080215393730281 14276767444560161545297711)
      ·
        refine ⟨21415151166840242317946567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14276767444560161545297711 21415151166840242317946567)
        ·
          refine ⟨32122726750260363476919851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21415151166840242317946567 32122726750260363476919851)
          ·
            refine ⟨48184090125390545215379777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32122726750260363476919851 48184090125390545215379777)
            ·
              refine ⟨36138067594042908911534833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48184090125390545215379777 36138067594042908911534833)
              ·
                refine ⟨27103550695532181683651125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36138067594042908911534833 27103550695532181683651125)
                ·
                  refine ⟨2540957877706142032842293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27103550695532181683651125 2540957877706142032842293)
                  ·
                    refine ⟨238214801034950815578965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2540957877706142032842293 238214801034950815578965)
                    ·
                      rfl

theorem cell23_1391765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1391765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391765 prefixEnd_1391765 := by exact prefixLift 1391765
  have htrace : WordTrace (prefixWord ++ tailWord_1391765) baseStart_1391765 baseEnd_1391765 := by
    simpa [prefixWord, tailWord_1391765, baseEnd_1391765] using wordTrace_append hprefix tailTrace_1391765
  have hstable : (prefixWord ++ tailWord_1391765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391765).length < 2 ^ (prefixWord ++ tailWord_1391765).sum := by decide
  have hdescent : baseEnd_1391765 < baseStart_1391765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391786 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 6]
def baseStart_1391786 : Nat := 118140960795 + 1391786 * 2 ^ 59
def prefixEnd_1391786 : Nat := 4983230072969 + 3 ^ 40 * 1391786 * 2
def baseEnd_1391786 : Nat := 79406131799844096063811

theorem tailTrace_1391786 : CollatzResearch.WordTrace tailWord_1391786 prefixEnd_1391786 79406131799844096063811 := by
  unfold tailWord_1391786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690651433951123742448803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33841737157202996646530141 12690651433951123742448803)
  ·
    refine ⟨19035977150926685613673205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12690651433951123742448803 19035977150926685613673205)
    ·
      refine ⟨1784622857899376776281863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19035977150926685613673205 1784622857899376776281863)
      ·
        refine ⟨2676934286849065164422795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784622857899376776281863 2676934286849065164422795)
        ·
          refine ⟨4015401430273597746634193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676934286849065164422795 4015401430273597746634193)
          ·
            refine ⟨3011551072705198309975645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4015401430273597746634193 3011551072705198309975645)
            ·
              refine ⟨1129331652264449366240867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3011551072705198309975645 1129331652264449366240867)
              ·
                refine ⟨1693997478396674049361301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129331652264449366240867 1693997478396674049361301)
                ·
                  refine ⟨79406131799844096063811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1693997478396674049361301 79406131799844096063811)
                  ·
                    rfl

theorem cell23_1391786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_1391786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391786 prefixEnd_1391786 := by exact prefixLift 1391786
  have htrace : WordTrace (prefixWord ++ tailWord_1391786) baseStart_1391786 baseEnd_1391786 := by
    simpa [prefixWord, tailWord_1391786, baseEnd_1391786] using wordTrace_append hprefix tailTrace_1391786
  have hstable : (prefixWord ++ tailWord_1391786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391786).length < 2 ^ (prefixWord ++ tailWord_1391786).sum := by decide
  have hdescent : baseEnd_1391786 < baseStart_1391786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391802 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2]
def baseStart_1391802 : Nat := 118140960795 + 1391802 * 2 ^ 59
def prefixEnd_1391802 : Nat := 4983230072969 + 3 ^ 40 * 1391802 * 2
def baseEnd_1391802 : Nat := 714663401889068801974225

theorem tailTrace_1391802 : CollatzResearch.WordTrace tailWord_1391802 prefixEnd_1391802 714663401889068801974225 := by
  unfold tailWord_1391802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690797325936632425594415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33842126202497686468251773 12690797325936632425594415)
  ·
    refine ⟨19036195988904948638391623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12690797325936632425594415 19036195988904948638391623)
    ·
      refine ⟨28554293983357422957587435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19036195988904948638391623 28554293983357422957587435)
      ·
        refine ⟨42831440975036134436381153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28554293983357422957587435 42831440975036134436381153)
        ·
          refine ⟨32123580731277100827285865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42831440975036134436381153 32123580731277100827285865)
          ·
            refine ⟨24092685548457825620464399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32123580731277100827285865 24092685548457825620464399)
            ·
              refine ⟨36139028322686738430696599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24092685548457825620464399 36139028322686738430696599)
              ·
                refine ⟨54208542484030107646044899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36139028322686738430696599 54208542484030107646044899)
                ·
                  refine ⟨81312813726045161469067349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54208542484030107646044899 81312813726045161469067349)
                  ·
                    refine ⟨952884535852091735965633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81312813726045161469067349 952884535852091735965633)
                    ·
                      refine ⟨714663401889068801974225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952884535852091735965633 714663401889068801974225)
                      ·
                        rfl

theorem cell23_1391802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_1391802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391802 prefixEnd_1391802 := by exact prefixLift 1391802
  have htrace : WordTrace (prefixWord ++ tailWord_1391802) baseStart_1391802 baseEnd_1391802 := by
    simpa [prefixWord, tailWord_1391802, baseEnd_1391802] using wordTrace_append hprefix tailTrace_1391802
  have hstable : (prefixWord ++ tailWord_1391802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391802).length < 2 ^ (prefixWord ++ tailWord_1391802).sum := by decide
  have hdescent : baseEnd_1391802 < baseStart_1391802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391829 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_1391829 : Nat := 118140960795 + 1391829 * 2 ^ 59
def prefixEnd_1391829 : Nat := 4983230072969 + 3 ^ 40 * 1391829 * 2
def baseEnd_1391829 : Nat := 238225755288913398778867

theorem tailTrace_1391829 : CollatzResearch.WordTrace tailWord_1391829 prefixEnd_1391829 238225755288913398778867 := by
  unfold tailWord_1391829
  simp only [CollatzResearch.WordTrace]
  refine ⟨50764174074648713313610541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33842782716432475542407027 50764174074648713313610541)
  ·
    refine ⟨19036565277993267492603953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50764174074648713313610541 19036565277993267492603953)
    ·
      refine ⟨14277423958494950619452965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19036565277993267492603953 14277423958494950619452965)
      ·
        refine ⟨2677016992217803241147431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14277423958494950619452965 2677016992217803241147431)
        ·
          refine ⟨4015525488326704861721147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677016992217803241147431 4015525488326704861721147)
          ·
            refine ⟨6023288232490057292581721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015525488326704861721147 6023288232490057292581721)
            ·
              refine ⟨4517466174367542969436291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6023288232490057292581721 4517466174367542969436291)
              ·
                refine ⟨6776199261551314454154437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517466174367542969436291 6776199261551314454154437)
                ·
                  refine ⟨1270537361540871460153957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6776199261551314454154437 1270537361540871460153957)
                  ·
                    refine ⟨238225755288913398778867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1270537361540871460153957 238225755288913398778867)
                    ·
                      rfl

theorem cell23_1391829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_1391829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391829 prefixEnd_1391829 := by exact prefixLift 1391829
  have htrace : WordTrace (prefixWord ++ tailWord_1391829) baseStart_1391829 baseEnd_1391829 := by
    simpa [prefixWord, tailWord_1391829, baseEnd_1391829] using wordTrace_append hprefix tailTrace_1391829
  have hstable : (prefixWord ++ tailWord_1391829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391829).length < 2 ^ (prefixWord ++ tailWord_1391829).sum := by decide
  have hdescent : baseEnd_1391829 < baseStart_1391829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391830 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1391830 : Nat := 118140960795 + 1391830 * 2 ^ 59
def prefixEnd_1391830 : Nat := 4983230072969 + 3 ^ 40 * 1391830 * 2
def baseEnd_1391830 : Nat := 714677779347394692424097

theorem tailTrace_1391830 : CollatzResearch.WordTrace tailWord_1391830 prefixEnd_1391830 714677779347394692424097 := by
  unfold tailWord_1391830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172763159227818155274809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33842807031763393656264629 3172763159227818155274809)
  ·
    refine ⟨2379572369420863616456107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3172763159227818155274809 2379572369420863616456107)
    ·
      refine ⟨3569358554131295424684161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2379572369420863616456107 3569358554131295424684161)
      ·
        refine ⟨2677018915598471568513121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3569358554131295424684161 2677018915598471568513121)
        ·
          refine ⟨2007764186698853676384841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677018915598471568513121 2007764186698853676384841)
          ·
            refine ⟨1505823140024140257288631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2007764186698853676384841 1505823140024140257288631)
            ·
              refine ⟨2258734710036210385932947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505823140024140257288631 2258734710036210385932947)
              ·
                refine ⟨3388102065054315578899421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258734710036210385932947 3388102065054315578899421)
                ·
                  refine ⟨1270538274395368342087283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3388102065054315578899421 1270538274395368342087283)
                  ·
                    refine ⟨1905807411593052513130925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1270538274395368342087283 1905807411593052513130925)
                    ·
                      refine ⟨714677779347394692424097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905807411593052513130925 714677779347394692424097)
                      ·
                        rfl

theorem cell23_1391830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1391830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391830 prefixEnd_1391830 := by exact prefixLift 1391830
  have htrace : WordTrace (prefixWord ++ tailWord_1391830) baseStart_1391830 baseEnd_1391830 := by
    simpa [prefixWord, tailWord_1391830, baseEnd_1391830] using wordTrace_append hprefix tailTrace_1391830
  have hstable : (prefixWord ++ tailWord_1391830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391830).length < 2 ^ (prefixWord ++ tailWord_1391830).sum := by decide
  have hdescent : baseEnd_1391830 < baseStart_1391830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391886 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1391886 : Nat := 118140960795 + 1391886 * 2 ^ 59
def prefixEnd_1391886 : Nat := 4983230072969 + 3 ^ 40 * 1391886 * 2
def baseEnd_1391886 : Nat := 714706534264046473323839

theorem tailTrace_1391886 : CollatzResearch.WordTrace tailWord_1391886 prefixEnd_1391886 714706534264046473323839 := by
  unfold tailWord_1391886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345781629430276506054439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33844168690294808032290341 6345781629430276506054439)
  ·
    refine ⟨9518672444145414759081659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6345781629430276506054439 9518672444145414759081659)
    ·
      refine ⟨14278008666218122138622489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9518672444145414759081659 14278008666218122138622489)
      ·
        refine ⟨10708506499663591603966867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14278008666218122138622489 10708506499663591603966867)
        ·
          refine ⟨16062759749495387405950301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708506499663591603966867 16062759749495387405950301)
          ·
            refine ⟨6023534906060770277231363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16062759749495387405950301 6023534906060770277231363)
            ·
              refine ⟨9035302359091155415847045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023534906060770277231363 9035302359091155415847045)
              ·
                refine ⟨1694119192329591640471321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9035302359091155415847045 1694119192329591640471321)
                ·
                  refine ⟨1270589394247193730353491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1694119192329591640471321 1270589394247193730353491)
                  ·
                    refine ⟨1905884091370790595530237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1270589394247193730353491 1905884091370790595530237)
                    ·
                      refine ⟨714706534264046473323839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905884091370790595530237 714706534264046473323839)
                      ·
                        rfl

theorem cell23_1391886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1391886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391886 prefixEnd_1391886 := by exact prefixLift 1391886
  have htrace : WordTrace (prefixWord ++ tailWord_1391886) baseStart_1391886 baseEnd_1391886 := by
    simpa [prefixWord, tailWord_1391886, baseEnd_1391886] using wordTrace_append hprefix tailTrace_1391886
  have hstable : (prefixWord ++ tailWord_1391886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391886).length < 2 ^ (prefixWord ++ tailWord_1391886).sum := by decide
  have hdescent : baseEnd_1391886 < baseStart_1391886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391943 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_1391943 : Nat := 118140960795 + 1391943 * 2 ^ 59
def prefixEnd_1391943 : Nat := 4983230072969 + 3 ^ 40 * 1391943 * 2
def baseEnd_1391943 : Nat := 714735802661352750311077

theorem tailTrace_1391943 : CollatzResearch.WordTrace tailWord_1391943 prefixEnd_1391943 714735802661352750311077 := by
  unfold tailWord_1391943
  simp only [CollatzResearch.WordTrace]
  refine ⟨50768331996235710783260483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33845554664157140522173655 50768331996235710783260483)
  ·
    refine ⟨76152497994353566174890725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50768331996235710783260483 76152497994353566174890725)
    ·
      refine ⟨14278593373941293657792011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76152497994353566174890725 14278593373941293657792011)
      ·
        refine ⟨21417890060911940486688017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14278593373941293657792011 21417890060911940486688017)
        ·
          refine ⟨16063417545683955365016013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21417890060911940486688017 16063417545683955365016013)
          ·
            refine ⟨6023781579631483261881005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16063417545683955365016013 6023781579631483261881005)
            ·
              refine ⟨2258918092361806223205377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6023781579631483261881005 2258918092361806223205377)
              ·
                refine ⟨1694188569271354667404033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2258918092361806223205377 1694188569271354667404033)
                ·
                  refine ⟨1270641426953516000553025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1694188569271354667404033 1270641426953516000553025)
                  ·
                    refine ⟨952981070215137000414769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1270641426953516000553025 952981070215137000414769)
                    ·
                      refine ⟨714735802661352750311077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952981070215137000414769 714735802661352750311077)
                      ·
                        rfl

theorem cell23_1391943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_1391943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391943 prefixEnd_1391943 := by exact prefixLift 1391943
  have htrace : WordTrace (prefixWord ++ tailWord_1391943) baseStart_1391943 baseEnd_1391943 := by
    simpa [prefixWord, tailWord_1391943, baseEnd_1391943] using wordTrace_append hprefix tailTrace_1391943
  have hstable : (prefixWord ++ tailWord_1391943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391943).length < 2 ^ (prefixWord ++ tailWord_1391943).sum := by decide
  have hdescent : baseEnd_1391943 < baseStart_1391943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391959 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_1391959 : Nat := 118140960795 + 1391959 * 2 ^ 59
def prefixEnd_1391959 : Nat := 4983230072969 + 3 ^ 40 * 1391959 * 2
def baseEnd_1391959 : Nat := 714744018351824687711003

theorem tailTrace_1391959 : CollatzResearch.WordTrace tailWord_1391959 prefixEnd_1391959 714744018351824687711003 := by
  unfold tailWord_1391959
  simp only [CollatzResearch.WordTrace]
  refine ⟨50768915564177745515842931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33845943709451830343895287 50768915564177745515842931)
  ·
    refine ⟨76153373346266618273764397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50768915564177745515842931 76153373346266618273764397)
    ·
      refine ⟨28557515004849981852661649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76153373346266618273764397 28557515004849981852661649)
      ·
        refine ⟨21418136253637486389496237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28557515004849981852661649 21418136253637486389496237)
        ·
          refine ⟨8031801095114057396061089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21418136253637486389496237 8031801095114057396061089)
          ·
            refine ⟨6023850821335543047045817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8031801095114057396061089 6023850821335543047045817)
            ·
              refine ⟨4517888116001657285284363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6023850821335543047045817 4517888116001657285284363)
              ·
                refine ⟨6776832174002485927926545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4517888116001657285284363 6776832174002485927926545)
                ·
                  refine ⟨5082624130501864445944909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6776832174002485927926545 5082624130501864445944909)
                  ·
                    refine ⟨1905984048938199167229341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5082624130501864445944909 1905984048938199167229341)
                    ·
                      refine ⟨714744018351824687711003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1905984048938199167229341 714744018351824687711003)
                      ·
                        rfl

theorem cell23_1391959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_1391959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391959 prefixEnd_1391959 := by exact prefixLift 1391959
  have htrace : WordTrace (prefixWord ++ tailWord_1391959) baseStart_1391959 baseEnd_1391959 := by
    simpa [prefixWord, tailWord_1391959, baseEnd_1391959] using wordTrace_append hprefix tailTrace_1391959
  have hstable : (prefixWord ++ tailWord_1391959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391959).length < 2 ^ (prefixWord ++ tailWord_1391959).sum := by decide
  have hdescent : baseEnd_1391959 < baseStart_1391959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391962 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_1391962 : Nat := 118140960795 + 1391962 * 2 ^ 59
def prefixEnd_1391962 : Nat := 4983230072969 + 3 ^ 40 * 1391962 * 2
def baseEnd_1391962 : Nat := 238248519597929391991163

theorem tailTrace_1391962 : CollatzResearch.WordTrace tailWord_1391962 prefixEnd_1391962 238248519597929391991163 := by
  unfold tailWord_1391962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12692256245791719257050535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33846016655444584685468093 12692256245791719257050535)
  ·
    refine ⟨19038384368687578885575803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12692256245791719257050535 19038384368687578885575803)
    ·
      refine ⟨28557576553031368328363705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19038384368687578885575803 28557576553031368328363705)
      ·
        refine ⟨21418182414773526246272779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28557576553031368328363705 21418182414773526246272779)
        ·
          refine ⟨32127273622160289369409169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21418182414773526246272779 32127273622160289369409169)
          ·
            refine ⟨24095455216620217027056877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32127273622160289369409169 24095455216620217027056877)
            ·
              refine ⟨9035795706232581385146329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24095455216620217027056877 9035795706232581385146329)
              ·
                refine ⟨6776846779674436038859747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9035795706232581385146329 6776846779674436038859747)
                ·
                  refine ⟨10165270169511654058289621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6776846779674436038859747 10165270169511654058289621)
                  ·
                    refine ⟨238248519597929391991163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10165270169511654058289621 238248519597929391991163)
                    ·
                      rfl

theorem cell23_1391962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_1391962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391962 prefixEnd_1391962 := by exact prefixLift 1391962
  have htrace : WordTrace (prefixWord ++ tailWord_1391962) baseStart_1391962 baseEnd_1391962 := by
    simpa [prefixWord, tailWord_1391962, baseEnd_1391962] using wordTrace_append hprefix tailTrace_1391962
  have hstable : (prefixWord ++ tailWord_1391962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391962).length < 2 ^ (prefixWord ++ tailWord_1391962).sum := by decide
  have hdescent : baseEnd_1391962 < baseStart_1391962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1391969 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_1391969 : Nat := 118140960795 + 1391969 * 2 ^ 59
def prefixEnd_1391969 : Nat := 4983230072969 + 3 ^ 40 * 1391969 * 2
def baseEnd_1391969 : Nat := 714749153158369648585957

theorem tailTrace_1391969 : CollatzResearch.WordTrace tailWord_1391969 prefixEnd_1391969 714749153158369648585957 := by
  unfold tailWord_1391969
  simp only [CollatzResearch.WordTrace]
  refine ⟨50769280294141517223706961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33846186862761011482471307 50769280294141517223706961)
  ·
    refine ⟨38076960220606137917780221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50769280294141517223706961 38076960220606137917780221)
    ·
      refine ⟨14278860082727301719167583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38076960220606137917780221 14278860082727301719167583)
      ·
        refine ⟨21418290124090952578751375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14278860082727301719167583 21418290124090952578751375)
        ·
          refine ⟨32127435186136428868127063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21418290124090952578751375 32127435186136428868127063)
          ·
            refine ⟨48191152779204643302190595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32127435186136428868127063 48191152779204643302190595)
            ·
              refine ⟨72286729168806964953285893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48191152779204643302190595 72286729168806964953285893)
              ·
                refine ⟨13553761719151305928741105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72286729168806964953285893 13553761719151305928741105)
                ·
                  refine ⟨10165321289363479446555829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13553761719151305928741105 10165321289363479446555829)
                  ·
                    refine ⟨952998870877826198114609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10165321289363479446555829 952998870877826198114609)
                    ·
                      refine ⟨714749153158369648585957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 952998870877826198114609 714749153158369648585957)
                      ·
                        rfl

theorem cell23_1391969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_1391969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1391969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1391969 prefixEnd_1391969 := by exact prefixLift 1391969
  have htrace : WordTrace (prefixWord ++ tailWord_1391969) baseStart_1391969 baseEnd_1391969 := by
    simpa [prefixWord, tailWord_1391969, baseEnd_1391969] using wordTrace_append hprefix tailTrace_1391969
  have hstable : (prefixWord ++ tailWord_1391969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1391969).length < 2 ^ (prefixWord ++ tailWord_1391969).sum := by decide
  have hdescent : baseEnd_1391969 < baseStart_1391969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1391969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392060 : List Nat := [2, 2, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_1392060 : Nat := 118140960795 + 1392060 * 2 ^ 59
def prefixEnd_1392060 : Nat := 4983230072969 + 3 ^ 40 * 1392060 * 2
def baseEnd_1392060 : Nat := 238265293299309597516013

theorem tailTrace_1392060 : CollatzResearch.WordTrace tailWord_1392060 prefixEnd_1392060 238265293299309597516013 := by
  unfold tailWord_1392060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25386299668405919882634817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33848399557874559843513089 25386299668405919882634817)
  ·
    refine ⟨19039724751304439911976113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25386299668405919882634817 19039724751304439911976113)
    ·
      refine ⟨14279793563478329933982085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19039724751304439911976113 14279793563478329933982085)
      ·
        refine ⟨2677461293152186862621641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14279793563478329933982085 2677461293152186862621641)
        ·
          refine ⟨2008095969864140146966231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677461293152186862621641 2008095969864140146966231)
          ·
            refine ⟨3012143954796210220449347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008095969864140146966231 3012143954796210220449347)
            ·
              refine ⟨4518215932194315330674021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012143954796210220449347 4518215932194315330674021)
              ·
                refine ⟨847165487286434124501379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4518215932194315330674021 847165487286434124501379)
                ·
                  refine ⟨1270748230929651186752069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847165487286434124501379 1270748230929651186752069)
                  ·
                    refine ⟨238265293299309597516013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1270748230929651186752069 238265293299309597516013)
                    ·
                      rfl

theorem cell23_1392060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_1392060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392060 prefixEnd_1392060 := by exact prefixLift 1392060
  have htrace : WordTrace (prefixWord ++ tailWord_1392060) baseStart_1392060 baseEnd_1392060 := by
    simpa [prefixWord, tailWord_1392060, baseEnd_1392060] using wordTrace_append hprefix tailTrace_1392060
  have hstable : (prefixWord ++ tailWord_1392060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392060).length < 2 ^ (prefixWord ++ tailWord_1392060).sum := by decide
  have hdescent : baseEnd_1392060 < baseStart_1392060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392093 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_1392093 : Nat := 118140960795 + 1392093 * 2 ^ 59
def prefixEnd_1392093 : Nat := 4983230072969 + 3 ^ 40 * 1392093 * 2
def baseEnd_1392093 : Nat := 714812824759527163435387

theorem tailTrace_1392093 : CollatzResearch.WordTrace tailWord_1392093 prefixEnd_1392093 714812824759527163435387 := by
  unfold tailWord_1392093
  simp only [CollatzResearch.WordTrace]
  refine ⟨50773802945692286401220933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33849201963794857600813955 50773802945692286401220933)
  ·
    refine ⟨9520088052317303700228925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50773802945692286401220933 9520088052317303700228925)
    ·
      refine ⟨3570033019618988887585847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9520088052317303700228925 3570033019618988887585847)
      ·
        refine ⟨5355049529428483331378771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3570033019618988887585847 5355049529428483331378771)
        ·
          refine ⟨8032574294142724997068157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5355049529428483331378771 8032574294142724997068157)
          ·
            refine ⟨3012215360303521873900559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8032574294142724997068157 3012215360303521873900559)
            ·
              refine ⟨4518323040455282810850839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012215360303521873900559 4518323040455282810850839)
              ·
                refine ⟨6777484560682924216276259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518323040455282810850839 6777484560682924216276259)
                ·
                  refine ⟨10166226841024386324414389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6777484560682924216276259 10166226841024386324414389)
                  ·
                    refine ⟨953083766346036217913849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10166226841024386324414389 953083766346036217913849)
                    ·
                      refine ⟨714812824759527163435387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953083766346036217913849 714812824759527163435387)
                      ·
                        rfl

theorem cell23_1392093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_1392093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392093 prefixEnd_1392093 := by exact prefixLift 1392093
  have htrace : WordTrace (prefixWord ++ tailWord_1392093) baseStart_1392093 baseEnd_1392093 := by
    simpa [prefixWord, tailWord_1392093, baseEnd_1392093] using wordTrace_append hprefix tailTrace_1392093
  have hstable : (prefixWord ++ tailWord_1392093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392093).length < 2 ^ (prefixWord ++ tailWord_1392093).sum := by decide
  have hdescent : baseEnd_1392093 < baseStart_1392093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392103 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1392103 : Nat := 118140960795 + 1392103 * 2 ^ 59
def prefixEnd_1392103 : Nat := 4983230072969 + 3 ^ 40 * 1392103 * 2
def baseEnd_1392103 : Nat := 238272653188690708103447

theorem tailTrace_1392103 : CollatzResearch.WordTrace tailWord_1392103 prefixEnd_1392103 238272653188690708103447 := by
  unfold tailWord_1392103
  simp only [CollatzResearch.WordTrace]
  refine ⟨50774167675656058109084963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33849445117104038739389975 50774167675656058109084963)
  ·
    refine ⟨76161251513484087163627445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50774167675656058109084963 76161251513484087163627445)
    ·
      refine ⟨7140117329389133171590073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76161251513484087163627445 7140117329389133171590073)
      ·
        refine ⟨5355087997041849878692555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7140117329389133171590073 5355087997041849878692555)
        ·
          refine ⟨8032631995562774818038833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5355087997041849878692555 8032631995562774818038833)
          ·
            refine ⟨6024473996672081113529125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8032631995562774818038833 6024473996672081113529125)
            ·
              refine ⟨1129588874376015208786711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6024473996672081113529125 1129588874376015208786711)
              ·
                refine ⟨1694383311564022813180067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129588874376015208786711 1694383311564022813180067)
                ·
                  refine ⟨2541574967346034219770101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694383311564022813180067 2541574967346034219770101)
                  ·
                    refine ⟨238272653188690708103447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2541574967346034219770101 238272653188690708103447)
                    ·
                      rfl

theorem cell23_1392103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1392103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392103 prefixEnd_1392103 := by exact prefixLift 1392103
  have htrace : WordTrace (prefixWord ++ tailWord_1392103) baseStart_1392103 baseEnd_1392103 := by
    simpa [prefixWord, tailWord_1392103, baseEnd_1392103] using wordTrace_append hprefix tailTrace_1392103
  have hstable : (prefixWord ++ tailWord_1392103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392103).length < 2 ^ (prefixWord ++ tailWord_1392103).sum := by decide
  have hdescent : baseEnd_1392103 < baseStart_1392103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392117 : List Nat := [1, 3, 5, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1392117 : Nat := 118140960795 + 1392117 * 2 ^ 59
def prefixEnd_1392117 : Nat := 4983230072969 + 3 ^ 40 * 1392117 * 2
def baseEnd_1392117 : Nat := 714825148295235069535277

theorem tailTrace_1392117 : CollatzResearch.WordTrace tailWord_1392117 prefixEnd_1392117 714825148295235069535277 := by
  unfold tailWord_1392117
  simp only [CollatzResearch.WordTrace]
  refine ⟨50774678297605338500094605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33849785531736892333396403 50774678297605338500094605)
  ·
    refine ⟨19040504361602001937535477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50774678297605338500094605 19040504361602001937535477)
    ·
      refine ⟨1785047283900187681643951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19040504361602001937535477 1785047283900187681643951)
      ·
        refine ⟨2677570925850281522465927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785047283900187681643951 2677570925850281522465927)
        ·
          refine ⟨4016356388775422283698891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677570925850281522465927 4016356388775422283698891)
          ·
            refine ⟨6024534583163133425548337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016356388775422283698891 6024534583163133425548337)
            ·
              refine ⟨4518400937372350069161253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6024534583163133425548337 4518400937372350069161253)
              ·
                refine ⟨847200175757315637967735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4518400937372350069161253 847200175757315637967735)
                ·
                  refine ⟨1270800263635973456951603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847200175757315637967735 1270800263635973456951603)
                  ·
                    refine ⟨1906200395453960185427405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1270800263635973456951603 1906200395453960185427405)
                    ·
                      refine ⟨714825148295235069535277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1906200395453960185427405 714825148295235069535277)
                      ·
                        rfl

theorem cell23_1392117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1392117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392117 prefixEnd_1392117 := by exact prefixLift 1392117
  have htrace : WordTrace (prefixWord ++ tailWord_1392117) baseStart_1392117 baseEnd_1392117 := by
    simpa [prefixWord, tailWord_1392117, baseEnd_1392117] using wordTrace_append hprefix tailTrace_1392117
  have hstable : (prefixWord ++ tailWord_1392117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392117).length < 2 ^ (prefixWord ++ tailWord_1392117).sum := by decide
  have hdescent : baseEnd_1392117 < baseStart_1392117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392136 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1392136 : Nat := 118140960795 + 1392136 * 2 ^ 59
def prefixEnd_1392136 : Nat := 4983230072969 + 3 ^ 40 * 1392136 * 2
def baseEnd_1392136 : Nat := 714834904427670495197689

theorem tailTrace_1392136 : CollatzResearch.WordTrace tailWord_1392136 prefixEnd_1392136 714834904427670495197689 := by
  unfold tailWord_1392136
  simp only [CollatzResearch.WordTrace]
  refine ⟨25387685642268252372518131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33850247523024336496690841 25387685642268252372518131)
  ·
    refine ⟨38081528463402378558777197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25387685642268252372518131 38081528463402378558777197)
    ·
      refine ⟨14280573173775891959541449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38081528463402378558777197 14280573173775891959541449)
      ·
        refine ⟨10710429880331918969656087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14280573173775891959541449 10710429880331918969656087)
        ·
          refine ⟨16065644820497878454484131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10710429880331918969656087 16065644820497878454484131)
          ·
            refine ⟨24098467230746817681726197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16065644820497878454484131 24098467230746817681726197)
            ·
              refine ⟨2259231302882514157661831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24098467230746817681726197 2259231302882514157661831)
              ·
                refine ⟨3388846954323771236492747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259231302882514157661831 3388846954323771236492747)
                ·
                  refine ⟨5083270431485656854739121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3388846954323771236492747 5083270431485656854739121)
                  ·
                    refine ⟨3812452823614242641054341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5083270431485656854739121 3812452823614242641054341)
                    ·
                      refine ⟨714834904427670495197689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3812452823614242641054341 714834904427670495197689)
                      ·
                        rfl

theorem cell23_1392136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1392136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392136 prefixEnd_1392136 := by exact prefixLift 1392136
  have htrace : WordTrace (prefixWord ++ tailWord_1392136) baseStart_1392136 baseEnd_1392136 := by
    simpa [prefixWord, tailWord_1392136, baseEnd_1392136] using wordTrace_append hprefix tailTrace_1392136
  have hstable : (prefixWord ++ tailWord_1392136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392136).length < 2 ^ (prefixWord ++ tailWord_1392136).sum := by decide
  have hdescent : baseEnd_1392136 < baseStart_1392136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392156 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1392156 : Nat := 118140960795 + 1392156 * 2 ^ 59
def prefixEnd_1392156 : Nat := 4983230072969 + 3 ^ 40 * 1392156 * 2
def baseEnd_1392156 : Nat := 714845174040760416947597

theorem tailTrace_1392156 : CollatzResearch.WordTrace tailWord_1392156 prefixEnd_1392156 714845174040760416947597 := by
  unfold tailWord_1392156
  simp only [CollatzResearch.WordTrace]
  refine ⟨25388050372232024080382161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33850733829642698773842881 25388050372232024080382161)
  ·
    refine ⟨19041037779174018060286621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25388050372232024080382161 19041037779174018060286621)
    ·
      refine ⟨7140389167190256772607483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19041037779174018060286621 7140389167190256772607483)
      ·
        refine ⟨10710583750785385158911225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7140389167190256772607483 10710583750785385158911225)
        ·
          refine ⟨8032937813089038869183419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10710583750785385158911225 8032937813089038869183419)
          ·
            refine ⟨12049406719633558303775129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8032937813089038869183419 12049406719633558303775129)
            ·
              refine ⟨9037055039725168727831347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12049406719633558303775129 9037055039725168727831347)
              ·
                refine ⟨13555582559587753091747021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9037055039725168727831347 13555582559587753091747021)
                ·
                  refine ⟨5083343459845407409405133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13555582559587753091747021 5083343459845407409405133)
                  ·
                    refine ⟨1906253797442027778526925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5083343459845407409405133 1906253797442027778526925)
                    ·
                      refine ⟨714845174040760416947597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1906253797442027778526925 714845174040760416947597)
                      ·
                        rfl

theorem cell23_1392156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1392156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392156 prefixEnd_1392156 := by exact prefixLift 1392156
  have htrace : WordTrace (prefixWord ++ tailWord_1392156) baseStart_1392156 baseEnd_1392156 := by
    simpa [prefixWord, tailWord_1392156, baseEnd_1392156] using wordTrace_append hprefix tailTrace_1392156
  have hstable : (prefixWord ++ tailWord_1392156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392156).length < 2 ^ (prefixWord ++ tailWord_1392156).sum := by decide
  have hdescent : baseEnd_1392156 < baseStart_1392156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392239 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_1392239 : Nat := 118140960795 + 1392239 * 2 ^ 59
def prefixEnd_1392239 : Nat := 4983230072969 + 3 ^ 40 * 1392239 * 2
def baseEnd_1392239 : Nat := 714887792935083592209715

theorem tailTrace_1392239 : CollatzResearch.WordTrace tailWord_1392239 prefixEnd_1392239 714887792935083592209715 := by
  unfold tailWord_1392239
  simp only [CollatzResearch.WordTrace]
  refine ⟨50779128003163353336035771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33852752002108902224023847 50779128003163353336035771)
  ·
    refine ⟨76168692004745030004053657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50779128003163353336035771 76168692004745030004053657)
    ·
      refine ⟨57126519003558772503040243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76168692004745030004053657 57126519003558772503040243)
      ·
        refine ⟨85689778505338158754560365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57126519003558772503040243 85689778505338158754560365)
        ·
          refine ⟨32133666939501809532960137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85689778505338158754560365 32133666939501809532960137)
          ·
            refine ⟨24100250204626357149720103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32133666939501809532960137 24100250204626357149720103)
            ·
              refine ⟨36150375306939535724580155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24100250204626357149720103 36150375306939535724580155)
              ·
                refine ⟨54225562960409303586870233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36150375306939535724580155 54225562960409303586870233)
                ·
                  refine ⟨40669172220306977690152675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54225562960409303586870233 40669172220306977690152675)
                  ·
                    refine ⟨61003758330460466535229013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40669172220306977690152675 61003758330460466535229013)
                    ·
                      refine ⟨714887792935083592209715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 61003758330460466535229013 714887792935083592209715)
                      ·
                        rfl

theorem cell23_1392239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_1392239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392239 prefixEnd_1392239 := by exact prefixLift 1392239
  have htrace : WordTrace (prefixWord ++ tailWord_1392239) baseStart_1392239 baseEnd_1392239 := by
    simpa [prefixWord, tailWord_1392239, baseEnd_1392239] using wordTrace_append hprefix tailTrace_1392239
  have hstable : (prefixWord ++ tailWord_1392239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392239).length < 2 ^ (prefixWord ++ tailWord_1392239).sum := by decide
  have hdescent : baseEnd_1392239 < baseStart_1392239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392270 : List Nat := [4, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_1392270 : Nat := 118140960795 + 1392270 * 2 ^ 59
def prefixEnd_1392270 : Nat := 4983230072969 + 3 ^ 40 * 1392270 * 2
def baseEnd_1392270 : Nat := 79433745648374774546897

theorem tailTrace_1392270 : CollatzResearch.WordTrace tailWord_1392270 prefixEnd_1392270 79433745648374774546897 := by
  unfold tailWord_1392270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347532333256380703801783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33853505777367363753609509 6347532333256380703801783)
  ·
    refine ⟨9521298499884571055702675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6347532333256380703801783 9521298499884571055702675)
    ·
      refine ⟨14281947749826856583554013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9521298499884571055702675 14281947749826856583554013)
      ·
        refine ⟨5355730406185071218832755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14281947749826856583554013 5355730406185071218832755)
        ·
          refine ⟨8033595609277606828249133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5355730406185071218832755 8033595609277606828249133)
          ·
            refine ⟨3012598353479102560593425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8033595609277606828249133 3012598353479102560593425)
            ·
              refine ⟨2259448765109326920445069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012598353479102560593425 2259448765109326920445069)
              ·
                refine ⟨847293286915997595166901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2259448765109326920445069 847293286915997595166901)
                ·
                  refine ⟨79433745648374774546897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 847293286915997595166901 79433745648374774546897)
                  ·
                    rfl

theorem cell23_1392270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_1392270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392270 prefixEnd_1392270 := by exact prefixLift 1392270
  have htrace : WordTrace (prefixWord ++ tailWord_1392270) baseStart_1392270 baseEnd_1392270 := by
    simpa [prefixWord, tailWord_1392270, baseEnd_1392270] using wordTrace_append hprefix tailTrace_1392270
  have hstable : (prefixWord ++ tailWord_1392270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392270).length < 2 ^ (prefixWord ++ tailWord_1392270).sum := by decide
  have hdescent : baseEnd_1392270 < baseStart_1392270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392303 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 2, 4, 2]
def baseStart_1392303 : Nat := 118140960795 + 1392303 * 2 ^ 59
def prefixEnd_1392303 : Nat := 4983230072969 + 3 ^ 40 * 1392303 * 2
def baseEnd_1392303 : Nat := 714920655696971341809421

theorem tailTrace_1392303 : CollatzResearch.WordTrace tailWord_1392303 prefixEnd_1392303 714920655696971341809421 := by
  unfold tailWord_1392303
  simp only [CollatzResearch.WordTrace]
  refine ⟨50781462274931492266365563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33854308183287661510910375 50781462274931492266365563)
  ·
    refine ⟨76172193412397238399548345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50781462274931492266365563 76172193412397238399548345)
    ·
      refine ⟨57129145059297928799661259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76172193412397238399548345 57129145059297928799661259)
      ·
        refine ⟨85693717588946893199491889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57129145059297928799661259 85693717588946893199491889)
        ·
          refine ⟨64270288191710169899618917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85693717588946893199491889 64270288191710169899618917)
          ·
            refine ⟨12050679035945656856178547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64270288191710169899618917 12050679035945656856178547)
            ·
              refine ⟨18076018553918485284267821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12050679035945656856178547 18076018553918485284267821)
              ·
                refine ⟨6778506957719431981600433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18076018553918485284267821 6778506957719431981600433)
                ·
                  refine ⟨5083880218289573986200325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6778506957719431981600433 5083880218289573986200325)
                  ·
                    refine ⟨953227540929295122412561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5083880218289573986200325 953227540929295122412561)
                    ·
                      refine ⟨714920655696971341809421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953227540929295122412561 714920655696971341809421)
                      ·
                        rfl

theorem cell23_1392303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 4, 2].length) (baseStart_1392303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392303 prefixEnd_1392303 := by exact prefixLift 1392303
  have htrace : WordTrace (prefixWord ++ tailWord_1392303) baseStart_1392303 baseEnd_1392303 := by
    simpa [prefixWord, tailWord_1392303, baseEnd_1392303] using wordTrace_append hprefix tailTrace_1392303
  have hstable : (prefixWord ++ tailWord_1392303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392303).length < 2 ^ (prefixWord ++ tailWord_1392303).sum := by decide
  have hdescent : baseEnd_1392303 < baseStart_1392303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392313 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 3, 4]
def baseStart_1392313 : Nat := 118140960795 + 1392313 * 2 ^ 59
def prefixEnd_1392313 : Nat := 4983230072969 + 3 ^ 40 * 1392313 * 2
def baseEnd_1392313 : Nat := 238308596834505434228125

theorem tailTrace_1392313 : CollatzResearch.WordTrace tailWord_1392313 prefixEnd_1392313 238308596834505434228125 := by
  unfold tailWord_1392313
  simp only [CollatzResearch.WordTrace]
  refine ⟨50781827004895263974229593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33854551336596842649486395 50781827004895263974229593)
  ·
    refine ⟨38086370253671447980672195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50781827004895263974229593 38086370253671447980672195)
    ·
      refine ⟨57129555380507171971008293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38086370253671447980672195 57129555380507171971008293)
      ·
        refine ⟨10711791633845094744564055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57129555380507171971008293 10711791633845094744564055)
        ·
          refine ⟨16067687450767642116846083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10711791633845094744564055 16067687450767642116846083)
          ·
            refine ⟨24101531176151463175269125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16067687450767642116846083 24101531176151463175269125)
            ·
              refine ⟨4519037095528399345362961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24101531176151463175269125 4519037095528399345362961)
              ·
                refine ⟨3389277821646299509022221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4519037095528399345362961 3389277821646299509022221)
                ·
                  refine ⟨1270979183117362315883333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3389277821646299509022221 1270979183117362315883333)
                  ·
                    refine ⟨238308596834505434228125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1270979183117362315883333 238308596834505434228125)
                    ·
                      rfl

theorem cell23_1392313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_1392313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392313 prefixEnd_1392313 := by exact prefixLift 1392313
  have htrace : WordTrace (prefixWord ++ tailWord_1392313) baseStart_1392313 baseEnd_1392313 := by
    simpa [prefixWord, tailWord_1392313, baseEnd_1392313] using wordTrace_append hprefix tailTrace_1392313
  have hstable : (prefixWord ++ tailWord_1392313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392313).length < 2 ^ (prefixWord ++ tailWord_1392313).sum := by decide
  have hdescent : baseEnd_1392313 < baseStart_1392313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392340 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1392340 : Nat := 118140960795 + 1392340 * 2 ^ 59
def prefixEnd_1392340 : Nat := 4983230072969 + 3 ^ 40 * 1392340 * 2
def baseEnd_1392340 : Nat := 714939654481187697046751

theorem tailTrace_1392340 : CollatzResearch.WordTrace tailWord_1392340 prefixEnd_1392340 714939654481187697046751 := by
  unfold tailWord_1392340
  simp only [CollatzResearch.WordTrace]
  refine ⟨25391405887898723792731237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33855207850531631723641649 25391405887898723792731237)
  ·
    refine ⟨4760888603981010711137107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25391405887898723792731237 4760888603981010711137107)
    ·
      refine ⟨7141332905971516066705661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760888603981010711137107 7141332905971516066705661)
      ·
        refine ⟨2677999839739318525014623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7141332905971516066705661 2677999839739318525014623)
        ·
          refine ⟨4016999759608977787521935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677999839739318525014623 4016999759608977787521935)
          ·
            refine ⟨6025499639413466681282903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016999759608977787521935 6025499639413466681282903)
            ·
              refine ⟨9038249459120200021924355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6025499639413466681282903 9038249459120200021924355)
              ·
                refine ⟨13557374188680300032886533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9038249459120200021924355 13557374188680300032886533)
                ·
                  refine ⟨2542007660377556256166225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13557374188680300032886533 2542007660377556256166225)
                  ·
                    refine ⟨1906505745283167192124669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2542007660377556256166225 1906505745283167192124669)
                    ·
                      refine ⟨714939654481187697046751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1906505745283167192124669 714939654481187697046751)
                      ·
                        rfl

theorem cell23_1392340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1392340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392340 prefixEnd_1392340 := by exact prefixLift 1392340
  have htrace : WordTrace (prefixWord ++ tailWord_1392340) baseStart_1392340 baseEnd_1392340 := by
    simpa [prefixWord, tailWord_1392340, baseEnd_1392340] using wordTrace_append hprefix tailTrace_1392340
  have hstable : (prefixWord ++ tailWord_1392340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392340).length < 2 ^ (prefixWord ++ tailWord_1392340).sum := by decide
  have hdescent : baseEnd_1392340 < baseStart_1392340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392360 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 6]
def baseStart_1392360 : Nat := 118140960795 + 1392360 * 2 ^ 59
def prefixEnd_1392360 : Nat := 4983230072969 + 3 ^ 40 * 1392360 * 2
def baseEnd_1392360 : Nat := 79438880454919735421851

theorem tailTrace_1392360 : CollatzResearch.WordTrace tailWord_1392360 prefixEnd_1392360 79438880454919735421851 := by
  unfold tailWord_1392360
  simp only [CollatzResearch.WordTrace]
  refine ⟨25391770617862495500595267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33855694157149994000793689 25391770617862495500595267)
  ·
    refine ⟨38087655926793743250892901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25391770617862495500595267 38087655926793743250892901)
    ·
      refine ⟨7141435486273826859542419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38087655926793743250892901 7141435486273826859542419)
      ·
        refine ⟨10712153229410740289313629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7141435486273826859542419 10712153229410740289313629)
        ·
          refine ⟨4017057461029027608492611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10712153229410740289313629 4017057461029027608492611)
          ·
            refine ⟨6025586191543541412738917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4017057461029027608492611 6025586191543541412738917)
            ·
              refine ⟨1129797410914414014888547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6025586191543541412738917 1129797410914414014888547)
              ·
                refine ⟨1694696116371621022332821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129797410914414014888547 1694696116371621022332821)
                ·
                  refine ⟨79438880454919735421851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1694696116371621022332821 79438880454919735421851)
                  ·
                    rfl

theorem cell23_1392360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 6].length) (baseStart_1392360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392360 prefixEnd_1392360 := by exact prefixLift 1392360
  have htrace : WordTrace (prefixWord ++ tailWord_1392360) baseStart_1392360 baseEnd_1392360 := by
    simpa [prefixWord, tailWord_1392360, baseEnd_1392360] using wordTrace_append hprefix tailTrace_1392360
  have hstable : (prefixWord ++ tailWord_1392360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392360).length < 2 ^ (prefixWord ++ tailWord_1392360).sum := by decide
  have hdescent : baseEnd_1392360 < baseStart_1392360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392363 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 3, 5, 2]
def baseStart_1392363 : Nat := 118140960795 + 1392363 * 2 ^ 59
def prefixEnd_1392363 : Nat := 4983230072969 + 3 ^ 40 * 1392363 * 2
def baseEnd_1392363 : Nat := 714951464536241107059145

theorem tailTrace_1392363 : CollatzResearch.WordTrace tailWord_1392363 prefixEnd_1392363 714951464536241107059145 := by
  unfold tailWord_1392363
  simp only [CollatzResearch.WordTrace]
  refine ⟨50783650654714122513549743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33855767103142748342366495 50783650654714122513549743)
  ·
    refine ⟨76175475982071183770324615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50783650654714122513549743 76175475982071183770324615)
    ·
      refine ⟨114263213973106775655486923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76175475982071183770324615 114263213973106775655486923)
      ·
        refine ⟨171394820959660163483230385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114263213973106775655486923 171394820959660163483230385)
        ·
          refine ⟨128546115719745122612422789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171394820959660163483230385 128546115719745122612422789)
          ·
            refine ⟨24102396697452210489829273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128546115719745122612422789 24102396697452210489829273)
            ·
              refine ⟨18076797523089157867371955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24102396697452210489829273 18076797523089157867371955)
              ·
                refine ⟨27115196284633736801057933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18076797523089157867371955 27115196284633736801057933)
                ·
                  refine ⟨10168198606737651300396725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27115196284633736801057933 10168198606737651300396725)
                  ·
                    refine ⟨953268619381654809412193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10168198606737651300396725 953268619381654809412193)
                    ·
                      refine ⟨714951464536241107059145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953268619381654809412193 714951464536241107059145)
                      ·
                        rfl

theorem cell23_1392363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 5, 2].length) (baseStart_1392363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392363 prefixEnd_1392363 := by exact prefixLift 1392363
  have htrace : WordTrace (prefixWord ++ tailWord_1392363) baseStart_1392363 baseEnd_1392363 := by
    simpa [prefixWord, tailWord_1392363, baseEnd_1392363] using wordTrace_append hprefix tailTrace_1392363
  have hstable : (prefixWord ++ tailWord_1392363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392363).length < 2 ^ (prefixWord ++ tailWord_1392363).sum := by decide
  have hdescent : baseEnd_1392363 < baseStart_1392363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392370 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1392370 : Nat := 118140960795 + 1392370 * 2 ^ 59
def prefixEnd_1392370 : Nat := 4983230072969 + 3 ^ 40 * 1392370 * 2
def baseEnd_1392370 : Nat := 714955058900822579671613

theorem tailTrace_1392370 : CollatzResearch.WordTrace tailWord_1392370 prefixEnd_1392370 714955058900822579671613 := by
  unfold tailWord_1392370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12695976491422190677263641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33855937310459175139369709 12695976491422190677263641)
  ·
    refine ⟨9521982368566643007947731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12695976491422190677263641 9521982368566643007947731)
    ·
      refine ⟨14282973552849964511921597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9521982368566643007947731 14282973552849964511921597)
      ·
        refine ⟨5356115082318736691970599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14282973552849964511921597 5356115082318736691970599)
        ·
          refine ⟨8034172623478105037955899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5356115082318736691970599 8034172623478105037955899)
          ·
            refine ⟨12051258935217157556933849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8034172623478105037955899 12051258935217157556933849)
            ·
              refine ⟨9038444201412868167700387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12051258935217157556933849 9038444201412868167700387)
              ·
                refine ⟨13557666302119302251550581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9038444201412868167700387 13557666302119302251550581)
                ·
                  refine ⟨1271031215823684586082867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13557666302119302251550581 1271031215823684586082867)
                  ·
                    refine ⟨1906546823735526879124301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1271031215823684586082867 1906546823735526879124301)
                    ·
                      refine ⟨714955058900822579671613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1906546823735526879124301 714955058900822579671613)
                      ·
                        rfl

theorem cell23_1392370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1392370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392370 prefixEnd_1392370 := by exact prefixLift 1392370
  have htrace : WordTrace (prefixWord ++ tailWord_1392370) baseStart_1392370 baseEnd_1392370 := by
    simpa [prefixWord, tailWord_1392370, baseEnd_1392370] using wordTrace_append hprefix tailTrace_1392370
  have hstable : (prefixWord ++ tailWord_1392370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392370).length < 2 ^ (prefixWord ++ tailWord_1392370).sum := by decide
  have hdescent : baseEnd_1392370 < baseStart_1392370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392420 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_1392420 : Nat := 118140960795 + 1392420 * 2 ^ 59
def prefixEnd_1392420 : Nat := 4983230072969 + 3 ^ 40 * 1392420 * 2
def baseEnd_1392420 : Nat := 238326910977849128015461

theorem tailTrace_1392420 : CollatzResearch.WordTrace tailWord_1392420 prefixEnd_1392420 238326910977849128015461 := by
  unfold tailWord_1392420
  simp only [CollatzResearch.WordTrace]
  refine ⟨25392864807753810624187357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33857153077005080832249809 25392864807753810624187357)
  ·
    refine ⟨9522324302907678984070259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25392864807753810624187357 9522324302907678984070259)
    ·
      refine ⟨14283486454361518476105389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9522324302907678984070259 14283486454361518476105389)
      ·
        refine ⟨5356307420385569428539521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14283486454361518476105389 5356307420385569428539521)
        ·
          refine ⟨4017230565289177071404641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5356307420385569428539521 4017230565289177071404641)
          ·
            refine ⟨3012922923966882803553481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4017230565289177071404641 3012922923966882803553481)
            ·
              refine ⟨2259692192975162102665111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012922923966882803553481 2259692192975162102665111)
              ·
                refine ⟨3389538289462743153997667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259692192975162102665111 3389538289462743153997667)
                ·
                  refine ⟨5084307434194114730996501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3389538289462743153997667 5084307434194114730996501)
                  ·
                    refine ⟨238326910977849128015461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5084307434194114730996501 238326910977849128015461)
                    ·
                      rfl

theorem cell23_1392420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_1392420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392420 prefixEnd_1392420 := by exact prefixLift 1392420
  have htrace : WordTrace (prefixWord ++ tailWord_1392420) baseStart_1392420 baseEnd_1392420 := by
    simpa [prefixWord, tailWord_1392420, baseEnd_1392420] using wordTrace_append hprefix tailTrace_1392420
  have hstable : (prefixWord ++ tailWord_1392420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392420).length < 2 ^ (prefixWord ++ tailWord_1392420).sum := by decide
  have hdescent : baseEnd_1392420 < baseStart_1392420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392441 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 1, 5]
def baseStart_1392441 : Nat := 118140960795 + 1392441 * 2 ^ 59
def prefixEnd_1392441 : Nat := 4983230072969 + 3 ^ 40 * 1392441 * 2
def baseEnd_1392441 : Nat := 238330505342430600627929

theorem tailTrace_1392441 : CollatzResearch.WordTrace tailWord_1392441 prefixEnd_1392441 238330505342430600627929 := by
  unfold tailWord_1392441
  simp only [CollatzResearch.WordTrace]
  refine ⟨50786495548431541834889177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33857663698954361223259451 50786495548431541834889177)
  ·
    refine ⟨38089871661323656376166883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50786495548431541834889177 38089871661323656376166883)
    ·
      refine ⟨57134807491985484564250325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38089871661323656376166883 57134807491985484564250325)
      ·
        refine ⟨1339097050593409794474617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 57134807491985484564250325 1339097050593409794474617)
        ·
          refine ⟨1004322787945057345855963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339097050593409794474617 1004322787945057345855963)
          ·
            refine ⟨1506484181917586018783945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004322787945057345855963 1506484181917586018783945)
            ·
              refine ⟨1129863136438189514087959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506484181917586018783945 1129863136438189514087959)
              ·
                refine ⟨1694794704657284271131939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129863136438189514087959 1694794704657284271131939)
                ·
                  refine ⟨2542192056985926406697909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694794704657284271131939 2542192056985926406697909)
                  ·
                    refine ⟨238330505342430600627929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2542192056985926406697909 238330505342430600627929)
                    ·
                      rfl

theorem cell23_1392441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 5].length) (baseStart_1392441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392441 prefixEnd_1392441 := by exact prefixLift 1392441
  have htrace : WordTrace (prefixWord ++ tailWord_1392441) baseStart_1392441 baseEnd_1392441 := by
    simpa [prefixWord, tailWord_1392441, baseEnd_1392441] using wordTrace_append hprefix tailTrace_1392441
  have hstable : (prefixWord ++ tailWord_1392441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392441).length < 2 ^ (prefixWord ++ tailWord_1392441).sum := by decide
  have hdescent : baseEnd_1392441 < baseStart_1392441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392444 : List Nat := [2, 2, 2, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_1392444 : Nat := 118140960795 + 1392444 * 2 ^ 59
def prefixEnd_1392444 : Nat := 4983230072969 + 3 ^ 40 * 1392444 * 2
def baseEnd_1392444 : Nat := 714993056469255290146273

theorem tailTrace_1392444 : CollatzResearch.WordTrace tailWord_1392444 prefixEnd_1392444 714993056469255290146273 := by
  unfold tailWord_1392444
  simp only [CollatzResearch.WordTrace]
  refine ⟨25393302483710336673624193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33857736644947115564832257 25393302483710336673624193)
  ·
    refine ⟨19044976862782752505218145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25393302483710336673624193 19044976862782752505218145)
    ·
      refine ⟨14283732647087064378913609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19044976862782752505218145 14283732647087064378913609)
      ·
        refine ⟨10712799485315298284185207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14283732647087064378913609 10712799485315298284185207)
        ·
          refine ⟨16069199227972947426277811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10712799485315298284185207 16069199227972947426277811)
          ·
            refine ⟨24103798841959421139416717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16069199227972947426277811 24103798841959421139416717)
            ·
              refine ⟨9038924565734782927281269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24103798841959421139416717 9038924565734782927281269)
              ·
                refine ⟨847399178037635899432619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9038924565734782927281269 847399178037635899432619)
                ·
                  refine ⟨1271098767056453849148929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847399178037635899432619 1271098767056453849148929)
                  ·
                    refine ⟨953324075292340386861697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271098767056453849148929 953324075292340386861697)
                    ·
                      refine ⟨714993056469255290146273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953324075292340386861697 714993056469255290146273)
                      ·
                        rfl

theorem cell23_1392444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_1392444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392444 prefixEnd_1392444 := by exact prefixLift 1392444
  have htrace : WordTrace (prefixWord ++ tailWord_1392444) baseStart_1392444 baseEnd_1392444 := by
    simpa [prefixWord, tailWord_1392444, baseEnd_1392444] using wordTrace_append hprefix tailTrace_1392444
  have hstable : (prefixWord ++ tailWord_1392444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392444).length < 2 ^ (prefixWord ++ tailWord_1392444).sum := by decide
  have hdescent : baseEnd_1392444 < baseStart_1392444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392447 : List Nat := [1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 3]
def baseStart_1392447 : Nat := 118140960795 + 1392447 * 2 ^ 59
def prefixEnd_1392447 : Nat := 4983230072969 + 3 ^ 40 * 1392447 * 2
def baseEnd_1392447 : Nat := 714994596911218778408759

theorem tailTrace_1392447 : CollatzResearch.WordTrace tailWord_1392447 prefixEnd_1392447 714994596911218778408759 := by
  unfold tailWord_1392447
  simp only [CollatzResearch.WordTrace]
  refine ⟨50786714386409804859607595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33857809590939869906405063 50786714386409804859607595)
  ·
    refine ⟨76180071579614707289411393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50786714386409804859607595 76180071579614707289411393)
    ·
      refine ⟨57135053684711030467058545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76180071579614707289411393 57135053684711030467058545)
      ·
        refine ⟨42851290263533272850293909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57135053684711030467058545 42851290263533272850293909)
        ·
          refine ⟨2008654231103122164857527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42851290263533272850293909 2008654231103122164857527)
          ·
            refine ⟨3012981346654683247286291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008654231103122164857527 3012981346654683247286291)
            ·
              refine ⟨4519472019982024870929437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012981346654683247286291 4519472019982024870929437)
              ·
                refine ⟨1694802007493259326598539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4519472019982024870929437 1694802007493259326598539)
                ·
                  refine ⟨2542203011239888989897809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694802007493259326598539 2542203011239888989897809)
                  ·
                    refine ⟨1906652258429916742423357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2542203011239888989897809 1906652258429916742423357)
                    ·
                      refine ⟨714994596911218778408759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1906652258429916742423357 714994596911218778408759)
                      ·
                        rfl

theorem cell23_1392447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_1392447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392447 prefixEnd_1392447 := by exact prefixLift 1392447
  have htrace : WordTrace (prefixWord ++ tailWord_1392447) baseStart_1392447 baseEnd_1392447 := by
    simpa [prefixWord, tailWord_1392447, baseEnd_1392447] using wordTrace_append hprefix tailTrace_1392447
  have hstable : (prefixWord ++ tailWord_1392447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392447).length < 2 ^ (prefixWord ++ tailWord_1392447).sum := by decide
  have hdescent : baseEnd_1392447 < baseStart_1392447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392454 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1392454 : Nat := 118140960795 + 1392454 * 2 ^ 59
def prefixEnd_1392454 : Nat := 4983230072969 + 3 ^ 40 * 1392454 * 2
def baseEnd_1392454 : Nat := 238332730425266750340409

theorem tailTrace_1392454 : CollatzResearch.WordTrace tailWord_1392454 prefixEnd_1392454 238332730425266750340409 := by
  unfold tailWord_1392454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587092803043263907972263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33857979798256296703408277 1587092803043263907972263)
  ·
    refine ⟨2380639204564895861958395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587092803043263907972263 2380639204564895861958395)
    ·
      refine ⟨3570958806847343792937593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2380639204564895861958395 3570958806847343792937593)
      ·
        refine ⟨2678219105135507844703195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3570958806847343792937593 2678219105135507844703195)
        ·
          refine ⟨4017328657703261767054793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678219105135507844703195 4017328657703261767054793)
          ·
            refine ⟨3012996493277446325291095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4017328657703261767054793 3012996493277446325291095)
            ·
              refine ⟨4519494739916169487936643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012996493277446325291095 4519494739916169487936643)
              ·
                refine ⟨6779242109874254231904965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4519494739916169487936643 6779242109874254231904965)
                ·
                  refine ⟨1271107895601422668482181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6779242109874254231904965 1271107895601422668482181)
                  ·
                    refine ⟨238332730425266750340409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1271107895601422668482181 238332730425266750340409)
                    ·
                      rfl

theorem cell23_1392454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1392454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392454 prefixEnd_1392454 := by exact prefixLift 1392454
  have htrace : WordTrace (prefixWord ++ tailWord_1392454) baseStart_1392454 baseEnd_1392454 := by
    simpa [prefixWord, tailWord_1392454, baseEnd_1392454] using wordTrace_append hprefix tailTrace_1392454
  have hstable : (prefixWord ++ tailWord_1392454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392454).length < 2 ^ (prefixWord ++ tailWord_1392454).sum := by decide
  have hdescent : baseEnd_1392454 < baseStart_1392454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392461 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1392461 : Nat := 118140960795 + 1392461 * 2 ^ 59
def prefixEnd_1392461 : Nat := 4983230072969 + 3 ^ 40 * 1392461 * 2
def baseEnd_1392461 : Nat := 715001785640381723633695

theorem tailTrace_1392461 : CollatzResearch.WordTrace tailWord_1392461 prefixEnd_1392461 715001785640381723633695 := by
  unfold tailWord_1392461
  simp only [CollatzResearch.WordTrace]
  refine ⟨50787225008359085250617237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33858150005572723500411491 50787225008359085250617237)
  ·
    refine ⟨2380651172266832121122683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50787225008359085250617237 2380651172266832121122683)
    ·
      refine ⟨3570976758400248181684025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2380651172266832121122683 3570976758400248181684025)
      ·
        refine ⟨2678232568800186136263019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3570976758400248181684025 2678232568800186136263019)
        ·
          refine ⟨4017348853200279204394529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678232568800186136263019 4017348853200279204394529)
          ·
            refine ⟨3013011639900209403295897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4017348853200279204394529 3013011639900209403295897)
            ·
              refine ⟨2259758729925157052471923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013011639900209403295897 2259758729925157052471923)
              ·
                refine ⟨3389638094887735578707885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259758729925157052471923 3389638094887735578707885)
                ·
                  refine ⟨1271114285582900842015457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3389638094887735578707885 1271114285582900842015457)
                  ·
                    refine ⟨953335714187175631511593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271114285582900842015457 953335714187175631511593)
                    ·
                      refine ⟨715001785640381723633695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953335714187175631511593 715001785640381723633695)
                      ·
                        rfl

theorem cell23_1392461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1392461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392461 prefixEnd_1392461 := by exact prefixLift 1392461
  have htrace : WordTrace (prefixWord ++ tailWord_1392461) baseStart_1392461 baseEnd_1392461 := by
    simpa [prefixWord, tailWord_1392461, baseEnd_1392461] using wordTrace_append hprefix tailTrace_1392461
  have hstable : (prefixWord ++ tailWord_1392461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392461).length < 2 ^ (prefixWord ++ tailWord_1392461).sum := by decide
  have hdescent : baseEnd_1392461 < baseStart_1392461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392493 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_1392493 : Nat := 118140960795 + 1392493 * 2 ^ 59
def prefixEnd_1392493 : Nat := 4983230072969 + 3 ^ 40 * 1392493 * 2
def baseEnd_1392493 : Nat := 238339405673775199477849

theorem tailTrace_1392493 : CollatzResearch.WordTrace tailWord_1392493 prefixEnd_1392493 238339405673775199477849 := by
  unfold tailWord_1392493
  simp only [CollatzResearch.WordTrace]
  refine ⟨50788392144243154715782133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33858928096162103143854755 50788392144243154715782133)
  ·
    refine ⟨4761411763522795754604575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50788392144243154715782133 4761411763522795754604575)
    ·
      refine ⟨7142117645284193631906863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4761411763522795754604575 7142117645284193631906863)
      ·
        refine ⟨10713176467926290447860295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142117645284193631906863 10713176467926290447860295)
        ·
          refine ⟨16069764701889435671790443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713176467926290447860295 16069764701889435671790443)
          ·
            refine ⟨24104647052834153507685665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16069764701889435671790443 24104647052834153507685665)
            ·
              refine ⟨18078485289625615130764249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24104647052834153507685665 18078485289625615130764249)
              ·
                refine ⟨13558863967219211348073187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18078485289625615130764249 13558863967219211348073187)
                ·
                  refine ⟨20338295950828817022109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13558863967219211348073187 20338295950828817022109781)
                  ·
                    refine ⟨238339405673775199477849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20338295950828817022109781 238339405673775199477849)
                    ·
                      rfl

theorem cell23_1392493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_1392493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392493 prefixEnd_1392493 := by exact prefixLift 1392493
  have htrace : WordTrace (prefixWord ++ tailWord_1392493) baseStart_1392493 baseEnd_1392493 := by
    simpa [prefixWord, tailWord_1392493, baseEnd_1392493] using wordTrace_append hprefix tailTrace_1392493
  have hstable : (prefixWord ++ tailWord_1392493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392493).length < 2 ^ (prefixWord ++ tailWord_1392493).sum := by decide
  have hdescent : baseEnd_1392493 < baseStart_1392493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392503 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_1392503 : Nat := 118140960795 + 1392503 * 2 ^ 59
def prefixEnd_1392503 : Nat := 4983230072969 + 3 ^ 40 * 1392503 * 2
def baseEnd_1392503 : Nat := 715023351827870559308501

theorem tailTrace_1392503 : CollatzResearch.WordTrace tailWord_1392503 prefixEnd_1392503 715023351827870559308501 := by
  unfold tailWord_1392503
  simp only [CollatzResearch.WordTrace]
  refine ⟨50788756874206926423646163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33859171249471284282430775 50788756874206926423646163)
  ·
    refine ⟨76183135311310389635469245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50788756874206926423646163 76183135311310389635469245)
    ·
      refine ⟨28568675741741396113300967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76183135311310389635469245 28568675741741396113300967)
      ·
        refine ⟨42853013612612094169951451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28568675741741396113300967 42853013612612094169951451)
        ·
          refine ⟨64279520418918141254927177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42853013612612094169951451 64279520418918141254927177)
          ·
            refine ⟨48209640314188605941195383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64279520418918141254927177 48209640314188605941195383)
            ·
              refine ⟨72314460471282908911793075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48209640314188605941195383 72314460471282908911793075)
              ·
                refine ⟨108471690706924363367689613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72314460471282908911793075 108471690706924363367689613)
                ·
                  refine ⟨40676884015096636262883605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108471690706924363367689613 40676884015096636262883605)
                  ·
                    refine ⟨1906728938207654824822669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40676884015096636262883605 1906728938207654824822669)
                    ·
                      refine ⟨715023351827870559308501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1906728938207654824822669 715023351827870559308501)
                      ·
                        rfl

theorem cell23_1392503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_1392503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392503 prefixEnd_1392503 := by exact prefixLift 1392503
  have htrace : WordTrace (prefixWord ++ tailWord_1392503) baseStart_1392503 baseEnd_1392503 := by
    simpa [prefixWord, tailWord_1392503, baseEnd_1392503] using wordTrace_append hprefix tailTrace_1392503
  have hstable : (prefixWord ++ tailWord_1392503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392503).length < 2 ^ (prefixWord ++ tailWord_1392503).sum := by decide
  have hdescent : baseEnd_1392503 < baseStart_1392503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392517 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 4, 2, 2]
def baseStart_1392517 : Nat := 118140960795 + 1392517 * 2 ^ 59
def prefixEnd_1392517 : Nat := 4983230072969 + 3 ^ 40 * 1392517 * 2
def baseEnd_1392517 : Nat := 715030540557033504533437

theorem tailTrace_1392517 : CollatzResearch.WordTrace tailWord_1392517 prefixEnd_1392517 715030540557033504533437 := by
  unfold tailWord_1392517
  simp only [CollatzResearch.WordTrace]
  refine ⟨50789267496156206814655805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33859511664104137876437203 50789267496156206814655805)
  ·
    refine ⟨19045975311058577555495927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50789267496156206814655805 19045975311058577555495927)
    ·
      refine ⟨28568962966587866333243891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19045975311058577555495927 28568962966587866333243891)
      ·
        refine ⟨42853444449881799499865837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28568962966587866333243891 42853444449881799499865837)
        ·
          refine ⟨16070041668705674812449689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42853444449881799499865837 16070041668705674812449689)
          ·
            refine ⟨12052531251529256109337267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16070041668705674812449689 12052531251529256109337267)
            ·
              refine ⟨18078796877293884164005901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12052531251529256109337267 18078796877293884164005901)
              ·
                refine ⟨6779548828985206561502213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18078796877293884164005901 6779548828985206561502213)
                ·
                  refine ⟨1271165405434726230281665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6779548828985206561502213 1271165405434726230281665)
                  ·
                    refine ⟨953374054076044672711249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271165405434726230281665 953374054076044672711249)
                    ·
                      refine ⟨715030540557033504533437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953374054076044672711249 715030540557033504533437)
                      ·
                        rfl

theorem cell23_1392517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_1392517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392517 prefixEnd_1392517 := by exact prefixLift 1392517
  have htrace : WordTrace (prefixWord ++ tailWord_1392517) baseStart_1392517 baseEnd_1392517 := by
    simpa [prefixWord, tailWord_1392517, baseEnd_1392517] using wordTrace_append hprefix tailTrace_1392517
  have hstable : (prefixWord ++ tailWord_1392517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392517).length < 2 ^ (prefixWord ++ tailWord_1392517).sum := by decide
  have hdescent : baseEnd_1392517 < baseStart_1392517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392560 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 6, 5, 2]
def baseStart_1392560 : Nat := 118140960795 + 1392560 * 2 ^ 59
def prefixEnd_1392560 : Nat := 4983230072969 + 3 ^ 40 * 1392560 * 2
def baseEnd_1392560 : Nat := 715052620225176836295739

theorem tailTrace_1392560 : CollatzResearch.WordTrace tailWord_1392560 prefixEnd_1392560 715052620225176836295739 := by
  unfold tailWord_1392560
  simp only [CollatzResearch.WordTrace]
  refine ⟨25395417917500212579235567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33860557223333616772314089 25395417917500212579235567)
  ·
    refine ⟨38093126876250318868853351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25395417917500212579235567 38093126876250318868853351)
    ·
      refine ⟨57139690314375478303280027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38093126876250318868853351 57139690314375478303280027)
      ·
        refine ⟨85709535471563217454920041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57139690314375478303280027 85709535471563217454920041)
        ·
          refine ⟨64282151603672413091190031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85709535471563217454920041 64282151603672413091190031)
          ·
            refine ⟨96423227405508619636785047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64282151603672413091190031 96423227405508619636785047)
            ·
              refine ⟨144634841108262929455177571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96423227405508619636785047 144634841108262929455177571)
              ·
                refine ⟨216952261662394394182766357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144634841108262929455177571 216952261662394394182766357)
                ·
                  refine ⟨10169637265424737227317173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216952261662394394182766357 10169637265424737227317173)
                  ·
                    refine ⟨953403493633569115060985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10169637265424737227317173 953403493633569115060985)
                    ·
                      refine ⟨715052620225176836295739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953403493633569115060985 715052620225176836295739)
                      ·
                        rfl

theorem cell23_1392560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 5, 2].length) (baseStart_1392560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392560 prefixEnd_1392560 := by exact prefixLift 1392560
  have htrace : WordTrace (prefixWord ++ tailWord_1392560) baseStart_1392560 baseEnd_1392560 := by
    simpa [prefixWord, tailWord_1392560, baseEnd_1392560] using wordTrace_append hprefix tailTrace_1392560
  have hstable : (prefixWord ++ tailWord_1392560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392560).length < 2 ^ (prefixWord ++ tailWord_1392560).sum := by decide
  have hdescent : baseEnd_1392560 < baseStart_1392560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392563 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5]
def baseStart_1392563 : Nat := 118140960795 + 1392563 * 2 ^ 59
def prefixEnd_1392563 : Nat := 4983230072969 + 3 ^ 40 * 1392563 * 2
def baseEnd_1392563 : Nat := 715054160667140324558225

theorem tailTrace_1392563 : CollatzResearch.WordTrace tailWord_1392563 prefixEnd_1392563 715054160667140324558225 := by
  unfold tailWord_1392563
  simp only [CollatzResearch.WordTrace]
  refine ⟨50790945253989556670830343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33860630169326371113886895 50790945253989556670830343)
  ·
    refine ⟨76186417880984335006245515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50790945253989556670830343 76186417880984335006245515)
    ·
      refine ⟨114279626821476502509368273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76186417880984335006245515 114279626821476502509368273)
      ·
        refine ⟨85709720116107376882026205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114279626821476502509368273 85709720116107376882026205)
        ·
          refine ⟨32141145043540266330759827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85709720116107376882026205 32141145043540266330759827)
          ·
            refine ⟨48211717565310399496139741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32141145043540266330759827 48211717565310399496139741)
            ·
              refine ⟨18079394086991399811052403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48211717565310399496139741 18079394086991399811052403)
              ·
                refine ⟨27119091130487099716578605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18079394086991399811052403 27119091130487099716578605)
                ·
                  refine ⟨10169659173932662393716977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27119091130487099716578605 10169659173932662393716977)
                  ·
                    refine ⟨7627244380449496795287733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10169659173932662393716977 7627244380449496795287733)
                    ·
                      refine ⟨715054160667140324558225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7627244380449496795287733 715054160667140324558225)
                      ·
                        rfl

theorem cell23_1392563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_1392563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392563 prefixEnd_1392563 := by exact prefixLift 1392563
  have htrace : WordTrace (prefixWord ++ tailWord_1392563) baseStart_1392563 baseEnd_1392563 := by
    simpa [prefixWord, tailWord_1392563, baseEnd_1392563] using wordTrace_append hprefix tailTrace_1392563
  have hstable : (prefixWord ++ tailWord_1392563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392563).length < 2 ^ (prefixWord ++ tailWord_1392563).sum := by decide
  have hdescent : baseEnd_1392563 < baseStart_1392563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392574 : List Nat := [4, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_1392574 : Nat := 118140960795 + 1392574 * 2 ^ 59
def prefixEnd_1392574 : Nat := 4983230072969 + 3 ^ 40 * 1392574 * 2
def baseEnd_1392574 : Nat := 79451089883815531280075

theorem tailTrace_1392574 : CollatzResearch.WordTrace tailWord_1392574 prefixEnd_1392574 79451089883815531280075 := by
  unfold tailWord_1392574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348918307118713193685097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33860897637966470366320517 6348918307118713193685097)
  ·
    refine ⟨4761688730339034895263823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6348918307118713193685097 4761688730339034895263823)
    ·
      refine ⟨7142533095508552342895735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4761688730339034895263823 7142533095508552342895735)
      ·
        refine ⟨10713799643262828514343603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7142533095508552342895735 10713799643262828514343603)
        ·
          refine ⟨16070699464894242771515405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713799643262828514343603 16070699464894242771515405)
          ·
            refine ⟨6026512299335341039318277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16070699464894242771515405 6026512299335341039318277)
            ·
              refine ⟨1129971056125376444872177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6026512299335341039318277 1129971056125376444872177)
              ·
                refine ⟨847478292094032333654133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129971056125376444872177 847478292094032333654133)
                ·
                  refine ⟨79451089883815531280075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 847478292094032333654133 79451089883815531280075)
                  ·
                    rfl

theorem cell23_1392574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_1392574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392574 prefixEnd_1392574 := by exact prefixLift 1392574
  have htrace : WordTrace (prefixWord ++ tailWord_1392574) baseStart_1392574 baseEnd_1392574 := by
    simpa [prefixWord, tailWord_1392574, baseEnd_1392574] using wordTrace_append hprefix tailTrace_1392574
  have hstable : (prefixWord ++ tailWord_1392574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392574).length < 2 ^ (prefixWord ++ tailWord_1392574).sum := by decide
  have hdescent : baseEnd_1392574 < baseStart_1392574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392583 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 2, 8]
def baseStart_1392583 : Nat := 118140960795 + 1392583 * 2 ^ 59
def prefixEnd_1392583 : Nat := 4983230072969 + 3 ^ 40 * 1392583 * 2
def baseEnd_1392583 : Nat := 238354810093410082102711

theorem tailTrace_1392583 : CollatzResearch.WordTrace tailWord_1392583 prefixEnd_1392583 238354810093410082102711 := by
  unfold tailWord_1392583
  simp only [CollatzResearch.WordTrace]
  refine ⟨50791674713917100086558403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33861116475944733391038935 50791674713917100086558403)
  ·
    refine ⟨76187512070875650129837605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50791674713917100086558403 76187512070875650129837605)
    ·
      refine ⟨14285158513289184399344551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76187512070875650129837605 14285158513289184399344551)
      ·
        refine ⟨21427737769933776599016827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285158513289184399344551 21427737769933776599016827)
        ·
          refine ⟨32141606654900664898525241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21427737769933776599016827 32141606654900664898525241)
          ·
            refine ⟨24106204991175498673893931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32141606654900664898525241 24106204991175498673893931)
            ·
              refine ⟨36159307486763248010840897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24106204991175498673893931 36159307486763248010840897)
              ·
                refine ⟨27119480615072436008130673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36159307486763248010840897 27119480615072436008130673)
                ·
                  refine ⟨20339610461304327006098005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27119480615072436008130673 20339610461304327006098005)
                  ·
                    refine ⟨238354810093410082102711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20339610461304327006098005 238354810093410082102711)
                    ·
                      rfl

theorem cell23_1392583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_1392583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392583 prefixEnd_1392583 := by exact prefixLift 1392583
  have htrace : WordTrace (prefixWord ++ tailWord_1392583) baseStart_1392583 baseEnd_1392583 := by
    simpa [prefixWord, tailWord_1392583, baseEnd_1392583] using wordTrace_append hprefix tailTrace_1392583
  have hstable : (prefixWord ++ tailWord_1392583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392583).length < 2 ^ (prefixWord ++ tailWord_1392583).sum := by decide
  have hdescent : baseEnd_1392583 < baseStart_1392583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392590 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1392590 : Nat := 118140960795 + 1392590 * 2 ^ 59
def prefixEnd_1392590 : Nat := 4983230072969 + 3 ^ 40 * 1392590 * 2
def baseEnd_1392590 : Nat := 715068024644811718920601

theorem tailTrace_1392590 : CollatzResearch.WordTrace tailWord_1392590 prefixEnd_1392590 715068024644811718920601 := by
  unfold tailWord_1392590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348991253111467535257903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33861286683261160188042149 6348991253111467535257903)
  ·
    refine ⟨9523486879667201302886855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6348991253111467535257903 9523486879667201302886855)
    ·
      refine ⟨14285230319500801954330283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9523486879667201302886855 14285230319500801954330283)
      ·
        refine ⟨21427845479251202931495425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14285230319500801954330283 21427845479251202931495425)
        ·
          refine ⟨16070884109438402198621569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21427845479251202931495425 16070884109438402198621569)
          ·
            refine ⟨12053163082078801648966177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16070884109438402198621569 12053163082078801648966177)
            ·
              refine ⟨9039872311559101236724633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12053163082078801648966177 9039872311559101236724633)
              ·
                refine ⟨6779904233669325927543475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9039872311559101236724633 6779904233669325927543475)
                ·
                  refine ⟨10169856350503988891315213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6779904233669325927543475 10169856350503988891315213)
                  ·
                    refine ⟨3813696131438995834243205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10169856350503988891315213 3813696131438995834243205)
                    ·
                      refine ⟨715068024644811718920601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3813696131438995834243205 715068024644811718920601)
                      ·
                        rfl

theorem cell23_1392590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1392590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392590 prefixEnd_1392590 := by exact prefixLift 1392590
  have htrace : WordTrace (prefixWord ++ tailWord_1392590) baseStart_1392590 baseEnd_1392590 := by
    simpa [prefixWord, tailWord_1392590, baseEnd_1392590] using wordTrace_append hprefix tailTrace_1392590
  have hstable : (prefixWord ++ tailWord_1392590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392590).length < 2 ^ (prefixWord ++ tailWord_1392590).sum := by decide
  have hdescent : baseEnd_1392590 < baseStart_1392590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392607 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 4]
def baseStart_1392607 : Nat := 118140960795 + 1392607 * 2 ^ 59
def prefixEnd_1392607 : Nat := 4983230072969 + 3 ^ 40 * 1392607 * 2
def baseEnd_1392607 : Nat := 715076753815938152408023

theorem tailTrace_1392607 : CollatzResearch.WordTrace tailWord_1392607 prefixEnd_1392607 715076753815938152408023 := by
  unfold tailWord_1392607
  simp only [CollatzResearch.WordTrace]
  refine ⟨50792550065830152185432075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33861700043886768123621383 50792550065830152185432075)
  ·
    refine ⟨76188825098745228278148113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50792550065830152185432075 76188825098745228278148113)
    ·
      refine ⟨57141618824058921208611085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76188825098745228278148113 57141618824058921208611085)
      ·
        refine ⟨21428107059022095453229157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57141618824058921208611085 21428107059022095453229157)
        ·
          refine ⟨4017770073566642897480467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21428107059022095453229157 4017770073566642897480467)
          ·
            refine ⟨6026655110349964346220701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4017770073566642897480467 6026655110349964346220701)
            ·
              refine ⟨2259995666381236629832763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6026655110349964346220701 2259995666381236629832763)
              ·
                refine ⟨3389993499571854944749145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259995666381236629832763 3389993499571854944749145)
                ·
                  refine ⟨2542495124678891208561859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3389993499571854944749145 2542495124678891208561859)
                  ·
                    refine ⟨3813742687018336812842789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2542495124678891208561859 3813742687018336812842789)
                    ·
                      refine ⟨715076753815938152408023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3813742687018336812842789 715076753815938152408023)
                      ·
                        rfl

theorem cell23_1392607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_1392607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392607 prefixEnd_1392607 := by exact prefixLift 1392607
  have htrace : WordTrace (prefixWord ++ tailWord_1392607) baseStart_1392607 baseEnd_1392607 := by
    simpa [prefixWord, tailWord_1392607, baseEnd_1392607] using wordTrace_append hprefix tailTrace_1392607
  have hstable : (prefixWord ++ tailWord_1392607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392607).length < 2 ^ (prefixWord ++ tailWord_1392607).sum := by decide
  have hdescent : baseEnd_1392607 < baseStart_1392607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392677 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_1392677 : Nat := 118140960795 + 1392677 * 2 ^ 59
def prefixEnd_1392677 : Nat := 4983230072969 + 3 ^ 40 * 1392677 * 2
def baseEnd_1392677 : Nat := 238370899153917626177567

theorem tailTrace_1392677 : CollatzResearch.WordTrace tailWord_1392677 prefixEnd_1392677 238370899153917626177567 := by
  unfold tailWord_1392677
  simp only [CollatzResearch.WordTrace]
  refine ⟨50795103175576554140480285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33863402117051036093653523 50795103175576554140480285)
  ·
    refine ⟨19048163690841207802680107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50795103175576554140480285 19048163690841207802680107)
    ·
      refine ⟨28572245536261811704020161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19048163690841207802680107 28572245536261811704020161)
      ·
        refine ⟨21429184152196358778015121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28572245536261811704020161 21429184152196358778015121)
        ·
          refine ⟨16071888114147269083511341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21429184152196358778015121 16071888114147269083511341)
          ·
            refine ⟨6026958042805225906316753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16071888114147269083511341 6026958042805225906316753)
            ·
              refine ⟨4520218532103919429737565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6026958042805225906316753 4520218532103919429737565)
              ·
                refine ⟨1695081949538969786151587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4520218532103919429737565 1695081949538969786151587)
                ·
                  refine ⟨2542622924308454679227381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695081949538969786151587 2542622924308454679227381)
                  ·
                    refine ⟨238370899153917626177567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2542622924308454679227381 238370899153917626177567)
                    ·
                      rfl

theorem cell23_1392677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_1392677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392677 prefixEnd_1392677 := by exact prefixLift 1392677
  have htrace : WordTrace (prefixWord ++ tailWord_1392677) baseStart_1392677 baseEnd_1392677 := by
    simpa [prefixWord, tailWord_1392677, baseEnd_1392677] using wordTrace_append hprefix tailTrace_1392677
  have hstable : (prefixWord ++ tailWord_1392677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392677).length < 2 ^ (prefixWord ++ tailWord_1392677).sum := by decide
  have hdescent : baseEnd_1392677 < baseStart_1392677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392714 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_1392714 : Nat := 118140960795 + 1392714 * 2 ^ 59
def prefixEnd_1392714 : Nat := 4983230072969 + 3 ^ 40 * 1392714 * 2
def baseEnd_1392714 : Nat := 715131696245969233770031

theorem tailTrace_1392714 : CollatzResearch.WordTrace tailWord_1392714 prefixEnd_1392714 715131696245969233770031 := by
  unfold tailWord_1392714
  simp only [CollatzResearch.WordTrace]
  refine ⟨12699113169110627364894299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33864301784295006306384797 12699113169110627364894299)
  ·
    refine ⟨19048669753665941047341449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12699113169110627364894299 19048669753665941047341449)
    ·
      refine ⟨14286502315249455785506087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19048669753665941047341449 14286502315249455785506087)
      ·
        refine ⟨21429753472874183678259131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14286502315249455785506087 21429753472874183678259131)
        ·
          refine ⟨32144630209311275517388697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21429753472874183678259131 32144630209311275517388697)
          ·
            refine ⟨24108472656983456638041523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32144630209311275517388697 24108472656983456638041523)
            ·
              refine ⟨36162708985475184957062285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24108472656983456638041523 36162708985475184957062285)
              ·
                refine ⟨13561015869553194358898357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36162708985475184957062285 13561015869553194358898357)
                ·
                  refine ⟨1271345237770611971146721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13561015869553194358898357 1271345237770611971146721)
                  ·
                    refine ⟨953508928327958978360041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271345237770611971146721 953508928327958978360041)
                    ·
                      refine ⟨715131696245969233770031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953508928327958978360041 715131696245969233770031)
                      ·
                        rfl

theorem cell23_1392714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_1392714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392714 prefixEnd_1392714 := by exact prefixLift 1392714
  have htrace : WordTrace (prefixWord ++ tailWord_1392714) baseStart_1392714 baseEnd_1392714 := by
    simpa [prefixWord, tailWord_1392714, baseEnd_1392714] using wordTrace_append hprefix tailTrace_1392714
  have hstable : (prefixWord ++ tailWord_1392714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392714).length < 2 ^ (prefixWord ++ tailWord_1392714).sum := by decide
  have hdescent : baseEnd_1392714 < baseStart_1392714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392748 : List Nat := [2, 2, 1, 1, 3, 4, 1, 4, 1, 2, 2]
def baseStart_1392748 : Nat := 118140960795 + 1392748 * 2 ^ 59
def prefixEnd_1392748 : Nat := 4983230072969 + 3 ^ 40 * 1392748 * 2
def baseEnd_1392748 : Nat := 715149154588222100744875

theorem tailTrace_1392748 : CollatzResearch.WordTrace tailWord_1392748 prefixEnd_1392748 715149154588222100744875 := by
  unfold tailWord_1392748
  simp only [CollatzResearch.WordTrace]
  refine ⟨25398846379159666633157449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33865128505546222177543265 25398846379159666633157449)
  ·
    refine ⟨19049134784369749974868087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25398846379159666633157449 19049134784369749974868087)
    ·
      refine ⟨28573702176554624962302131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19049134784369749974868087 28573702176554624962302131)
      ·
        refine ⟨42860553264831937443453197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28573702176554624962302131 42860553264831937443453197)
        ·
          refine ⟨16072707474311976541294949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42860553264831937443453197 16072707474311976541294949)
          ·
            refine ⟨3013632651433495601492803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16072707474311976541294949 3013632651433495601492803)
            ·
              refine ⟨4520448977150243402239205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013632651433495601492803 4520448977150243402239205)
              ·
                refine ⟨847584183215670637919851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4520448977150243402239205 847584183215670637919851)
                ·
                  refine ⟨1271376274823505956879777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847584183215670637919851 1271376274823505956879777)
                  ·
                    refine ⟨953532206117629467659833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271376274823505956879777 953532206117629467659833)
                    ·
                      refine ⟨715149154588222100744875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953532206117629467659833 715149154588222100744875)
                      ·
                        rfl

theorem cell23_1392748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_1392748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392748 prefixEnd_1392748 := by exact prefixLift 1392748
  have htrace : WordTrace (prefixWord ++ tailWord_1392748) baseStart_1392748 baseEnd_1392748 := by
    simpa [prefixWord, tailWord_1392748, baseEnd_1392748] using wordTrace_append hprefix tailTrace_1392748
  have hstable : (prefixWord ++ tailWord_1392748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392748).length < 2 ^ (prefixWord ++ tailWord_1392748).sum := by decide
  have hdescent : baseEnd_1392748 < baseStart_1392748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392760 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1392760 : Nat := 118140960795 + 1392760 * 2 ^ 59
def prefixEnd_1392760 : Nat := 4983230072969 + 3 ^ 40 * 1392760 * 2
def baseEnd_1392760 : Nat := 715155316356076053794819

theorem tailTrace_1392760 : CollatzResearch.WordTrace tailWord_1392760 prefixEnd_1392760 715155316356076053794819 := by
  unfold tailWord_1392760
  simp only [CollatzResearch.WordTrace]
  refine ⟨25399065217137929657875867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33865420289517239543834489 25399065217137929657875867)
  ·
    refine ⟨38098597825706894486813801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25399065217137929657875867 38098597825706894486813801)
    ·
      refine ⟨28573948369280170865110351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38098597825706894486813801 28573948369280170865110351)
      ·
        refine ⟨42860922553920256297665527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28573948369280170865110351 42860922553920256297665527)
        ·
          refine ⟨64291383830880384446498291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42860922553920256297665527 64291383830880384446498291)
          ·
            refine ⟨96437075746320576669747437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64291383830880384446498291 96437075746320576669747437)
            ·
              refine ⟨36163903404870216251155289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96437075746320576669747437 36163903404870216251155289)
              ·
                refine ⟨27122927553652662188366467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36163903404870216251155289 27122927553652662188366467)
                ·
                  refine ⟨40684391330478993282549701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27122927553652662188366467 40684391330478993282549701)
                  ·
                    refine ⟨7628323374464811240478069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40684391330478993282549701 7628323374464811240478069)
                    ·
                      refine ⟨715155316356076053794819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7628323374464811240478069 715155316356076053794819)
                      ·
                        rfl

theorem cell23_1392760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1392760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392760 prefixEnd_1392760 := by exact prefixLift 1392760
  have htrace : WordTrace (prefixWord ++ tailWord_1392760) baseStart_1392760 baseEnd_1392760 := by
    simpa [prefixWord, tailWord_1392760, baseEnd_1392760] using wordTrace_append hprefix tailTrace_1392760
  have hstable : (prefixWord ++ tailWord_1392760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392760).length < 2 ^ (prefixWord ++ tailWord_1392760).sum := by decide
  have hdescent : baseEnd_1392760 < baseStart_1392760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392764 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_1392764 : Nat := 118140960795 + 1392764 * 2 ^ 59
def prefixEnd_1392764 : Nat := 4983230072969 + 3 ^ 40 * 1392764 * 2
def baseEnd_1392764 : Nat := 715157370278694038144801

theorem tailTrace_1392764 : CollatzResearch.WordTrace tailWord_1392764 prefixEnd_1392764 715157370278694038144801 := by
  unfold tailWord_1392764
  simp only [CollatzResearch.WordTrace]
  refine ⟨25399138163130683999448673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33865517550840911999264897 25399138163130683999448673)
  ·
    refine ⟨19049353622348012999586505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25399138163130683999448673 19049353622348012999586505)
    ·
      refine ⟨14287015216761009749689879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19049353622348012999586505 14287015216761009749689879)
      ·
        refine ⟨21430522825141514624534819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14287015216761009749689879 21430522825141514624534819)
        ·
          refine ⟨32145784237712271936802229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21430522825141514624534819 32145784237712271936802229)
          ·
            refine ⟨3013667272285525494075209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32145784237712271936802229 3013667272285525494075209)
            ·
              refine ⟨2260250454214144120556407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3013667272285525494075209 2260250454214144120556407)
              ·
                refine ⟨3390375681321216180834611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260250454214144120556407 3390375681321216180834611)
                ·
                  refine ⟨5085563521981824271251917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3390375681321216180834611 5085563521981824271251917)
                  ·
                    refine ⟨1907086320743184101719469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5085563521981824271251917 1907086320743184101719469)
                    ·
                      refine ⟨715157370278694038144801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907086320743184101719469 715157370278694038144801)
                      ·
                        rfl

theorem cell23_1392764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_1392764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392764 prefixEnd_1392764 := by exact prefixLift 1392764
  have htrace : WordTrace (prefixWord ++ tailWord_1392764) baseStart_1392764 baseEnd_1392764 := by
    simpa [prefixWord, tailWord_1392764, baseEnd_1392764] using wordTrace_append hprefix tailTrace_1392764
  have hstable : (prefixWord ++ tailWord_1392764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392764).length < 2 ^ (prefixWord ++ tailWord_1392764).sum := by decide
  have hdescent : baseEnd_1392764 < baseStart_1392764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392797 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1392797 : Nat := 118140960795 + 1392797 * 2 ^ 59
def prefixEnd_1392797 : Nat := 4983230072969 + 3 ^ 40 * 1392797 * 2
def baseEnd_1392797 : Nat := 238391438380097469677383

theorem tailTrace_1392797 : CollatzResearch.WordTrace tailWord_1392797 prefixEnd_1392797 238391438380097469677383 := by
  unfold tailWord_1392797
  simp only [CollatzResearch.WordTrace]
  refine ⟨50799479935141814634848645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33866319956761209756565763 50799479935141814634848645)
  ·
    refine ⟨9524902487839090244034121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50799479935141814634848645 9524902487839090244034121)
    ·
      refine ⟨7143676865879317683025591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9524902487839090244034121 7143676865879317683025591)
      ·
        refine ⟨10715515298818976524538387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143676865879317683025591 10715515298818976524538387)
        ·
          refine ⟨16073272948228464786807581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10715515298818976524538387 16073272948228464786807581)
          ·
            refine ⟨6027477355585674295052843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16073272948228464786807581 6027477355585674295052843)
            ·
              refine ⟨9041216033378511442579265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6027477355585674295052843 9041216033378511442579265)
              ·
                refine ⟨6780912025033883581934449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9041216033378511442579265 6780912025033883581934449)
                ·
                  refine ⟨5085684018775412686450837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6780912025033883581934449 5085684018775412686450837)
                  ·
                    refine ⟨238391438380097469677383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5085684018775412686450837 238391438380097469677383)
                    ·
                      rfl

theorem cell23_1392797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1392797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392797 prefixEnd_1392797 := by exact prefixLift 1392797
  have htrace : WordTrace (prefixWord ++ tailWord_1392797) baseStart_1392797 baseEnd_1392797 := by
    simpa [prefixWord, tailWord_1392797, baseEnd_1392797] using wordTrace_append hprefix tailTrace_1392797
  have hstable : (prefixWord ++ tailWord_1392797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392797).length < 2 ^ (prefixWord ++ tailWord_1392797).sum := by decide
  have hdescent : baseEnd_1392797 < baseStart_1392797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392798 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1392798 : Nat := 118140960795 + 1392798 * 2 ^ 59
def prefixEnd_1392798 : Nat := 4983230072969 + 3 ^ 40 * 1392798 * 2
def baseEnd_1392798 : Nat := 715174828620946905119645

theorem tailTrace_1392798 : CollatzResearch.WordTrace tailWord_1392798 prefixEnd_1392798 715174828620946905119645 := by
  unfold tailWord_1392798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349939551017273975704381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33866344272092127870423365 6349939551017273975704381)
  ·
    refine ⟨2381227331631477740889143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6349939551017273975704381 2381227331631477740889143)
    ·
      refine ⟨3571840997447216611333715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381227331631477740889143 3571840997447216611333715)
      ·
        refine ⟨5357761496170824917000573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3571840997447216611333715 5357761496170824917000573)
        ·
          refine ⟨2009160561064059343875215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5357761496170824917000573 2009160561064059343875215)
          ·
            refine ⟨3013740841596089015812823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009160561064059343875215 3013740841596089015812823)
            ·
              refine ⟨4520611262394133523719235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013740841596089015812823 4520611262394133523719235)
              ·
                refine ⟨6780916893591200285578853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4520611262394133523719235 6780916893591200285578853)
                ·
                  refine ⟨1271421917548350053546035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6780916893591200285578853 1271421917548350053546035)
                  ·
                    refine ⟨1907132876322525080319053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1271421917548350053546035 1907132876322525080319053)
                    ·
                      refine ⟨715174828620946905119645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907132876322525080319053 715174828620946905119645)
                      ·
                        rfl

theorem cell23_1392798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1392798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392798 prefixEnd_1392798 := by exact prefixLift 1392798
  have htrace : WordTrace (prefixWord ++ tailWord_1392798) baseStart_1392798 baseEnd_1392798 := by
    simpa [prefixWord, tailWord_1392798, baseEnd_1392798] using wordTrace_append hprefix tailTrace_1392798
  have hstable : (prefixWord ++ tailWord_1392798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392798).length < 2 ^ (prefixWord ++ tailWord_1392798).sum := by decide
  have hdescent : baseEnd_1392798 < baseStart_1392798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392837 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_1392837 : Nat := 118140960795 + 1392837 * 2 ^ 59
def prefixEnd_1392837 : Nat := 4983230072969 + 3 ^ 40 * 1392837 * 2
def baseEnd_1392837 : Nat := 715194854366472252531965

theorem tailTrace_1392837 : CollatzResearch.WordTrace tailWord_1392837 prefixEnd_1392837 715194854366472252531965 := by
  unfold tailWord_1392837
  simp only [CollatzResearch.WordTrace]
  refine ⟨50800938854996901466304765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33867292569997934310869843 50800938854996901466304765)
  ·
    refine ⟨19050352070623838049864287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50800938854996901466304765 19050352070623838049864287)
    ·
      refine ⟨28575528105935757074796431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050352070623838049864287 28575528105935757074796431)
      ·
        refine ⟨42863292158903635612194647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28575528105935757074796431 42863292158903635612194647)
        ·
          refine ⟨64294938238355453418291971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42863292158903635612194647 64294938238355453418291971)
          ·
            refine ⟨96442407357533180127437957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64294938238355453418291971 96442407357533180127437957)
            ·
              refine ⟨18082951379537471273894617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96442407357533180127437957 18082951379537471273894617)
              ·
                refine ⟨13562213534653103455420963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18082951379537471273894617 13562213534653103455420963)
                ·
                  refine ⟨20343320301979655183131445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13562213534653103455420963 20343320301979655183131445)
                  ·
                    refine ⟨1907186278310592673418573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20343320301979655183131445 1907186278310592673418573)
                    ·
                      refine ⟨715194854366472252531965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907186278310592673418573 715194854366472252531965)
                      ·
                        rfl

theorem cell23_1392837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_1392837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392837 prefixEnd_1392837 := by exact prefixLift 1392837
  have htrace : WordTrace (prefixWord ++ tailWord_1392837) baseStart_1392837 baseEnd_1392837 := by
    simpa [prefixWord, tailWord_1392837, baseEnd_1392837] using wordTrace_append hprefix tailTrace_1392837
  have hstable : (prefixWord ++ tailWord_1392837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392837).length < 2 ^ (prefixWord ++ tailWord_1392837).sum := by decide
  have hdescent : baseEnd_1392837 < baseStart_1392837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392857 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 4, 5]
def baseStart_1392857 : Nat := 118140960795 + 1392857 * 2 ^ 59
def prefixEnd_1392857 : Nat := 4983230072969 + 3 ^ 40 * 1392857 * 2
def baseEnd_1392857 : Nat := 238401707993187391427291

theorem tailTrace_1392857 : CollatzResearch.WordTrace tailWord_1392857 prefixEnd_1392857 238401707993187391427291 := by
  unfold tailWord_1392857
  simp only [CollatzResearch.WordTrace]
  refine ⟨50801668314924444882032825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33867778876616296588021883 50801668314924444882032825)
  ·
    refine ⟨38101251236193333661524619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50801668314924444882032825 38101251236193333661524619)
    ·
      refine ⟨57151876854290000492286929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38101251236193333661524619 57151876854290000492286929)
      ·
        refine ⟨42863907640717500369215197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57151876854290000492286929 42863907640717500369215197)
        ·
          refine ⟨16073965365269062638455699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42863907640717500369215197 16073965365269062638455699)
          ·
            refine ⟨24110948047903593957683549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16073965365269062638455699 24110948047903593957683549)
            ·
              refine ⟨9041605517963847734131331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24110948047903593957683549 9041605517963847734131331)
              ·
                refine ⟨13562408276945771601196997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9041605517963847734131331 13562408276945771601196997)
                ·
                  refine ⟨2542951551927332175224437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13562408276945771601196997 2542951551927332175224437)
                  ·
                    refine ⟨238401707993187391427291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2542951551927332175224437 238401707993187391427291)
                    ·
                      rfl

theorem cell23_1392857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_1392857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392857 prefixEnd_1392857 := by exact prefixLift 1392857
  have htrace : WordTrace (prefixWord ++ tailWord_1392857) baseStart_1392857 baseEnd_1392857 := by
    simpa [prefixWord, tailWord_1392857, baseEnd_1392857] using wordTrace_append hprefix tailTrace_1392857
  have hstable : (prefixWord ++ tailWord_1392857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392857).length < 2 ^ (prefixWord ++ tailWord_1392857).sum := by decide
  have hdescent : baseEnd_1392857 < baseStart_1392857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392861 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 7]
def baseStart_1392861 : Nat := 118140960795 + 1392861 * 2 ^ 59
def prefixEnd_1392861 : Nat := 4983230072969 + 3 ^ 40 * 1392861 * 2
def baseEnd_1392861 : Nat := 79467464211353350959095

theorem tailTrace_1392861 : CollatzResearch.WordTrace tailWord_1392861 prefixEnd_1392861 79467464211353350959095 := by
  unfold tailWord_1392861
  simp only [CollatzResearch.WordTrace]
  refine ⟨50801814206909953565178437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33867876137939969043452291 50801814206909953565178437)
  ·
    refine ⟨9525340163795616293470957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50801814206909953565178437 9525340163795616293470957)
    ·
      refine ⟨3572002561423356110051609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9525340163795616293470957 3572002561423356110051609)
      ·
        refine ⟨2679001921067517082538707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3572002561423356110051609 2679001921067517082538707)
        ·
          refine ⟨4018502881601275623808061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679001921067517082538707 4018502881601275623808061)
          ·
            refine ⟨1506938580600478358928023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4018502881601275623808061 1506938580600478358928023)
            ·
              refine ⟨2260407870900717538392035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506938580600478358928023 2260407870900717538392035)
              ·
                refine ⟨3390611806351076307588053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260407870900717538392035 3390611806351076307588053)
                ·
                  refine ⟨79467464211353350959095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3390611806351076307588053 79467464211353350959095)
                  ·
                    rfl

theorem cell23_1392861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_1392861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392861 prefixEnd_1392861 := by exact prefixLift 1392861
  have htrace : WordTrace (prefixWord ++ tailWord_1392861) baseStart_1392861 baseEnd_1392861 := by
    simpa [prefixWord, tailWord_1392861, baseEnd_1392861] using wordTrace_append hprefix tailTrace_1392861
  have hstable : (prefixWord ++ tailWord_1392861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392861).length < 2 ^ (prefixWord ++ tailWord_1392861).sum := by decide
  have hdescent : baseEnd_1392861 < baseStart_1392861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392864 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 2, 5, 2]
def baseStart_1392864 : Nat := 118140960795 + 1392864 * 2 ^ 59
def prefixEnd_1392864 : Nat := 4983230072969 + 3 ^ 40 * 1392864 * 2
def baseEnd_1392864 : Nat := 715208718344143646894341

theorem tailTrace_1392864 : CollatzResearch.WordTrace tailWord_1392864 prefixEnd_1392864 715208718344143646894341 := by
  unfold tailWord_1392864
  simp only [CollatzResearch.WordTrace]
  refine ⟨25400961812949542538768823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33867949083932723385025097 25400961812949542538768823)
  ·
    refine ⟨38101442719424313808153235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25400961812949542538768823 38101442719424313808153235)
    ·
      refine ⟨57152164079136470712229853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38101442719424313808153235 57152164079136470712229853)
      ·
        refine ⟨21432061529676176517086195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57152164079136470712229853 21432061529676176517086195)
        ·
          refine ⟨32148092294514264775629293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21432061529676176517086195 32148092294514264775629293)
          ·
            refine ⟨12055534610442849290860985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32148092294514264775629293 12055534610442849290860985)
            ·
              refine ⟨9041650957832136968145739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12055534610442849290860985 9041650957832136968145739)
              ·
                refine ⟨13562476436748205452218609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9041650957832136968145739 13562476436748205452218609)
                ·
                  refine ⟨10171857327561154089163957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13562476436748205452218609 10171857327561154089163957)
                  ·
                    refine ⟨953611624458858195859121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10171857327561154089163957 953611624458858195859121)
                    ·
                      refine ⟨715208718344143646894341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953611624458858195859121 715208718344143646894341)
                      ·
                        rfl

theorem cell23_1392864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_1392864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392864 prefixEnd_1392864 := by exact prefixLift 1392864
  have htrace : WordTrace (prefixWord ++ tailWord_1392864) baseStart_1392864 baseEnd_1392864 := by
    simpa [prefixWord, tailWord_1392864, baseEnd_1392864] using wordTrace_append hprefix tailTrace_1392864
  have hstable : (prefixWord ++ tailWord_1392864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392864).length < 2 ^ (prefixWord ++ tailWord_1392864).sum := by decide
  have hdescent : baseEnd_1392864 < baseStart_1392864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392866 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1392866 : Nat := 118140960795 + 1392866 * 2 ^ 59
def prefixEnd_1392866 : Nat := 4983230072969 + 3 ^ 40 * 1392866 * 2
def baseEnd_1392866 : Nat := 715209745305452639069333

theorem tailTrace_1392866 : CollatzResearch.WordTrace tailWord_1392866 prefixEnd_1392866 715209745305452639069333 := by
  unfold tailWord_1392866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12700499142972959854777613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33867997714594559612740301 12700499142972959854777613)
  ·
    refine ⟨4762687178614859945541605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12700499142972959854777613 4762687178614859945541605)
    ·
      refine ⟨893003845990286239789051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4762687178614859945541605 893003845990286239789051)
      ·
        refine ⟨1339505768985429359683577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893003845990286239789051 1339505768985429359683577)
        ·
          refine ⟨1004629326739072019762683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339505768985429359683577 1004629326739072019762683)
          ·
            refine ⟨1506943990108608029644025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004629326739072019762683 1506943990108608029644025)
            ·
              refine ⟨1130207992581456022233019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506943990108608029644025 1130207992581456022233019)
              ·
                refine ⟨1695311988872184033349529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130207992581456022233019 1695311988872184033349529)
                ·
                  refine ⟨1271483991654138025012147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695311988872184033349529 1271483991654138025012147)
                  ·
                    refine ⟨1907225987481207037518221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1271483991654138025012147 1907225987481207037518221)
                    ·
                      refine ⟨715209745305452639069333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907225987481207037518221 715209745305452639069333)
                      ·
                        rfl

theorem cell23_1392866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1392866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392866 prefixEnd_1392866 := by exact prefixLift 1392866
  have htrace : WordTrace (prefixWord ++ tailWord_1392866) baseStart_1392866 baseEnd_1392866 := by
    simpa [prefixWord, tailWord_1392866, baseEnd_1392866] using wordTrace_append hprefix tailTrace_1392866
  have hstable : (prefixWord ++ tailWord_1392866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392866).length < 2 ^ (prefixWord ++ tailWord_1392866).sum := by decide
  have hdescent : baseEnd_1392866 < baseStart_1392866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392907 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6]
def baseStart_1392907 : Nat := 118140960795 + 1392907 * 2 ^ 59
def prefixEnd_1392907 : Nat := 4983230072969 + 3 ^ 40 * 1392907 * 2
def baseEnd_1392907 : Nat := 715230798012286978656643

theorem tailTrace_1392907 : CollatzResearch.WordTrace tailWord_1392907 prefixEnd_1392907 715230798012286978656643 := by
  unfold tailWord_1392907
  simp only [CollatzResearch.WordTrace]
  refine ⟨50803491964743303421352975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33868994643162202280901983 50803491964743303421352975)
  ·
    refine ⟨76205237947114955132029463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50803491964743303421352975 76205237947114955132029463)
    ·
      refine ⟨114307856920672432698044195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76205237947114955132029463 114307856920672432698044195)
      ·
        refine ⟨171461785381008649047066293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114307856920672432698044195 171461785381008649047066293)
        ·
          refine ⟨16074542379469560848162465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171461785381008649047066293 16074542379469560848162465)
          ·
            refine ⟨12055906784602170636121849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16074542379469560848162465 12055906784602170636121849)
            ·
              refine ⟨9041930088451627977091387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12055906784602170636121849 9041930088451627977091387)
              ·
                refine ⟨13562895132677441965637081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9041930088451627977091387 13562895132677441965637081)
                ·
                  refine ⟨10172171349508081474227811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13562895132677441965637081 10172171349508081474227811)
                  ·
                    refine ⟨15258257024262122211341717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10172171349508081474227811 15258257024262122211341717)
                    ·
                      refine ⟨715230798012286978656643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15258257024262122211341717 715230798012286978656643)
                      ·
                        rfl

theorem cell23_1392907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_1392907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392907 prefixEnd_1392907 := by exact prefixLift 1392907
  have htrace : WordTrace (prefixWord ++ tailWord_1392907) baseStart_1392907 baseEnd_1392907 := by
    simpa [prefixWord, tailWord_1392907, baseEnd_1392907] using wordTrace_append hprefix tailTrace_1392907
  have hstable : (prefixWord ++ tailWord_1392907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392907).length < 2 ^ (prefixWord ++ tailWord_1392907).sum := by decide
  have hdescent : baseEnd_1392907 < baseStart_1392907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392917 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 8]
def baseStart_1392917 : Nat := 118140960795 + 1392917 * 2 ^ 59
def prefixEnd_1392917 : Nat := 4983230072969 + 3 ^ 40 * 1392917 * 2
def baseEnd_1392917 : Nat := 79470659202092437725733

theorem tailTrace_1392917 : CollatzResearch.WordTrace tailWord_1392917 prefixEnd_1392917 79470659202092437725733 := by
  unfold tailWord_1392917
  simp only [CollatzResearch.WordTrace]
  refine ⟨50803856694707075129217005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33869237796471383419478003 50803856694707075129217005)
  ·
    refine ⟨19051446260515153173456377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50803856694707075129217005 19051446260515153173456377)
    ·
      refine ⟨14288584695386364880092283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19051446260515153173456377 14288584695386364880092283)
      ·
        refine ⟨21432877043079547320138425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14288584695386364880092283 21432877043079547320138425)
        ·
          refine ⟨16074657782309660490103819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21432877043079547320138425 16074657782309660490103819)
          ·
            refine ⟨24111986673464490735155729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16074657782309660490103819 24111986673464490735155729)
            ·
              refine ⟨18083990005098368051366797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24111986673464490735155729 18083990005098368051366797)
              ·
                refine ⟨6781496251911888019262549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18083990005098368051366797 6781496251911888019262549)
                ·
                  refine ⟨79470659202092437725733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6781496251911888019262549 79470659202092437725733)
                  ·
                    rfl

theorem cell23_1392917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_1392917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392917 prefixEnd_1392917 := by exact prefixLift 1392917
  have htrace : WordTrace (prefixWord ++ tailWord_1392917) baseStart_1392917 baseEnd_1392917 := by
    simpa [prefixWord, tailWord_1392917, baseEnd_1392917] using wordTrace_append hprefix tailTrace_1392917
  have hstable : (prefixWord ++ tailWord_1392917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392917).length < 2 ^ (prefixWord ++ tailWord_1392917).sum := by decide
  have hdescent : baseEnd_1392917 < baseStart_1392917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392938 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1392938 : Nat := 118140960795 + 1392938 * 2 ^ 59
def prefixEnd_1392938 : Nat := 4983230072969 + 3 ^ 40 * 1392938 * 2
def baseEnd_1392938 : Nat := 238415571970858785789667

theorem tailTrace_1392938 : CollatzResearch.WordTrace tailWord_1392938 prefixEnd_1392938 238415571970858785789667 := by
  unfold tailWord_1392938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12701155656907748928932867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33869748418420663810487645 12701155656907748928932867)
  ·
    refine ⟨19051733485361623393399301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12701155656907748928932867 19051733485361623393399301)
    ·
      refine ⟨3572200028505304386262369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19051733485361623393399301 3572200028505304386262369)
      ·
        refine ⟨2679150021378978289696777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3572200028505304386262369 2679150021378978289696777)
        ·
          refine ⟨2009362516034233717272583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2679150021378978289696777 2009362516034233717272583)
          ·
            refine ⟨3014043774051350575908875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009362516034233717272583 3014043774051350575908875)
            ·
              refine ⟨4521065661077025863863313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014043774051350575908875 4521065661077025863863313)
              ·
                refine ⟨3390799245807769397897485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4521065661077025863863313 3390799245807769397897485)
                ·
                  refine ⟨1271549717177913524211557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3390799245807769397897485 1271549717177913524211557)
                  ·
                    refine ⟨238415571970858785789667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1271549717177913524211557 238415571970858785789667)
                    ·
                      rfl

theorem cell23_1392938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1392938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392938 prefixEnd_1392938 := by exact prefixLift 1392938
  have htrace : WordTrace (prefixWord ++ tailWord_1392938) baseStart_1392938 baseEnd_1392938 := by
    simpa [prefixWord, tailWord_1392938, baseEnd_1392938] using wordTrace_append hprefix tailTrace_1392938
  have hstable : (prefixWord ++ tailWord_1392938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392938).length < 2 ^ (prefixWord ++ tailWord_1392938).sum := by decide
  have hdescent : baseEnd_1392938 < baseStart_1392938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392948 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1392948 : Nat := 118140960795 + 1392948 * 2 ^ 59
def prefixEnd_1392948 : Nat := 4983230072969 + 3 ^ 40 * 1392948 * 2
def baseEnd_1392948 : Nat := 715251850719121318243955

theorem tailTrace_1392948 : CollatzResearch.WordTrace tailWord_1392948 prefixEnd_1392948 715251850719121318243955 := by
  unfold tailWord_1392948
  simp only [CollatzResearch.WordTrace]
  refine ⟨25402493678797383711797749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33869991571729844949063665 25402493678797383711797749)
  ·
    refine ⟨2381483782387254722981039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25402493678797383711797749 2381483782387254722981039)
    ·
      refine ⟨3572225673580882084471559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381483782387254722981039 3572225673580882084471559)
      ·
        refine ⟨5358338510371323126707339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572225673580882084471559 5358338510371323126707339)
        ·
          refine ⟨8037507765556984690061009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5358338510371323126707339 8037507765556984690061009)
          ·
            refine ⟨6028130824167738517545757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8037507765556984690061009 6028130824167738517545757)
            ·
              refine ⟨2260549059062901944079659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6028130824167738517545757 2260549059062901944079659)
              ·
                refine ⟨3390823588594352916119489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260549059062901944079659 3390823588594352916119489)
                ·
                  refine ⟨2543117691445764687089617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3390823588594352916119489 2543117691445764687089617)
                  ·
                    refine ⟨1907338268584323515317213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2543117691445764687089617 1907338268584323515317213)
                    ·
                      refine ⟨715251850719121318243955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907338268584323515317213 715251850719121318243955)
                      ·
                        rfl

theorem cell23_1392948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1392948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392948 prefixEnd_1392948 := by exact prefixLift 1392948
  have htrace : WordTrace (prefixWord ++ tailWord_1392948) baseStart_1392948 baseEnd_1392948 := by
    simpa [prefixWord, tailWord_1392948, baseEnd_1392948] using wordTrace_append hprefix tailTrace_1392948
  have hstable : (prefixWord ++ tailWord_1392948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392948).length < 2 ^ (prefixWord ++ tailWord_1392948).sum := by decide
  have hdescent : baseEnd_1392948 < baseStart_1392948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1392984 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1392984 : Nat := 118140960795 + 1392984 * 2 ^ 59
def prefixEnd_1392984 : Nat := 4983230072969 + 3 ^ 40 * 1392984 * 2
def baseEnd_1392984 : Nat := 715270336022683177393789

theorem tailTrace_1392984 : CollatzResearch.WordTrace tailWord_1392984 prefixEnd_1392984 715270336022683177393789 := by
  unfold tailWord_1392984
  simp only [CollatzResearch.WordTrace]
  refine ⟨25403150192732172785953003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33870866923642897047937337 25403150192732172785953003)
  ·
    refine ⟨38104725289098259178929505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25403150192732172785953003 38104725289098259178929505)
    ·
      refine ⟨28578543966823694384197129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38104725289098259178929505 28578543966823694384197129)
      ·
        refine ⟨21433907975117770788147847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28578543966823694384197129 21433907975117770788147847)
        ·
          refine ⟨32150861962676656182221771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21433907975117770788147847 32150861962676656182221771)
          ·
            refine ⟨48226292944014984273332657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32150861962676656182221771 48226292944014984273332657)
            ·
              refine ⟨36169719708011238204999493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48226292944014984273332657 36169719708011238204999493)
              ·
                refine ⟨6781822445252107163437405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36169719708011238204999493 6781822445252107163437405)
                ·
                  refine ⟨2543183416969540186289027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6781822445252107163437405 2543183416969540186289027)
                  ·
                    refine ⟨3814775125454310279433541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2543183416969540186289027 3814775125454310279433541)
                    ·
                      refine ⟨715270336022683177393789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3814775125454310279433541 715270336022683177393789)
                      ·
                        rfl

theorem cell23_1392984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1392984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1392984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1392984 prefixEnd_1392984 := by exact prefixLift 1392984
  have htrace : WordTrace (prefixWord ++ tailWord_1392984) baseStart_1392984 baseEnd_1392984 := by
    simpa [prefixWord, tailWord_1392984, baseEnd_1392984] using wordTrace_append hprefix tailTrace_1392984
  have hstable : (prefixWord ++ tailWord_1392984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1392984).length < 2 ^ (prefixWord ++ tailWord_1392984).sum := by decide
  have hdescent : baseEnd_1392984 < baseStart_1392984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1392984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393001 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 4]
def baseStart_1393001 : Nat := 118140960795 + 1393001 * 2 ^ 59
def prefixEnd_1393001 : Nat := 4983230072969 + 3 ^ 40 * 1393001 * 2
def baseEnd_1393001 : Nat := 715279065193809610881211

theorem tailTrace_1393001 : CollatzResearch.WordTrace tailWord_1393001 prefixEnd_1393001 715279065193809610881211 := by
  unfold tailWord_1393001
  simp only [CollatzResearch.WordTrace]
  refine ⟨50806920426402757475274857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33871280284268504983516571 50806920426402757475274857)
  ·
    refine ⟨38105190319802068106456143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50806920426402757475274857 38105190319802068106456143)
    ·
      refine ⟨57157785479703102159684215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38105190319802068106456143 57157785479703102159684215)
      ·
        refine ⟨85736678219554653239526323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57157785479703102159684215 85736678219554653239526323)
        ·
          refine ⟨128605017329331979859289485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85736678219554653239526323 128605017329331979859289485)
          ·
            refine ⟨48226881498499492447233557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128605017329331979859289485 48226881498499492447233557)
            ·
              refine ⟨2260635070242163708464073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48226881498499492447233557 2260635070242163708464073)
              ·
                refine ⟨1695476302681622781348055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260635070242163708464073 1695476302681622781348055)
                ·
                  refine ⟨2543214454022434172022083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695476302681622781348055 2543214454022434172022083)
                  ·
                    refine ⟨3814821681033651258033125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2543214454022434172022083 3814821681033651258033125)
                    ·
                      refine ⟨715279065193809610881211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3814821681033651258033125 715279065193809610881211)
                      ·
                        rfl

theorem cell23_1393001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_1393001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393001 prefixEnd_1393001 := by exact prefixLift 1393001
  have htrace : WordTrace (prefixWord ++ tailWord_1393001) baseStart_1393001 baseEnd_1393001 := by
    simpa [prefixWord, tailWord_1393001, baseEnd_1393001] using wordTrace_append hprefix tailTrace_1393001
  have hstable : (prefixWord ++ tailWord_1393001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393001).length < 2 ^ (prefixWord ++ tailWord_1393001).sum := by decide
  have hdescent : baseEnd_1393001 < baseStart_1393001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393021 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1393021 : Nat := 118140960795 + 1393021 * 2 ^ 59
def prefixEnd_1393021 : Nat := 4983230072969 + 3 ^ 40 * 1393021 * 2
def baseEnd_1393021 : Nat := 715289334806899532631119

theorem tailTrace_1393021 : CollatzResearch.WordTrace tailWord_1393021 prefixEnd_1393021 715289334806899532631119 := by
  unfold tailWord_1393021
  simp only [CollatzResearch.WordTrace]
  refine ⟨50807649886330300891002917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33871766590886867260668611 50807649886330300891002917)
  ·
    refine ⟨9526434353686931417063047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50807649886330300891002917 9526434353686931417063047)
    ·
      refine ⟨14289651530530397125594571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9526434353686931417063047 14289651530530397125594571)
      ·
        refine ⟨21434477295795595688391857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14289651530530397125594571 21434477295795595688391857)
        ·
          refine ⟨16075857971846696766293893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21434477295795595688391857 16075857971846696766293893)
          ·
            refine ⟨3014223369721255643680105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16075857971846696766293893 3014223369721255643680105)
            ·
              refine ⟨2260667527290941732760079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3014223369721255643680105 2260667527290941732760079)
              ·
                refine ⟨3391001290936412599140119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260667527290941732760079 3391001290936412599140119)
                ·
                  refine ⟨5086501936404618898710179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391001290936412599140119 5086501936404618898710179)
                  ·
                    refine ⟨7629752904606928348065269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5086501936404618898710179 7629752904606928348065269)
                    ·
                      refine ⟨715289334806899532631119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7629752904606928348065269 715289334806899532631119)
                      ·
                        rfl

theorem cell23_1393021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1393021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393021 prefixEnd_1393021 := by exact prefixLift 1393021
  have htrace : WordTrace (prefixWord ++ tailWord_1393021) baseStart_1393021 baseEnd_1393021 := by
    simpa [prefixWord, tailWord_1393021, baseEnd_1393021] using wordTrace_append hprefix tailTrace_1393021
  have hstable : (prefixWord ++ tailWord_1393021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393021).length < 2 ^ (prefixWord ++ tailWord_1393021).sum := by decide
  have hdescent : baseEnd_1393021 < baseStart_1393021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393035 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 3, 2, 2]
def baseStart_1393035 : Nat := 118140960795 + 1393035 * 2 ^ 59
def prefixEnd_1393035 : Nat := 4983230072969 + 3 ^ 40 * 1393035 * 2
def baseEnd_1393035 : Nat := 715296523536062477856055

theorem tailTrace_1393035 : CollatzResearch.WordTrace tailWord_1393035 prefixEnd_1393035 715296523536062477856055 := by
  unfold tailWord_1393035
  simp only [CollatzResearch.WordTrace]
  refine ⟨50808160508279581282012559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33872107005519720854675039 50808160508279581282012559)
  ·
    refine ⟨76212240762419371923018839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50808160508279581282012559 76212240762419371923018839)
    ·
      refine ⟨114318361143629057884528259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76212240762419371923018839 114318361143629057884528259)
      ·
        refine ⟨171477541715443586826792389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114318361143629057884528259 171477541715443586826792389)
        ·
          refine ⟨32152039071645672530023573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171477541715443586826792389 32152039071645672530023573)
          ·
            refine ⟨1507126831483390899844855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32152039071645672530023573 1507126831483390899844855)
            ·
              refine ⟨2260690247225086349767283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507126831483390899844855 2260690247225086349767283)
              ·
                refine ⟨3391035370837629524650925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260690247225086349767283 3391035370837629524650925)
                ·
                  refine ⟨1271638264064111071744097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3391035370837629524650925 1271638264064111071744097)
                  ·
                    refine ⟨953728698048083303808073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271638264064111071744097 953728698048083303808073)
                    ·
                      refine ⟨715296523536062477856055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953728698048083303808073 715296523536062477856055)
                      ·
                        rfl

theorem cell23_1393035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 2, 2].length) (baseStart_1393035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393035 prefixEnd_1393035 := by exact prefixLift 1393035
  have htrace : WordTrace (prefixWord ++ tailWord_1393035) baseStart_1393035 baseEnd_1393035 := by
    simpa [prefixWord, tailWord_1393035, baseEnd_1393035] using wordTrace_append hprefix tailTrace_1393035
  have hstable : (prefixWord ++ tailWord_1393035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393035).length < 2 ^ (prefixWord ++ tailWord_1393035).sum := by decide
  have hdescent : baseEnd_1393035 < baseStart_1393035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393085 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1393085 : Nat := 118140960795 + 1393085 * 2 ^ 59
def prefixEnd_1393085 : Nat := 4983230072969 + 3 ^ 40 * 1393085 * 2
def baseEnd_1393085 : Nat := 715322197568787282230825

theorem tailTrace_1393085 : CollatzResearch.WordTrace tailWord_1393085 prefixEnd_1393085 715322197568787282230825 := by
  unfold tailWord_1393085
  simp only [CollatzResearch.WordTrace]
  refine ⟨50809984158098439821332709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33873322772065626547555139 50809984158098439821332709)
  ·
    refine ⟨9526872029643457466499883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50809984158098439821332709 9526872029643457466499883)
    ·
      refine ⟨14290308044465186199749825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9526872029643457466499883 14290308044465186199749825)
      ·
        refine ⟨10717731033348889649812369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14290308044465186199749825 10717731033348889649812369)
        ·
          refine ⟨8038298275011667237359277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10717731033348889649812369 8038298275011667237359277)
          ·
            refine ⟨3014361853129375214009729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8038298275011667237359277 3014361853129375214009729)
            ·
              refine ⟨2260771389847031410507297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3014361853129375214009729 2260771389847031410507297)
              ·
                refine ⟨1695578542385273557880473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260771389847031410507297 1695578542385273557880473)
                ·
                  refine ⟨1271683906788955168410355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695578542385273557880473 1271683906788955168410355)
                  ·
                    refine ⟨1907525860183432752615533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1271683906788955168410355 1907525860183432752615533)
                    ·
                      refine ⟨715322197568787282230825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907525860183432752615533 715322197568787282230825)
                      ·
                        rfl

theorem cell23_1393085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1393085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393085 prefixEnd_1393085 := by exact prefixLift 1393085
  have htrace : WordTrace (prefixWord ++ tailWord_1393085) baseStart_1393085 baseEnd_1393085 := by
    simpa [prefixWord, tailWord_1393085, baseEnd_1393085] using wordTrace_append hprefix tailTrace_1393085
  have hstable : (prefixWord ++ tailWord_1393085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393085).length < 2 ^ (prefixWord ++ tailWord_1393085).sum := by decide
  have hdescent : baseEnd_1393085 < baseStart_1393085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393091 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 5, 4, 2]
def baseStart_1393091 : Nat := 118140960795 + 1393091 * 2 ^ 59
def prefixEnd_1393091 : Nat := 4983230072969 + 3 ^ 40 * 1393091 * 2
def baseEnd_1393091 : Nat := 715325278452714258755797

theorem tailTrace_1393091 : CollatzResearch.WordTrace tailWord_1393091 prefixEnd_1393091 715325278452714258755797 := by
  unfold tailWord_1393091
  simp only [CollatzResearch.WordTrace]
  refine ⟨50810202996076702846051127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33873468664051135230700751 50810202996076702846051127)
  ·
    refine ⟨76215304494115054269076691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50810202996076702846051127 76215304494115054269076691)
    ·
      refine ⟨114322956741172581403615037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76215304494115054269076691 114322956741172581403615037)
      ·
        refine ⟨42871108777939718026355639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114322956741172581403615037 42871108777939718026355639)
        ·
          refine ⟨64306663166909577039533459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42871108777939718026355639 64306663166909577039533459)
          ·
            refine ⟨96459994750364365559300189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64306663166909577039533459 96459994750364365559300189)
            ·
              refine ⟨36172498031386637084737571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96459994750364365559300189 36172498031386637084737571)
              ·
                refine ⟨54258747047079955627106357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36172498031386637084737571 54258747047079955627106357)
                ·
                  refine ⟨5086757535663745840041221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54258747047079955627106357 5086757535663745840041221)
                  ·
                    refine ⟨953767037936952345007729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5086757535663745840041221 953767037936952345007729)
                    ·
                      refine ⟨715325278452714258755797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953767037936952345007729 715325278452714258755797)
                      ·
                        rfl

theorem cell23_1393091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_1393091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393091 prefixEnd_1393091 := by exact prefixLift 1393091
  have htrace : WordTrace (prefixWord ++ tailWord_1393091) baseStart_1393091 baseEnd_1393091 := by
    simpa [prefixWord, tailWord_1393091, baseEnd_1393091] using wordTrace_append hprefix tailTrace_1393091
  have hstable : (prefixWord ++ tailWord_1393091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393091).length < 2 ^ (prefixWord ++ tailWord_1393091).sum := by decide
  have hdescent : baseEnd_1393091 < baseStart_1393091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393124 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_1393124 : Nat := 118140960795 + 1393124 * 2 ^ 59
def prefixEnd_1393124 : Nat := 4983230072969 + 3 ^ 40 * 1393124 * 2
def baseEnd_1393124 : Nat := 715342223314312629643145

theorem tailTrace_1393124 : CollatzResearch.WordTrace tailWord_1393124 prefixEnd_1393124 715342223314312629643145 := by
  unfold tailWord_1393124
  simp only [CollatzResearch.WordTrace]
  refine ⟨25405703302478574741001213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33874271069971432988001617 25405703302478574741001213)
  ·
    refine ⟨9527138738429465527875455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25405703302478574741001213 9527138738429465527875455)
    ·
      refine ⟨14290708107644198291813183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9527138738429465527875455 14290708107644198291813183)
      ·
        refine ⟨21436062161466297437719775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14290708107644198291813183 21436062161466297437719775)
        ·
          refine ⟨32154093242199446156579663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21436062161466297437719775 32154093242199446156579663)
          ·
            refine ⟨48231139863299169234869495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32154093242199446156579663 48231139863299169234869495)
            ·
              refine ⟨72346709794948753852304243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48231139863299169234869495 72346709794948753852304243)
              ·
                refine ⟨108520064692423130778456365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72346709794948753852304243 108520064692423130778456365)
                ·
                  refine ⟨40695024259658674041921137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108520064692423130778456365 40695024259658674041921137)
                  ·
                    refine ⟨30521268194744005531440853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40695024259658674041921137 30521268194744005531440853)
                    ·
                      refine ⟨715342223314312629643145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30521268194744005531440853 715342223314312629643145)
                      ·
                        rfl

theorem cell23_1393124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_1393124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393124 prefixEnd_1393124 := by exact prefixLift 1393124
  have htrace : WordTrace (prefixWord ++ tailWord_1393124) baseStart_1393124 baseEnd_1393124 := by
    simpa [prefixWord, tailWord_1393124, baseEnd_1393124] using wordTrace_append hprefix tailTrace_1393124
  have hstable : (prefixWord ++ tailWord_1393124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393124).length < 2 ^ (prefixWord ++ tailWord_1393124).sum := by decide
  have hdescent : baseEnd_1393124 < baseStart_1393124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393159 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_1393159 : Nat := 118140960795 + 1393159 * 2 ^ 59
def prefixEnd_1393159 : Nat := 4983230072969 + 3 ^ 40 * 1393159 * 2
def baseEnd_1393159 : Nat := 715360195137219992705485

theorem tailTrace_1393159 : CollatzResearch.WordTrace tailWord_1393159 prefixEnd_1393159 715360195137219992705485 := by
  unfold tailWord_1393159
  simp only [CollatzResearch.WordTrace]
  refine ⟨50812683159830350459526531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33875122106553566973017687 50812683159830350459526531)
  ·
    refine ⟨76219024739745525689289797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50812683159830350459526531 76219024739745525689289797)
    ·
      refine ⟨14291067138702286066741837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76219024739745525689289797 14291067138702286066741837)
      ·
        refine ⟨5359150177013357275028189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14291067138702286066741837 5359150177013357275028189)
        ·
          refine ⟨2009681316380008978135571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5359150177013357275028189 2009681316380008978135571)
          ·
            refine ⟨3014521974570013467203357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009681316380008978135571 3014521974570013467203357)
            ·
              refine ⟨1130445740463755050201259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3014521974570013467203357 1130445740463755050201259)
              ·
                refine ⟨1695668610695632575301889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130445740463755050201259 1695668610695632575301889)
                ·
                  refine ⟨1271751458021724431476417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695668610695632575301889 1271751458021724431476417)
                  ·
                    refine ⟨953813593516293323607313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271751458021724431476417 953813593516293323607313)
                    ·
                      refine ⟨715360195137219992705485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953813593516293323607313 715360195137219992705485)
                      ·
                        rfl

theorem cell23_1393159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_1393159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393159 prefixEnd_1393159 := by exact prefixLift 1393159
  have htrace : WordTrace (prefixWord ++ tailWord_1393159) baseStart_1393159 baseEnd_1393159 := by
    simpa [prefixWord, tailWord_1393159, baseEnd_1393159] using wordTrace_append hprefix tailTrace_1393159
  have hstable : (prefixWord ++ tailWord_1393159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393159).length < 2 ^ (prefixWord ++ tailWord_1393159).sum := by decide
  have hdescent : baseEnd_1393159 < baseStart_1393159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393165 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1393165 : Nat := 118140960795 + 1393165 * 2 ^ 59
def prefixEnd_1393165 : Nat := 4983230072969 + 3 ^ 40 * 1393165 * 2
def baseEnd_1393165 : Nat := 79484808446794107692273

theorem tailTrace_1393165 : CollatzResearch.WordTrace tailWord_1393165 prefixEnd_1393165 79484808446794107692273 := by
  unfold tailWord_1393165
  simp only [CollatzResearch.WordTrace]
  refine ⟨50812901997808613484244949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33875267998539075656163299 50812901997808613484244949)
  ·
    refine ⟨1190927390573639378536991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50812901997808613484244949 1190927390573639378536991)
    ·
      refine ⟨1786391085860459067805487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190927390573639378536991 1786391085860459067805487)
      ·
        refine ⟨2679586628790688601708231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786391085860459067805487 2679586628790688601708231)
        ·
          refine ⟨4019379943186032902562347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679586628790688601708231 4019379943186032902562347)
          ·
            refine ⟨6029069914779049353843521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019379943186032902562347 6029069914779049353843521)
            ·
              refine ⟨4521802436084287015382641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6029069914779049353843521 4521802436084287015382641)
              ·
                refine ⟨3391351827063215261536981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4521802436084287015382641 3391351827063215261536981)
                ·
                  refine ⟨79484808446794107692273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3391351827063215261536981 79484808446794107692273)
                  ·
                    rfl

theorem cell23_1393165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1393165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393165 prefixEnd_1393165 := by exact prefixLift 1393165
  have htrace : WordTrace (prefixWord ++ tailWord_1393165) baseStart_1393165 baseEnd_1393165 := by
    simpa [prefixWord, tailWord_1393165, baseEnd_1393165] using wordTrace_append hprefix tailTrace_1393165
  have hstable : (prefixWord ++ tailWord_1393165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393165).length < 2 ^ (prefixWord ++ tailWord_1393165).sum := by decide
  have hdescent : baseEnd_1393165 < baseStart_1393165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393231 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 3]
def baseStart_1393231 : Nat := 118140960795 + 1393231 * 2 ^ 59
def prefixEnd_1393231 : Nat := 4983230072969 + 3 ^ 40 * 1393231 * 2
def baseEnd_1393231 : Nat := 715397165744343711005153

theorem tailTrace_1393231 : CollatzResearch.WordTrace tailWord_1393231 prefixEnd_1393231 715397165744343711005153 := by
  unfold tailWord_1393231
  simp only [CollatzResearch.WordTrace]
  refine ⟨50815309215569506756147547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33876872810379671170765031 50815309215569506756147547)
  ·
    refine ⟨76222963823354260134221321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50815309215569506756147547 76222963823354260134221321)
    ·
      refine ⟨57167222867515695100665991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76222963823354260134221321 57167222867515695100665991)
      ·
        refine ⟨85750834301273542650998987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57167222867515695100665991 85750834301273542650998987)
        ·
          refine ⟨128626251451910313976498481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85750834301273542650998987 128626251451910313976498481)
          ·
            refine ⟨96469688588932735482373861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128626251451910313976498481 96469688588932735482373861)
            ·
              refine ⟨18088066610424887902945099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96469688588932735482373861 18088066610424887902945099)
              ·
                refine ⟨27132099915637331854417649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18088066610424887902945099 27132099915637331854417649)
                ·
                  refine ⟨20349074936727998890813237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27132099915637331854417649 20349074936727998890813237)
                  ·
                    refine ⟨1907725775318249896013741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20349074936727998890813237 1907725775318249896013741)
                    ·
                      refine ⟨715397165744343711005153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907725775318249896013741 715397165744343711005153)
                      ·
                        rfl

theorem cell23_1393231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_1393231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393231 prefixEnd_1393231 := by exact prefixLift 1393231
  have htrace : WordTrace (prefixWord ++ tailWord_1393231) baseStart_1393231 baseEnd_1393231 := by
    simpa [prefixWord, tailWord_1393231, baseEnd_1393231] using wordTrace_append hprefix tailTrace_1393231
  have hstable : (prefixWord ++ tailWord_1393231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393231).length < 2 ^ (prefixWord ++ tailWord_1393231).sum := by decide
  have hdescent : baseEnd_1393231 < baseStart_1393231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393291 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5]
def baseStart_1393291 : Nat := 118140960795 + 1393291 * 2 ^ 59
def prefixEnd_1393291 : Nat := 4983230072969 + 3 ^ 40 * 1393291 * 2
def baseEnd_1393291 : Nat := 715427974583613476254877

theorem tailTrace_1393291 : CollatzResearch.WordTrace tailWord_1393291 prefixEnd_1393291 715427974583613476254877 := by
  unfold tailWord_1393291
  simp only [CollatzResearch.WordTrace]
  refine ⟨50817497595352137003331727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33878331730234758002221151 50817497595352137003331727)
  ·
    refine ⟨76226246393028205504997591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50817497595352137003331727 76226246393028205504997591)
    ·
      refine ⟨114339369589542308257496387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76226246393028205504997591 114339369589542308257496387)
      ·
        refine ⟨171509054384313462386244581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114339369589542308257496387 171509054384313462386244581)
        ·
          refine ⟨32157947697058774197420859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171509054384313462386244581 32157947697058774197420859)
          ·
            refine ⟨48236921545588161296131289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32157947697058774197420859 48236921545588161296131289)
            ·
              refine ⟨36177691159191120972098467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48236921545588161296131289 36177691159191120972098467)
              ·
                refine ⟨54266536738786681458147701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36177691159191120972098467 54266536738786681458147701)
                ·
                  refine ⟨5087487819261251386701347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54266536738786681458147701 5087487819261251386701347)
                  ·
                    refine ⟨7631231728891877080052021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087487819261251386701347 7631231728891877080052021)
                    ·
                      refine ⟨715427974583613476254877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7631231728891877080052021 715427974583613476254877)
                      ·
                        rfl

theorem cell23_1393291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_1393291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393291 prefixEnd_1393291 := by exact prefixLift 1393291
  have htrace : WordTrace (prefixWord ++ tailWord_1393291) baseStart_1393291 baseEnd_1393291 := by
    simpa [prefixWord, tailWord_1393291, baseEnd_1393291] using wordTrace_append hprefix tailTrace_1393291
  have hstable : (prefixWord ++ tailWord_1393291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393291).length < 2 ^ (prefixWord ++ tailWord_1393291).sum := by decide
  have hdescent : baseEnd_1393291 < baseStart_1393291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393301 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_1393301 : Nat := 118140960795 + 1393301 * 2 ^ 59
def prefixEnd_1393301 : Nat := 4983230072969 + 3 ^ 40 * 1393301 * 2
def baseEnd_1393301 : Nat := 715433109390158437129831

theorem tailTrace_1393301 : CollatzResearch.WordTrace tailWord_1393301 prefixEnd_1393301 715433109390158437129831 := by
  unfold tailWord_1393301
  simp only [CollatzResearch.WordTrace]
  refine ⟨50817862325315908711195757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33878574883543939140797171 50817862325315908711195757)
  ·
    refine ⟨19056698371993465766698409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50817862325315908711195757 19056698371993465766698409)
    ·
      refine ⟨14292523778995099325023807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19056698371993465766698409 14292523778995099325023807)
      ·
        refine ⟨21438785668492648987535711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14292523778995099325023807 21438785668492648987535711)
        ·
          refine ⟨32158178502738973481303567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21438785668492648987535711 32158178502738973481303567)
          ·
            refine ⟨48237267754108460221955351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32158178502738973481303567 48237267754108460221955351)
            ·
              refine ⟨72355901631162690332933027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48237267754108460221955351 72355901631162690332933027)
              ·
                refine ⟨108533852446744035499399541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72355901631162690332933027 108533852446744035499399541)
                ·
                  refine ⟨10175048666882253328068707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108533852446744035499399541 10175048666882253328068707)
                  ·
                    refine ⟨15262573000323379992103061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10175048666882253328068707 15262573000323379992103061)
                    ·
                      refine ⟨715433109390158437129831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15262573000323379992103061 715433109390158437129831)
                      ·
                        rfl

theorem cell23_1393301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_1393301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393301 prefixEnd_1393301 := by exact prefixLift 1393301
  have htrace : WordTrace (prefixWord ++ tailWord_1393301) baseStart_1393301 baseEnd_1393301 := by
    simpa [prefixWord, tailWord_1393301, baseEnd_1393301] using wordTrace_append hprefix tailTrace_1393301
  have hstable : (prefixWord ++ tailWord_1393301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393301).length < 2 ^ (prefixWord ++ tailWord_1393301).sum := by decide
  have hdescent : baseEnd_1393301 < baseStart_1393301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393305 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 5, 2, 2]
def baseStart_1393305 : Nat := 118140960795 + 1393305 * 2 ^ 59
def prefixEnd_1393305 : Nat := 4983230072969 + 3 ^ 40 * 1393305 * 2
def baseEnd_1393305 : Nat := 715435163312776421479813

theorem tailTrace_1393305 : CollatzResearch.WordTrace tailWord_1393305 prefixEnd_1393305 715435163312776421479813 := by
  unfold tailWord_1393305
  simp only [CollatzResearch.WordTrace]
  refine ⟨50818008217301417394341369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33878672144867611596227579 50818008217301417394341369)
  ·
    refine ⟨38113506162976063045756027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50818008217301417394341369 38113506162976063045756027)
    ·
      refine ⟨57170259244464094568634041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38113506162976063045756027 57170259244464094568634041)
      ·
        refine ⟨42877694433348070926475531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57170259244464094568634041 42877694433348070926475531)
        ·
          refine ⟨64316541650022106389713297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42877694433348070926475531 64316541650022106389713297)
          ·
            refine ⟨48237406237516579792284973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64316541650022106389713297 48237406237516579792284973)
            ·
              refine ⟨18089027339068717422106865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48237406237516579792284973 18089027339068717422106865)
              ·
                refine ⟨13566770504301538066580149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18089027339068717422106865 13566770504301538066580149)
                ·
                  refine ⟨1271884734778269193741889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13566770504301538066580149 1271884734778269193741889)
                  ·
                    refine ⟨953913551083701895306417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271884734778269193741889 953913551083701895306417)
                    ·
                      refine ⟨715435163312776421479813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953913551083701895306417 715435163312776421479813)
                      ·
                        rfl

theorem cell23_1393305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_1393305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393305 prefixEnd_1393305 := by exact prefixLift 1393305
  have htrace : WordTrace (prefixWord ++ tailWord_1393305) baseStart_1393305 baseEnd_1393305 := by
    simpa [prefixWord, tailWord_1393305, baseEnd_1393305] using wordTrace_append hprefix tailTrace_1393305
  have hstable : (prefixWord ++ tailWord_1393305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393305).length < 2 ^ (prefixWord ++ tailWord_1393305).sum := by decide
  have hdescent : baseEnd_1393305 < baseStart_1393305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393325 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1393325 : Nat := 118140960795 + 1393325 * 2 ^ 59
def prefixEnd_1393325 : Nat := 4983230072969 + 3 ^ 40 * 1393325 * 2
def baseEnd_1393325 : Nat := 715445432925866343229721

theorem tailTrace_1393325 : CollatzResearch.WordTrace tailWord_1393325 prefixEnd_1393325 715445432925866343229721 := by
  unfold tailWord_1393325
  simp only [CollatzResearch.WordTrace]
  refine ⟨50818737677228960810069429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33879158451485973873379619 50818737677228960810069429)
  ·
    refine ⟨4764256657240215075944009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50818737677228960810069429 4764256657240215075944009)
    ·
      refine ⟨3573192492930161306958007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4764256657240215075944009 3573192492930161306958007)
      ·
        refine ⟨5359788739395241960437011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3573192492930161306958007 5359788739395241960437011)
        ·
          refine ⟨8039683109092862940655517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359788739395241960437011 8039683109092862940655517)
          ·
            refine ⟨3014881165909823602745819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8039683109092862940655517 3014881165909823602745819)
            ·
              refine ⟨4522321748864735404118729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3014881165909823602745819 4522321748864735404118729)
              ·
                refine ⟨3391741311648551553089047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522321748864735404118729 3391741311648551553089047)
                ·
                  refine ⟨5087611967472827329633571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391741311648551553089047 5087611967472827329633571)
                  ·
                    refine ⟨7631417951209240994450357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087611967472827329633571 7631417951209240994450357)
                    ·
                      refine ⟨715445432925866343229721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7631417951209240994450357 715445432925866343229721)
                      ·
                        rfl

theorem cell23_1393325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1393325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393325 prefixEnd_1393325 := by exact prefixLift 1393325
  have htrace : WordTrace (prefixWord ++ tailWord_1393325) baseStart_1393325 baseEnd_1393325 := by
    simpa [prefixWord, tailWord_1393325, baseEnd_1393325] using wordTrace_append hprefix tailTrace_1393325
  have hstable : (prefixWord ++ tailWord_1393325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393325).length < 2 ^ (prefixWord ++ tailWord_1393325).sum := by decide
  have hdescent : baseEnd_1393325 < baseStart_1393325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393342 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_1393342 : Nat := 118140960795 + 1393342 * 2 ^ 59
def prefixEnd_1393342 : Nat := 4983230072969 + 3 ^ 40 * 1393342 * 2
def baseEnd_1393342 : Nat := 715454162096992776717143

theorem tailTrace_1393342 : CollatzResearch.WordTrace tailWord_1393342 prefixEnd_1393342 715454162096992776717143 := by
  unfold tailWord_1393342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6352419714770921589179785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33879571812111581808958853 6352419714770921589179785)
  ·
    refine ⟨4764314786078191191884839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6352419714770921589179785 4764314786078191191884839)
    ·
      refine ⟨7146472179117286787827259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4764314786078191191884839 7146472179117286787827259)
      ·
        refine ⟨10719708268675930181740889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7146472179117286787827259 10719708268675930181740889)
        ·
          refine ⟨8039781201506947636305667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10719708268675930181740889 8039781201506947636305667)
          ·
            refine ⟨12059671802260421454458501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8039781201506947636305667 12059671802260421454458501)
            ·
              refine ⟨2261188462923829022710969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12059671802260421454458501 2261188462923829022710969)
              ·
                refine ⟨1695891347192871767033227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261188462923829022710969 1695891347192871767033227)
                ·
                  refine ⟨2543837020789307650549841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695891347192871767033227 2543837020789307650549841)
                  ·
                    refine ⟨1907877765591980737912381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2543837020789307650549841 1907877765591980737912381)
                    ·
                      refine ⟨715454162096992776717143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907877765591980737912381 715454162096992776717143)
                      ·
                        rfl

theorem cell23_1393342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_1393342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393342 prefixEnd_1393342 := by exact prefixLift 1393342
  have htrace : WordTrace (prefixWord ++ tailWord_1393342) baseStart_1393342 baseEnd_1393342 := by
    simpa [prefixWord, tailWord_1393342, baseEnd_1393342] using wordTrace_append hprefix tailTrace_1393342
  have hstable : (prefixWord ++ tailWord_1393342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393342).length < 2 ^ (prefixWord ++ tailWord_1393342).sum := by decide
  have hdescent : baseEnd_1393342 < baseStart_1393342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393350 : List Nat := [6, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1393350 : Nat := 118140960795 + 1393350 * 2 ^ 59
def prefixEnd_1393350 : Nat := 4983230072969 + 3 ^ 40 * 1393350 * 2
def baseEnd_1393350 : Nat := 715458269942228745417107

theorem tailTrace_1393350 : CollatzResearch.WordTrace tailWord_1393350 prefixEnd_1393350 715458269942228745417107 := by
  unfold tailWord_1393350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588114046941824689991547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33879766334758926719819669 1588114046941824689991547)
  ·
    refine ⟨2382171070412737034987321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588114046941824689991547 2382171070412737034987321)
    ·
      refine ⟨1786628302809552776240491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2382171070412737034987321 1786628302809552776240491)
      ·
        refine ⟨2679942454214329164360737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786628302809552776240491 2679942454214329164360737)
        ·
          refine ⟨2009956840660746873270553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2679942454214329164360737 2009956840660746873270553)
          ·
            refine ⟨1507467630495560154952915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2009956840660746873270553 1507467630495560154952915)
            ·
              refine ⟨2261201445743340232429373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507467630495560154952915 2261201445743340232429373)
              ·
                refine ⟨847950542153752587161015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2261201445743340232429373 847950542153752587161015)
                ·
                  refine ⟨1271925813230628880741523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847950542153752587161015 1271925813230628880741523)
                  ·
                    refine ⟨1907888719845943321112285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1271925813230628880741523 1907888719845943321112285)
                    ·
                      refine ⟨715458269942228745417107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1907888719845943321112285 715458269942228745417107)
                      ·
                        rfl

theorem cell23_1393350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1393350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393350 prefixEnd_1393350 := by exact prefixLift 1393350
  have htrace : WordTrace (prefixWord ++ tailWord_1393350) baseStart_1393350 baseEnd_1393350 := by
    simpa [prefixWord, tailWord_1393350, baseEnd_1393350] using wordTrace_append hprefix tailTrace_1393350
  have hstable : (prefixWord ++ tailWord_1393350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393350).length < 2 ^ (prefixWord ++ tailWord_1393350).sum := by decide
  have hdescent : baseEnd_1393350 < baseStart_1393350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393356 : List Nat := [2, 2, 1, 5, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1393356 : Nat := 118140960795 + 1393356 * 2 ^ 59
def prefixEnd_1393356 : Nat := 4983230072969 + 3 ^ 40 * 1393356 * 2
def baseEnd_1393356 : Nat := 715461350826155721942079

theorem tailTrace_1393356 : CollatzResearch.WordTrace tailWord_1393356 prefixEnd_1393356 715461350826155721942079 := by
  unfold tailWord_1393356
  simp only [CollatzResearch.WordTrace]
  refine ⟨25409934170058326552223961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33879912226744435402965281 25409934170058326552223961)
  ·
    refine ⟨19057450627543744914167971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25409934170058326552223961 19057450627543744914167971)
    ·
      refine ⟨28586175941315617371251957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19057450627543744914167971 28586175941315617371251957)
      ·
        refine ⟨2679953994498339128554871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28586175941315617371251957 2679953994498339128554871)
        ·
          refine ⟨4019930991747508692832307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2679953994498339128554871 4019930991747508692832307)
          ·
            refine ⟨6029896487621263039248461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4019930991747508692832307 6029896487621263039248461)
            ·
              refine ⟨2261211182857973639718173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6029896487621263039248461 2261211182857973639718173)
              ·
                refine ⟨847954193571740114894315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2261211182857973639718173 847954193571740114894315)
                ·
                  refine ⟨1271931290357610172341473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847954193571740114894315 1271931290357610172341473)
                  ·
                    refine ⟨953948467768207629256105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271931290357610172341473 953948467768207629256105)
                    ·
                      refine ⟨715461350826155721942079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953948467768207629256105 715461350826155721942079)
                      ·
                        rfl

theorem cell23_1393356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1393356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393356 prefixEnd_1393356 := by exact prefixLift 1393356
  have htrace : WordTrace (prefixWord ++ tailWord_1393356) baseStart_1393356 baseEnd_1393356 := by
    simpa [prefixWord, tailWord_1393356, baseEnd_1393356] using wordTrace_append hprefix tailTrace_1393356
  have hstable : (prefixWord ++ tailWord_1393356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393356).length < 2 ^ (prefixWord ++ tailWord_1393356).sum := by decide
  have hdescent : baseEnd_1393356 < baseStart_1393356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393371 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 5, 8]
def baseStart_1393371 : Nat := 118140960795 + 1393371 * 2 ^ 59
def prefixEnd_1393371 : Nat := 4983230072969 + 3 ^ 40 * 1393371 * 2
def baseEnd_1393371 : Nat := 238489684345324387751503

theorem tailTrace_1393371 : CollatzResearch.WordTrace tailWord_1393371 prefixEnd_1393371 238489684345324387751503 := by
  unfold tailWord_1393371
  simp only [CollatzResearch.WordTrace]
  refine ⟨50820415435062310666243967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33880276956708207110829311 50820415435062310666243967)
  ·
    refine ⟨76230623152593465999365951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50820415435062310666243967 76230623152593465999365951)
    ·
      refine ⟨114345934728890198999048927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76230623152593465999365951 114345934728890198999048927)
      ·
        refine ⟨171518902093335298498573391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114345934728890198999048927 171518902093335298498573391)
        ·
          refine ⟨257278353140002947747860087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171518902093335298498573391 257278353140002947747860087)
          ·
            refine ⟨385917529710004421621790131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257278353140002947747860087 385917529710004421621790131)
            ·
              refine ⟨578876294565006632432685197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385917529710004421621790131 578876294565006632432685197)
              ·
                refine ⟨217078610461877487162256949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 578876294565006632432685197 217078610461877487162256949)
                ·
                  refine ⟨20351119730801014421461589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 217078610461877487162256949 20351119730801014421461589)
                  ·
                    refine ⟨238489684345324387751503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20351119730801014421461589 238489684345324387751503)
                    ·
                      rfl

theorem cell23_1393371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_1393371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393371 prefixEnd_1393371 := by exact prefixLift 1393371
  have htrace : WordTrace (prefixWord ++ tailWord_1393371) baseStart_1393371 baseEnd_1393371 := by
    simpa [prefixWord, tailWord_1393371, baseEnd_1393371] using wordTrace_append hprefix tailTrace_1393371
  have hstable : (prefixWord ++ tailWord_1393371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393371).length < 2 ^ (prefixWord ++ tailWord_1393371).sum := by decide
  have hdescent : baseEnd_1393371 < baseStart_1393371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393395 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 1, 4, 2]
def baseStart_1393395 : Nat := 118140960795 + 1393395 * 2 ^ 59
def prefixEnd_1393395 : Nat := 4983230072969 + 3 ^ 40 * 1393395 * 2
def baseEnd_1393395 : Nat := 715481376571681069354399

theorem tailTrace_1393395 : CollatzResearch.WordTrace tailWord_1393395 prefixEnd_1393395 715481376571681069354399 := by
  unfold tailWord_1393395
  simp only [CollatzResearch.WordTrace]
  refine ⟨50821290786975362765117639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33880860524650241843411759 50821290786975362765117639)
  ·
    refine ⟨76231936180463044147676459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50821290786975362765117639 76231936180463044147676459)
    ·
      refine ⟨114347904270694566221514689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76231936180463044147676459 114347904270694566221514689)
      ·
        refine ⟨85760928203020924666136017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114347904270694566221514689 85760928203020924666136017)
        ·
          refine ⟨64320696152265693499602013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85760928203020924666136017 64320696152265693499602013)
          ·
            refine ⟨24120261057099635062350755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64320696152265693499602013 24120261057099635062350755)
            ·
              refine ⟨36180391585649452593526133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24120261057099635062350755 36180391585649452593526133)
              ·
                refine ⟨3391911711154636180643075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36180391585649452593526133 3391911711154636180643075)
                ·
                  refine ⟨5087867566731954270964613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391911711154636180643075 5087867566731954270964613)
                  ·
                    refine ⟨953975168762241425805865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087867566731954270964613 953975168762241425805865)
                    ·
                      refine ⟨715481376571681069354399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953975168762241425805865 715481376571681069354399)
                      ·
                        rfl

theorem cell23_1393395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 4, 2].length) (baseStart_1393395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393395 prefixEnd_1393395 := by exact prefixLift 1393395
  have htrace : WordTrace (prefixWord ++ tailWord_1393395) baseStart_1393395 baseEnd_1393395 := by
    simpa [prefixWord, tailWord_1393395, baseEnd_1393395] using wordTrace_append hprefix tailTrace_1393395
  have hstable : (prefixWord ++ tailWord_1393395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393395).length < 2 ^ (prefixWord ++ tailWord_1393395).sum := by decide
  have hdescent : baseEnd_1393395 < baseStart_1393395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393412 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_1393412 : Nat := 118140960795 + 1393412 * 2 ^ 59
def prefixEnd_1393412 : Nat := 4983230072969 + 3 ^ 40 * 1393412 * 2
def baseEnd_1393412 : Nat := 715490105742807502841821

theorem tailTrace_1393412 : CollatzResearch.WordTrace tailWord_1393412 prefixEnd_1393412 715490105742807502841821 := by
  unfold tailWord_1393412
  simp only [CollatzResearch.WordTrace]
  refine ⟨25410955413956887334243245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33881273885275849778990993 25410955413956887334243245)
  ·
    refine ⟨9529108280233832750341217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25410955413956887334243245 9529108280233832750341217)
    ·
      refine ⟨7146831210175374562755913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9529108280233832750341217 7146831210175374562755913)
      ·
        refine ⟨5360123407631530922066935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7146831210175374562755913 5360123407631530922066935)
        ·
          refine ⟨8040185111447296383100403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360123407631530922066935 8040185111447296383100403)
          ·
            refine ⟨12060277667170944574650605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040185111447296383100403 12060277667170944574650605)
            ·
              refine ⟨4522604125189104215493977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12060277667170944574650605 4522604125189104215493977)
              ·
                refine ⟨3391953093891828161620483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522604125189104215493977 3391953093891828161620483)
                ·
                  refine ⟨5087929640837742242430725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3391953093891828161620483 5087929640837742242430725)
                  ·
                    refine ⟨953986807657076670455761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5087929640837742242430725 953986807657076670455761)
                    ·
                      refine ⟨715490105742807502841821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953986807657076670455761 715490105742807502841821)
                      ·
                        rfl

theorem cell23_1393412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_1393412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393412 prefixEnd_1393412 := by exact prefixLift 1393412
  have htrace : WordTrace (prefixWord ++ tailWord_1393412) baseStart_1393412 baseEnd_1393412 := by
    simpa [prefixWord, tailWord_1393412, baseEnd_1393412] using wordTrace_append hprefix tailTrace_1393412
  have hstable : (prefixWord ++ tailWord_1393412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393412).length < 2 ^ (prefixWord ++ tailWord_1393412).sum := by decide
  have hdescent : baseEnd_1393412 < baseStart_1393412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393415 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1393415 : Nat := 118140960795 + 1393415 * 2 ^ 59
def prefixEnd_1393415 : Nat := 4983230072969 + 3 ^ 40 * 1393415 * 2
def baseEnd_1393415 : Nat := 715491646184770991104307

theorem tailTrace_1393415 : CollatzResearch.WordTrace tailWord_1393415 prefixEnd_1393415 715491646184770991104307 := by
  unfold tailWord_1393415
  simp only [CollatzResearch.WordTrace]
  refine ⟨50822020246902906180845699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33881346831268604120563799 50822020246902906180845699)
  ·
    refine ⟨76233030370354359271268549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50822020246902906180845699 76233030370354359271268549)
    ·
      refine ⟨14293693194441442363362853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76233030370354359271268549 14293693194441442363362853)
      ·
        refine ⟨2680067473957770443130535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14293693194441442363362853 2680067473957770443130535)
        ·
          refine ⟨4020101210936655664695803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680067473957770443130535 4020101210936655664695803)
          ·
            refine ⟨6030151816404983497043705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020101210936655664695803 6030151816404983497043705)
            ·
              refine ⟨4522613862303737622782779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6030151816404983497043705 4522613862303737622782779)
              ·
                refine ⟨6783920793455606434174169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522613862303737622782779 6783920793455606434174169)
                ·
                  refine ⟨5087940595091704825630627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6783920793455606434174169 5087940595091704825630627)
                  ·
                    refine ⟨7631910892637557238445941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5087940595091704825630627 7631910892637557238445941)
                    ·
                      refine ⟨715491646184770991104307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7631910892637557238445941 715491646184770991104307)
                      ·
                        rfl

theorem cell23_1393415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1393415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393415 prefixEnd_1393415 := by exact prefixLift 1393415
  have htrace : WordTrace (prefixWord ++ tailWord_1393415) baseStart_1393415 baseEnd_1393415 := by
    simpa [prefixWord, tailWord_1393415, baseEnd_1393415] using wordTrace_append hprefix tailTrace_1393415
  have hstable : (prefixWord ++ tailWord_1393415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393415).length < 2 ^ (prefixWord ++ tailWord_1393415).sum := by decide
  have hdescent : baseEnd_1393415 < baseStart_1393415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393429 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_1393429 : Nat := 118140960795 + 1393429 * 2 ^ 59
def prefixEnd_1393429 : Nat := 4983230072969 + 3 ^ 40 * 1393429 * 2
def baseEnd_1393429 : Nat := 715498834913933936329243

theorem tailTrace_1393429 : CollatzResearch.WordTrace tailWord_1393429 prefixEnd_1393429 715498834913933936329243 := by
  unfold tailWord_1393429
  simp only [CollatzResearch.WordTrace]
  refine ⟨50822530868852186571855341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33881687245901457714570227 50822530868852186571855341)
  ·
    refine ⟨19058449075819569964445753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50822530868852186571855341 19058449075819569964445753)
    ·
      refine ⟨14293836806864677473334315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19058449075819569964445753 14293836806864677473334315)
      ·
        refine ⟨21440755210297016210001473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14293836806864677473334315 21440755210297016210001473)
        ·
          refine ⟨16080566407722762157501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21440755210297016210001473 16080566407722762157501105)
          ·
            refine ⟨12060424805792071618125829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16080566407722762157501105 12060424805792071618125829)
            ·
              refine ⟨2261329651086013428398593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12060424805792071618125829 2261329651086013428398593)
              ·
                refine ⟨1695997238314510071298945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261329651086013428398593 1695997238314510071298945)
                ·
                  refine ⟨1271997928735882553474209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1695997238314510071298945 1271997928735882553474209)
                  ·
                    refine ⟨953998446551911915105657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1271997928735882553474209 953998446551911915105657)
                    ·
                      refine ⟨715498834913933936329243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 953998446551911915105657 715498834913933936329243)
                      ·
                        rfl

theorem cell23_1393429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_1393429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393429 prefixEnd_1393429 := by exact prefixLift 1393429
  have htrace : WordTrace (prefixWord ++ tailWord_1393429) baseStart_1393429 baseEnd_1393429 := by
    simpa [prefixWord, tailWord_1393429, baseEnd_1393429] using wordTrace_append hprefix tailTrace_1393429
  have hstable : (prefixWord ++ tailWord_1393429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393429).length < 2 ^ (prefixWord ++ tailWord_1393429).sum := by decide
  have hdescent : baseEnd_1393429 < baseStart_1393429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393445 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_1393445 : Nat := 118140960795 + 1393445 * 2 ^ 59
def prefixEnd_1393445 : Nat := 4983230072969 + 3 ^ 40 * 1393445 * 2
def baseEnd_1393445 : Nat := 715507050604405873729169

theorem tailTrace_1393445 : CollatzResearch.WordTrace tailWord_1393445 prefixEnd_1393445 715507050604405873729169 := by
  unfold tailWord_1393445
  simp only [CollatzResearch.WordTrace]
  refine ⟨50823114436794221304437789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33882076291196147536291859 50823114436794221304437789)
  ·
    refine ⟨19058667913797832989164171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50823114436794221304437789 19058667913797832989164171)
    ·
      refine ⟨28588001870696749483746257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19058667913797832989164171 28588001870696749483746257)
      ·
        refine ⟨21441001403022562112809693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28588001870696749483746257 21441001403022562112809693)
        ·
          refine ⟨8040375526133460792303635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21441001403022562112809693 8040375526133460792303635)
          ·
            refine ⟨12060563289200191188455453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8040375526133460792303635 12060563289200191188455453)
            ·
              refine ⟨4522711233450071695670795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12060563289200191188455453 4522711233450071695670795)
              ·
                refine ⟨6784066850175107543506193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4522711233450071695670795 6784066850175107543506193)
                ·
                  refine ⟨5088050137631330657629645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6784066850175107543506193 5088050137631330657629645)
                  ·
                    refine ⟨1908018801611748996611117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5088050137631330657629645 1908018801611748996611117)
                    ·
                      refine ⟨715507050604405873729169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1908018801611748996611117 715507050604405873729169)
                      ·
                        rfl

theorem cell23_1393445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_1393445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393445 prefixEnd_1393445 := by exact prefixLift 1393445
  have htrace : WordTrace (prefixWord ++ tailWord_1393445) baseStart_1393445 baseEnd_1393445 := by
    simpa [prefixWord, tailWord_1393445, baseEnd_1393445] using wordTrace_append hprefix tailTrace_1393445
  have hstable : (prefixWord ++ tailWord_1393445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393445).length < 2 ^ (prefixWord ++ tailWord_1393445).sum := by decide
  have hdescent : baseEnd_1393445 < baseStart_1393445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393469 : List Nat := [1, 4, 1, 4, 2, 1, 2, 3, 5]
def baseStart_1393469 : Nat := 118140960795 + 1393469 * 2 ^ 59
def prefixEnd_1393469 : Nat := 4983230072969 + 3 ^ 40 * 1393469 * 2
def baseEnd_1393469 : Nat := 79502152682234864425451

theorem tailTrace_1393469 : CollatzResearch.WordTrace tailWord_1393469 prefixEnd_1393469 79502152682234864425451 := by
  unfold tailWord_1393469
  simp only [CollatzResearch.WordTrace]
  refine ⟨50823989788707273403311461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33882659859138182268874307 50823989788707273403311461)
  ·
    refine ⟨9529498085382613763120899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50823989788707273403311461 9529498085382613763120899)
    ·
      refine ⟨14294247128073920644681349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9529498085382613763120899 14294247128073920644681349)
      ·
        refine ⟨2680171336513860120877753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14294247128073920644681349 2680171336513860120877753)
        ·
          refine ⟨2010128502385395090658315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2680171336513860120877753 2010128502385395090658315)
          ·
            refine ⟨3015192753578092635987473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010128502385395090658315 3015192753578092635987473)
            ·
              refine ⟨2261394565183569476990605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015192753578092635987473 2261394565183569476990605)
              ·
                refine ⟨848022961943838553871477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2261394565183569476990605 848022961943838553871477)
                ·
                  refine ⟨79502152682234864425451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 848022961943838553871477 79502152682234864425451)
                  ·
                    rfl

theorem cell23_1393469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_1393469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393469 prefixEnd_1393469 := by exact prefixLift 1393469
  have htrace : WordTrace (prefixWord ++ tailWord_1393469) baseStart_1393469 baseEnd_1393469 := by
    simpa [prefixWord, tailWord_1393469, baseEnd_1393469] using wordTrace_append hprefix tailTrace_1393469
  have hstable : (prefixWord ++ tailWord_1393469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393469).length < 2 ^ (prefixWord ++ tailWord_1393469).sum := by decide
  have hdescent : baseEnd_1393469 < baseStart_1393469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393488 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_1393488 : Nat := 118140960795 + 1393488 * 2 ^ 59
def prefixEnd_1393488 : Nat := 4983230072969 + 3 ^ 40 * 1393488 * 2
def baseEnd_1393488 : Nat := 715529130272549205491471

theorem tailTrace_1393488 : CollatzResearch.WordTrace tailWord_1393488 prefixEnd_1393488 715529130272549205491471 := by
  unfold tailWord_1393488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25412341387819219824126559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33883121850425626432168745 25412341387819219824126559)
  ·
    refine ⟨38118512081728829736189839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25412341387819219824126559 38118512081728829736189839)
    ·
      refine ⟨57177768122593244604284759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38118512081728829736189839 57177768122593244604284759)
      ·
        refine ⟨85766652183889866906427139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57177768122593244604284759 85766652183889866906427139)
        ·
          refine ⟨128649978275834800359640709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85766652183889866906427139 128649978275834800359640709)
          ·
            refine ⟨24121870926719025067432633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128649978275834800359640709 24121870926719025067432633)
            ·
              refine ⟨18091403195039268800574475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24121870926719025067432633 18091403195039268800574475)
              ·
                refine ⟨27137104792558903200861713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18091403195039268800574475 27137104792558903200861713)
                ·
                  refine ⟨20352828594419177400646285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27137104792558903200861713 20352828594419177400646285)
                  ·
                    refine ⟨7632310722907191525242357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20352828594419177400646285 7632310722907191525242357)
                    ·
                      refine ⟨715529130272549205491471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7632310722907191525242357 715529130272549205491471)
                      ·
                        rfl

theorem cell23_1393488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_1393488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393488 prefixEnd_1393488 := by exact prefixLift 1393488
  have htrace : WordTrace (prefixWord ++ tailWord_1393488) baseStart_1393488 baseEnd_1393488 := by
    simpa [prefixWord, tailWord_1393488, baseEnd_1393488] using wordTrace_append hprefix tailTrace_1393488
  have hstable : (prefixWord ++ tailWord_1393488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393488).length < 2 ^ (prefixWord ++ tailWord_1393488).sum := by decide
  have hdescent : baseEnd_1393488 < baseStart_1393488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393505 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_1393505 : Nat := 118140960795 + 1393505 * 2 ^ 59
def prefixEnd_1393505 : Nat := 4983230072969 + 3 ^ 40 * 1393505 * 2
def baseEnd_1393505 : Nat := 715537859443675638978893

theorem tailTrace_1393505 : CollatzResearch.WordTrace tailWord_1393505 prefixEnd_1393505 715537859443675638978893 := by
  unfold tailWord_1393505
  simp only [CollatzResearch.WordTrace]
  refine ⟨50825302816576851551621969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33883535211051234367747979 50825302816576851551621969)
  ·
    refine ⟨38118977112432638663716477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50825302816576851551621969 38118977112432638663716477)
    ·
      refine ⟨14294616417162239498893679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38118977112432638663716477 14294616417162239498893679)
      ·
        refine ⟨21441924625743359248340519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14294616417162239498893679 21441924625743359248340519)
        ·
          refine ⟨32162886938615038872510779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21441924625743359248340519 32162886938615038872510779)
          ·
            refine ⟨48244330407922558308766169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32162886938615038872510779 48244330407922558308766169)
            ·
              refine ⟨36183247805941918731574627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48244330407922558308766169 36183247805941918731574627)
              ·
                refine ⟨54274871708912878097361941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36183247805941918731574627 54274871708912878097361941)
                ·
                  refine ⟨2544134611355291160813841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54274871708912878097361941 2544134611355291160813841)
                  ·
                    refine ⟨1908100958516468370610381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2544134611355291160813841 1908100958516468370610381)
                    ·
                      refine ⟨715537859443675638978893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1908100958516468370610381 715537859443675638978893)
                      ·
                        rfl

theorem cell23_1393505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_1393505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393505 prefixEnd_1393505 := by exact prefixLift 1393505
  have htrace : WordTrace (prefixWord ++ tailWord_1393505) baseStart_1393505 baseEnd_1393505 := by
    simpa [prefixWord, tailWord_1393505, baseEnd_1393505] using wordTrace_append hprefix tailTrace_1393505
  have hstable : (prefixWord ++ tailWord_1393505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393505).length < 2 ^ (prefixWord ++ tailWord_1393505).sum := by decide
  have hdescent : baseEnd_1393505 < baseStart_1393505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393512 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1393512 : Nat := 118140960795 + 1393512 * 2 ^ 59
def prefixEnd_1393512 : Nat := 4983230072969 + 3 ^ 40 * 1393512 * 2
def baseEnd_1393512 : Nat := 238513817936085703863787

theorem tailTrace_1393512 : CollatzResearch.WordTrace tailWord_1393512 prefixEnd_1393512 238513817936085703863787 := by
  unfold tailWord_1393512
  simp only [CollatzResearch.WordTrace]
  refine ⟨25412779063775745873563395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33883705418367661164751193 25412779063775745873563395)
  ·
    refine ⟨38119168595663618810345093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25412779063775745873563395 38119168595663618810345093)
    ·
      refine ⟨7147344111686928526939705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38119168595663618810345093 7147344111686928526939705)
      ·
        refine ⟨5360508083765196395204779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7147344111686928526939705 5360508083765196395204779)
        ·
          refine ⟨8040762125647794592807169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360508083765196395204779 8040762125647794592807169)
          ·
            refine ⟨6030571594235845944605377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8040762125647794592807169 6030571594235845944605377)
            ·
              refine ⟨4522928695676884458454033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6030571594235845944605377 4522928695676884458454033)
              ·
                refine ⟨3392196521757663343840525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4522928695676884458454033 3392196521757663343840525)
                ·
                  refine ⟨1272073695659123753940197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3392196521757663343840525 1272073695659123753940197)
                  ·
                    refine ⟨238513817936085703863787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1272073695659123753940197 238513817936085703863787)
                    ·
                      rfl

theorem cell23_1393512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1393512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393512 prefixEnd_1393512 := by exact prefixLift 1393512
  have htrace : WordTrace (prefixWord ++ tailWord_1393512) baseStart_1393512 baseEnd_1393512 := by
    simpa [prefixWord, tailWord_1393512, baseEnd_1393512] using wordTrace_append hprefix tailTrace_1393512
  have hstable : (prefixWord ++ tailWord_1393512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393512).length < 2 ^ (prefixWord ++ tailWord_1393512).sum := by decide
  have hdescent : baseEnd_1393512 < baseStart_1393512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393525 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 8]
def baseStart_1393525 : Nat := 118140960795 + 1393525 * 2 ^ 59
def prefixEnd_1393525 : Nat := 4983230072969 + 3 ^ 40 * 1393525 * 2
def baseEnd_1393525 : Nat := 79505347672973951192089

theorem tailTrace_1393525 : CollatzResearch.WordTrace tailWord_1393525 prefixEnd_1393525 79505347672973951192089 := by
  unfold tailWord_1393525
  simp only [CollatzResearch.WordTrace]
  refine ⟨50826032276504394967350029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33884021517669596644900019 50826032276504394967350029)
  ·
    refine ⟨19059762103689148112756261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50826032276504394967350029 19059762103689148112756261)
    ·
      refine ⟨3573705394441715271141799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19059762103689148112756261 3573705394441715271141799)
      ·
        refine ⟨5360558091662572906712699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3573705394441715271141799 5360558091662572906712699)
        ·
          refine ⟨8040837137493859360069049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360558091662572906712699 8040837137493859360069049)
          ·
            refine ⟨6030627853120394520051787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8040837137493859360069049 6030627853120394520051787)
            ·
              refine ⟨9045941779680591780077681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6030627853120394520051787 9045941779680591780077681)
              ·
                refine ⟨6784456334760443835058261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9045941779680591780077681 6784456334760443835058261)
                ·
                  refine ⟨79505347672973951192089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6784456334760443835058261 79505347672973951192089)
                  ·
                    rfl

theorem cell23_1393525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_1393525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393525 prefixEnd_1393525 := by exact prefixLift 1393525
  have htrace : WordTrace (prefixWord ++ tailWord_1393525) baseStart_1393525 baseEnd_1393525 := by
    simpa [prefixWord, tailWord_1393525, baseEnd_1393525] using wordTrace_append hprefix tailTrace_1393525
  have hstable : (prefixWord ++ tailWord_1393525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393525).length < 2 ^ (prefixWord ++ tailWord_1393525).sum := by decide
  have hdescent : baseEnd_1393525 < baseStart_1393525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393528 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1393528 : Nat := 118140960795 + 1393528 * 2 ^ 59
def prefixEnd_1393528 : Nat := 4983230072969 + 3 ^ 40 * 1393528 * 2
def baseEnd_1393528 : Nat := 715549669498729048991287

theorem tailTrace_1393528 : CollatzResearch.WordTrace tailWord_1393528 prefixEnd_1393528 715549669498729048991287 := by
  unfold tailWord_1393528
  simp only [CollatzResearch.WordTrace]
  refine ⟨25413070847746763239854619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33884094463662350986472825 25413070847746763239854619)
  ·
    refine ⟨38119606271620144859781929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25413070847746763239854619 38119606271620144859781929)
    ·
      refine ⟨28589704703715108644836447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38119606271620144859781929 28589704703715108644836447)
      ·
        refine ⟨42884557055572662967254671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28589704703715108644836447 42884557055572662967254671)
        ·
          refine ⟨64326835583358994450882007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42884557055572662967254671 64326835583358994450882007)
          ·
            refine ⟨96490253375038491676323011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64326835583358994450882007 96490253375038491676323011)
            ·
              refine ⟨144735380062557737514484517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96490253375038491676323011 144735380062557737514484517)
              ·
                refine ⟨27137883761729575783965847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144735380062557737514484517 27137883761729575783965847)
                ·
                  refine ⟨40706825642594363675948771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27137883761729575783965847 40706825642594363675948771)
                  ·
                    refine ⟨61060238463891545513923157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40706825642594363675948771 61060238463891545513923157)
                    ·
                      refine ⟨715549669498729048991287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 61060238463891545513923157 715549669498729048991287)
                      ·
                        rfl

theorem cell23_1393528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1393528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393528 prefixEnd_1393528 := by exact prefixLift 1393528
  have htrace : WordTrace (prefixWord ++ tailWord_1393528) baseStart_1393528 baseEnd_1393528 := by
    simpa [prefixWord, tailWord_1393528, baseEnd_1393528] using wordTrace_append hprefix tailTrace_1393528
  have hstable : (prefixWord ++ tailWord_1393528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393528).length < 2 ^ (prefixWord ++ tailWord_1393528).sum := by decide
  have hdescent : baseEnd_1393528 < baseStart_1393528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393529 : List Nat := [1, 2, 1, 3, 2, 3, 3, 3, 1, 4]
def baseStart_1393529 : Nat := 118140960795 + 1393529 * 2 ^ 59
def prefixEnd_1393529 : Nat := 4983230072969 + 3 ^ 40 * 1393529 * 2
def baseEnd_1393529 : Nat := 238516727659794515026261

theorem tailTrace_1393529 : CollatzResearch.WordTrace tailWord_1393529 prefixEnd_1393529 238516727659794515026261 := by
  unfold tailWord_1393529
  simp only [CollatzResearch.WordTrace]
  refine ⟨50826178168489903650495641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33884118778993269100330427 50826178168489903650495641)
  ·
    refine ⟨38119633626367427737871731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50826178168489903650495641 38119633626367427737871731)
    ·
      refine ⟨57179450439551141606807597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38119633626367427737871731 57179450439551141606807597)
      ·
        refine ⟨21442293914831678102552849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57179450439551141606807597 21442293914831678102552849)
        ·
          refine ⟨16081720436123758576914637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21442293914831678102552849 16081720436123758576914637)
          ·
            refine ⟨6030645163546409466342989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16081720436123758576914637 6030645163546409466342989)
            ·
              refine ⟨2261491936329903549878621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6030645163546409466342989 2261491936329903549878621)
              ·
                refine ⟨848059476123713831204483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2261491936329903549878621 848059476123713831204483)
                ·
                  refine ⟨1272089214185570746806725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848059476123713831204483 1272089214185570746806725)
                  ·
                    refine ⟨238516727659794515026261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1272089214185570746806725 238516727659794515026261)
                    ·
                      rfl

theorem cell23_1393529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 4].length) (baseStart_1393529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393529 prefixEnd_1393529 := by exact prefixLift 1393529
  have htrace : WordTrace (prefixWord ++ tailWord_1393529) baseStart_1393529 baseEnd_1393529 := by
    simpa [prefixWord, tailWord_1393529, baseEnd_1393529] using wordTrace_append hprefix tailTrace_1393529
  have hstable : (prefixWord ++ tailWord_1393529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393529).length < 2 ^ (prefixWord ++ tailWord_1393529).sum := by decide
  have hdescent : baseEnd_1393529 < baseStart_1393529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393589 : List Nat := [1, 3, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1393589 : Nat := 118140960795 + 1393589 * 2 ^ 59
def prefixEnd_1393589 : Nat := 4983230072969 + 3 ^ 40 * 1393589 * 2
def baseEnd_1393589 : Nat := 238526997272884436776169

theorem tailTrace_1393589 : CollatzResearch.WordTrace tailWord_1393589 prefixEnd_1393589 238526997272884436776169 := by
  unfold tailWord_1393589
  simp only [CollatzResearch.WordTrace]
  refine ⟨50828366548272533897679821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33885577698848355931786547 50828366548272533897679821)
  ·
    refine ⟨19060637455602200211629933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50828366548272533897679821 19060637455602200211629933)
    ·
      refine ⟨7147739045850825079361225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19060637455602200211629933 7147739045850825079361225)
      ·
        refine ⟨5360804284388118809520919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7147739045850825079361225 5360804284388118809520919)
        ·
          refine ⟨8041206426582178214281379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360804284388118809520919 8041206426582178214281379)
          ·
            refine ⟨12061809639873267321422069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041206426582178214281379 12061809639873267321422069)
            ·
              refine ⟨1130794653738118811383319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12061809639873267321422069 1130794653738118811383319)
              ·
                refine ⟨1696191980607178217074979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130794653738118811383319 1696191980607178217074979)
                ·
                  refine ⟨2544287970910767325612469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696191980607178217074979 2544287970910767325612469)
                  ·
                    refine ⟨238526997272884436776169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2544287970910767325612469 238526997272884436776169)
                    ·
                      rfl

theorem cell23_1393589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1393589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393589 prefixEnd_1393589 := by exact prefixLift 1393589
  have htrace : WordTrace (prefixWord ++ tailWord_1393589) baseStart_1393589 baseEnd_1393589 := by
    simpa [prefixWord, tailWord_1393589, baseEnd_1393589] using wordTrace_append hprefix tailTrace_1393589
  have hstable : (prefixWord ++ tailWord_1393589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393589).length < 2 ^ (prefixWord ++ tailWord_1393589).sum := by decide
  have hdescent : baseEnd_1393589 < baseStart_1393589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393612 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1393612 : Nat := 118140960795 + 1393612 * 2 ^ 59
def prefixEnd_1393612 : Nat := 4983230072969 + 3 ^ 40 * 1393612 * 2
def baseEnd_1393612 : Nat := 715592801873706720340901

theorem tailTrace_1393612 : CollatzResearch.WordTrace tailWord_1393612 prefixEnd_1393612 715592801873706720340901 := by
  unfold tailWord_1393612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25414602713594604412883545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33886136951459472550511393 25414602713594604412883545)
  ·
    refine ⟨19060952035195953309662659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25414602713594604412883545 19060952035195953309662659)
    ·
      refine ⟨28591428052793929964493989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19060952035195953309662659 28591428052793929964493989)
      ·
        refine ⟨5360892759898861868342623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28591428052793929964493989 5360892759898861868342623)
        ·
          refine ⟨8041339139848292802513935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360892759898861868342623 8041339139848292802513935)
          ·
            refine ⟨12062008709772439203770903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041339139848292802513935 12062008709772439203770903)
            ·
              refine ⟨18093013064658658805656355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12062008709772439203770903 18093013064658658805656355)
              ·
                refine ⟨27139519596987988208484533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18093013064658658805656355 27139519596987988208484533)
                ·
                  refine ⟨2544329962217623894545425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27139519596987988208484533 2544329962217623894545425)
                  ·
                    refine ⟨1908247471663217920909069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2544329962217623894545425 1908247471663217920909069)
                    ·
                      refine ⟨715592801873706720340901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1908247471663217920909069 715592801873706720340901)
                      ·
                        rfl

theorem cell23_1393612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1393612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393612 prefixEnd_1393612 := by exact prefixLift 1393612
  have htrace : WordTrace (prefixWord ++ tailWord_1393612) baseStart_1393612 baseEnd_1393612 := by
    simpa [prefixWord, tailWord_1393612, baseEnd_1393612] using wordTrace_append hprefix tailTrace_1393612
  have hstable : (prefixWord ++ tailWord_1393612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393612).length < 2 ^ (prefixWord ++ tailWord_1393612).sum := by decide
  have hdescent : baseEnd_1393612 < baseStart_1393612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393615 : List Nat := [1, 1, 2, 1, 1, 6, 3, 8]
def baseStart_1393615 : Nat := 118140960795 + 1393615 * 2 ^ 59
def prefixEnd_1393615 : Nat := 4983230072969 + 3 ^ 40 * 1393615 * 2
def baseEnd_1393615 : Nat := 26503494159839637355681

theorem tailTrace_1393615 : CollatzResearch.WordTrace tailWord_1393615 prefixEnd_1393615 26503494159839637355681 := by
  unfold tailWord_1393615
  simp only [CollatzResearch.WordTrace]
  refine ⟨50829314846178340338126299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33886209897452226892084199 50829314846178340338126299)
  ·
    refine ⟨76243972269267510507189449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50829314846178340338126299 76243972269267510507189449)
    ·
      refine ⟨57182979201950632880392087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76243972269267510507189449 57182979201950632880392087)
      ·
        refine ⟨85774468802925949320588131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57182979201950632880392087 85774468802925949320588131)
        ·
          refine ⟨128661703204388923980882197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85774468802925949320588131 128661703204388923980882197)
          ·
            refine ⟨6031017337705730811603853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128661703204388923980882197 6031017337705730811603853)
            ·
              refine ⟨2261631501639649054351445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6031017337705730811603853 2261631501639649054351445)
              ·
                refine ⟨26503494159839637355681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2261631501639649054351445 26503494159839637355681)
                ·
                  rfl

theorem cell23_1393615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 8].length) (baseStart_1393615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393615 prefixEnd_1393615 := by exact prefixLift 1393615
  have htrace : WordTrace (prefixWord ++ tailWord_1393615) baseStart_1393615 baseEnd_1393615 := by
    simpa [prefixWord, tailWord_1393615, baseEnd_1393615] using wordTrace_append hprefix tailTrace_1393615
  have hstable : (prefixWord ++ tailWord_1393615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393615).length < 2 ^ (prefixWord ++ tailWord_1393615).sum := by decide
  have hdescent : baseEnd_1393615 < baseStart_1393615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393626 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2]
def baseStart_1393626 : Nat := 118140960795 + 1393626 * 2 ^ 59
def prefixEnd_1393626 : Nat := 4983230072969 + 3 ^ 40 * 1393626 * 2
def baseEnd_1393626 : Nat := 715599990602869665565837

theorem tailTrace_1393626 : CollatzResearch.WordTrace tailWord_1393626 prefixEnd_1393626 715599990602869665565837 := by
  unfold tailWord_1393626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707429012284622304194183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33886477366092326144517821 12707429012284622304194183)
  ·
    refine ⟨19061143518426933456291275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12707429012284622304194183 19061143518426933456291275)
    ·
      refine ⟨28591715277640400184436913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19061143518426933456291275 28591715277640400184436913)
      ·
        refine ⟨21443786458230300138327685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28591715277640400184436913 21443786458230300138327685)
        ·
          refine ⟨4020709960918181275936441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21443786458230300138327685 4020709960918181275936441)
          ·
            refine ⟨3015532470688635956952331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4020709960918181275936441 3015532470688635956952331)
            ·
              refine ⟨4523298706032953935428497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015532470688635956952331 4523298706032953935428497)
              ·
                refine ⟨3392474029524715451571373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523298706032953935428497 3392474029524715451571373)
                ·
                  refine ⟨1272177761071768294339265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3392474029524715451571373 1272177761071768294339265)
                  ·
                    refine ⟨954133320803826220754449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1272177761071768294339265 954133320803826220754449)
                    ·
                      refine ⟨715599990602869665565837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954133320803826220754449 715599990602869665565837)
                      ·
                        rfl

theorem cell23_1393626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_1393626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393626 prefixEnd_1393626 := by exact prefixLift 1393626
  have htrace : WordTrace (prefixWord ++ tailWord_1393626) baseStart_1393626 baseEnd_1393626 := by
    simpa [prefixWord, tailWord_1393626, baseEnd_1393626] using wordTrace_append hprefix tailTrace_1393626
  have hstable : (prefixWord ++ tailWord_1393626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393626).length < 2 ^ (prefixWord ++ tailWord_1393626).sum := by decide
  have hdescent : baseEnd_1393626 < baseStart_1393626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393629 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1393629 : Nat := 118140960795 + 1393629 * 2 ^ 59
def prefixEnd_1393629 : Nat := 4983230072969 + 3 ^ 40 * 1393629 * 2
def baseEnd_1393629 : Nat := 715601531044833153828323

theorem tailTrace_1393629 : CollatzResearch.WordTrace tailWord_1393629 prefixEnd_1393629 715601531044833153828323 := by
  unfold tailWord_1393629
  simp only [CollatzResearch.WordTrace]
  refine ⟨50829825468127620729135941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33886550312085080486090627 50829825468127620729135941)
  ·
    refine ⟨9530592275273928886712989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50829825468127620729135941 9530592275273928886712989)
    ·
      refine ⟨3573972103227723332517371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9530592275273928886712989 3573972103227723332517371)
      ·
        refine ⟨5360958154841584998776057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3573972103227723332517371 5360958154841584998776057)
        ·
          refine ⟨4020718616131188749082043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5360958154841584998776057 4020718616131188749082043)
          ·
            refine ⟨6031077924196783123623065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020718616131188749082043 6031077924196783123623065)
            ·
              refine ⟨4523308443147587342717299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6031077924196783123623065 4523308443147587342717299)
              ·
                refine ⟨6784962664721381014075949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4523308443147587342717299 6784962664721381014075949)
                ·
                  refine ⟨2544360999270517880278481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6784962664721381014075949 2544360999270517880278481)
                  ·
                    refine ⟨1908270749452888410208861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2544360999270517880278481 1908270749452888410208861)
                    ·
                      refine ⟨715601531044833153828323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1908270749452888410208861 715601531044833153828323)
                      ·
                        rfl

theorem cell23_1393629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1393629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393629 prefixEnd_1393629 := by exact prefixLift 1393629
  have htrace : WordTrace (prefixWord ++ tailWord_1393629) baseStart_1393629 baseEnd_1393629 := by
    simpa [prefixWord, tailWord_1393629, baseEnd_1393629] using wordTrace_append hprefix tailTrace_1393629
  have hstable : (prefixWord ++ tailWord_1393629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393629).length < 2 ^ (prefixWord ++ tailWord_1393629).sum := by decide
  have hdescent : baseEnd_1393629 < baseStart_1393629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393646 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_1393646 : Nat := 118140960795 + 1393646 * 2 ^ 59
def prefixEnd_1393646 : Nat := 4983230072969 + 3 ^ 40 * 1393646 * 2
def baseEnd_1393646 : Nat := 715610260215959587315745

theorem tailTrace_1393646 : CollatzResearch.WordTrace tailWord_1393646 prefixEnd_1393646 715610260215959587315745 := by
  unfold tailWord_1393646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353805688633254079063099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33886963672710688421669861 6353805688633254079063099)
  ·
    refine ⟨9530708532949881118594649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6353805688633254079063099 9530708532949881118594649)
    ·
      refine ⟨7148031399712410838945987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9530708532949881118594649 7148031399712410838945987)
      ·
        refine ⟨10722047099568616258418981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148031399712410838945987 10722047099568616258418981)
        ·
          refine ⟨2010383831169115548453559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10722047099568616258418981 2010383831169115548453559)
          ·
            refine ⟨3015575746753673322680339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010383831169115548453559 3015575746753673322680339)
            ·
              refine ⟨4523363620130509984020509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015575746753673322680339 4523363620130509984020509)
              ·
                refine ⟨1696261357548941244007691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4523363620130509984020509 1696261357548941244007691)
                ·
                  refine ⟨2544392036323411866011537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696261357548941244007691 2544392036323411866011537)
                  ·
                    refine ⟨1908294027242558899508653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2544392036323411866011537 1908294027242558899508653)
                    ·
                      refine ⟨715610260215959587315745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1908294027242558899508653 715610260215959587315745)
                      ·
                        rfl

theorem cell23_1393646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_1393646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393646 prefixEnd_1393646 := by exact prefixLift 1393646
  have htrace : WordTrace (prefixWord ++ tailWord_1393646) baseStart_1393646 baseEnd_1393646 := by
    simpa [prefixWord, tailWord_1393646, baseEnd_1393646] using wordTrace_append hprefix tailTrace_1393646
  have hstable : (prefixWord ++ tailWord_1393646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393646).length < 2 ^ (prefixWord ++ tailWord_1393646).sum := by decide
  have hdescent : baseEnd_1393646 < baseStart_1393646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393703 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1393703 : Nat := 118140960795 + 1393703 * 2 ^ 59
def prefixEnd_1393703 : Nat := 4983230072969 + 3 ^ 40 * 1393703 * 2
def baseEnd_1393703 : Nat := 715639528613265864302983

theorem tailTrace_1393703 : CollatzResearch.WordTrace tailWord_1393703 prefixEnd_1393703 715639528613265864302983 := by
  unfold tailWord_1393703
  simp only [CollatzResearch.WordTrace]
  refine ⟨50832524469859531367329763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33888349646573020911553175 50832524469859531367329763)
  ·
    refine ⟨76248786704789297050994645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50832524469859531367329763 76248786704789297050994645)
    ·
      refine ⟨1787080938393499149632687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 76248786704789297050994645 1787080938393499149632687)
      ·
        refine ⟨2680621407590248724449031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787080938393499149632687 2680621407590248724449031)
        ·
          refine ⟨4020932111385373086673547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680621407590248724449031 4020932111385373086673547)
          ·
            refine ⟨6031398167078059630010321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020932111385373086673547 6031398167078059630010321)
            ·
              refine ⟨4523548625308544722507741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6031398167078059630010321 4523548625308544722507741)
              ·
                refine ⟨1696330734490704270940403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4523548625308544722507741 1696330734490704270940403)
                ·
                  refine ⟨2544496101736056406410605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1696330734490704270940403 2544496101736056406410605)
                  ·
                    refine ⟨954186038151021152403977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544496101736056406410605 954186038151021152403977)
                    ·
                      refine ⟨715639528613265864302983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954186038151021152403977 715639528613265864302983)
                      ·
                        rfl

theorem cell23_1393703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1393703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393703 prefixEnd_1393703 := by exact prefixLift 1393703
  have htrace : WordTrace (prefixWord ++ tailWord_1393703) baseStart_1393703 baseEnd_1393703 := by
    simpa [prefixWord, tailWord_1393703, baseEnd_1393703] using wordTrace_append hprefix tailTrace_1393703
  have hstable : (prefixWord ++ tailWord_1393703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393703).length < 2 ^ (prefixWord ++ tailWord_1393703).sum := by decide
  have hdescent : baseEnd_1393703 < baseStart_1393703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393715 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9]
def baseStart_1393715 : Nat := 118140960795 + 1393715 * 2 ^ 59
def prefixEnd_1393715 : Nat := 4983230072969 + 3 ^ 40 * 1393715 * 2
def baseEnd_1393715 : Nat := 715645690381119817352927

theorem tailTrace_1393715 : CollatzResearch.WordTrace tailWord_1393715 prefixEnd_1393715 715645690381119817352927 := by
  unfold tailWord_1393715
  simp only [CollatzResearch.WordTrace]
  refine ⟨50832962145816057416766599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33888641430544038277844399 50832962145816057416766599)
  ·
    refine ⟨76249443218724086125149899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50832962145816057416766599 76249443218724086125149899)
    ·
      refine ⟨114374164828086129187724849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76249443218724086125149899 114374164828086129187724849)
      ·
        refine ⟨85780623621064596890793637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114374164828086129187724849 85780623621064596890793637)
        ·
          refine ⟨16083866928949611917023807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85780623621064596890793637 16083866928949611917023807)
          ·
            refine ⟨24125800393424417875535711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16083866928949611917023807 24125800393424417875535711)
            ·
              refine ⟨36188700590136626813303567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24125800393424417875535711 36188700590136626813303567)
              ·
                refine ⟨54283050885204940219955351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36188700590136626813303567 54283050885204940219955351)
                ·
                  refine ⟨81424576327807410329933027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54283050885204940219955351 81424576327807410329933027)
                  ·
                    refine ⟨122136864491711115494899541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81424576327807410329933027 122136864491711115494899541)
                    ·
                      refine ⟨715645690381119817352927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 122136864491711115494899541 715645690381119817352927)
                      ·
                        rfl

theorem cell23_1393715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_1393715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393715 prefixEnd_1393715 := by exact prefixLift 1393715
  have htrace : WordTrace (prefixWord ++ tailWord_1393715) baseStart_1393715 baseEnd_1393715 := by
    simpa [prefixWord, tailWord_1393715, baseEnd_1393715] using wordTrace_append hprefix tailTrace_1393715
  have hstable : (prefixWord ++ tailWord_1393715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393715).length < 2 ^ (prefixWord ++ tailWord_1393715).sum := by decide
  have hdescent : baseEnd_1393715 < baseStart_1393715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393722 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 7]
def baseStart_1393722 : Nat := 118140960795 + 1393722 * 2 ^ 59
def prefixEnd_1393722 : Nat := 4983230072969 + 3 ^ 40 * 1393722 * 2
def baseEnd_1393722 : Nat := 79516587193966809996155

theorem tailTrace_1393722 : CollatzResearch.WordTrace tailWord_1393722 prefixEnd_1393722 79516587193966809996155 := by
  unfold tailWord_1393722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12708304364197674403067855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33888811637860465074847613 12708304364197674403067855)
  ·
    refine ⟨19062456546296511604601783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12708304364197674403067855 19062456546296511604601783)
    ·
      refine ⟨28593684819444767406902675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19062456546296511604601783 28593684819444767406902675)
      ·
        refine ⟨42890527229167151110354013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28593684819444767406902675 42890527229167151110354013)
        ·
          refine ⟨16083947710937681666382755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42890527229167151110354013 16083947710937681666382755)
          ·
            refine ⟨24125921566406522499574133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16083947710937681666382755 24125921566406522499574133)
            ·
              refine ⟨2261805146850611484335075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24125921566406522499574133 2261805146850611484335075)
              ·
                refine ⟨3392707720275917226502613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261805146850611484335075 3392707720275917226502613)
                ·
                  refine ⟨79516587193966809996155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3392707720275917226502613 79516587193966809996155)
                  ·
                    rfl

theorem cell23_1393722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_1393722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393722 prefixEnd_1393722 := by exact prefixLift 1393722
  have htrace : WordTrace (prefixWord ++ tailWord_1393722) baseStart_1393722 baseEnd_1393722 := by
    simpa [prefixWord, tailWord_1393722, baseEnd_1393722] using wordTrace_append hprefix tailTrace_1393722
  have hstable : (prefixWord ++ tailWord_1393722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393722).length < 2 ^ (prefixWord ++ tailWord_1393722).sum := by decide
  have hdescent : baseEnd_1393722 < baseStart_1393722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393733 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 2, 2, 2]
def baseStart_1393733 : Nat := 118140960795 + 1393733 * 2 ^ 59
def prefixEnd_1393733 : Nat := 4983230072969 + 3 ^ 40 * 1393733 * 2
def baseEnd_1393733 : Nat := 715654933032900746927845

theorem tailTrace_1393733 : CollatzResearch.WordTrace tailWord_1393733 prefixEnd_1393733 715654933032900746927845 := by
  unfold tailWord_1393733
  simp only [CollatzResearch.WordTrace]
  refine ⟨50833618659750846490921853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33889079106500564327281235 50833618659750846490921853)
  ·
    refine ⟨19062606997406567434095695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50833618659750846490921853 19062606997406567434095695)
    ·
      refine ⟨28593910496109851151143543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19062606997406567434095695 28593910496109851151143543)
      ·
        refine ⟨42890865744164776726715315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28593910496109851151143543 42890865744164776726715315)
        ·
          refine ⟨64336298616247165090072973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42890865744164776726715315 64336298616247165090072973)
          ·
            refine ⟨24126111981092686908777365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64336298616247165090072973 24126111981092686908777365)
            ·
              refine ⟨1130911499113719698848939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24126111981092686908777365 1130911499113719698848939)
              ·
                refine ⟨1696367248670579548273409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130911499113719698848939 1696367248670579548273409)
                ·
                  refine ⟨1272275436502934661205057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1696367248670579548273409 1272275436502934661205057)
                  ·
                    refine ⟨954206577377200995903793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1272275436502934661205057 954206577377200995903793)
                    ·
                      refine ⟨715654933032900746927845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954206577377200995903793 715654933032900746927845)
                      ·
                        rfl

theorem cell23_1393733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_1393733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393733 prefixEnd_1393733 := by exact prefixLift 1393733
  have htrace : WordTrace (prefixWord ++ tailWord_1393733) baseStart_1393733 baseEnd_1393733 := by
    simpa [prefixWord, tailWord_1393733, baseEnd_1393733] using wordTrace_append hprefix tailTrace_1393733
  have hstable : (prefixWord ++ tailWord_1393733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393733).length < 2 ^ (prefixWord ++ tailWord_1393733).sum := by decide
  have hdescent : baseEnd_1393733 < baseStart_1393733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393750 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_1393750 : Nat := 118140960795 + 1393750 * 2 ^ 59
def prefixEnd_1393750 : Nat := 4983230072969 + 3 ^ 40 * 1393750 * 2
def baseEnd_1393750 : Nat := 715663662204027180415267

theorem tailTrace_1393750 : CollatzResearch.WordTrace tailWord_1393750 prefixEnd_1393750 715663662204027180415267 := by
  unfold tailWord_1393750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177139918793078649643169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33889492467126172262860469 3177139918793078649643169)
  ·
    refine ⟨2382854939094808987232377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3177139918793078649643169 2382854939094808987232377)
    ·
      refine ⟨1787141204321106740424283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2382854939094808987232377 1787141204321106740424283)
      ·
        refine ⟨2680711806481660110636425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787141204321106740424283 2680711806481660110636425)
        ·
          refine ⟨2010533854861245082977319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2680711806481660110636425 2010533854861245082977319)
          ·
            refine ⟨3015800782291867624465979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010533854861245082977319 3015800782291867624465979)
            ·
              refine ⟨4523701173437801436698969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015800782291867624465979 4523701173437801436698969)
              ·
                refine ⟨3392775880078351077524227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4523701173437801436698969 3392775880078351077524227)
                ·
                  refine ⟨5089163820117526616286341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3392775880078351077524227 5089163820117526616286341)
                  ·
                    refine ⟨954218216272036240553689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5089163820117526616286341 954218216272036240553689)
                    ·
                      refine ⟨715663662204027180415267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954218216272036240553689 715663662204027180415267)
                      ·
                        rfl

theorem cell23_1393750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_1393750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393750 prefixEnd_1393750 := by exact prefixLift 1393750
  have htrace : WordTrace (prefixWord ++ tailWord_1393750) baseStart_1393750 baseEnd_1393750 := by
    simpa [prefixWord, tailWord_1393750, baseEnd_1393750] using wordTrace_append hprefix tailTrace_1393750
  have hstable : (prefixWord ++ tailWord_1393750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393750).length < 2 ^ (prefixWord ++ tailWord_1393750).sum := by decide
  have hdescent : baseEnd_1393750 < baseStart_1393750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393773 : List Nat := [1, 5, 1, 1, 2, 4, 2, 2, 5]
def baseStart_1393773 : Nat := 118140960795 + 1393773 * 2 ^ 59
def prefixEnd_1393773 : Nat := 4983230072969 + 3 ^ 40 * 1393773 * 2
def baseEnd_1393773 : Nat := 79519496917675621158629

theorem tailTrace_1393773 : CollatzResearch.WordTrace tailWord_1393773 prefixEnd_1393773 79519496917675621158629 := by
  unfold tailWord_1393773
  simp only [CollatzResearch.WordTrace]
  refine ⟨50835077579605933322377973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33890051719737288881585315 50835077579605933322377973)
  ·
    refine ⟨4765788523088056248972935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50835077579605933322377973 4765788523088056248972935)
    ·
      refine ⟨7148682784632084373459403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4765788523088056248972935 7148682784632084373459403)
      ·
        refine ⟨10723024176948126560189105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148682784632084373459403 10723024176948126560189105)
        ·
          refine ⟨8042268132711094920141829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10723024176948126560189105 8042268132711094920141829)
          ·
            refine ⟨1507925274883330297526593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8042268132711094920141829 1507925274883330297526593)
            ·
              refine ⟨1130943956162497723144945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1507925274883330297526593 1130943956162497723144945)
              ·
                refine ⟨848207967121873292358709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1130943956162497723144945 848207967121873292358709)
                ·
                  refine ⟨79519496917675621158629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 848207967121873292358709 79519496917675621158629)
                  ·
                    rfl

theorem cell23_1393773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_1393773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393773 prefixEnd_1393773 := by exact prefixLift 1393773
  have htrace : WordTrace (prefixWord ++ tailWord_1393773) baseStart_1393773 baseEnd_1393773 := by
    simpa [prefixWord, tailWord_1393773, baseEnd_1393773] using wordTrace_append hprefix tailTrace_1393773
  have hstable : (prefixWord ++ tailWord_1393773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393773).length < 2 ^ (prefixWord ++ tailWord_1393773).sum := by decide
  have hdescent : baseEnd_1393773 < baseStart_1393773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393806 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1393806 : Nat := 118140960795 + 1393806 * 2 ^ 59
def prefixEnd_1393806 : Nat := 4983230072969 + 3 ^ 40 * 1393806 * 2
def baseEnd_1393806 : Nat := 715692417120678961315009

theorem tailTrace_1393806 : CollatzResearch.WordTrace tailWord_1393806 prefixEnd_1393806 715692417120678961315009 := by
  unfold tailWord_1393806
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354535148560797494791159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33890854125657586638886181 6354535148560797494791159)
  ·
    refine ⟨9531802722841196242186739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6354535148560797494791159 9531802722841196242186739)
    ·
      refine ⟨14297704084261794363280109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9531802722841196242186739 14297704084261794363280109)
      ·
        refine ⟨5361639031598172886230041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14297704084261794363280109 5361639031598172886230041)
        ·
          refine ⟨4021229273698629664672531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5361639031598172886230041 4021229273698629664672531)
          ·
            refine ⟨6031843910547944497008797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021229273698629664672531 6031843910547944497008797)
            ·
              refine ⟨2261941466455479186378299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6031843910547944497008797 2261941466455479186378299)
              ·
                refine ⟨3392912199683218779567449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261941466455479186378299 3392912199683218779567449)
                ·
                  refine ⟨2544684149762414084675587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3392912199683218779567449 2544684149762414084675587)
                  ·
                    refine ⟨3817026224643621127013381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2544684149762414084675587 3817026224643621127013381)
                    ·
                      refine ⟨715692417120678961315009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3817026224643621127013381 715692417120678961315009)
                      ·
                        rfl

theorem cell23_1393806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1393806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393806 prefixEnd_1393806 := by exact prefixLift 1393806
  have htrace : WordTrace (prefixWord ++ tailWord_1393806) baseStart_1393806 baseEnd_1393806 := by
    simpa [prefixWord, tailWord_1393806, baseEnd_1393806] using wordTrace_append hprefix tailTrace_1393806
  have hstable : (prefixWord ++ tailWord_1393806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393806).length < 2 ^ (prefixWord ++ tailWord_1393806).sum := by decide
  have hdescent : baseEnd_1393806 < baseStart_1393806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393829 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 6]
def baseStart_1393829 : Nat := 118140960795 + 1393829 * 2 ^ 59
def prefixEnd_1393829 : Nat := 4983230072969 + 3 ^ 40 * 1393829 * 2
def baseEnd_1393829 : Nat := 79522691908414707925267

theorem tailTrace_1393829 : CollatzResearch.WordTrace tailWord_1393829 prefixEnd_1393829 79522691908414707925267 := by
  unfold tailWord_1393829
  simp only [CollatzResearch.WordTrace]
  refine ⟨50837120067403054886416541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33891413378268703257611027 50837120067403054886416541)
  ·
    refine ⟨19063920025276145582406203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50837120067403054886416541 19063920025276145582406203)
    ·
      refine ⟨28595880037914218373609305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19063920025276145582406203 28595880037914218373609305)
      ·
        refine ⟨21446910028435663780206979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28595880037914218373609305 21446910028435663780206979)
        ·
          refine ⟨32170365042653495670310469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21446910028435663780206979 32170365042653495670310469)
          ·
            refine ⟨6031943445497530438183213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32170365042653495670310469 6031943445497530438183213)
            ·
              refine ⟨2261978792061573914318705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6031943445497530438183213 2261978792061573914318705)
              ·
                refine ⟨1696484094046180435739029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261978792061573914318705 1696484094046180435739029)
                ·
                  refine ⟨79522691908414707925267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1696484094046180435739029 79522691908414707925267)
                  ·
                    rfl

theorem cell23_1393829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_1393829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393829 prefixEnd_1393829 := by exact prefixLift 1393829
  have htrace : WordTrace (prefixWord ++ tailWord_1393829) baseStart_1393829 baseEnd_1393829 := by
    simpa [prefixWord, tailWord_1393829, baseEnd_1393829] using wordTrace_append hprefix tailTrace_1393829
  have hstable : (prefixWord ++ tailWord_1393829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393829).length < 2 ^ (prefixWord ++ tailWord_1393829).sum := by decide
  have hdescent : baseEnd_1393829 < baseStart_1393829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393866 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_1393866 : Nat := 118140960795 + 1393866 * 2 ^ 59
def prefixEnd_1393866 : Nat := 4983230072969 + 3 ^ 40 * 1393866 * 2
def baseEnd_1393866 : Nat := 715723225959948726564733

theorem tailTrace_1393866 : CollatzResearch.WordTrace tailWord_1393866 prefixEnd_1393866 715723225959948726564733 := by
  unfold tailWord_1393866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12709617392067252551378363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33892313045512673470342301 12709617392067252551378363)
  ·
    refine ⟨19064426088100878827067545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12709617392067252551378363 19064426088100878827067545)
    ·
      refine ⟨14298319566075659120300659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19064426088100878827067545 14298319566075659120300659)
      ·
        refine ⟨21447479349113488680450989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14298319566075659120300659 21447479349113488680450989)
        ·
          refine ⟨8042804755917558255169121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21447479349113488680450989 8042804755917558255169121)
          ·
            refine ⟨6032103566938168691376841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8042804755917558255169121 6032103566938168691376841)
            ·
              refine ⟨4524077675203626518532631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032103566938168691376841 4524077675203626518532631)
              ·
                refine ⟨6786116512805439777798947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524077675203626518532631 6786116512805439777798947)
                ·
                  refine ⟨10179174769208159666698421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786116512805439777798947 10179174769208159666698421)
                  ·
                    refine ⟨954297634613264968752977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10179174769208159666698421 954297634613264968752977)
                    ·
                      refine ⟨715723225959948726564733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954297634613264968752977 715723225959948726564733)
                      ·
                        rfl

theorem cell23_1393866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_1393866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393866 prefixEnd_1393866 := by exact prefixLift 1393866
  have htrace : WordTrace (prefixWord ++ tailWord_1393866) baseStart_1393866 baseEnd_1393866 := by
    simpa [prefixWord, tailWord_1393866, baseEnd_1393866] using wordTrace_append hprefix tailTrace_1393866
  have hstable : (prefixWord ++ tailWord_1393866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393866).length < 2 ^ (prefixWord ++ tailWord_1393866).sum := by decide
  have hdescent : baseEnd_1393866 < baseStart_1393866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393899 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5]
def baseStart_1393899 : Nat := 118140960795 + 1393899 * 2 ^ 59
def prefixEnd_1393899 : Nat := 4983230072969 + 3 ^ 40 * 1393899 * 2
def baseEnd_1393899 : Nat := 715740170821547097452081

theorem tailTrace_1393899 : CollatzResearch.WordTrace tailWord_1393899 prefixEnd_1393899 715740170821547097452081 := by
  unfold tailWord_1393899
  simp only [CollatzResearch.WordTrace]
  refine ⟨50839673177149456841464751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33893115451432971227643167 50839673177149456841464751)
  ·
    refine ⟨76259509765724185262197127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50839673177149456841464751 76259509765724185262197127)
    ·
      refine ⟨114389264648586277893295691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76259509765724185262197127 114389264648586277893295691)
      ·
        refine ⟨171583896972879416839943537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114389264648586277893295691 171583896972879416839943537)
        ·
          refine ⟨128687922729659562629957653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171583896972879416839943537 128687922729659562629957653)
          ·
            refine ⟨6032246377952791998279265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128687922729659562629957653 6032246377952791998279265)
            ·
              refine ⟨4524184783464593998709449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032246377952791998279265 4524184783464593998709449)
              ·
                refine ⟨3393138587598445499032087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4524184783464593998709449 3393138587598445499032087)
                ·
                  refine ⟨5089707881397668248548131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393138587598445499032087 5089707881397668248548131)
                  ·
                    refine ⟨7634561822096502372822197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5089707881397668248548131 7634561822096502372822197)
                    ·
                      refine ⟨715740170821547097452081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7634561822096502372822197 715740170821547097452081)
                      ·
                        rfl

theorem cell23_1393899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5].length) (baseStart_1393899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393899 prefixEnd_1393899 := by exact prefixLift 1393899
  have htrace : WordTrace (prefixWord ++ tailWord_1393899) baseStart_1393899 baseEnd_1393899 := by
    simpa [prefixWord, tailWord_1393899, baseEnd_1393899] using wordTrace_append hprefix tailTrace_1393899
  have hstable : (prefixWord ++ tailWord_1393899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393899).length < 2 ^ (prefixWord ++ tailWord_1393899).sum := by decide
  have hdescent : baseEnd_1393899 < baseStart_1393899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393930 : List Nat := [3, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2]
def baseStart_1393930 : Nat := 118140960795 + 1393930 * 2 ^ 59
def prefixEnd_1393930 : Nat := 4983230072969 + 3 ^ 40 * 1393930 * 2
def baseEnd_1393930 : Nat := 715756088721836476164439

theorem tailTrace_1393930 : CollatzResearch.WordTrace tailWord_1393930 prefixEnd_1393930 715756088721836476164439 := by
  unfold tailWord_1393930
  simp only [CollatzResearch.WordTrace]
  refine ⟨12710200960009287283960811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33893869226691432757228829 12710200960009287283960811)
  ·
    refine ⟨19065301440013930925941217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12710200960009287283960811 19065301440013930925941217)
    ·
      refine ⟨14298976080010448194455913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19065301440013930925941217 14298976080010448194455913)
      ·
        refine ⟨10724232060007836145841935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14298976080010448194455913 10724232060007836145841935)
        ·
          refine ⟨16086348090011754218762903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10724232060007836145841935 16086348090011754218762903)
          ·
            refine ⟨24129522135017631328144355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16086348090011754218762903 24129522135017631328144355)
            ·
              refine ⟨36194283202526446992216533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24129522135017631328144355 36194283202526446992216533)
              ·
                refine ⟨848303512559213601380075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36194283202526446992216533 848303512559213601380075)
                ·
                  refine ⟨1272455268838820402070113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848303512559213601380075 1272455268838820402070113)
                  ·
                    refine ⟨954341451629115301552585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1272455268838820402070113 954341451629115301552585)
                    ·
                      refine ⟨715756088721836476164439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954341451629115301552585 715756088721836476164439)
                      ·
                        rfl

theorem cell23_1393930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_1393930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393930 prefixEnd_1393930 := by exact prefixLift 1393930
  have htrace : WordTrace (prefixWord ++ tailWord_1393930) baseStart_1393930 baseEnd_1393930 := by
    simpa [prefixWord, tailWord_1393930, baseEnd_1393930] using wordTrace_append hprefix tailTrace_1393930
  have hstable : (prefixWord ++ tailWord_1393930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393930).length < 2 ^ (prefixWord ++ tailWord_1393930).sum := by decide
  have hdescent : baseEnd_1393930 < baseStart_1393930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393973 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_1393973 : Nat := 118140960795 + 1393973 * 2 ^ 59
def prefixEnd_1393973 : Nat := 4983230072969 + 3 ^ 40 * 1393973 * 2
def baseEnd_1393973 : Nat := 715778168389979807926741

theorem tailTrace_1393973 : CollatzResearch.WordTrace tailWord_1393973 prefixEnd_1393973 715778168389979807926741 := by
  unfold tailWord_1393973
  simp only [CollatzResearch.WordTrace]
  refine ⟨50842372178881367479658573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33894914785920911653105715 50842372178881367479658573)
  ·
    refine ⟨19065889567080512804871965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50842372178881367479658573 19065889567080512804871965)
    ·
      refine ⟨7149708587655192301826987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19065889567080512804871965 7149708587655192301826987)
      ·
        refine ⟨10724562881482788452740481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7149708587655192301826987 10724562881482788452740481)
        ·
          refine ⟨8043422161112091339555361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10724562881482788452740481 8043422161112091339555361)
          ·
            refine ⟨6032566620834068504666521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8043422161112091339555361 6032566620834068504666521)
            ·
              refine ⟨4524424965625551378499891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032566620834068504666521 4524424965625551378499891)
              ·
                refine ⟨6786637448438327067749837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524424965625551378499891 6786637448438327067749837)
                ·
                  refine ⟨2544989043164372650406189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6786637448438327067749837 2544989043164372650406189)
                  ·
                    refine ⟨954370891186639743902321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2544989043164372650406189 954370891186639743902321)
                    ·
                      refine ⟨715778168389979807926741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954370891186639743902321 715778168389979807926741)
                      ·
                        rfl

theorem cell23_1393973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_1393973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393973 prefixEnd_1393973 := by exact prefixLift 1393973
  have htrace : WordTrace (prefixWord ++ tailWord_1393973) baseStart_1393973 baseEnd_1393973 := by
    simpa [prefixWord, tailWord_1393973, baseEnd_1393973] using wordTrace_append hprefix tailTrace_1393973
  have hstable : (prefixWord ++ tailWord_1393973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393973).length < 2 ^ (prefixWord ++ tailWord_1393973).sum := by decide
  have hdescent : baseEnd_1393973 < baseStart_1393973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393989 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_1393989 : Nat := 118140960795 + 1393989 * 2 ^ 59
def prefixEnd_1393989 : Nat := 4983230072969 + 3 ^ 40 * 1393989 * 2
def baseEnd_1393989 : Nat := 715786384080451745326667

theorem tailTrace_1393989 : CollatzResearch.WordTrace tailWord_1393989 prefixEnd_1393989 715786384080451745326667 := by
  unfold tailWord_1393989
  simp only [CollatzResearch.WordTrace]
  refine ⟨50842955746823402212241021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33895303831215601474827347 50842955746823402212241021)
  ·
    refine ⟨19066108405058775829590383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50842955746823402212241021 19066108405058775829590383)
    ·
      refine ⟨28599162607588163744385575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19066108405058775829590383 28599162607588163744385575)
      ·
        refine ⟨42898743911382245616578363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28599162607588163744385575 42898743911382245616578363)
        ·
          refine ⟨64348115867073368424867545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42898743911382245616578363 64348115867073368424867545)
          ·
            refine ⟨48261086900305026318650659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64348115867073368424867545 48261086900305026318650659)
            ·
              refine ⟨72391630350457539477975989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48261086900305026318650659 72391630350457539477975989)
              ·
                refine ⟨6786715345355394326060249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72391630350457539477975989 6786715345355394326060249)
                ·
                  refine ⟨5090036509016545744545187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6786715345355394326060249 5090036509016545744545187)
                  ·
                    refine ⟨7635054763524818616817781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5090036509016545744545187 7635054763524818616817781)
                    ·
                      refine ⟨715786384080451745326667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7635054763524818616817781 715786384080451745326667)
                      ·
                        rfl

theorem cell23_1393989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_1393989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393989 prefixEnd_1393989 := by exact prefixLift 1393989
  have htrace : WordTrace (prefixWord ++ tailWord_1393989) baseStart_1393989 baseEnd_1393989 := by
    simpa [prefixWord, tailWord_1393989, baseEnd_1393989] using wordTrace_append hprefix tailTrace_1393989
  have hstable : (prefixWord ++ tailWord_1393989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393989).length < 2 ^ (prefixWord ++ tailWord_1393989).sum := by decide
  have hdescent : baseEnd_1393989 < baseStart_1393989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1393997 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1393997 : Nat := 118140960795 + 1393997 * 2 ^ 59
def prefixEnd_1393997 : Nat := 4983230072969 + 3 ^ 40 * 1393997 * 2
def baseEnd_1393997 : Nat := 715790491925687714026631

theorem tailTrace_1393997 : CollatzResearch.WordTrace tailWord_1393997 prefixEnd_1393997 715790491925687714026631 := by
  unfold tailWord_1393997
  simp only [CollatzResearch.WordTrace]
  refine ⟨50843247530794419578532245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33895498353862946385688163 50843247530794419578532245)
  ·
    refine ⟨2383277228005988417743699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50843247530794419578532245 2383277228005988417743699)
    ·
      refine ⟨3574915842008982626615549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383277228005988417743699 3574915842008982626615549)
      ·
        refine ⟨1340593440753368484980831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3574915842008982626615549 1340593440753368484980831)
        ·
          refine ⟨2010890161130052727471247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340593440753368484980831 2010890161130052727471247)
          ·
            refine ⟨3016335241695079091206871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010890161130052727471247 3016335241695079091206871)
            ·
              refine ⟨4524502862542618636810307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016335241695079091206871 4524502862542618636810307)
              ·
                refine ⟨6786754293813927955215461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524502862542618636810307 6786754293813927955215461)
                ·
                  refine ⟨1272516430090111491602899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6786754293813927955215461 1272516430090111491602899)
                  ·
                    refine ⟨1908774645135167237404349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1272516430090111491602899 1908774645135167237404349)
                    ·
                      refine ⟨715790491925687714026631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1908774645135167237404349 715790491925687714026631)
                      ·
                        rfl

theorem cell23_1393997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1393997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1393997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1393997 prefixEnd_1393997 := by exact prefixLift 1393997
  have htrace : WordTrace (prefixWord ++ tailWord_1393997) baseStart_1393997 baseEnd_1393997 := by
    simpa [prefixWord, tailWord_1393997, baseEnd_1393997] using wordTrace_append hprefix tailTrace_1393997
  have hstable : (prefixWord ++ tailWord_1393997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1393997).length < 2 ^ (prefixWord ++ tailWord_1393997).sum := by decide
  have hdescent : baseEnd_1393997 < baseStart_1393997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1393997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394003 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 4, 2, 2]
def baseStart_1394003 : Nat := 118140960795 + 1394003 * 2 ^ 59
def prefixEnd_1394003 : Nat := 4983230072969 + 3 ^ 40 * 1394003 * 2
def baseEnd_1394003 : Nat := 715793572809614690551603

theorem tailTrace_1394003 : CollatzResearch.WordTrace tailWord_1394003 prefixEnd_1394003 715793572809614690551603 := by
  unfold tailWord_1394003
  simp only [CollatzResearch.WordTrace]
  refine ⟨50843466368772682603250663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33895644245848455068833775 50843466368772682603250663)
  ·
    refine ⟨76265199553159023904875995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50843466368772682603250663 76265199553159023904875995)
    ·
      refine ⟨114397799329738535857313993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76265199553159023904875995 114397799329738535857313993)
      ·
        refine ⟨85798349497303901892985495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114397799329738535857313993 85798349497303901892985495)
        ·
          refine ⟨128697524245955852839478243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85798349497303901892985495 128697524245955852839478243)
          ·
            refine ⟨193046286368933779259217365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128697524245955852839478243 193046286368933779259217365)
            ·
              refine ⟨4524522336771885451387907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 193046286368933779259217365 4524522336771885451387907)
              ·
                refine ⟨6786783505157828177081861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524522336771885451387907 6786783505157828177081861)
                ·
                  refine ⟨1272521907217092783202849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6786783505157828177081861 1272521907217092783202849)
                  ·
                    refine ⟨954391430412819587402137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1272521907217092783202849 954391430412819587402137)
                    ·
                      refine ⟨715793572809614690551603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954391430412819587402137 715793572809614690551603)
                      ·
                        rfl

theorem cell23_1394003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 2, 2].length) (baseStart_1394003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394003 prefixEnd_1394003 := by exact prefixLift 1394003
  have htrace : WordTrace (prefixWord ++ tailWord_1394003) baseStart_1394003 baseEnd_1394003 := by
    simpa [prefixWord, tailWord_1394003, baseEnd_1394003] using wordTrace_append hprefix tailTrace_1394003
  have hstable : (prefixWord ++ tailWord_1394003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394003).length < 2 ^ (prefixWord ++ tailWord_1394003).sum := by decide
  have hdescent : baseEnd_1394003 < baseStart_1394003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394009 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 7]
def baseStart_1394009 : Nat := 118140960795 + 1394009 * 2 ^ 59
def prefixEnd_1394009 : Nat := 4983230072969 + 3 ^ 40 * 1394009 * 2
def baseEnd_1394009 : Nat := 79532961521504629675175

theorem tailTrace_1394009 : CollatzResearch.WordTrace tailWord_1394009 prefixEnd_1394009 79532961521504629675175 := by
  unfold tailWord_1394009
  simp only [CollatzResearch.WordTrace]
  refine ⟨50843685206750945627969081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33895790137833963751979387 50843685206750945627969081)
  ·
    refine ⟨38132763905063209220976811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50843685206750945627969081 38132763905063209220976811)
    ·
      refine ⟨57199145857594813831465217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38132763905063209220976811 57199145857594813831465217)
      ·
        refine ⟨42899359393196110373598913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57199145857594813831465217 42899359393196110373598913)
        ·
          refine ⟨32174519544897082780199185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42899359393196110373598913 32174519544897082780199185)
          ·
            refine ⟨24130889658672812085149389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32174519544897082780199185 24130889658672812085149389)
            ·
              refine ⟨9049083622002304531931021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24130889658672812085149389 9049083622002304531931021)
              ·
                refine ⟨3393406358250864199474133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9049083622002304531931021 3393406358250864199474133)
                ·
                  refine ⟨79532961521504629675175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3393406358250864199474133 79532961521504629675175)
                  ·
                    rfl

theorem cell23_1394009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_1394009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394009 prefixEnd_1394009 := by exact prefixLift 1394009
  have htrace : WordTrace (prefixWord ++ tailWord_1394009) baseStart_1394009 baseEnd_1394009 := by
    simpa [prefixWord, tailWord_1394009, baseEnd_1394009] using wordTrace_append hprefix tailTrace_1394009
  have hstable : (prefixWord ++ tailWord_1394009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394009).length < 2 ^ (prefixWord ++ tailWord_1394009).sum := by decide
  have hdescent : baseEnd_1394009 < baseStart_1394009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394016 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1394016 : Nat := 118140960795 + 1394016 * 2 ^ 59
def prefixEnd_1394016 : Nat := 4983230072969 + 3 ^ 40 * 1394016 * 2
def baseEnd_1394016 : Nat := 715800248058123139689043

theorem tailTrace_1394016 : CollatzResearch.WordTrace tailWord_1394016 prefixEnd_1394016 715800248058123139689043 := by
  unfold tailWord_1394016
  simp only [CollatzResearch.WordTrace]
  refine ⟨25421970258862792911736951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33895960345150390548982601 25421970258862792911736951)
  ·
    refine ⟨38132955388294189367605427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25421970258862792911736951 38132955388294189367605427)
    ·
      refine ⟨57199433082441284051408141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38132955388294189367605427 57199433082441284051408141)
      ·
        refine ⟨21449787405915481519278053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57199433082441284051408141 21449787405915481519278053)
        ·
          refine ⟨4021835138609152784864635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21449787405915481519278053 4021835138609152784864635)
          ·
            refine ⟨6032752707913729177296953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021835138609152784864635 6032752707913729177296953)
            ·
              refine ⟨4524564530935296882972715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032752707913729177296953 4524564530935296882972715)
              ·
                refine ⟨6786846796402945324459073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524564530935296882972715 6786846796402945324459073)
                ·
                  refine ⟨5090135097302208993344305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6786846796402945324459073 5090135097302208993344305)
                  ·
                    refine ⟨3817601322976656745008229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5090135097302208993344305 3817601322976656745008229)
                    ·
                      refine ⟨715800248058123139689043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3817601322976656745008229 715800248058123139689043)
                      ·
                        rfl

theorem cell23_1394016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1394016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394016 prefixEnd_1394016 := by exact prefixLift 1394016
  have htrace : WordTrace (prefixWord ++ tailWord_1394016) baseStart_1394016 baseEnd_1394016 := by
    simpa [prefixWord, tailWord_1394016, baseEnd_1394016] using wordTrace_append hprefix tailTrace_1394016
  have hstable : (prefixWord ++ tailWord_1394016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394016).length < 2 ^ (prefixWord ++ tailWord_1394016).sum := by decide
  have hdescent : baseEnd_1394016 < baseStart_1394016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394020 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_1394020 : Nat := 118140960795 + 1394020 * 2 ^ 59
def prefixEnd_1394020 : Nat := 4983230072969 + 3 ^ 40 * 1394020 * 2
def baseEnd_1394020 : Nat := 715802301980741124039025

theorem tailTrace_1394020 : CollatzResearch.WordTrace tailWord_1394020 prefixEnd_1394020 715802301980741124039025 := by
  unfold tailWord_1394020
  simp only [CollatzResearch.WordTrace]
  refine ⟨25422043204855547253309757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33896057606474063004413009 25422043204855547253309757)
  ·
    refine ⟨9533266201820830219991159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25422043204855547253309757 9533266201820830219991159)
    ·
      refine ⟨14299899302731245329986739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9533266201820830219991159 14299899302731245329986739)
      ·
        refine ⟨21449848954096867994980109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14299899302731245329986739 21449848954096867994980109)
        ·
          refine ⟨8043693357786325498117541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21449848954096867994980109 8043693357786325498117541)
          ·
            refine ⟨1508192504584936030897039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8043693357786325498117541 1508192504584936030897039)
            ·
              refine ⟨2262288756877404046345559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508192504584936030897039 2262288756877404046345559)
              ·
                refine ⟨3393433135316106069518339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262288756877404046345559 3393433135316106069518339)
                ·
                  refine ⟨5090149702974159104277509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393433135316106069518339 5090149702974159104277509)
                  ·
                    refine ⟨954403069307654832052033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5090149702974159104277509 954403069307654832052033)
                    ·
                      refine ⟨715802301980741124039025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954403069307654832052033 715802301980741124039025)
                      ·
                        rfl

theorem cell23_1394020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_1394020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394020 prefixEnd_1394020 := by exact prefixLift 1394020
  have htrace : WordTrace (prefixWord ++ tailWord_1394020) baseStart_1394020 baseEnd_1394020 := by
    simpa [prefixWord, tailWord_1394020, baseEnd_1394020] using wordTrace_append hprefix tailTrace_1394020
  have hstable : (prefixWord ++ tailWord_1394020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394020).length < 2 ^ (prefixWord ++ tailWord_1394020).sum := by decide
  have hdescent : baseEnd_1394020 < baseStart_1394020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394039 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 1, 7]
def baseStart_1394039 : Nat := 118140960795 + 1394039 * 2 ^ 59
def prefixEnd_1394039 : Nat := 4983230072969 + 3 ^ 40 * 1394039 * 2
def baseEnd_1394039 : Nat := 238604019371058849900479

theorem tailTrace_1394039 : CollatzResearch.WordTrace tailWord_1394039 prefixEnd_1394039 238604019371058849900479 := by
  unfold tailWord_1394039
  simp only [CollatzResearch.WordTrace]
  refine ⟨50844779396642260751561171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33896519597761507167707447 50844779396642260751561171)
  ·
    refine ⟨76267169094963391127341757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50844779396642260751561171 76267169094963391127341757)
    ·
      refine ⟨28600188410611271672753159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76267169094963391127341757 28600188410611271672753159)
      ·
        refine ⟨42900282615916907509129739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28600188410611271672753159 42900282615916907509129739)
        ·
          refine ⟨64350423923875361263694609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42900282615916907509129739 64350423923875361263694609)
          ·
            refine ⟨48262817942906520947770957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64350423923875361263694609 48262817942906520947770957)
            ·
              refine ⟨18098556728589945355414109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48262817942906520947770957 18098556728589945355414109)
              ·
                refine ⟨6786958773221229508280291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18098556728589945355414109 6786958773221229508280291)
                ·
                  refine ⟨10180438159831844262420437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786958773221229508280291 10180438159831844262420437)
                  ·
                    refine ⟨238604019371058849900479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10180438159831844262420437 238604019371058849900479)
                    ·
                      rfl

theorem cell23_1394039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_1394039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394039 prefixEnd_1394039 := by exact prefixLift 1394039
  have htrace : WordTrace (prefixWord ++ tailWord_1394039) baseStart_1394039 baseEnd_1394039 := by
    simpa [prefixWord, tailWord_1394039, baseEnd_1394039] using wordTrace_append hprefix tailTrace_1394039
  have hstable : (prefixWord ++ tailWord_1394039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394039).length < 2 ^ (prefixWord ++ tailWord_1394039).sum := by decide
  have hdescent : baseEnd_1394039 < baseStart_1394039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394056 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 4, 5]
def baseStart_1394056 : Nat := 118140960795 + 1394056 * 2 ^ 59
def prefixEnd_1394056 : Nat := 4983230072969 + 3 ^ 40 * 1394056 * 2
def baseEnd_1394056 : Nat := 238606929094767661062953

theorem tailTrace_1394056 : CollatzResearch.WordTrace tailWord_1394056 prefixEnd_1394056 238606929094767661062953 := by
  unfold tailWord_1394056
  simp only [CollatzResearch.WordTrace]
  refine ⟨25422699718790336327465011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33896932958387115103286681 25422699718790336327465011)
  ·
    refine ⟨38134049578185504491197517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25422699718790336327465011 38134049578185504491197517)
    ·
      refine ⟨14300268591819564184199069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38134049578185504491197517 14300268591819564184199069)
      ·
        refine ⟨5362600721932336569074651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14300268591819564184199069 5362600721932336569074651)
        ·
          refine ⟨8043901082898504853611977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362600721932336569074651 8043901082898504853611977)
          ·
            refine ⟨6032925812173878640208983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8043901082898504853611977 6032925812173878640208983)
            ·
              refine ⟨9049388718260817960313475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032925812173878640208983 9049388718260817960313475)
              ·
                refine ⟨13574083077391226940470213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049388718260817960313475 13574083077391226940470213)
                ·
                  refine ⟨2545140577010855051338165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13574083077391226940470213 2545140577010855051338165)
                  ·
                    refine ⟨238606929094767661062953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2545140577010855051338165 238606929094767661062953)
                    ·
                      rfl

theorem cell23_1394056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_1394056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394056 prefixEnd_1394056 := by exact prefixLift 1394056
  have htrace : WordTrace (prefixWord ++ tailWord_1394056) baseStart_1394056 baseEnd_1394056 := by
    simpa [prefixWord, tailWord_1394056, baseEnd_1394056] using wordTrace_append hprefix tailTrace_1394056
  have hstable : (prefixWord ++ tailWord_1394056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394056).length < 2 ^ (prefixWord ++ tailWord_1394056).sum := by decide
  have hdescent : baseEnd_1394056 < baseStart_1394056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394089 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_1394089 : Nat := 118140960795 + 1394089 * 2 ^ 59
def prefixEnd_1394089 : Nat := 4983230072969 + 3 ^ 40 * 1394089 * 2
def baseEnd_1394089 : Nat := 715837732145901354076207

theorem tailTrace_1394089 : CollatzResearch.WordTrace tailWord_1394089 prefixEnd_1394089 715837732145901354076207 := by
  unfold tailWord_1394089
  simp only [CollatzResearch.WordTrace]
  refine ⟨50846603046461119290881321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33897735364307412860587547 50846603046461119290881321)
  ·
    refine ⟨38134952284845839468160991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50846603046461119290881321 38134952284845839468160991)
    ·
      refine ⟨57202428427268759202241487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38134952284845839468160991 57202428427268759202241487)
      ·
        refine ⟨85803642640903138803362231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57202428427268759202241487 85803642640903138803362231)
        ·
          refine ⟨128705463961354708205043347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85803642640903138803362231 128705463961354708205043347)
          ·
            refine ⟨193058195942032062307565021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128705463961354708205043347 193058195942032062307565021)
            ·
              refine ⟨72396823478262023365336883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193058195942032062307565021 72396823478262023365336883)
              ·
                refine ⟨108595235217393035048005325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72396823478262023365336883 108595235217393035048005325)
                ·
                  refine ⟨40723213206522388143001997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108595235217393035048005325 40723213206522388143001997)
                  ·
                    refine ⟨15271204952445895553625749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40723213206522388143001997 15271204952445895553625749)
                    ·
                      refine ⟨715837732145901354076207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15271204952445895553625749 715837732145901354076207)
                      ·
                        rfl

theorem cell23_1394089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_1394089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394089 prefixEnd_1394089 := by exact prefixLift 1394089
  have htrace : WordTrace (prefixWord ++ tailWord_1394089) baseStart_1394089 baseEnd_1394089 := by
    simpa [prefixWord, tailWord_1394089, baseEnd_1394089] using wordTrace_append hprefix tailTrace_1394089
  have hstable : (prefixWord ++ tailWord_1394089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394089).length < 2 ^ (prefixWord ++ tailWord_1394089).sum := by decide
  have hdescent : baseEnd_1394089 < baseStart_1394089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394099 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 10]
def baseStart_1394099 : Nat := 118140960795 + 1394099 * 2 ^ 59
def prefixEnd_1394099 : Nat := 4983230072969 + 3 ^ 40 * 1394099 * 2
def baseEnd_1394099 : Nat := 79538096328049590550129

theorem tailTrace_1394099 : CollatzResearch.WordTrace tailWord_1394099 prefixEnd_1394099 79538096328049590550129 := by
  unfold tailWord_1394099
  simp only [CollatzResearch.WordTrace]
  refine ⟨50846967776424890998745351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33897978517616593999163567 50846967776424890998745351)
  ·
    refine ⟨76270451664637336498118027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50846967776424890998745351 76270451664637336498118027)
    ·
      refine ⟨114405677496956004747177041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76270451664637336498118027 114405677496956004747177041)
      ·
        refine ⟨85804258122717003560382781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114405677496956004747177041 85804258122717003560382781)
        ·
          refine ⟨32176596796018876335143543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85804258122717003560382781 32176596796018876335143543)
          ·
            refine ⟨48264895194028314502715315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32176596796018876335143543 48264895194028314502715315)
            ·
              refine ⟨72397342791042471754072973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48264895194028314502715315 72397342791042471754072973)
              ·
                refine ⟨27149003546640926907777365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72397342791042471754072973 27149003546640926907777365)
                ·
                  refine ⟨79538096328049590550129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 27149003546640926907777365 79538096328049590550129)
                  ·
                    rfl

theorem cell23_1394099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 10].length) (baseStart_1394099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394099 prefixEnd_1394099 := by exact prefixLift 1394099
  have htrace : WordTrace (prefixWord ++ tailWord_1394099) baseStart_1394099 baseEnd_1394099 := by
    simpa [prefixWord, tailWord_1394099, baseEnd_1394099] using wordTrace_append hprefix tailTrace_1394099
  have hstable : (prefixWord ++ tailWord_1394099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394099).length < 2 ^ (prefixWord ++ tailWord_1394099).sum := by decide
  have hdescent : baseEnd_1394099 < baseStart_1394099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394120 : List Nat := [2, 1, 3, 1, 3, 1, 3, 4, 1, 4]
def baseStart_1394120 : Nat := 118140960795 + 1394120 * 2 ^ 59
def prefixEnd_1394120 : Nat := 4983230072969 + 3 ^ 40 * 1394120 * 2
def baseEnd_1394120 : Nat := 238617883348730244262855

theorem tailTrace_1394120 : CollatzResearch.WordTrace tailWord_1394120 prefixEnd_1394120 238617883348730244262855 := by
  unfold tailWord_1394120
  simp only [CollatzResearch.WordTrace]
  refine ⟨25423866854674405792629907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33898489139565874390173209 25423866854674405792629907)
  ·
    refine ⟨38135800282011608688944861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25423866854674405792629907 38135800282011608688944861)
    ·
      refine ⟨14300925105754353258354323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38135800282011608688944861 14300925105754353258354323)
      ·
        refine ⟨21451387658631529887531485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14300925105754353258354323 21451387658631529887531485)
        ·
          refine ⟨8044270371986823707824307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21451387658631529887531485 8044270371986823707824307)
          ·
            refine ⟨12066405557980235561736461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044270371986823707824307 12066405557980235561736461)
            ·
              refine ⟨4524902084242588335651173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12066405557980235561736461 4524902084242588335651173)
              ·
                refine ⟨848419140795485312934595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4524902084242588335651173 848419140795485312934595)
                ·
                  refine ⟨1272628711193227969401893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848419140795485312934595 1272628711193227969401893)
                  ·
                    refine ⟨238617883348730244262855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1272628711193227969401893 238617883348730244262855)
                    ·
                      rfl

theorem cell23_1394120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_1394120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394120 prefixEnd_1394120 := by exact prefixLift 1394120
  have htrace : WordTrace (prefixWord ++ tailWord_1394120) baseStart_1394120 baseEnd_1394120 := by
    simpa [prefixWord, tailWord_1394120, baseEnd_1394120] using wordTrace_append hprefix tailTrace_1394120
  have hstable : (prefixWord ++ tailWord_1394120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394120).length < 2 ^ (prefixWord ++ tailWord_1394120).sum := by decide
  have hdescent : baseEnd_1394120 < baseStart_1394120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394177 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1394177 : Nat := 118140960795 + 1394177 * 2 ^ 59
def prefixEnd_1394177 : Nat := 4983230072969 + 3 ^ 40 * 1394177 * 2
def baseEnd_1394177 : Nat := 715882918443497009775803

theorem tailTrace_1394177 : CollatzResearch.WordTrace tailWord_1394177 prefixEnd_1394177 715882918443497009775803 := by
  unfold tailWord_1394177
  simp only [CollatzResearch.WordTrace]
  refine ⟨50849812670142310320084785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33899875113428206880056523 50849812670142310320084785)
  ·
    refine ⟨38137359502606732740063589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50849812670142310320084785 38137359502606732740063589)
    ·
      refine ⟨7150754906738762388761923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38137359502606732740063589 7150754906738762388761923)
      ·
        refine ⟨10726132360108143583142885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7150754906738762388761923 10726132360108143583142885)
        ·
          refine ⟨2011149817520276921839291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10726132360108143583142885 2011149817520276921839291)
          ·
            refine ⟨3016724726280415382758937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011149817520276921839291 3016724726280415382758937)
            ·
              refine ⟨2262543544710311537069203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3016724726280415382758937 2262543544710311537069203)
              ·
                refine ⟨3393815317065467305603805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262543544710311537069203 3393815317065467305603805)
                ·
                  refine ⟨1272680743899550239601427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3393815317065467305603805 1272680743899550239601427)
                  ·
                    refine ⟨1909021115849325359402141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1272680743899550239601427 1909021115849325359402141)
                    ·
                      refine ⟨715882918443497009775803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909021115849325359402141 715882918443497009775803)
                      ·
                        rfl

theorem cell23_1394177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1394177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394177 prefixEnd_1394177 := by exact prefixLift 1394177
  have htrace : WordTrace (prefixWord ++ tailWord_1394177) baseStart_1394177 baseEnd_1394177 := by
    simpa [prefixWord, tailWord_1394177, baseEnd_1394177] using wordTrace_append hprefix tailTrace_1394177
  have hstable : (prefixWord ++ tailWord_1394177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394177).length < 2 ^ (prefixWord ++ tailWord_1394177).sum := by decide
  have hdescent : baseEnd_1394177 < baseStart_1394177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394211 : List Nat := [1, 1, 1, 4, 6, 1, 1, 3, 1, 1, 3]
def baseStart_1394211 : Nat := 118140960795 + 1394211 * 2 ^ 59
def prefixEnd_1394211 : Nat := 4983230072969 + 3 ^ 40 * 1394211 * 2
def baseEnd_1394211 : Nat := 715900376785749876750647

theorem tailTrace_1394211 : CollatzResearch.WordTrace tailWord_1394211 prefixEnd_1394211 715900376785749876750647 := by
  unfold tailWord_1394211
  simp only [CollatzResearch.WordTrace]
  refine ⟨50851052752019134126822487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33900701834679422751214991 50851052752019134126822487)
  ·
    refine ⟨76276579128028701190233731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50851052752019134126822487 76276579128028701190233731)
    ·
      refine ⟨114414868692043051785350597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76276579128028701190233731 114414868692043051785350597)
      ·
        refine ⟨21452787879758072209753237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114414868692043051785350597 21452787879758072209753237)
        ·
          refine ⟨1005599431863659634832183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21452787879758072209753237 1005599431863659634832183)
          ·
            refine ⟨1508399147795489452248275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005599431863659634832183 1508399147795489452248275)
            ·
              refine ⟨2262598721693234178372413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508399147795489452248275 2262598721693234178372413)
              ·
                refine ⟨848474520634962816889655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2262598721693234178372413 848474520634962816889655)
                ·
                  refine ⟨1272711780952444225334483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848474520634962816889655 1272711780952444225334483)
                  ·
                    refine ⟨1909067671428666338001725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1272711780952444225334483 1909067671428666338001725)
                    ·
                      refine ⟨715900376785749876750647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909067671428666338001725 715900376785749876750647)
                      ·
                        rfl

theorem cell23_1394211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_1394211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394211 prefixEnd_1394211 := by exact prefixLift 1394211
  have htrace : WordTrace (prefixWord ++ tailWord_1394211) baseStart_1394211 baseEnd_1394211 := by
    simpa [prefixWord, tailWord_1394211, baseEnd_1394211] using wordTrace_append hprefix tailTrace_1394211
  have hstable : (prefixWord ++ tailWord_1394211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394211).length < 2 ^ (prefixWord ++ tailWord_1394211).sum := by decide
  have hdescent : baseEnd_1394211 < baseStart_1394211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394243 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 1, 9, 2]
def baseStart_1394243 : Nat := 118140960795 + 1394243 * 2 ^ 59
def prefixEnd_1394243 : Nat := 4983230072969 + 3 ^ 40 * 1394243 * 2
def baseEnd_1394243 : Nat := 715916808166693751550499

theorem tailTrace_1394243 : CollatzResearch.WordTrace tailWord_1394243 prefixEnd_1394243 715916808166693751550499 := by
  unfold tailWord_1394243
  simp only [CollatzResearch.WordTrace]
  refine ⟨50852219887903203591987383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33901479925268802394658255 50852219887903203591987383)
  ·
    refine ⟨76278329831854805387981075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50852219887903203591987383 76278329831854805387981075)
    ·
      refine ⟨114417494747782208081971613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76278329831854805387981075 114417494747782208081971613)
      ·
        refine ⟨42906560530418328030739355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114417494747782208081971613 42906560530418328030739355)
        ·
          refine ⟨64359840795627492046109033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42906560530418328030739355 64359840795627492046109033)
          ·
            refine ⟨48269880596720619034581775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64359840795627492046109033 48269880596720619034581775)
            ·
              refine ⟨72404820895080928551872663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48269880596720619034581775 72404820895080928551872663)
              ·
                refine ⟨108607231342621392827808995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72404820895080928551872663 108607231342621392827808995)
                ·
                  refine ⟨162910847013932089241713493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108607231342621392827808995 162910847013932089241713493)
                  ·
                    refine ⟨954555744222258335400665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162910847013932089241713493 954555744222258335400665)
                    ·
                      refine ⟨715916808166693751550499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954555744222258335400665 715916808166693751550499)
                      ·
                        rfl

theorem cell23_1394243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_1394243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394243 prefixEnd_1394243 := by exact prefixLift 1394243
  have htrace : WordTrace (prefixWord ++ tailWord_1394243) baseStart_1394243 baseEnd_1394243 := by
    simpa [prefixWord, tailWord_1394243, baseEnd_1394243] using wordTrace_append hprefix tailTrace_1394243
  have hstable : (prefixWord ++ tailWord_1394243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394243).length < 2 ^ (prefixWord ++ tailWord_1394243).sum := by decide
  have hdescent : baseEnd_1394243 < baseStart_1394243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394285 : List Nat := [1, 5, 1, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_1394285 : Nat := 118140960795 + 1394285 * 2 ^ 59
def prefixEnd_1394285 : Nat := 4983230072969 + 3 ^ 40 * 1394285 * 2
def baseEnd_1394285 : Nat := 715938374354182587225307

theorem tailTrace_1394285 : CollatzResearch.WordTrace tailWord_1394285 prefixEnd_1394285 715938374354182587225307 := by
  unfold tailWord_1394285
  simp only [CollatzResearch.WordTrace]
  refine ⟨50853751753751044765016309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33902501169167363176677539 50853751753751044765016309)
  ·
    refine ⟨4767539226914160446720279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50853751753751044765016309 4767539226914160446720279)
    ·
      refine ⟨7151308840371240670080419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4767539226914160446720279 7151308840371240670080419)
      ·
        refine ⟨10726963260556861005120629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7151308840371240670080419 10726963260556861005120629)
        ·
          refine ⟨1005652805677205719230059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10726963260556861005120629 1005652805677205719230059)
          ·
            refine ⟨1508479208515808578845089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005652805677205719230059 1508479208515808578845089)
            ·
              refine ⟨1131359406386856434133817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508479208515808578845089 1131359406386856434133817)
              ·
                refine ⟨848519554790142325600363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131359406386856434133817 848519554790142325600363)
                ·
                  refine ⟨1272779332185213488400545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848519554790142325600363 1272779332185213488400545)
                  ·
                    refine ⟨954584499138910116300409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1272779332185213488400545 954584499138910116300409)
                    ·
                      refine ⟨715938374354182587225307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954584499138910116300409 715938374354182587225307)
                      ·
                        rfl

theorem cell23_1394285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_1394285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394285 prefixEnd_1394285 := by exact prefixLift 1394285
  have htrace : WordTrace (prefixWord ++ tailWord_1394285) baseStart_1394285 baseEnd_1394285 := by
    simpa [prefixWord, tailWord_1394285, baseEnd_1394285] using wordTrace_append hprefix tailTrace_1394285
  have hstable : (prefixWord ++ tailWord_1394285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394285).length < 2 ^ (prefixWord ++ tailWord_1394285).sum := by decide
  have hdescent : baseEnd_1394285 < baseStart_1394285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394323 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 3]
def baseStart_1394323 : Nat := 118140960795 + 1394323 * 2 ^ 59
def prefixEnd_1394323 : Nat := 4983230072969 + 3 ^ 40 * 1394323 * 2
def baseEnd_1394323 : Nat := 715957886619053438550131

theorem tailTrace_1394323 : CollatzResearch.WordTrace tailWord_1394323 prefixEnd_1394323 715957886619053438550131 := by
  unfold tailWord_1394323
  simp only [CollatzResearch.WordTrace]
  refine ⟨50855137727613377254899623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33903425151742251503266415 50855137727613377254899623)
  ·
    refine ⟨76282706591420065882349435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50855137727613377254899623 76282706591420065882349435)
    ·
      refine ⟨114424059887130098823524153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76282706591420065882349435 114424059887130098823524153)
      ·
        refine ⟨85818044915347574117643115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114424059887130098823524153 85818044915347574117643115)
        ·
          refine ⟨128727067373021361176464673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85818044915347574117643115 128727067373021361176464673)
          ·
            refine ⟨96545300529766020882348505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128727067373021361176464673 96545300529766020882348505)
            ·
              refine ⟨72408975397324515661761379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96545300529766020882348505 72408975397324515661761379)
              ·
                refine ⟨108613463095986773492642069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72408975397324515661761379 108613463095986773492642069)
                ·
                  refine ⟨5091256082624380007467597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108613463095986773492642069 5091256082624380007467597)
                  ·
                    refine ⟨1909221030984142502800349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5091256082624380007467597 1909221030984142502800349)
                    ·
                      refine ⟨715957886619053438550131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909221030984142502800349 715957886619053438550131)
                      ·
                        rfl

theorem cell23_1394323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_1394323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394323 prefixEnd_1394323 := by exact prefixLift 1394323
  have htrace : WordTrace (prefixWord ++ tailWord_1394323) baseStart_1394323 baseEnd_1394323 := by
    simpa [prefixWord, tailWord_1394323, baseEnd_1394323] using wordTrace_append hprefix tailTrace_1394323
  have hstable : (prefixWord ++ tailWord_1394323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394323).length < 2 ^ (prefixWord ++ tailWord_1394323).sum := by decide
  have hdescent : baseEnd_1394323 < baseStart_1394323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394340 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_1394340 : Nat := 118140960795 + 1394340 * 2 ^ 59
def prefixEnd_1394340 : Nat := 4983230072969 + 3 ^ 40 * 1394340 * 2
def baseEnd_1394340 : Nat := 715966615790179872037553

theorem tailTrace_1394340 : CollatzResearch.WordTrace tailWord_1394340 prefixEnd_1394340 715966615790179872037553 := by
  unfold tailWord_1394340
  simp only [CollatzResearch.WordTrace]
  refine ⟨25427878884275894579134237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33903838512367859438845649 25427878884275894579134237)
  ·
    refine ⟨9535454581603460467175339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25427878884275894579134237 9535454581603460467175339)
    ·
      refine ⟨14303181872405190700763009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9535454581603460467175339 14303181872405190700763009)
      ·
        refine ⟨10727386404303893025572257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14303181872405190700763009 10727386404303893025572257)
        ·
          refine ⟨8045539803227919769179193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10727386404303893025572257 8045539803227919769179193)
          ·
            refine ⟨6034154852420939826884395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045539803227919769179193 6034154852420939826884395)
            ·
              refine ⟨9051232278631409740326593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034154852420939826884395 9051232278631409740326593)
              ·
                refine ⟨6788424208973557305244945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9051232278631409740326593 6788424208973557305244945)
                ·
                  refine ⟨5091318156730167978933709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6788424208973557305244945 5091318156730167978933709)
                  ·
                    refine ⟨1909244308773812992100141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5091318156730167978933709 1909244308773812992100141)
                    ·
                      refine ⟨715966615790179872037553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909244308773812992100141 715966615790179872037553)
                      ·
                        rfl

theorem cell23_1394340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_1394340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394340 prefixEnd_1394340 := by exact prefixLift 1394340
  have htrace : WordTrace (prefixWord ++ tailWord_1394340) baseStart_1394340 baseEnd_1394340 := by
    simpa [prefixWord, tailWord_1394340, baseEnd_1394340] using wordTrace_append hprefix tailTrace_1394340
  have hstable : (prefixWord ++ tailWord_1394340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394340).length < 2 ^ (prefixWord ++ tailWord_1394340).sum := by decide
  have hdescent : baseEnd_1394340 < baseStart_1394340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394381 : List Nat := [1, 6, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1394381 : Nat := 118140960795 + 1394381 * 2 ^ 59
def prefixEnd_1394381 : Nat := 4983230072969 + 3 ^ 40 * 1394381 * 2
def baseEnd_1394381 : Nat := 79554185388557134624985

theorem tailTrace_1394381 : CollatzResearch.WordTrace tailWord_1394381 prefixEnd_1394381 79554185388557134624985 := by
  unfold tailWord_1394381
  simp only [CollatzResearch.WordTrace]
  refine ⟨50857253161403253160510997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33904835440935502107007331 50857253161403253160510997)
  ·
    refine ⟨2383933741940777491898953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50857253161403253160510997 2383933741940777491898953)
    ·
      refine ⟨1787950306455583118924215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2383933741940777491898953 1787950306455583118924215)
      ·
        refine ⟨2681925459683374678386323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787950306455583118924215 2681925459683374678386323)
        ·
          refine ⟨4022888189525062017579485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681925459683374678386323 4022888189525062017579485)
          ·
            refine ⟨1508583071071898256592307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4022888189525062017579485 1508583071071898256592307)
            ·
              refine ⟨2262874606607847384888461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508583071071898256592307 2262874606607847384888461)
              ·
                refine ⟨848577977477942769333173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2262874606607847384888461 848577977477942769333173)
                ·
                  refine ⟨79554185388557134624985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 848577977477942769333173 79554185388557134624985)
                  ·
                    rfl

theorem cell23_1394381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1394381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394381 prefixEnd_1394381 := by exact prefixLift 1394381
  have htrace : WordTrace (prefixWord ++ tailWord_1394381) baseStart_1394381 baseEnd_1394381 := by
    simpa [prefixWord, tailWord_1394381, baseEnd_1394381] using wordTrace_append hprefix tailTrace_1394381
  have hstable : (prefixWord ++ tailWord_1394381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394381).length < 2 ^ (prefixWord ++ tailWord_1394381).sum := by decide
  have hdescent : baseEnd_1394381 < baseStart_1394381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394400 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3]
def baseStart_1394400 : Nat := 118140960795 + 1394400 * 2 ^ 59
def prefixEnd_1394400 : Nat := 4983230072969 + 3 ^ 40 * 1394400 * 2
def baseEnd_1394400 : Nat := 715997424629449637287277

theorem tailTrace_1394400 : CollatzResearch.WordTrace tailWord_1394400 prefixEnd_1394400 715997424629449637287277 := by
  unfold tailWord_1394400
  simp only [CollatzResearch.WordTrace]
  refine ⟨25428973074167209702726327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33905297432222946270301769 25428973074167209702726327)
  ·
    refine ⟨38143459611250814554089491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25428973074167209702726327 38143459611250814554089491)
    ·
      refine ⟨57215189416876221831134237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38143459611250814554089491 57215189416876221831134237)
      ·
        refine ⟨21455696031328583186675339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57215189416876221831134237 21455696031328583186675339)
        ·
          refine ⟨32183544046992874780013009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21455696031328583186675339 32183544046992874780013009)
          ·
            refine ⟨24137658035244656085009757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32183544046992874780013009 24137658035244656085009757)
            ·
              refine ⟨9051621763216746031878659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24137658035244656085009757 9051621763216746031878659)
              ·
                refine ⟨13577432644825119047817989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9051621763216746031878659 13577432644825119047817989)
                ·
                  refine ⟨2545768620904709821465873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13577432644825119047817989 2545768620904709821465873)
                  ·
                    refine ⟨1909326465678532366099405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545768620904709821465873 1909326465678532366099405)
                    ·
                      refine ⟨715997424629449637287277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909326465678532366099405 715997424629449637287277)
                      ·
                        rfl

theorem cell23_1394400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_1394400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394400 prefixEnd_1394400 := by exact prefixLift 1394400
  have htrace : WordTrace (prefixWord ++ tailWord_1394400) baseStart_1394400 baseEnd_1394400 := by
    simpa [prefixWord, tailWord_1394400, baseEnd_1394400] using wordTrace_append hprefix tailTrace_1394400
  have hstable : (prefixWord ++ tailWord_1394400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394400).length < 2 ^ (prefixWord ++ tailWord_1394400).sum := by decide
  have hdescent : baseEnd_1394400 < baseStart_1394400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394423 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_1394423 : Nat := 118140960795 + 1394423 * 2 ^ 59
def prefixEnd_1394423 : Nat := 4983230072969 + 3 ^ 40 * 1394423 * 2
def baseEnd_1394423 : Nat := 716009234684503047299671

theorem tailTrace_1394423 : CollatzResearch.WordTrace tailWord_1394423 prefixEnd_1394423 716009234684503047299671 := by
  unfold tailWord_1394423
  simp only [CollatzResearch.WordTrace]
  refine ⟨50858785027251094333539923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33905856684834062889026615 50858785027251094333539923)
  ·
    refine ⟨76288177540876641500309885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50858785027251094333539923 76288177540876641500309885)
    ·
      refine ⟨28608066577828740562616207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76288177540876641500309885 28608066577828740562616207)
      ·
        refine ⟨42912099866743110843924311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28608066577828740562616207 42912099866743110843924311)
        ·
          refine ⟨64368149800114666265886467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42912099866743110843924311 64368149800114666265886467)
          ·
            refine ⟨96552224700171999398829701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64368149800114666265886467 96552224700171999398829701)
            ·
              refine ⟨18103542131282249887280569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96552224700171999398829701 18103542131282249887280569)
              ·
                refine ⟨13577656598461687415460427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18103542131282249887280569 13577656598461687415460427)
                ·
                  refine ⟨20366484897692531123190641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13577656598461687415460427 20366484897692531123190641)
                  ·
                    refine ⟨15274863673269398342392981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20366484897692531123190641 15274863673269398342392981)
                    ·
                      refine ⟨716009234684503047299671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15274863673269398342392981 716009234684503047299671)
                      ·
                        rfl

theorem cell23_1394423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_1394423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394423 prefixEnd_1394423 := by exact prefixLift 1394423
  have htrace : WordTrace (prefixWord ++ tailWord_1394423) baseStart_1394423 baseEnd_1394423 := by
    simpa [prefixWord, tailWord_1394423, baseEnd_1394423] using wordTrace_append hprefix tailTrace_1394423
  have hstable : (prefixWord ++ tailWord_1394423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394423).length < 2 ^ (prefixWord ++ tailWord_1394423).sum := by decide
  have hdescent : baseEnd_1394423 < baseStart_1394423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394434 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1394434 : Nat := 118140960795 + 1394434 * 2 ^ 59
def prefixEnd_1394434 : Nat := 4983230072969 + 3 ^ 40 * 1394434 * 2
def baseEnd_1394434 : Nat := 716014882971702504262121

theorem tailTrace_1394434 : CollatzResearch.WordTrace tailWord_1394434 prefixEnd_1394434 716014882971702504262121 := by
  unfold tailWord_1394434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12714796557552810803047589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33906124153474162141460237 12714796557552810803047589)
  ·
    refine ⟨2384024354541152025571423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12714796557552810803047589 2384024354541152025571423)
    ·
      refine ⟨3576036531811728038357135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2384024354541152025571423 3576036531811728038357135)
      ·
        refine ⟨5364054797717592057535703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3576036531811728038357135 5364054797717592057535703)
        ·
          refine ⟨8046082196576388086303555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5364054797717592057535703 8046082196576388086303555)
          ·
            refine ⟨12069123294864582129455333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8046082196576388086303555 12069123294864582129455333)
            ·
              refine ⟨2262960617787109149272875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12069123294864582129455333 2262960617787109149272875)
              ·
                refine ⟨3394440926680663723909313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262960617787109149272875 3394440926680663723909313)
                ·
                  refine ⟨2545830695010497792931985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3394440926680663723909313 2545830695010497792931985)
                  ·
                    refine ⟨1909373021257873344698989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2545830695010497792931985 1909373021257873344698989)
                    ·
                      refine ⟨716014882971702504262121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909373021257873344698989 716014882971702504262121)
                      ·
                        rfl

theorem cell23_1394434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1394434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394434 prefixEnd_1394434 := by exact prefixLift 1394434
  have htrace : WordTrace (prefixWord ++ tailWord_1394434) baseStart_1394434 baseEnd_1394434 := by
    simpa [prefixWord, tailWord_1394434, baseEnd_1394434] using wordTrace_append hprefix tailTrace_1394434
  have hstable : (prefixWord ++ tailWord_1394434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394434).length < 2 ^ (prefixWord ++ tailWord_1394434).sum := by decide
  have hdescent : baseEnd_1394434 < baseStart_1394434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394480 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 8, 4]
def baseStart_1394480 : Nat := 118140960795 + 1394480 * 2 ^ 59
def prefixEnd_1394480 : Nat := 4983230072969 + 3 ^ 40 * 1394480 * 2
def baseEnd_1394480 : Nat := 238679501027269774762303

theorem tailTrace_1394480 : CollatzResearch.WordTrace tailWord_1394480 prefixEnd_1394480 238679501027269774762303 := by
  unfold tailWord_1394480
  simp only [CollatzResearch.WordTrace]
  refine ⟨25430431994022296534182447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33907242658696395378909929 25430431994022296534182447)
  ·
    refine ⟨38145647991033444801273671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25430431994022296534182447 38145647991033444801273671)
    ·
      refine ⟨57218471986550167201910507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38145647991033444801273671 57218471986550167201910507)
      ·
        refine ⟨85827707979825250802865761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57218471986550167201910507 85827707979825250802865761)
        ·
          refine ⟨64370780984868938102149321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85827707979825250802865761 64370780984868938102149321)
          ·
            refine ⟨48278085738651703576611991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64370780984868938102149321 48278085738651703576611991)
            ·
              refine ⟨72417128607977555364917987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48278085738651703576611991 72417128607977555364917987)
              ·
                refine ⟨108625692911966333047376981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72417128607977555364917987 108625692911966333047376981)
                ·
                  refine ⟨1272957338812105465398949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 108625692911966333047376981 1272957338812105465398949)
                  ·
                    refine ⟨238679501027269774762303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1272957338812105465398949 238679501027269774762303)
                    ·
                      rfl

theorem cell23_1394480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_1394480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394480 prefixEnd_1394480 := by exact prefixLift 1394480
  have htrace : WordTrace (prefixWord ++ tailWord_1394480) baseStart_1394480 baseEnd_1394480 := by
    simpa [prefixWord, tailWord_1394480, baseEnd_1394480] using wordTrace_append hprefix tailTrace_1394480
  have hstable : (prefixWord ++ tailWord_1394480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394480).length < 2 ^ (prefixWord ++ tailWord_1394480).sum := by decide
  have hdescent : baseEnd_1394480 < baseStart_1394480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394504 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_1394504 : Nat := 118140960795 + 1394504 * 2 ^ 59
def prefixEnd_1394504 : Nat := 4983230072969 + 3 ^ 40 * 1394504 * 2
def baseEnd_1394504 : Nat := 716050826617517230386799

theorem tailTrace_1394504 : CollatzResearch.WordTrace tailWord_1394504 prefixEnd_1394504 716050826617517230386799 := by
  unfold tailWord_1394504
  simp only [CollatzResearch.WordTrace]
  refine ⟨25430869669978822583619283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33907826226638430111492377 25430869669978822583619283)
  ·
    refine ⟨38146304504968233875428925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25430869669978822583619283 38146304504968233875428925)
    ·
      refine ⟨14304864189363087703285847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38146304504968233875428925 14304864189363087703285847)
      ·
        refine ⟨21457296284044631554928771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14304864189363087703285847 21457296284044631554928771)
        ·
          refine ⟨32185944426066947332393157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21457296284044631554928771 32185944426066947332393157)
          ·
            refine ⟨6034864579887552624823717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32185944426066947332393157 6034864579887552624823717)
            ·
              refine ⟨1131537108728916117154447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6034864579887552624823717 1131537108728916117154447)
              ·
                refine ⟨1697305663093374175731671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131537108728916117154447 1697305663093374175731671)
                ·
                  refine ⟨2545958494640061263597507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697305663093374175731671 2545958494640061263597507)
                  ·
                    refine ⟨3818937741960091895396261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2545958494640061263597507 3818937741960091895396261)
                    ·
                      refine ⟨716050826617517230386799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3818937741960091895396261 716050826617517230386799)
                      ·
                        rfl

theorem cell23_1394504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_1394504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394504 prefixEnd_1394504 := by exact prefixLift 1394504
  have htrace : WordTrace (prefixWord ++ tailWord_1394504) baseStart_1394504 baseEnd_1394504 := by
    simpa [prefixWord, tailWord_1394504, baseEnd_1394504] using wordTrace_append hprefix tailTrace_1394504
  have hstable : (prefixWord ++ tailWord_1394504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394504).length < 2 ^ (prefixWord ++ tailWord_1394504).sum := by decide
  have hdescent : baseEnd_1394504 < baseStart_1394504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394514 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_1394514 : Nat := 118140960795 + 1394514 * 2 ^ 59
def prefixEnd_1394514 : Nat := 4983230072969 + 3 ^ 40 * 1394514 * 2
def baseEnd_1394514 : Nat := 238685320474687397087251

theorem tailTrace_1394514 : CollatzResearch.WordTrace tailWord_1394514 prefixEnd_1394514 238685320474687397087251 := by
  unfold tailWord_1394514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715526017480354218775649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33908069379947611250068397 12715526017480354218775649)
  ·
    refine ⟨9536644513110265664081737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12715526017480354218775649 9536644513110265664081737)
    ·
      refine ⟨7152483384832699248061303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9536644513110265664081737 7152483384832699248061303)
      ·
        refine ⟨10728725077249048872091955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7152483384832699248061303 10728725077249048872091955)
        ·
          refine ⟨16093087615873573308137933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10728725077249048872091955 16093087615873573308137933)
          ·
            refine ⟨6034907855952589990551725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16093087615873573308137933 6034907855952589990551725)
            ·
              refine ⟨2263090445982221246456897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6034907855952589990551725 2263090445982221246456897)
              ·
                refine ⟨1697317834486665934842673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263090445982221246456897 1697317834486665934842673)
                ·
                  refine ⟨1272988375864999451132005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697317834486665934842673 1272988375864999451132005)
                  ·
                    refine ⟨238685320474687397087251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1272988375864999451132005 238685320474687397087251)
                    ·
                      rfl

theorem cell23_1394514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_1394514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394514 prefixEnd_1394514 := by exact prefixLift 1394514
  have htrace : WordTrace (prefixWord ++ tailWord_1394514) baseStart_1394514 baseEnd_1394514 := by
    simpa [prefixWord, tailWord_1394514, baseEnd_1394514] using wordTrace_append hprefix tailTrace_1394514
  have hstable : (prefixWord ++ tailWord_1394514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394514).length < 2 ^ (prefixWord ++ tailWord_1394514).sum := by decide
  have hdescent : baseEnd_1394514 < baseStart_1394514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394520 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1394520 : Nat := 118140960795 + 1394520 * 2 ^ 59
def prefixEnd_1394520 : Nat := 4983230072969 + 3 ^ 40 * 1394520 * 2
def baseEnd_1394520 : Nat := 716059042307989167786725

theorem tailTrace_1394520 : CollatzResearch.WordTrace tailWord_1394520 prefixEnd_1394520 716059042307989167786725 := by
  unfold tailWord_1394520
  simp only [CollatzResearch.WordTrace]
  refine ⟨25431161453949839949910507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33908215271933119933214009 25431161453949839949910507)
  ·
    refine ⟨38146742180924759924865761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25431161453949839949910507 38146742180924759924865761)
    ·
      refine ⟨28610056635693569943649321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38146742180924759924865761 28610056635693569943649321)
      ·
        refine ⟨21457542476770177457736991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28610056635693569943649321 21457542476770177457736991)
        ·
          refine ⟨32186313715155266186605487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21457542476770177457736991 32186313715155266186605487)
          ·
            refine ⟨48279470572732899279908231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32186313715155266186605487 48279470572732899279908231)
            ·
              refine ⟨72419205859099348919862347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48279470572732899279908231 72419205859099348919862347)
              ·
                refine ⟨108628808788649023379793521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72419205859099348919862347 108628808788649023379793521)
                ·
                  refine ⟨81471606591486767534845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108628808788649023379793521 81471606591486767534845141)
                  ·
                    refine ⟨1909490779487971114097933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 81471606591486767534845141 1909490779487971114097933)
                    ·
                      refine ⟨716059042307989167786725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909490779487971114097933 716059042307989167786725)
                      ·
                        rfl

theorem cell23_1394520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1394520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394520 prefixEnd_1394520 := by exact prefixLift 1394520
  have htrace : WordTrace (prefixWord ++ tailWord_1394520) baseStart_1394520 baseEnd_1394520 := by
    simpa [prefixWord, tailWord_1394520, baseEnd_1394520] using wordTrace_append hprefix tailTrace_1394520
  have hstable : (prefixWord ++ tailWord_1394520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394520).length < 2 ^ (prefixWord ++ tailWord_1394520).sum := by decide
  have hdescent : baseEnd_1394520 < baseStart_1394520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394521 : List Nat := [1, 2, 1, 2, 2, 3, 1, 6, 1, 2, 2]
def baseStart_1394521 : Nat := 118140960795 + 1394521 * 2 ^ 59
def prefixEnd_1394521 : Nat := 4983230072969 + 3 ^ 40 * 1394521 * 2
def baseEnd_1394521 : Nat := 716059555788643663874221

theorem tailTrace_1394521 : CollatzResearch.WordTrace tailWord_1394521 prefixEnd_1394521 716059555788643663874221 := by
  unfold tailWord_1394521
  simp only [CollatzResearch.WordTrace]
  refine ⟨50862359380896057070607417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33908239587264038047071611 50862359380896057070607417)
  ·
    refine ⟨38146769535672042802955563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50862359380896057070607417 38146769535672042802955563)
    ·
      refine ⟨57220154303508064204433345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38146769535672042802955563 57220154303508064204433345)
      ·
        refine ⟨42915115727631048153325009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57220154303508064204433345 42915115727631048153325009)
        ·
          refine ⟨32186336795723286114993757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42915115727631048153325009 32186336795723286114993757)
          ·
            refine ⟨12069876298396232293122659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32186336795723286114993757 12069876298396232293122659)
            ·
              refine ⟨18104814447594348439683989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12069876298396232293122659 18104814447594348439683989)
              ·
                refine ⟨848663177230985083110187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18104814447594348439683989 848663177230985083110187)
                ·
                  refine ⟨1272994765846477624665281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848663177230985083110187 1272994765846477624665281)
                  ·
                    refine ⟨954746074384858218498961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1272994765846477624665281 954746074384858218498961)
                    ·
                      refine ⟨716059555788643663874221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954746074384858218498961 716059555788643663874221)
                      ·
                        rfl

theorem cell23_1394521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_1394521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394521 prefixEnd_1394521 := by exact prefixLift 1394521
  have htrace : WordTrace (prefixWord ++ tailWord_1394521) baseStart_1394521 baseEnd_1394521 := by
    simpa [prefixWord, tailWord_1394521, baseEnd_1394521] using wordTrace_append hprefix tailTrace_1394521
  have hstable : (prefixWord ++ tailWord_1394521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394521).length < 2 ^ (prefixWord ++ tailWord_1394521).sum := by decide
  have hdescent : baseEnd_1394521 < baseStart_1394521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394524 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1394524 : Nat := 118140960795 + 1394524 * 2 ^ 59
def prefixEnd_1394524 : Nat := 4983230072969 + 3 ^ 40 * 1394524 * 2
def baseEnd_1394524 : Nat := 716061096230607152136707

theorem tailTrace_1394524 : CollatzResearch.WordTrace tailWord_1394524 prefixEnd_1394524 716061096230607152136707 := by
  unfold tailWord_1394524
  simp only [CollatzResearch.WordTrace]
  refine ⟨25431234399942594291483313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33908312533256792388644417 25431234399942594291483313)
  ·
    refine ⟨19073425799956945718612485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25431234399942594291483313 19073425799956945718612485)
    ·
      refine ⟨3576267337491927322239841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19073425799956945718612485 3576267337491927322239841)
      ·
        refine ⟨2682200503118945491679881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3576267337491927322239841 2682200503118945491679881)
        ·
          refine ⟨2011650377339209118759911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2682200503118945491679881 2011650377339209118759911)
          ·
            refine ⟨3017475566008813678139867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011650377339209118759911 3017475566008813678139867)
            ·
              refine ⟨4526213349013220517209801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017475566008813678139867 4526213349013220517209801)
              ·
                refine ⟨3394660011759915387907351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526213349013220517209801 3394660011759915387907351)
                ·
                  refine ⟨5091990017639873081861027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394660011759915387907351 5091990017639873081861027)
                  ·
                    refine ⟨7637985026459809622791541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5091990017639873081861027 7637985026459809622791541)
                    ·
                      refine ⟨716061096230607152136707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7637985026459809622791541 716061096230607152136707)
                      ·
                        rfl

theorem cell23_1394524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1394524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394524 prefixEnd_1394524 := by exact prefixLift 1394524
  have htrace : WordTrace (prefixWord ++ tailWord_1394524) baseStart_1394524 baseEnd_1394524 := by
    simpa [prefixWord, tailWord_1394524, baseEnd_1394524] using wordTrace_append hprefix tailTrace_1394524
  have hstable : (prefixWord ++ tailWord_1394524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394524).length < 2 ^ (prefixWord ++ tailWord_1394524).sum := by decide
  have hdescent : baseEnd_1394524 < baseStart_1394524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394531 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 2, 4]
def baseStart_1394531 : Nat := 118140960795 + 1394531 * 2 ^ 59
def prefixEnd_1394531 : Nat := 4983230072969 + 3 ^ 40 * 1394531 * 2
def baseEnd_1394531 : Nat := 238688230198396208249725

theorem tailTrace_1394531 : CollatzResearch.WordTrace tailWord_1394531 prefixEnd_1394531 238688230198396208249725 := by
  unfold tailWord_1394531
  simp only [CollatzResearch.WordTrace]
  refine ⟨50862724110859828778471447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33908482740573219185647631 50862724110859828778471447)
  ·
    refine ⟨76294086166289743167707171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50862724110859828778471447 76294086166289743167707171)
    ·
      refine ⟨114441129249434614751560757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76294086166289743167707171 114441129249434614751560757)
      ·
        refine ⟨10728855867134495132958821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114441129249434614751560757 10728855867134495132958821)
        ·
          refine ⟨2011660475087717837429779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10728855867134495132958821 2011660475087717837429779)
          ·
            refine ⟨3017490712631576756144669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011660475087717837429779 3017490712631576756144669)
            ·
              refine ⟨1131559017236841283554251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3017490712631576756144669 1131559017236841283554251)
              ·
                refine ⟨1697338525855261925331377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131559017236841283554251 1697338525855261925331377)
                ·
                  refine ⟨1273003894391446443998533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697338525855261925331377 1273003894391446443998533)
                  ·
                    refine ⟨238688230198396208249725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273003894391446443998533 238688230198396208249725)
                    ·
                      rfl

theorem cell23_1394531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 2, 4].length) (baseStart_1394531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394531 prefixEnd_1394531 := by exact prefixLift 1394531
  have htrace : WordTrace (prefixWord ++ tailWord_1394531) baseStart_1394531 baseEnd_1394531 := by
    simpa [prefixWord, tailWord_1394531, baseEnd_1394531] using wordTrace_append hprefix tailTrace_1394531
  have hstable : (prefixWord ++ tailWord_1394531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394531).length < 2 ^ (prefixWord ++ tailWord_1394531).sum := by decide
  have hdescent : baseEnd_1394531 < baseStart_1394531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394582 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_1394582 : Nat := 118140960795 + 1394582 * 2 ^ 59
def prefixEnd_1394582 : Nat := 4983230072969 + 3 ^ 40 * 1394582 * 2
def baseEnd_1394582 : Nat := 238696959369522641737147

theorem tailTrace_1394582 : CollatzResearch.WordTrace tailWord_1394582 prefixEnd_1394582 238696959369522641737147 := by
  unfold tailWord_1394582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179036514604691530536125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33909722822450042992385333 3179036514604691530536125)
  ·
    refine ⟨1192138692976759323951047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3179036514604691530536125 1192138692976759323951047)
    ·
      refine ⟨1788208039465138985926571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1192138692976759323951047 1788208039465138985926571)
      ·
        refine ⟨2682312059197708478889857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1788208039465138985926571 2682312059197708478889857)
        ·
          refine ⟨2011734044398281359167393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2682312059197708478889857 2011734044398281359167393)
          ·
            refine ⟨1508800533298711019375545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2011734044398281359167393 1508800533298711019375545)
            ·
              refine ⟨1131600399974033264531659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508800533298711019375545 1131600399974033264531659)
              ·
                refine ⟨1697400599961049896797489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131600399974033264531659 1697400599961049896797489)
                ·
                  refine ⟨1273050449970787422598117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697400599961049896797489 1273050449970787422598117)
                  ·
                    refine ⟨238696959369522641737147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273050449970787422598117 238696959369522641737147)
                    ·
                      rfl

theorem cell23_1394582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_1394582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394582 prefixEnd_1394582 := by exact prefixLift 1394582
  have htrace : WordTrace (prefixWord ++ tailWord_1394582) baseStart_1394582 baseEnd_1394582 := by
    simpa [prefixWord, tailWord_1394582, baseEnd_1394582] using wordTrace_append hprefix tailTrace_1394582
  have hstable : (prefixWord ++ tailWord_1394582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394582).length < 2 ^ (prefixWord ++ tailWord_1394582).sum := by decide
  have hdescent : baseEnd_1394582 < baseStart_1394582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394588 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1394588 : Nat := 118140960795 + 1394588 * 2 ^ 59
def prefixEnd_1394588 : Nat := 4983230072969 + 3 ^ 40 * 1394588 * 2
def baseEnd_1394588 : Nat := 716093958992494901736413

theorem tailTrace_1394588 : CollatzResearch.WordTrace tailWord_1394588 prefixEnd_1394588 716093958992494901736413 := by
  unfold tailWord_1394588
  simp only [CollatzResearch.WordTrace]
  refine ⟨25432401535826663756648209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33909868714435551675530945 25432401535826663756648209)
  ·
    refine ⟨19074301151869997817486157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25432401535826663756648209 19074301151869997817486157)
    ·
      refine ⟨7152862931951249181557309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19074301151869997817486157 7152862931951249181557309)
      ·
        refine ⟨2682323599481718443083991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7152862931951249181557309 2682323599481718443083991)
        ·
          refine ⟨4023485399222577664625987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682323599481718443083991 4023485399222577664625987)
          ·
            refine ⟨6035228098833866496938981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023485399222577664625987 6035228098833866496938981)
            ·
              refine ⟨1131605268531349968176059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6035228098833866496938981 1131605268531349968176059)
              ·
                refine ⟨1697407902797024952264089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131605268531349968176059 1697407902797024952264089)
                ·
                  refine ⟨1273055927097768714198067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697407902797024952264089 1273055927097768714198067)
                  ·
                    refine ⟨1909583890646653071297101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273055927097768714198067 1909583890646653071297101)
                    ·
                      refine ⟨716093958992494901736413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909583890646653071297101 716093958992494901736413)
                      ·
                        rfl

theorem cell23_1394588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1394588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394588 prefixEnd_1394588 := by exact prefixLift 1394588
  have htrace : WordTrace (prefixWord ++ tailWord_1394588) baseStart_1394588 baseEnd_1394588 := by
    simpa [prefixWord, tailWord_1394588, baseEnd_1394588] using wordTrace_append hprefix tailTrace_1394588
  have hstable : (prefixWord ++ tailWord_1394588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394588).length < 2 ^ (prefixWord ++ tailWord_1394588).sum := by decide
  have hdescent : baseEnd_1394588 < baseStart_1394588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394644 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1394644 : Nat := 118140960795 + 1394644 * 2 ^ 59
def prefixEnd_1394644 : Nat := 4983230072969 + 3 ^ 40 * 1394644 * 2
def baseEnd_1394644 : Nat := 716122713909146682636155

theorem tailTrace_1394644 : CollatzResearch.WordTrace tailWord_1394644 prefixEnd_1394644 716122713909146682636155 := by
  unfold tailWord_1394644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25433422779725224538667493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33911230372966966051556657 25433422779725224538667493)
  ·
    refine ⟨4768766771198479601000155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25433422779725224538667493 4768766771198479601000155)
    ·
      refine ⟨7153150156797719401500233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4768766771198479601000155 7153150156797719401500233)
      ·
        refine ⟨5364862617598289551125175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7153150156797719401500233 5364862617598289551125175)
        ·
          refine ⟨8047293926397434326687763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5364862617598289551125175 8047293926397434326687763)
          ·
            refine ⟨12070940889596151490031645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8047293926397434326687763 12070940889596151490031645)
            ·
              refine ⟨4526602833598556808761867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12070940889596151490031645 4526602833598556808761867)
              ·
                refine ⟨6789904250397835213142801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526602833598556808761867 6789904250397835213142801)
                ·
                  refine ⟨5092428187798376409857101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6789904250397835213142801 5092428187798376409857101)
                  ·
                    refine ⟨1909660570424391153696413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5092428187798376409857101 1909660570424391153696413)
                    ·
                      refine ⟨716122713909146682636155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909660570424391153696413 716122713909146682636155)
                      ·
                        rfl

theorem cell23_1394644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1394644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394644 prefixEnd_1394644 := by exact prefixLift 1394644
  have htrace : WordTrace (prefixWord ++ tailWord_1394644) baseStart_1394644 baseEnd_1394644 := by
    simpa [prefixWord, tailWord_1394644, baseEnd_1394644] using wordTrace_append hprefix tailTrace_1394644
  have hstable : (prefixWord ++ tailWord_1394644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394644).length < 2 ^ (prefixWord ++ tailWord_1394644).sum := by decide
  have hdescent : baseEnd_1394644 < baseStart_1394644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394684 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_1394684 : Nat := 118140960795 + 1394684 * 2 ^ 59
def prefixEnd_1394684 : Nat := 4983230072969 + 3 ^ 40 * 1394684 * 2
def baseEnd_1394684 : Nat := 716143253135326526135971

theorem tailTrace_1394684 : CollatzResearch.WordTrace tailWord_1394684 prefixEnd_1394684 716143253135326526135971 := by
  unfold tailWord_1394684
  simp only [CollatzResearch.WordTrace]
  refine ⟨25434152239652767954395553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33912202986203690605860737 25434152239652767954395553)
  ·
    refine ⟨19075614179739575965796665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25434152239652767954395553 19075614179739575965796665)
    ·
      refine ⟨14306710634804681974347499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19075614179739575965796665 14306710634804681974347499)
      ·
        refine ⟨21460065952207022961521249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14306710634804681974347499 21460065952207022961521249)
        ·
          refine ⟨16095049464155267221140937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21460065952207022961521249 16095049464155267221140937)
          ·
            refine ⟨12071287098116450415855703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16095049464155267221140937 12071287098116450415855703)
            ·
              refine ⟨18106930647174675623783555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12071287098116450415855703 18106930647174675623783555)
              ·
                refine ⟨27160395970762013435675333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18106930647174675623783555 27160395970762013435675333)
                ·
                  refine ⟨5092574244517877519189125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27160395970762013435675333 5092574244517877519189125)
                  ·
                    refine ⟨954857670847102034847961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5092574244517877519189125 954857670847102034847961)
                    ·
                      refine ⟨716143253135326526135971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 954857670847102034847961 716143253135326526135971)
                      ·
                        rfl

theorem cell23_1394684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_1394684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394684 prefixEnd_1394684 := by exact prefixLift 1394684
  have htrace : WordTrace (prefixWord ++ tailWord_1394684) baseStart_1394684 baseEnd_1394684 := by
    simpa [prefixWord, tailWord_1394684, baseEnd_1394684] using wordTrace_append hprefix tailTrace_1394684
  have hstable : (prefixWord ++ tailWord_1394684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394684).length < 2 ^ (prefixWord ++ tailWord_1394684).sum := by decide
  have hdescent : baseEnd_1394684 < baseStart_1394684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394707 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 6]
def baseStart_1394707 : Nat := 118140960795 + 1394707 * 2 ^ 59
def prefixEnd_1394707 : Nat := 4983230072969 + 3 ^ 40 * 1394707 * 2
def baseEnd_1394707 : Nat := 79572784798931104016485

theorem tailTrace_1394707 : CollatzResearch.WordTrace tailWord_1394707 prefixEnd_1394707 79572784798931104016485 := by
  unfold tailWord_1394707
  simp only [CollatzResearch.WordTrace]
  refine ⟨50869143358222210836878375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33912762238814807224585583 50869143358222210836878375)
  ·
    refine ⟨76303715037333316255317563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50869143358222210836878375 76303715037333316255317563)
    ·
      refine ⟨114455572555999974382976345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76303715037333316255317563 114455572555999974382976345)
      ·
        refine ⟨85841679416999980787232259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114455572555999974382976345 85841679416999980787232259)
        ·
          refine ⟨128762519125499971180848389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85841679416999980787232259 128762519125499971180848389)
          ·
            refine ⟨24142972336031244596409073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128762519125499971180848389 24142972336031244596409073)
            ·
              refine ⟨18107229252023433447306805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24142972336031244596409073 18107229252023433447306805)
              ·
                refine ⟨1697552742377196885685013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18107229252023433447306805 1697552742377196885685013)
                ·
                  refine ⟨79572784798931104016485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1697552742377196885685013 79572784798931104016485)
                  ·
                    rfl

theorem cell23_1394707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 6].length) (baseStart_1394707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394707 prefixEnd_1394707 := by exact prefixLift 1394707
  have htrace : WordTrace (prefixWord ++ tailWord_1394707) baseStart_1394707 baseEnd_1394707 := by
    simpa [prefixWord, tailWord_1394707, baseEnd_1394707] using wordTrace_append hprefix tailTrace_1394707
  have hstable : (prefixWord ++ tailWord_1394707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394707).length < 2 ^ (prefixWord ++ tailWord_1394707).sum := by decide
  have hdescent : baseEnd_1394707 < baseStart_1394707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394745 : List Nat := [1, 2, 1, 5, 3, 1, 3, 2, 1, 4]
def baseStart_1394745 : Nat := 118140960795 + 1394745 * 2 ^ 59
def prefixEnd_1394745 : Nat := 4983230072969 + 3 ^ 40 * 1394745 * 2
def baseEnd_1394745 : Nat := 238724858485083595824397

theorem tailTrace_1394745 : CollatzResearch.WordTrace tailWord_1394745 prefixEnd_1394745 238724858485083595824397 := by
  unfold tailWord_1394745
  simp only [CollatzResearch.WordTrace]
  refine ⟨50870529332084543326761689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33913686221389695551174459 50870529332084543326761689)
  ·
    refine ⟨38152896999063407495071267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50870529332084543326761689 38152896999063407495071267)
    ·
      refine ⟨57229345498595111242606901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38152896999063407495071267 57229345498595111242606901)
      ·
        refine ⟨5365251140493291678994397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57229345498595111242606901 5365251140493291678994397)
        ·
          refine ⟨2011969177684984379622899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5365251140493291678994397 2011969177684984379622899)
          ·
            refine ⟨3017953766527476569434349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011969177684984379622899 3017953766527476569434349)
            ·
              refine ⟨1131732662447803713537881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3017953766527476569434349 1131732662447803713537881)
              ·
                refine ⟨848799496835852785153411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131732662447803713537881 848799496835852785153411)
                ·
                  refine ⟨1273199245253779177730117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848799496835852785153411 1273199245253779177730117)
                  ·
                    refine ⟨238724858485083595824397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273199245253779177730117 238724858485083595824397)
                    ·
                      rfl

theorem cell23_1394745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 4].length) (baseStart_1394745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394745 prefixEnd_1394745 := by exact prefixLift 1394745
  have htrace : WordTrace (prefixWord ++ tailWord_1394745) baseStart_1394745 baseEnd_1394745 := by
    simpa [prefixWord, tailWord_1394745, baseEnd_1394745] using wordTrace_append hprefix tailTrace_1394745
  have hstable : (prefixWord ++ tailWord_1394745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394745).length < 2 ^ (prefixWord ++ tailWord_1394745).sum := by decide
  have hdescent : baseEnd_1394745 < baseStart_1394745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394751 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 3]
def baseStart_1394751 : Nat := 118140960795 + 1394751 * 2 ^ 59
def prefixEnd_1394751 : Nat := 4983230072969 + 3 ^ 40 * 1394751 * 2
def baseEnd_1394751 : Nat := 716177656339177763998163

theorem tailTrace_1394751 : CollatzResearch.WordTrace tailWord_1394751 prefixEnd_1394751 716177656339177763998163 := by
  unfold tailWord_1394751
  simp only [CollatzResearch.WordTrace]
  refine ⟨50870748170062806351480107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33913832113375204234320071 50870748170062806351480107)
  ·
    refine ⟨76306122255094209527220161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50870748170062806351480107 76306122255094209527220161)
    ·
      refine ⟨57229591691320657145415121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76306122255094209527220161 57229591691320657145415121)
      ·
        refine ⟨42922193768490492859061341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57229591691320657145415121 42922193768490492859061341)
        ·
          refine ⟨16095822663183934822148003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42922193768490492859061341 16095822663183934822148003)
          ·
            refine ⟨24143733994775902233222005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16095822663183934822148003 24143733994775902233222005)
            ·
              refine ⟨2263475062010240834364563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24143733994775902233222005 2263475062010240834364563)
              ·
                refine ⟨3395212593015361251546845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263475062010240834364563 3395212593015361251546845)
                ·
                  refine ⟨1273204722380760469330067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3395212593015361251546845 1273204722380760469330067)
                  ·
                    refine ⟨1909807083571140703995101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273204722380760469330067 1909807083571140703995101)
                    ·
                      refine ⟨716177656339177763998163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909807083571140703995101 716177656339177763998163)
                      ·
                        rfl

theorem cell23_1394751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_1394751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394751 prefixEnd_1394751 := by exact prefixLift 1394751
  have htrace : WordTrace (prefixWord ++ tailWord_1394751) baseStart_1394751 baseEnd_1394751 := by
    simpa [prefixWord, tailWord_1394751, baseEnd_1394751] using wordTrace_append hprefix tailTrace_1394751
  have hstable : (prefixWord ++ tailWord_1394751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394751).length < 2 ^ (prefixWord ++ tailWord_1394751).sum := by decide
  have hdescent : baseEnd_1394751 < baseStart_1394751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394757 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_1394757 : Nat := 118140960795 + 1394757 * 2 ^ 59
def prefixEnd_1394757 : Nat := 4983230072969 + 3 ^ 40 * 1394757 * 2
def baseEnd_1394757 : Nat := 716180737223104740523135

theorem tailTrace_1394757 : CollatzResearch.WordTrace tailWord_1394757 prefixEnd_1394757 716180737223104740523135 := by
  unfold tailWord_1394757
  simp only [CollatzResearch.WordTrace]
  refine ⟨50870967008041069376198525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33913978005360712917465683 50870967008041069376198525)
  ·
    refine ⟨19076612628015401016074447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50870967008041069376198525 19076612628015401016074447)
    ·
      refine ⟨28614918942023101524111671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19076612628015401016074447 28614918942023101524111671)
      ·
        refine ⟨42922378413034652286167507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28614918942023101524111671 42922378413034652286167507)
        ·
          refine ⟨64383567619551978429251261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42922378413034652286167507 64383567619551978429251261)
          ·
            refine ⟨24143837857331991910969223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64383567619551978429251261 24143837857331991910969223)
            ·
              refine ⟨36215756785997987866453835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24143837857331991910969223 36215756785997987866453835)
              ·
                refine ⟨54323635178996981799680753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36215756785997987866453835 54323635178996981799680753)
                ·
                  refine ⟨40742726384247736349760565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54323635178996981799680753 40742726384247736349760565)
                  ·
                    refine ⟨3819630598523225282790053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40742726384247736349760565 3819630598523225282790053)
                    ·
                      refine ⟨716180737223104740523135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3819630598523225282790053 716180737223104740523135)
                      ·
                        rfl

theorem cell23_1394757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_1394757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394757 prefixEnd_1394757 := by exact prefixLift 1394757
  have htrace : WordTrace (prefixWord ++ tailWord_1394757) baseStart_1394757 baseEnd_1394757 := by
    simpa [prefixWord, tailWord_1394757, baseEnd_1394757] using wordTrace_append hprefix tailTrace_1394757
  have hstable : (prefixWord ++ tailWord_1394757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394757).length < 2 ^ (prefixWord ++ tailWord_1394757).sum := by decide
  have hdescent : baseEnd_1394757 < baseStart_1394757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394784 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 1, 6]
def baseStart_1394784 : Nat := 118140960795 + 1394784 * 2 ^ 59
def prefixEnd_1394784 : Nat := 4983230072969 + 3 ^ 40 * 1394784 * 2
def baseEnd_1394784 : Nat := 238731533733592044961837

theorem tailTrace_1394784 : CollatzResearch.WordTrace tailWord_1394784 prefixEnd_1394784 238731533733592044961837 := by
  unfold tailWord_1394784
  simp only [CollatzResearch.WordTrace]
  refine ⟨25435975889471626493715703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33914634519295501991620937 25435975889471626493715703)
  ·
    refine ⟨38153963834207439740573555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25435975889471626493715703 38153963834207439740573555)
    ·
      refine ⟨57230945751311159610860333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38153963834207439740573555 57230945751311159610860333)
      ·
        refine ⟨21461604656741684854072625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57230945751311159610860333 21461604656741684854072625)
        ·
          refine ⟨16096203492556263640554469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21461604656741684854072625 16096203492556263640554469)
          ·
            refine ⟨3018038154854299432603963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16096203492556263640554469 3018038154854299432603963)
            ·
              refine ⟨4527057232281449148905945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018038154854299432603963 4527057232281449148905945)
              ·
                refine ⟨3395292924211086861679459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527057232281449148905945 3395292924211086861679459)
                ·
                  refine ⟨5092939386316630292519189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395292924211086861679459 5092939386316630292519189)
                  ·
                    refine ⟨238731533733592044961837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5092939386316630292519189 238731533733592044961837)
                    ·
                      rfl

theorem cell23_1394784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_1394784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394784 prefixEnd_1394784 := by exact prefixLift 1394784
  have htrace : WordTrace (prefixWord ++ tailWord_1394784) baseStart_1394784 baseEnd_1394784 := by
    simpa [prefixWord, tailWord_1394784, baseEnd_1394784] using wordTrace_append hprefix tailTrace_1394784
  have hstable : (prefixWord ++ tailWord_1394784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394784).length < 2 ^ (prefixWord ++ tailWord_1394784).sum := by decide
  have hdescent : baseEnd_1394784 < baseStart_1394784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394801 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 2, 4]
def baseStart_1394801 : Nat := 118140960795 + 1394801 * 2 ^ 59
def prefixEnd_1394801 : Nat := 4983230072969 + 3 ^ 40 * 1394801 * 2
def baseEnd_1394801 : Nat := 238734443457300856124311

theorem tailTrace_1394801 : CollatzResearch.WordTrace tailWord_1394801 prefixEnd_1394801 238734443457300856124311 := by
  unfold tailWord_1394801
  simp only [CollatzResearch.WordTrace]
  refine ⟨50872571819881664890800257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33915047879921109927200171 50872571819881664890800257)
  ·
    refine ⟨38154428864911248668100193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50872571819881664890800257 38154428864911248668100193)
    ·
      refine ⟨28615821648683436501075145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38154428864911248668100193 28615821648683436501075145)
      ·
        refine ⟨21461866236512577375806359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28615821648683436501075145 21461866236512577375806359)
        ·
          refine ⟨32192799354768866063709539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21461866236512577375806359 32192799354768866063709539)
          ·
            refine ⟨48289199032153299095564309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32192799354768866063709539 48289199032153299095564309)
            ·
              refine ⟨2263556204632185895104577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48289199032153299095564309 2263556204632185895104577)
              ·
                refine ⟨1697667153474139421328433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263556204632185895104577 1697667153474139421328433)
                ·
                  refine ⟨1273250365105604565996325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697667153474139421328433 1273250365105604565996325)
                  ·
                    refine ⟨238734443457300856124311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273250365105604565996325 238734443457300856124311)
                    ·
                      rfl

theorem cell23_1394801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_1394801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394801 prefixEnd_1394801 := by exact prefixLift 1394801
  have htrace : WordTrace (prefixWord ++ tailWord_1394801) baseStart_1394801 baseEnd_1394801 := by
    simpa [prefixWord, tailWord_1394801, baseEnd_1394801] using wordTrace_append hprefix tailTrace_1394801
  have hstable : (prefixWord ++ tailWord_1394801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394801).length < 2 ^ (prefixWord ++ tailWord_1394801).sum := by decide
  have hdescent : baseEnd_1394801 < baseStart_1394801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394802 : List Nat := [3, 2, 1, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_1394802 : Nat := 118140960795 + 1394802 * 2 ^ 59
def prefixEnd_1394802 : Nat := 4983230072969 + 3 ^ 40 * 1394802 * 2
def baseEnd_1394802 : Nat := 716203843852557064460429

theorem tailTrace_1394802 : CollatzResearch.WordTrace tailWord_1394802 prefixEnd_1394802 716203843852557064460429 := by
  unfold tailWord_1394802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718152073219510515396665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33915072195252028041057773 12718152073219510515396665)
  ·
    refine ⟨9538614054914632886547499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12718152073219510515396665 9538614054914632886547499)
    ·
      refine ⟨14307921082371949329821249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9538614054914632886547499 14307921082371949329821249)
      ·
        refine ⟨10730940811778961997365937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14307921082371949329821249 10730940811778961997365937)
        ·
          refine ⟨8048205608834221498024453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10730940811778961997365937 8048205608834221498024453)
          ·
            refine ⟨1509038551656416530879585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8048205608834221498024453 1509038551656416530879585)
            ·
              refine ⟨1131778913742312398159689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509038551656416530879585 1131778913742312398159689)
              ·
                refine ⟨848834185306734298619767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131778913742312398159689 848834185306734298619767)
                ·
                  refine ⟨1273251277960101447929651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848834185306734298619767 1273251277960101447929651)
                  ·
                    refine ⟨1909876916940152171894477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273251277960101447929651 1909876916940152171894477)
                    ·
                      refine ⟨716203843852557064460429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909876916940152171894477 716203843852557064460429)
                      ·
                        rfl

theorem cell23_1394802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_1394802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394802 prefixEnd_1394802 := by exact prefixLift 1394802
  have htrace : WordTrace (prefixWord ++ tailWord_1394802) baseStart_1394802 baseEnd_1394802 := by
    simpa [prefixWord, tailWord_1394802, baseEnd_1394802] using wordTrace_append hprefix tailTrace_1394802
  have hstable : (prefixWord ++ tailWord_1394802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394802).length < 2 ^ (prefixWord ++ tailWord_1394802).sum := by decide
  have hdescent : baseEnd_1394802 < baseStart_1394802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394821 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_1394821 : Nat := 118140960795 + 1394821 * 2 ^ 59
def prefixEnd_1394821 : Nat := 4983230072969 + 3 ^ 40 * 1394821 * 2
def baseEnd_1394821 : Nat := 716213599984992490122841

theorem tailTrace_1394821 : CollatzResearch.WordTrace tailWord_1394821 prefixEnd_1394821 716213599984992490122841 := by
  unfold tailWord_1394821
  simp only [CollatzResearch.WordTrace]
  refine ⟨50873301279809208306528317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33915534186539472204352211 50873301279809208306528317)
  ·
    refine ⟨19077487979928453114948119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50873301279809208306528317 19077487979928453114948119)
    ·
      refine ⟨28616231969892679672422179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19077487979928453114948119 28616231969892679672422179)
      ·
        refine ⟨42924347954839019508633269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28616231969892679672422179 42924347954839019508633269)
        ·
          refine ⟨4024157620766158078934369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42924347954839019508633269 4024157620766158078934369)
          ·
            refine ⟨3018118215574618559200777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024157620766158078934369 3018118215574618559200777)
            ·
              refine ⟨2263588661680963919400583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3018118215574618559200777 2263588661680963919400583)
              ·
                refine ⟨3395382992521445879100875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263588661680963919400583 3395382992521445879100875)
                ·
                  refine ⟨5093074488782168818651313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395382992521445879100875 5093074488782168818651313)
                  ·
                    refine ⟨3819805866586626613988485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5093074488782168818651313 3819805866586626613988485)
                    ·
                      refine ⟨716213599984992490122841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3819805866586626613988485 716213599984992490122841)
                      ·
                        rfl

theorem cell23_1394821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_1394821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394821 prefixEnd_1394821 := by exact prefixLift 1394821
  have htrace : WordTrace (prefixWord ++ tailWord_1394821) baseStart_1394821 baseEnd_1394821 := by
    simpa [prefixWord, tailWord_1394821, baseEnd_1394821] using wordTrace_append hprefix tailTrace_1394821
  have hstable : (prefixWord ++ tailWord_1394821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394821).length < 2 ^ (prefixWord ++ tailWord_1394821).sum := by decide
  have hdescent : baseEnd_1394821 < baseStart_1394821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394842 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1394842 : Nat := 118140960795 + 1394842 * 2 ^ 59
def prefixEnd_1394842 : Nat := 4983230072969 + 3 ^ 40 * 1394842 * 2
def baseEnd_1394842 : Nat := 716224383078736907960245

theorem tailTrace_1394842 : CollatzResearch.WordTrace tailWord_1394842 prefixEnd_1394842 716224383078736907960245 := by
  unfold tailWord_1394842
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718516803183282223260695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33916044808488752595361853 12718516803183282223260695)
  ·
    refine ⟨19077775204774923334891043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12718516803183282223260695 19077775204774923334891043)
    ·
      refine ⟨28616662807162385002336565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19077775204774923334891043 28616662807162385002336565)
      ·
        refine ⟨2682812138171473593969053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28616662807162385002336565 2682812138171473593969053)
        ·
          refine ⟨1006054551814302597738395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2682812138171473593969053 1006054551814302597738395)
          ·
            refine ⟨1509081827721453896607593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006054551814302597738395 1509081827721453896607593)
            ·
              refine ⟨1131811370791090422455695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509081827721453896607593 1131811370791090422455695)
              ·
                refine ⟨1697717056186635633683543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131811370791090422455695 1697717056186635633683543)
                ·
                  refine ⟨2546575584279953450525315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697717056186635633683543 2546575584279953450525315)
                  ·
                    refine ⟨3819863376419930175787973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2546575584279953450525315 3819863376419930175787973)
                    ·
                      refine ⟨716224383078736907960245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3819863376419930175787973 716224383078736907960245)
                      ·
                        rfl

theorem cell23_1394842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1394842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394842 prefixEnd_1394842 := by exact prefixLift 1394842
  have htrace : WordTrace (prefixWord ++ tailWord_1394842) baseStart_1394842 baseEnd_1394842 := by
    simpa [prefixWord, tailWord_1394842, baseEnd_1394842] using wordTrace_append hprefix tailTrace_1394842
  have hstable : (prefixWord ++ tailWord_1394842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394842).length < 2 ^ (prefixWord ++ tailWord_1394842).sum := by decide
  have hdescent : baseEnd_1394842 < baseStart_1394842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394845 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_1394845 : Nat := 118140960795 + 1394845 * 2 ^ 59
def prefixEnd_1394845 : Nat := 4983230072969 + 3 ^ 40 * 1394845 * 2
def baseEnd_1394845 : Nat := 716225923520700396222731

theorem tailTrace_1394845 : CollatzResearch.WordTrace tailWord_1394845 prefixEnd_1394845 716225923520700396222731 := by
  unfold tailWord_1394845
  simp only [CollatzResearch.WordTrace]
  refine ⟨50874176631722260405401989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33916117754481506936934659 50874176631722260405401989)
  ·
    refine ⟨9538908118447923826012873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50874176631722260405401989 9538908118447923826012873)
    ·
      refine ⟨7154181088835942869509655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9538908118447923826012873 7154181088835942869509655)
      ·
        refine ⟨10731271633253914304264483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7154181088835942869509655 10731271633253914304264483)
        ·
          refine ⟨16096907449880871456396725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10731271633253914304264483 16096907449880871456396725)
          ·
            refine ⟨1509085073426331699037193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16096907449880871456396725 1509085073426331699037193)
            ·
              refine ⟨1131813805069748774277895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509085073426331699037193 1131813805069748774277895)
              ·
                refine ⟨1697720707604623161416843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131813805069748774277895 1697720707604623161416843)
                ·
                  refine ⟨2546581061406934742125265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697720707604623161416843 2546581061406934742125265)
                  ·
                    refine ⟨1909935796055201056593949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2546581061406934742125265 1909935796055201056593949)
                    ·
                      refine ⟨716225923520700396222731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1909935796055201056593949 716225923520700396222731)
                      ·
                        rfl

theorem cell23_1394845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_1394845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394845 prefixEnd_1394845 := by exact prefixLift 1394845
  have htrace : WordTrace (prefixWord ++ tailWord_1394845) baseStart_1394845 baseEnd_1394845 := by
    simpa [prefixWord, tailWord_1394845, baseEnd_1394845] using wordTrace_append hprefix tailTrace_1394845
  have hstable : (prefixWord ++ tailWord_1394845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394845).length < 2 ^ (prefixWord ++ tailWord_1394845).sum := by decide
  have hdescent : baseEnd_1394845 < baseStart_1394845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394874 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_1394874 : Nat := 118140960795 + 1394874 * 2 ^ 59
def prefixEnd_1394874 : Nat := 4983230072969 + 3 ^ 40 * 1394874 * 2
def baseEnd_1394874 : Nat := 238746938153226927586699

theorem tailTrace_1394874 : CollatzResearch.WordTrace tailWord_1394874 prefixEnd_1394874 238746938153226927586699 := by
  unfold tailWord_1394874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718808587154299589551919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33916822899078132238805117 12718808587154299589551919)
  ·
    refine ⟨19078212880731449384327879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12718808587154299589551919 19078212880731449384327879)
    ·
      refine ⟨28617319321097174076491819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19078212880731449384327879 28617319321097174076491819)
      ·
        refine ⟨42925978981645761114737729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28617319321097174076491819 42925978981645761114737729)
        ·
          refine ⟨32194484236234320836053297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42925978981645761114737729 32194484236234320836053297)
          ·
            refine ⟨24145863177175740627039973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32194484236234320836053297 24145863177175740627039973)
            ·
              refine ⟨4527349345720451367569995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24145863177175740627039973 4527349345720451367569995)
              ·
                refine ⟨6791024018580677051354993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527349345720451367569995 6791024018580677051354993)
                ·
                  refine ⟨5093268013935507788516245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6791024018580677051354993 5093268013935507788516245)
                  ·
                    refine ⟨238746938153226927586699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5093268013935507788516245 238746938153226927586699)
                    ·
                      rfl

theorem cell23_1394874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_1394874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394874 prefixEnd_1394874 := by exact prefixLift 1394874
  have htrace : WordTrace (prefixWord ++ tailWord_1394874) baseStart_1394874 baseEnd_1394874 := by
    simpa [prefixWord, tailWord_1394874, baseEnd_1394874] using wordTrace_append hprefix tailTrace_1394874
  have hstable : (prefixWord ++ tailWord_1394874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394874).length < 2 ^ (prefixWord ++ tailWord_1394874).sum := by decide
  have hdescent : baseEnd_1394874 < baseStart_1394874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394902 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_1394902 : Nat := 118140960795 + 1394902 * 2 ^ 59
def prefixEnd_1394902 : Nat := 4983230072969 + 3 ^ 40 * 1394902 * 2
def baseEnd_1394902 : Nat := 716255191918006673209969

theorem tailTrace_1394902 : CollatzResearch.WordTrace tailWord_1394902 prefixEnd_1394902 716255191918006673209969 := by
  unfold tailWord_1394902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179765974532234946264185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33917503728343839426817973 3179765974532234946264185)
  ·
    refine ⟨2384824480899176209698139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3179765974532234946264185 2384824480899176209698139)
    ·
      refine ⟨3577236721348764314547209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2384824480899176209698139 3577236721348764314547209)
      ·
        refine ⟨2682927541011573235910407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3577236721348764314547209 2682927541011573235910407)
        ·
          refine ⟨4024391311517359853865611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682927541011573235910407 4024391311517359853865611)
          ·
            refine ⟨6036586967276039780798417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024391311517359853865611 6036586967276039780798417)
            ·
              refine ⟨4527440225457029835598813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6036586967276039780798417 4527440225457029835598813)
              ·
                refine ⟨1697790084546386188349555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4527440225457029835598813 1697790084546386188349555)
                ·
                  refine ⟨2546685126819579282524333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697790084546386188349555 2546685126819579282524333)
                  ·
                    refine ⟨955006922557342230946625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2546685126819579282524333 955006922557342230946625)
                    ·
                      refine ⟨716255191918006673209969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955006922557342230946625 716255191918006673209969)
                      ·
                        rfl

theorem cell23_1394902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_1394902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394902 prefixEnd_1394902 := by exact prefixLift 1394902
  have htrace : WordTrace (prefixWord ++ tailWord_1394902) baseStart_1394902 baseEnd_1394902 := by
    simpa [prefixWord, tailWord_1394902, baseEnd_1394902] using wordTrace_append hprefix tailTrace_1394902
  have hstable : (prefixWord ++ tailWord_1394902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394902).length < 2 ^ (prefixWord ++ tailWord_1394902).sum := by decide
  have hdescent : baseEnd_1394902 < baseStart_1394902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394971 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 4]
def baseStart_1394971 : Nat := 118140960795 + 1394971 * 2 ^ 59
def prefixEnd_1394971 : Nat := 4983230072969 + 3 ^ 40 * 1394971 * 2
def baseEnd_1394971 : Nat := 716290622083166903247151

theorem tailTrace_1394971 : CollatzResearch.WordTrace tailWord_1394971 prefixEnd_1394971 716290622083166903247151 := by
  unfold tailWord_1394971
  simp only [CollatzResearch.WordTrace]
  refine ⟨50878772229265783924488767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33919181486177189282992511 50878772229265783924488767)
  ·
    refine ⟨76318158343898675886733151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50878772229265783924488767 76318158343898675886733151)
    ·
      refine ⟨114477237515848013830099727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76318158343898675886733151 114477237515848013830099727)
      ·
        refine ⟨171715856273772020745149591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114477237515848013830099727 171715856273772020745149591)
        ·
          refine ⟨257573784410658031117724387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171715856273772020745149591 257573784410658031117724387)
          ·
            refine ⟨386360676615987046676586581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257573784410658031117724387 386360676615987046676586581)
            ·
              refine ⟨4527664179093598203241249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 386360676615987046676586581 4527664179093598203241249)
              ·
                refine ⟨3395748134320198652430937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527664179093598203241249 3395748134320198652430937)
                ·
                  refine ⟨2546811100740148989323203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395748134320198652430937 2546811100740148989323203)
                  ·
                    refine ⟨3820216651110223483984805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2546811100740148989323203 3820216651110223483984805)
                    ·
                      refine ⟨716290622083166903247151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3820216651110223483984805 716290622083166903247151)
                      ·
                        rfl

theorem cell23_1394971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 4].length) (baseStart_1394971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394971 prefixEnd_1394971 := by exact prefixLift 1394971
  have htrace : WordTrace (prefixWord ++ tailWord_1394971) baseStart_1394971 baseEnd_1394971 := by
    simpa [prefixWord, tailWord_1394971, baseEnd_1394971] using wordTrace_append hprefix tailTrace_1394971
  have hstable : (prefixWord ++ tailWord_1394971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394971).length < 2 ^ (prefixWord ++ tailWord_1394971).sum := by decide
  have hdescent : baseEnd_1394971 < baseStart_1394971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1394991 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 3]
def baseStart_1394991 : Nat := 118140960795 + 1394991 * 2 ^ 59
def prefixEnd_1394991 : Nat := 4983230072969 + 3 ^ 40 * 1394991 * 2
def baseEnd_1394991 : Nat := 716300891696256824997059

theorem tailTrace_1394991 : CollatzResearch.WordTrace tailWord_1394991 prefixEnd_1394991 716300891696256824997059 := by
  unfold tailWord_1394991
  simp only [CollatzResearch.WordTrace]
  refine ⟨50879501689193327340216827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33919667792795551560144551 50879501689193327340216827)
  ·
    refine ⟨76319252533789991010325241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50879501689193327340216827 76319252533789991010325241)
    ·
      refine ⟨57239439400342493257743931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76319252533789991010325241 57239439400342493257743931)
      ·
        refine ⟨85859159100513739886615897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57239439400342493257743931 85859159100513739886615897)
        ·
          refine ⟨64394369325385304914961923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85859159100513739886615897 64394369325385304914961923)
          ·
            refine ⟨96591553988077957372442885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64394369325385304914961923 96591553988077957372442885)
            ·
              refine ⟨18110916372764617007333041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96591553988077957372442885 18110916372764617007333041)
              ·
                refine ⟨13583187279573462755499781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18110916372764617007333041 13583187279573462755499781)
                ·
                  refine ⟨2546847614920024266656209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13583187279573462755499781 2546847614920024266656209)
                  ·
                    refine ⟨1910135711190018199992157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2546847614920024266656209 1910135711190018199992157)
                    ·
                      refine ⟨716300891696256824997059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1910135711190018199992157 716300891696256824997059)
                      ·
                        rfl

theorem cell23_1394991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_1394991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1394991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1394991 prefixEnd_1394991 := by exact prefixLift 1394991
  have htrace : WordTrace (prefixWord ++ tailWord_1394991) baseStart_1394991 baseEnd_1394991 := by
    simpa [prefixWord, tailWord_1394991, baseEnd_1394991] using wordTrace_append hprefix tailTrace_1394991
  have hstable : (prefixWord ++ tailWord_1394991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1394991).length < 2 ^ (prefixWord ++ tailWord_1394991).sum := by decide
  have hdescent : baseEnd_1394991 < baseStart_1394991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1394991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395015 : List Nat := [1, 1, 4, 1, 2, 2, 4, 3, 1, 4]
def baseStart_1395015 : Nat := 118140960795 + 1395015 * 2 ^ 59
def prefixEnd_1395015 : Nat := 4983230072969 + 3 ^ 40 * 1395015 * 2
def baseEnd_1395015 : Nat := 238771071743988243698983

theorem tailTrace_1395015 : CollatzResearch.WordTrace tailWord_1395015 prefixEnd_1395015 238771071743988243698983 := by
  unfold tailWord_1395015
  simp only [CollatzResearch.WordTrace]
  refine ⟨50880377041106379439090499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33920251360737586292726999 50880377041106379439090499)
  ·
    refine ⟨76320565561659569158635749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50880377041106379439090499 76320565561659569158635749)
    ·
      refine ⟨14310106042811169217244203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76320565561659569158635749 14310106042811169217244203)
      ·
        refine ⟨21465159064216753825866305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14310106042811169217244203 21465159064216753825866305)
        ·
          refine ⟨16098869298162565369399729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21465159064216753825866305 16098869298162565369399729)
          ·
            refine ⟨12074151973621924027049797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16098869298162565369399729 12074151973621924027049797)
            ·
              refine ⟨2263903495054110755071837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12074151973621924027049797 2263903495054110755071837)
              ·
                refine ⟨848963810645291533151939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2263903495054110755071837 848963810645291533151939)
                ·
                  refine ⟨1273445715967937299727909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848963810645291533151939 1273445715967937299727909)
                  ·
                    refine ⟨238771071743988243698983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273445715967937299727909 238771071743988243698983)
                    ·
                      rfl

theorem cell23_1395015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_1395015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395015 prefixEnd_1395015 := by exact prefixLift 1395015
  have htrace : WordTrace (prefixWord ++ tailWord_1395015) baseStart_1395015 baseEnd_1395015 := by
    simpa [prefixWord, tailWord_1395015, baseEnd_1395015] using wordTrace_append hprefix tailTrace_1395015
  have hstable : (prefixWord ++ tailWord_1395015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395015).length < 2 ^ (prefixWord ++ tailWord_1395015).sum := by decide
  have hdescent : baseEnd_1395015 < baseStart_1395015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395028 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1395028 : Nat := 118140960795 + 1395028 * 2 ^ 59
def prefixEnd_1395028 : Nat := 4983230072969 + 3 ^ 40 * 1395028 * 2
def baseEnd_1395028 : Nat := 79591098942274797803821

theorem tailTrace_1395028 : CollatzResearch.WordTrace tailWord_1395028 prefixEnd_1395028 79591098942274797803821 := by
  unfold tailWord_1395028
  simp only [CollatzResearch.WordTrace]
  refine ⟨25440425595029641329656869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33920567460039521772875825 25440425595029641329656869)
  ·
    refine ⟨4770079799068057749310663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25440425595029641329656869 4770079799068057749310663)
    ·
      refine ⟨7155119698602086623965995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770079799068057749310663 7155119698602086623965995)
      ·
        refine ⟨10732679547903129935948993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7155119698602086623965995 10732679547903129935948993)
        ·
          refine ⟨8049509660927347451961745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10732679547903129935948993 8049509660927347451961745)
          ·
            refine ⟨6037132245695510588971309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8049509660927347451961745 6037132245695510588971309)
            ·
              refine ⟨2263924592135816470864241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6037132245695510588971309 2263924592135816470864241)
              ·
                refine ⟨1697943444101862353148181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2263924592135816470864241 1697943444101862353148181)
                ·
                  refine ⟨79591098942274797803821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1697943444101862353148181 79591098942274797803821)
                  ·
                    rfl

theorem cell23_1395028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1395028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395028 prefixEnd_1395028 := by exact prefixLift 1395028
  have htrace : WordTrace (prefixWord ++ tailWord_1395028) baseStart_1395028 baseEnd_1395028 := by
    simpa [prefixWord, tailWord_1395028, baseEnd_1395028] using wordTrace_append hprefix tailTrace_1395028
  have hstable : (prefixWord ++ tailWord_1395028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395028).length < 2 ^ (prefixWord ++ tailWord_1395028).sum := by decide
  have hdescent : baseEnd_1395028 < baseStart_1395028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395058 : List Nat := [3, 2, 1, 2, 1, 3, 1, 4, 1, 5]
def baseStart_1395058 : Nat := 118140960795 + 1395058 * 2 ^ 59
def prefixEnd_1395058 : Nat := 4983230072969 + 3 ^ 40 * 1395058 * 2
def baseEnd_1395058 : Nat := 238778431633369354286417

theorem tailTrace_1395058 : CollatzResearch.WordTrace tailWord_1395058 prefixEnd_1395058 238778431633369354286417 := by
  unfold tailWord_1395058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12720486344987649445726457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33921296919967065188603885 12720486344987649445726457)
  ·
    refine ⟨9540364758740737084294843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12720486344987649445726457 9540364758740737084294843)
    ·
      refine ⟨14310547138111105626442265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9540364758740737084294843 14310547138111105626442265)
      ·
        refine ⟨10732910353583329219831699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14310547138111105626442265 10732910353583329219831699)
        ·
          refine ⟨16099365530374993829747549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10732910353583329219831699 16099365530374993829747549)
          ·
            refine ⟨6037262073890622686155331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16099365530374993829747549 6037262073890622686155331)
            ·
              refine ⟨9055893110835934029232997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6037262073890622686155331 9055893110835934029232997)
              ·
                refine ⟨1697979958281737630481187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9055893110835934029232997 1697979958281737630481187)
                ·
                  refine ⟨2546969937422606445721781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1697979958281737630481187 2546969937422606445721781)
                  ·
                    refine ⟨238778431633369354286417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2546969937422606445721781 238778431633369354286417)
                    ·
                      rfl

theorem cell23_1395058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_1395058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395058 prefixEnd_1395058 := by exact prefixLift 1395058
  have htrace : WordTrace (prefixWord ++ tailWord_1395058) baseStart_1395058 baseEnd_1395058 := by
    simpa [prefixWord, tailWord_1395058, baseEnd_1395058] using wordTrace_append hprefix tailTrace_1395058
  have hstable : (prefixWord ++ tailWord_1395058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395058).length < 2 ^ (prefixWord ++ tailWord_1395058).sum := by decide
  have hdescent : baseEnd_1395058 < baseStart_1395058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395098 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1395098 : Nat := 118140960795 + 1395098 * 2 ^ 59
def prefixEnd_1395098 : Nat := 4983230072969 + 3 ^ 40 * 1395098 * 2
def baseEnd_1395098 : Nat := 716355834126287906359067

theorem tailTrace_1395098 : CollatzResearch.WordTrace tailWord_1395098 prefixEnd_1395098 716355834126287906359067 := by
  unfold tailWord_1395098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12720851074951421153590487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33922269533203789742907965 12720851074951421153590487)
  ·
    refine ⟨19081276612427131730385731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12720851074951421153590487 19081276612427131730385731)
    ·
      refine ⟨28621914918640697595578597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19081276612427131730385731 28621914918640697595578597)
      ·
        refine ⟨5366609047245130799170987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28621914918640697595578597 5366609047245130799170987)
        ·
          refine ⟨8049913570867696198756481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5366609047245130799170987 8049913570867696198756481)
          ·
            refine ⟨6037435178150772149067361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8049913570867696198756481 6037435178150772149067361)
            ·
              refine ⟨4528076383613079111800521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6037435178150772149067361 4528076383613079111800521)
              ·
                refine ⟨3396057287709809333850391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4528076383613079111800521 3396057287709809333850391)
                ·
                  refine ⟨5094085931564714000775587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396057287709809333850391 5094085931564714000775587)
                  ·
                    refine ⟨7641128897347071001163381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5094085931564714000775587 7641128897347071001163381)
                    ·
                      refine ⟨716355834126287906359067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7641128897347071001163381 716355834126287906359067)
                      ·
                        rfl

theorem cell23_1395098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1395098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395098 prefixEnd_1395098 := by exact prefixLift 1395098
  have htrace : WordTrace (prefixWord ++ tailWord_1395098) baseStart_1395098 baseEnd_1395098 := by
    simpa [prefixWord, tailWord_1395098, baseEnd_1395098] using wordTrace_append hprefix tailTrace_1395098
  have hstable : (prefixWord ++ tailWord_1395098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395098).length < 2 ^ (prefixWord ++ tailWord_1395098).sum := by decide
  have hdescent : baseEnd_1395098 < baseStart_1395098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395112 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1395112 : Nat := 118140960795 + 1395112 * 2 ^ 59
def prefixEnd_1395112 : Nat := 4983230072969 + 3 ^ 40 * 1395112 * 2
def baseEnd_1395112 : Nat := 716363022855450851584003

theorem tailTrace_1395112 : CollatzResearch.WordTrace tailWord_1395112 prefixEnd_1395112 716363022855450851584003 := by
  unfold tailWord_1395112
  simp only [CollatzResearch.WordTrace]
  refine ⟨25441957460877482502685795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33922609947836643336914393 25441957460877482502685795)
  ·
    refine ⟨38162936191316223754028693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25441957460877482502685795 38162936191316223754028693)
    ·
      refine ⟨1788887633967947988470095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38162936191316223754028693 1788887633967947988470095)
      ·
        refine ⟨2683331450951921982705143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1788887633967947988470095 2683331450951921982705143)
        ·
          refine ⟨4024997176427882974057715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683331450951921982705143 4024997176427882974057715)
          ·
            refine ⟨6037495764641824461086573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024997176427882974057715 6037495764641824461086573)
            ·
              refine ⟨2264060911740684172907465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6037495764641824461086573 2264060911740684172907465)
              ·
                refine ⟨1698045683805513129680599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264060911740684172907465 1698045683805513129680599)
                ·
                  refine ⟨2547068525708269694520899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698045683805513129680599 2547068525708269694520899)
                  ·
                    refine ⟨3820602788562404541781349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2547068525708269694520899 3820602788562404541781349)
                    ·
                      refine ⟨716363022855450851584003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3820602788562404541781349 716363022855450851584003)
                      ·
                        rfl

theorem cell23_1395112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1395112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395112 prefixEnd_1395112 := by exact prefixLift 1395112
  have htrace : WordTrace (prefixWord ++ tailWord_1395112) baseStart_1395112 baseEnd_1395112 := by
    simpa [prefixWord, tailWord_1395112, baseEnd_1395112] using wordTrace_append hprefix tailTrace_1395112
  have hstable : (prefixWord ++ tailWord_1395112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395112).length < 2 ^ (prefixWord ++ tailWord_1395112).sum := by decide
  have hdescent : baseEnd_1395112 < baseStart_1395112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395125 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1395125 : Nat := 118140960795 + 1395125 * 2 ^ 59
def prefixEnd_1395125 : Nat := 4983230072969 + 3 ^ 40 * 1395125 * 2
def baseEnd_1395125 : Nat := 716369698103959300721443

theorem tailTrace_1395125 : CollatzResearch.WordTrace tailWord_1395125 prefixEnd_1395125 716369698103959300721443 := by
  unfold tailWord_1395125
  simp only [CollatzResearch.WordTrace]
  refine ⟨50884389070707868225594829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33922926047138578817063219 50884389070707868225594829)
  ·
    refine ⟨19081645901515450584598061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50884389070707868225594829 19081645901515450584598061)
    ·
      refine ⟨7155617213068293969224273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19081645901515450584598061 7155617213068293969224273)
      ·
        refine ⟨5366712909801220476918205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7155617213068293969224273 5366712909801220476918205)
        ·
          refine ⟨2012517341175457678844327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5366712909801220476918205 2012517341175457678844327)
          ·
            refine ⟨3018776011763186518266491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012517341175457678844327 3018776011763186518266491)
            ·
              refine ⟨4528164017644779777399737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018776011763186518266491 4528164017644779777399737)
              ·
                refine ⟨3396123013233584833049803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4528164017644779777399737 3396123013233584833049803)
                ·
                  refine ⟨5094184519850377249574705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396123013233584833049803 5094184519850377249574705)
                  ·
                    refine ⟨3820638389887782937181029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094184519850377249574705 3820638389887782937181029)
                    ·
                      refine ⟨716369698103959300721443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3820638389887782937181029 716369698103959300721443)
                      ·
                        rfl

theorem cell23_1395125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1395125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395125 prefixEnd_1395125 := by exact prefixLift 1395125
  have htrace : WordTrace (prefixWord ++ tailWord_1395125) baseStart_1395125 baseEnd_1395125 := by
    simpa [prefixWord, tailWord_1395125, baseEnd_1395125] using wordTrace_append hprefix tailTrace_1395125
  have hstable : (prefixWord ++ tailWord_1395125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395125).length < 2 ^ (prefixWord ++ tailWord_1395125).sum := by decide
  have hdescent : baseEnd_1395125 < baseStart_1395125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395145 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 3]
def baseStart_1395145 : Nat := 118140960795 + 1395145 * 2 ^ 59
def prefixEnd_1395145 : Nat := 4983230072969 + 3 ^ 40 * 1395145 * 2
def baseEnd_1395145 : Nat := 716379967717049222471351

theorem tailTrace_1395145 : CollatzResearch.WordTrace tailWord_1395145 prefixEnd_1395145 716379967717049222471351 := by
  unfold tailWord_1395145
  simp only [CollatzResearch.WordTrace]
  refine ⟨50885118530635411641322889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33923412353756941094215259 50885118530635411641322889)
  ·
    refine ⟨38163838897976558730992167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50885118530635411641322889 38163838897976558730992167)
    ·
      refine ⟨57245758346964838096488251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38163838897976558730992167 57245758346964838096488251)
      ·
        refine ⟨85868637520447257144732377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57245758346964838096488251 85868637520447257144732377)
        ·
          refine ⟨64401478140335442858549283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85868637520447257144732377 64401478140335442858549283)
          ·
            refine ⟨96602217210503164287823925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64401478140335442858549283 96602217210503164287823925)
            ·
              refine ⟨9056457863484671651983493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96602217210503164287823925 9056457863484671651983493)
              ·
                refine ⟨1698085849403375934746905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9056457863484671651983493 1698085849403375934746905)
                ·
                  refine ⟨1273564387052531951060179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698085849403375934746905 1273564387052531951060179)
                  ·
                    refine ⟨1910346580578797926590269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273564387052531951060179 1910346580578797926590269)
                    ·
                      refine ⟨716379967717049222471351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1910346580578797926590269 716379967717049222471351)
                      ·
                        rfl

theorem cell23_1395145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 3].length) (baseStart_1395145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395145 prefixEnd_1395145 := by exact prefixLift 1395145
  have htrace : WordTrace (prefixWord ++ tailWord_1395145) baseStart_1395145 baseEnd_1395145 := by
    simpa [prefixWord, tailWord_1395145, baseEnd_1395145] using wordTrace_append hprefix tailTrace_1395145
  have hstable : (prefixWord ++ tailWord_1395145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395145).length < 2 ^ (prefixWord ++ tailWord_1395145).sum := by decide
  have hdescent : baseEnd_1395145 < baseStart_1395145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395185 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 1, 4, 2]
def baseStart_1395185 : Nat := 118140960795 + 1395185 * 2 ^ 59
def prefixEnd_1395185 : Nat := 4983230072969 + 3 ^ 40 * 1395185 * 2
def baseEnd_1395185 : Nat := 716400506943229065971167

theorem tailTrace_1395185 : CollatzResearch.WordTrace tailWord_1395185 prefixEnd_1395185 716400506943229065971167 := by
  unfold tailWord_1395185
  simp only [CollatzResearch.WordTrace]
  refine ⟨50886577450490498472779009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33924384966993665648519339 50886577450490498472779009)
  ·
    refine ⟨38164933087867873854584257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50886577450490498472779009 38164933087867873854584257)
    ·
      refine ⟨28623699815900905390938193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38164933087867873854584257 28623699815900905390938193)
      ·
        refine ⟨21467774861925679043203645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28623699815900905390938193 21467774861925679043203645)
        ·
          refine ⟨8050415573222129641201367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21467774861925679043203645 8050415573222129641201367)
          ·
            refine ⟨12075623359833194461802051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050415573222129641201367 12075623359833194461802051)
            ·
              refine ⟨18113435039749791692703077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12075623359833194461802051 18113435039749791692703077)
              ·
                refine ⟨3396269069953085942381827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18113435039749791692703077 3396269069953085942381827)
                ·
                  refine ⟨5094403604929628913572741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396269069953085942381827 5094403604929628913572741)
                  ·
                    refine ⟨955200675924305421294889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5094403604929628913572741 955200675924305421294889)
                    ·
                      refine ⟨716400506943229065971167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955200675924305421294889 716400506943229065971167)
                      ·
                        rfl

theorem cell23_1395185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_1395185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395185 prefixEnd_1395185 := by exact prefixLift 1395185
  have htrace : WordTrace (prefixWord ++ tailWord_1395185) baseStart_1395185 baseEnd_1395185 := by
    simpa [prefixWord, tailWord_1395185, baseEnd_1395185] using wordTrace_append hprefix tailTrace_1395185
  have hstable : (prefixWord ++ tailWord_1395185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395185).length < 2 ^ (prefixWord ++ tailWord_1395185).sum := by decide
  have hdescent : baseEnd_1395185 < baseStart_1395185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395213 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1395213 : Nat := 118140960795 + 1395213 * 2 ^ 59
def prefixEnd_1395213 : Nat := 4983230072969 + 3 ^ 40 * 1395213 * 2
def baseEnd_1395213 : Nat := 716414884401554956421039

theorem tailTrace_1395213 : CollatzResearch.WordTrace tailWord_1395213 prefixEnd_1395213 716414884401554956421039 := by
  unfold tailWord_1395213
  simp only [CollatzResearch.WordTrace]
  refine ⟨50887598694389059254798293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33925065796259372836532195 50887598694389059254798293)
  ·
    refine ⟨1192678094399743576284335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 50887598694389059254798293 1192678094399743576284335)
    ·
      refine ⟨1789017141599615364426503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1192678094399743576284335 1789017141599615364426503)
      ·
        refine ⟨2683525712399423046639755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789017141599615364426503 2683525712399423046639755)
        ·
          refine ⟨4025288568599134569959633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683525712399423046639755 4025288568599134569959633)
          ·
            refine ⟨3018966426449350927469725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4025288568599134569959633 3018966426449350927469725)
            ·
              refine ⟨1132112409918506597801147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3018966426449350927469725 1132112409918506597801147)
              ·
                refine ⟨1698168614877759896701721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132112409918506597801147 1698168614877759896701721)
                ·
                  refine ⟨1273626461158319922526291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698168614877759896701721 1273626461158319922526291)
                  ·
                    refine ⟨1910439691737479883789437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273626461158319922526291 1910439691737479883789437)
                    ·
                      refine ⟨716414884401554956421039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1910439691737479883789437 716414884401554956421039)
                      ·
                        rfl

theorem cell23_1395213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1395213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395213 prefixEnd_1395213 := by exact prefixLift 1395213
  have htrace : WordTrace (prefixWord ++ tailWord_1395213) baseStart_1395213 baseEnd_1395213 := by
    simpa [prefixWord, tailWord_1395213, baseEnd_1395213] using wordTrace_append hprefix tailTrace_1395213
  have hstable : (prefixWord ++ tailWord_1395213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395213).length < 2 ^ (prefixWord ++ tailWord_1395213).sum := by decide
  have hdescent : baseEnd_1395213 < baseStart_1395213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395219 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 2, 2, 2]
def baseStart_1395219 : Nat := 118140960795 + 1395219 * 2 ^ 59
def prefixEnd_1395219 : Nat := 4983230072969 + 3 ^ 40 * 1395219 * 2
def baseEnd_1395219 : Nat := 716417965285481932946011

theorem tailTrace_1395219 : CollatzResearch.WordTrace tailWord_1395219 prefixEnd_1395219 716417965285481932946011 := by
  unfold tailWord_1395219
  simp only [CollatzResearch.WordTrace]
  refine ⟨50887817532367322279516711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33925211688244881519677807 50887817532367322279516711)
  ·
    refine ⟨76331726298550983419275067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50887817532367322279516711 76331726298550983419275067)
    ·
      refine ⟨114497589447826475128912601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76331726298550983419275067 114497589447826475128912601)
      ·
        refine ⟨85873192085869856346684451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114497589447826475128912601 85873192085869856346684451)
        ·
          refine ⟨128809788128804784520026677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85873192085869856346684451 128809788128804784520026677)
          ·
            refine ⟨12075917637075448548752501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128809788128804784520026677 12075917637075448548752501)
            ·
              refine ⟨1132117278475823301445547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12075917637075448548752501 1132117278475823301445547)
              ·
                refine ⟨1698175917713734952168321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132117278475823301445547 1698175917713734952168321)
                ·
                  refine ⟨1273631938285301214126241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698175917713734952168321 1273631938285301214126241)
                  ·
                    refine ⟨955223953713975910594681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1273631938285301214126241 955223953713975910594681)
                    ·
                      refine ⟨716417965285481932946011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955223953713975910594681 716417965285481932946011)
                      ·
                        rfl

theorem cell23_1395219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 2, 2, 2].length) (baseStart_1395219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395219 prefixEnd_1395219 := by exact prefixLift 1395219
  have htrace : WordTrace (prefixWord ++ tailWord_1395219) baseStart_1395219 baseEnd_1395219 := by
    simpa [prefixWord, tailWord_1395219, baseEnd_1395219] using wordTrace_append hprefix tailTrace_1395219
  have hstable : (prefixWord ++ tailWord_1395219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395219).length < 2 ^ (prefixWord ++ tailWord_1395219).sum := by decide
  have hdescent : baseEnd_1395219 < baseStart_1395219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395242 : List Nat := [3, 1, 4, 1, 1, 2, 3, 3, 5]
def baseStart_1395242 : Nat := 118140960795 + 1395242 * 2 ^ 59
def prefixEnd_1395242 : Nat := 4983230072969 + 3 ^ 40 * 1395242 * 2
def baseEnd_1395242 : Nat := 79603308371170593662045

theorem tailTrace_1395242 : CollatzResearch.WordTrace tailWord_1395242 prefixEnd_1395242 79603308371170593662045 := by
  unfold tailWord_1395242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722164102820999301900995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33925770940855998138402653 12722164102820999301900995)
  ·
    refine ⟨19083246154231498952851493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12722164102820999301900995 19083246154231498952851493)
    ·
      refine ⟨3578108653918406053659655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19083246154231498952851493 3578108653918406053659655)
      ·
        refine ⟨5367162980877609080489483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578108653918406053659655 5367162980877609080489483)
        ·
          refine ⟨8050744471316413620734225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367162980877609080489483 8050744471316413620734225)
          ·
            refine ⟨6038058353487310215550669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8050744471316413620734225 6038058353487310215550669)
            ·
              refine ⟨2264271882557741330831501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6038058353487310215550669 2264271882557741330831501)
              ·
                refine ⟨849101955959152999061813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264271882557741330831501 849101955959152999061813)
                ·
                  refine ⟨79603308371170593662045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 849101955959152999061813 79603308371170593662045)
                  ·
                    rfl

theorem cell23_1395242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_1395242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395242 prefixEnd_1395242 := by exact prefixLift 1395242
  have htrace : WordTrace (prefixWord ++ tailWord_1395242) baseStart_1395242 baseEnd_1395242 := by
    simpa [prefixWord, tailWord_1395242, baseEnd_1395242] using wordTrace_append hprefix tailTrace_1395242
  have hstable : (prefixWord ++ tailWord_1395242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395242).length < 2 ^ (prefixWord ++ tailWord_1395242).sum := by decide
  have hdescent : baseEnd_1395242 < baseStart_1395242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395265 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1395265 : Nat := 118140960795 + 1395265 * 2 ^ 59
def prefixEnd_1395265 : Nat := 4983230072969 + 3 ^ 40 * 1395265 * 2
def baseEnd_1395265 : Nat := 716441585395588752970799

theorem tailTrace_1395265 : CollatzResearch.WordTrace tailWord_1395265 prefixEnd_1395265 716441585395588752970799 := by
  unfold tailWord_1395265
  simp only [CollatzResearch.WordTrace]
  refine ⟨50889495290200672135691249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33926330193467114757127499 50889495290200672135691249)
  ·
    refine ⟨38167121467650504101768437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50889495290200672135691249 38167121467650504101768437)
    ·
      refine ⟨3578167637592234759540791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38167121467650504101768437 3578167637592234759540791)
      ·
        refine ⟨5367251456388352139311187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578167637592234759540791 5367251456388352139311187)
        ·
          refine ⟨8050877184582528208966781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367251456388352139311187 8050877184582528208966781)
          ·
            refine ⟨3019078944218448078362543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8050877184582528208966781 3019078944218448078362543)
            ·
              refine ⟨4528618416327672117543815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019078944218448078362543 4528618416327672117543815)
              ·
                refine ⟨6792927624491508176315723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528618416327672117543815 6792927624491508176315723)
                ·
                  refine ⟨10189391436737262264473585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792927624491508176315723 10189391436737262264473585)
                  ·
                    refine ⟨7642043577552946698355189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10189391436737262264473585 7642043577552946698355189)
                    ·
                      refine ⟨716441585395588752970799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7642043577552946698355189 716441585395588752970799)
                      ·
                        rfl

theorem cell23_1395265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1395265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395265 prefixEnd_1395265 := by exact prefixLift 1395265
  have htrace : WordTrace (prefixWord ++ tailWord_1395265) baseStart_1395265 baseEnd_1395265 := by
    simpa [prefixWord, tailWord_1395265, baseEnd_1395265] using wordTrace_append hprefix tailTrace_1395265
  have hstable : (prefixWord ++ tailWord_1395265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395265).length < 2 ^ (prefixWord ++ tailWord_1395265).sum := by decide
  have hdescent : baseEnd_1395265 < baseStart_1395265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395270 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1395270 : Nat := 118140960795 + 1395270 * 2 ^ 59
def prefixEnd_1395270 : Nat := 4983230072969 + 3 ^ 40 * 1395270 * 2
def baseEnd_1395270 : Nat := 716444152798861233408277

theorem tailTrace_1395270 : CollatzResearch.WordTrace tailWord_1395270 prefixEnd_1395270 716444152798861233408277 := by
  unfold tailWord_1395270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590302426724454937175727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33926451770121705326415509 1590302426724454937175727)
  ·
    refine ⟨2385453640086682405763591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1590302426724454937175727 2385453640086682405763591)
    ·
      refine ⟨3578180460130023608645387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2385453640086682405763591 3578180460130023608645387)
      ·
        refine ⟨5367270690195035412968081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578180460130023608645387 5367270690195035412968081)
        ·
          refine ⟨4025453017646276559726061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5367270690195035412968081 4025453017646276559726061)
          ·
            refine ⟨1509544881617353709897273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4025453017646276559726061 1509544881617353709897273)
            ·
              refine ⟨1132158661213015282422955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509544881617353709897273 1132158661213015282422955)
              ·
                refine ⟨1698237991819522923634433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132158661213015282422955 1698237991819522923634433)
                ·
                  refine ⟨1273678493864642192725825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698237991819522923634433 1273678493864642192725825)
                  ·
                    refine ⟨955258870398481644544369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1273678493864642192725825 955258870398481644544369)
                    ·
                      refine ⟨716444152798861233408277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955258870398481644544369 716444152798861233408277)
                      ·
                        rfl

theorem cell23_1395270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1395270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395270 prefixEnd_1395270 := by exact prefixLift 1395270
  have htrace : WordTrace (prefixWord ++ tailWord_1395270) baseStart_1395270 baseEnd_1395270 := by
    simpa [prefixWord, tailWord_1395270, baseEnd_1395270] using wordTrace_append hprefix tailTrace_1395270
  have hstable : (prefixWord ++ tailWord_1395270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395270).length < 2 ^ (prefixWord ++ tailWord_1395270).sum := by decide
  have hdescent : baseEnd_1395270 < baseStart_1395270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395275 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 2, 4, 2]
def baseStart_1395275 : Nat := 118140960795 + 1395275 * 2 ^ 59
def prefixEnd_1395275 : Nat := 4983230072969 + 3 ^ 40 * 1395275 * 2
def baseEnd_1395275 : Nat := 716446720202133713845753

theorem tailTrace_1395275 : CollatzResearch.WordTrace tailWord_1395275 prefixEnd_1395275 716446720202133713845753 := by
  unfold tailWord_1395275
  simp only [CollatzResearch.WordTrace]
  refine ⟨50889860020164443843555279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33926573346776295895703519 50889860020164443843555279)
  ·
    refine ⟨76334790030246665765332919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50889860020164443843555279 76334790030246665765332919)
    ·
      refine ⟨114502185045369998647999379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76334790030246665765332919 114502185045369998647999379)
      ·
        refine ⟨171753277568054997971999069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114502185045369998647999379 171753277568054997971999069)
        ·
          refine ⟨64407479088020624239499651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171753277568054997971999069 64407479088020624239499651)
          ·
            refine ⟨96611218632030936359249477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64407479088020624239499651 96611218632030936359249477)
            ·
              refine ⟨18114603493505800567359277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96611218632030936359249477 18114603493505800567359277)
              ·
                refine ⟨6792976310064675212759729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18114603493505800567359277 6792976310064675212759729)
                ·
                  refine ⟨5094732232548506409569797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792976310064675212759729 5094732232548506409569797)
                  ·
                    refine ⟨955262293602844951794337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5094732232548506409569797 955262293602844951794337)
                    ·
                      refine ⟨716446720202133713845753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955262293602844951794337 716446720202133713845753)
                      ·
                        rfl

theorem cell23_1395275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4, 2].length) (baseStart_1395275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395275 prefixEnd_1395275 := by exact prefixLift 1395275
  have htrace : WordTrace (prefixWord ++ tailWord_1395275) baseStart_1395275 baseEnd_1395275 := by
    simpa [prefixWord, tailWord_1395275, baseEnd_1395275] using wordTrace_append hprefix tailTrace_1395275
  have hstable : (prefixWord ++ tailWord_1395275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395275).length < 2 ^ (prefixWord ++ tailWord_1395275).sum := by decide
  have hdescent : baseEnd_1395275 < baseStart_1395275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395285 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_1395285 : Nat := 118140960795 + 1395285 * 2 ^ 59
def prefixEnd_1395285 : Nat := 4983230072969 + 3 ^ 40 * 1395285 * 2
def baseEnd_1395285 : Nat := 238817285002892891573569

theorem tailTrace_1395285 : CollatzResearch.WordTrace tailWord_1395285 prefixEnd_1395285 238817285002892891573569 := by
  unfold tailWord_1395285
  simp only [CollatzResearch.WordTrace]
  refine ⟨50890224750128215551419309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33926816500085477034279539 50890224750128215551419309)
  ·
    refine ⟨19083834281298080831782241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50890224750128215551419309 19083834281298080831782241)
    ·
      refine ⟨14312875710973560623836681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19083834281298080831782241 14312875710973560623836681)
      ·
        refine ⟨10734656783230170467877511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14312875710973560623836681 10734656783230170467877511)
        ·
          refine ⟨16101985174845255701816267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734656783230170467877511 16101985174845255701816267)
          ·
            refine ⟨24152977762267883552724401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16101985174845255701816267 24152977762267883552724401)
            ·
              refine ⟨18114733321700912664543301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24152977762267883552724401 18114733321700912664543301)
              ·
                refine ⟨3396512497818921124601869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18114733321700912664543301 3396512497818921124601869)
                ·
                  refine ⟨1273692186682095421725701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3396512497818921124601869 1273692186682095421725701)
                  ·
                    refine ⟨238817285002892891573569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273692186682095421725701 238817285002892891573569)
                    ·
                      rfl

theorem cell23_1395285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_1395285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395285 prefixEnd_1395285 := by exact prefixLift 1395285
  have htrace : WordTrace (prefixWord ++ tailWord_1395285) baseStart_1395285 baseEnd_1395285 := by
    simpa [prefixWord, tailWord_1395285, baseEnd_1395285] using wordTrace_append hprefix tailTrace_1395285
  have hstable : (prefixWord ++ tailWord_1395285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395285).length < 2 ^ (prefixWord ++ tailWord_1395285).sum := by decide
  have hdescent : baseEnd_1395285 < baseStart_1395285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395288 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1395288 : Nat := 118140960795 + 1395288 * 2 ^ 59
def prefixEnd_1395288 : Nat := 4983230072969 + 3 ^ 40 * 1395288 * 2
def baseEnd_1395288 : Nat := 716453395450642162983193

theorem tailTrace_1395288 : CollatzResearch.WordTrace tailWord_1395288 prefixEnd_1395288 716453395450642162983193 := by
  unfold tailWord_1395288
  simp only [CollatzResearch.WordTrace]
  refine ⟨25445167084558673531889259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33926889446078231375852345 25445167084558673531889259)
  ·
    refine ⟨38167750626838010297833889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25445167084558673531889259 38167750626838010297833889)
    ·
      refine ⟨28625812970128507723375417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38167750626838010297833889 28625812970128507723375417)
      ·
        refine ⟨21469359727596380792531563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28625812970128507723375417 21469359727596380792531563)
        ·
          refine ⟨32204039591394571188797345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21469359727596380792531563 32204039591394571188797345)
          ·
            refine ⟨24153029693545928391598009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32204039591394571188797345 24153029693545928391598009)
            ·
              refine ⟨18114772270159446293698507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24153029693545928391598009 18114772270159446293698507)
              ·
                refine ⟨27172158405239169440547761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18114772270159446293698507 27172158405239169440547761)
                ·
                  refine ⟨20379118803929377080410821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27172158405239169440547761 20379118803929377080410821)
                  ·
                    refine ⟨3821084775736758202577029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20379118803929377080410821 3821084775736758202577029)
                    ·
                      refine ⟨716453395450642162983193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3821084775736758202577029 716453395450642162983193)
                      ·
                        rfl

theorem cell23_1395288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1395288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395288 prefixEnd_1395288 := by exact prefixLift 1395288
  have htrace : WordTrace (prefixWord ++ tailWord_1395288) baseStart_1395288 baseEnd_1395288 := by
    simpa [prefixWord, tailWord_1395288, baseEnd_1395288] using wordTrace_append hprefix tailTrace_1395288
  have hstable : (prefixWord ++ tailWord_1395288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395288).length < 2 ^ (prefixWord ++ tailWord_1395288).sum := by decide
  have hdescent : baseEnd_1395288 < baseStart_1395288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395319 : List Nat := [1, 1, 3, 1, 1, 3, 6, 2, 1, 4]
def baseStart_1395319 : Nat := 118140960795 + 1395319 * 2 ^ 59
def prefixEnd_1395319 : Nat := 4983230072969 + 3 ^ 40 * 1395319 * 2
def baseEnd_1395319 : Nat := 238823104450310513898517

theorem tailTrace_1395319 : CollatzResearch.WordTrace tailWord_1395319 prefixEnd_1395319 238823104450310513898517 := by
  unfold tailWord_1395319
  simp only [CollatzResearch.WordTrace]
  refine ⟨50891464832005039358157011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33927643221336692905438007 50891464832005039358157011)
  ·
    refine ⟨76337197248007559037235517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50891464832005039358157011 76337197248007559037235517)
    ·
      refine ⟨28626448968002834638963319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76337197248007559037235517 28626448968002834638963319)
      ·
        refine ⟨42939673452004251958444979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28626448968002834638963319 42939673452004251958444979)
        ·
          refine ⟨64409510178006377937667469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42939673452004251958444979 64409510178006377937667469)
          ·
            refine ⟨24153566316752391726625301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64409510178006377937667469 24153566316752391726625301)
            ·
              refine ⟨1132198421097768362185561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24153566316752391726625301 1132198421097768362185561)
              ·
                refine ⟨849148815823326271639171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132198421097768362185561 849148815823326271639171)
                ·
                  refine ⟨1273723223734989407458757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849148815823326271639171 1273723223734989407458757)
                  ·
                    refine ⟨238823104450310513898517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1273723223734989407458757 238823104450310513898517)
                    ·
                      rfl

theorem cell23_1395319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_1395319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395319 prefixEnd_1395319 := by exact prefixLift 1395319
  have htrace : WordTrace (prefixWord ++ tailWord_1395319) baseStart_1395319 baseEnd_1395319 := by
    simpa [prefixWord, tailWord_1395319, baseEnd_1395319] using wordTrace_append hprefix tailTrace_1395319
  have hstable : (prefixWord ++ tailWord_1395319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395319).length < 2 ^ (prefixWord ++ tailWord_1395319).sum := by decide
  have hdescent : baseEnd_1395319 < baseStart_1395319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395352 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1395352 : Nat := 118140960795 + 1395352 * 2 ^ 59
def prefixEnd_1395352 : Nat := 4983230072969 + 3 ^ 40 * 1395352 * 2
def baseEnd_1395352 : Nat := 716486258212529912582899

theorem tailTrace_1395352 : CollatzResearch.WordTrace tailWord_1395352 prefixEnd_1395352 716486258212529912582899 := by
  unfold tailWord_1395352
  simp only [CollatzResearch.WordTrace]
  refine ⟨25446334220442742997054155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33928445627256990662738873 25446334220442742997054155)
  ·
    refine ⟨38169501330664114495581233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25446334220442742997054155 38169501330664114495581233)
    ·
      refine ⟨28627125997998085871685925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38169501330664114495581233 28627125997998085871685925)
      ·
        refine ⟨5367586124624641100941111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28627125997998085871685925 5367586124624641100941111)
        ·
          refine ⟨8051379186936961651411667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367586124624641100941111 8051379186936961651411667)
          ·
            refine ⟨12077068780405442477117501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8051379186936961651411667 12077068780405442477117501)
            ·
              refine ⟨4528900792652040928919063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12077068780405442477117501 4528900792652040928919063)
              ·
                refine ⟨6793351188978061393378595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528900792652040928919063 6793351188978061393378595)
                ·
                  refine ⟨10190026783467092090067893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6793351188978061393378595 10190026783467092090067893)
                  ·
                    refine ⟨955315010950039883443865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10190026783467092090067893 955315010950039883443865)
                    ·
                      refine ⟨716486258212529912582899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955315010950039883443865 716486258212529912582899)
                      ·
                        rfl

theorem cell23_1395352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1395352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395352 prefixEnd_1395352 := by exact prefixLift 1395352
  have htrace : WordTrace (prefixWord ++ tailWord_1395352) baseStart_1395352 baseEnd_1395352 := by
    simpa [prefixWord, tailWord_1395352, baseEnd_1395352] using wordTrace_append hprefix tailTrace_1395352
  have hstable : (prefixWord ++ tailWord_1395352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395352).length < 2 ^ (prefixWord ++ tailWord_1395352).sum := by decide
  have hdescent : baseEnd_1395352 < baseStart_1395352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395392 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 1, 6]
def baseStart_1395392 : Nat := 118140960795 + 1395392 * 2 ^ 59
def prefixEnd_1395392 : Nat := 4983230072969 + 3 ^ 40 * 1395392 * 2
def baseEnd_1395392 : Nat := 238835599146236585360905

theorem tailTrace_1395392 : CollatzResearch.WordTrace tailWord_1395392 prefixEnd_1395392 238835599146236585360905 := by
  unfold tailWord_1395392
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447063680370286412782215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33929418240493715217042953 25447063680370286412782215)
  ·
    refine ⟨38170595520555429619173323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25447063680370286412782215 38170595520555429619173323)
    ·
      refine ⟨57255893280833144428759985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38170595520555429619173323 57255893280833144428759985)
      ·
        refine ⟨42941919960624858321569989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57255893280833144428759985 42941919960624858321569989)
        ·
          refine ⟨8051609992617160935294373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42941919960624858321569989 8051609992617160935294373)
          ·
            refine ⟨1509676873615717675367695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8051609992617160935294373 1509676873615717675367695)
            ·
              refine ⟨2264515310423576513051543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509676873615717675367695 2264515310423576513051543)
              ·
                refine ⟨3396772965635364769577315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264515310423576513051543 3396772965635364769577315)
                ·
                  refine ⟨5095159448453047154365973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396772965635364769577315 5095159448453047154365973)
                  ·
                    refine ⟨238835599146236585360905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5095159448453047154365973 238835599146236585360905)
                    ·
                      rfl

theorem cell23_1395392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_1395392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395392 prefixEnd_1395392 := by exact prefixLift 1395392
  have htrace : WordTrace (prefixWord ++ tailWord_1395392) baseStart_1395392 baseEnd_1395392 := by
    simpa [prefixWord, tailWord_1395392, baseEnd_1395392] using wordTrace_append hprefix tailTrace_1395392
  have hstable : (prefixWord ++ tailWord_1395392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395392).length < 2 ^ (prefixWord ++ tailWord_1395392).sum := by decide
  have hdescent : baseEnd_1395392 < baseStart_1395392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395410 : List Nat := [3, 2, 2, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_1395410 : Nat := 118140960795 + 1395410 * 2 ^ 59
def prefixEnd_1395410 : Nat := 4983230072969 + 3 ^ 40 * 1395410 * 2
def baseEnd_1395410 : Nat := 716516040090490685657633

theorem tailTrace_1395410 : CollatzResearch.WordTrace tailWord_1395410 prefixEnd_1395410 716516040090490685657633 := by
  unfold tailWord_1395410
  simp only [CollatzResearch.WordTrace]
  refine ⟨12723695968668840474929921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33929855916450241266479789 12723695968668840474929921)
  ·
    refine ⟨9542771976501630356197441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12723695968668840474929921 9542771976501630356197441)
    ·
      refine ⟨7157078982376222767148081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9542771976501630356197441 7157078982376222767148081)
      ·
        refine ⟨5367809236782167075361061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7157078982376222767148081 5367809236782167075361061)
        ·
          refine ⟨1006464231896656326630199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5367809236782167075361061 1006464231896656326630199)
          ·
            refine ⟨1509696347844984489945299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006464231896656326630199 1509696347844984489945299)
            ·
              refine ⟨2264544521767476734917949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509696347844984489945299 2264544521767476734917949)
              ·
                refine ⟨849204195662803775594231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264544521767476734917949 849204195662803775594231)
                ·
                  refine ⟨1273806293494205663391347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849204195662803775594231 1273806293494205663391347)
                  ·
                    refine ⟨1910709440241308495087021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1273806293494205663391347 1910709440241308495087021)
                    ·
                      refine ⟨716516040090490685657633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1910709440241308495087021 716516040090490685657633)
                      ·
                        rfl

theorem cell23_1395410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_1395410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395410 prefixEnd_1395410 := by exact prefixLift 1395410
  have htrace : WordTrace (prefixWord ++ tailWord_1395410) baseStart_1395410 baseEnd_1395410 := by
    simpa [prefixWord, tailWord_1395410, baseEnd_1395410] using wordTrace_append hprefix tailTrace_1395410
  have hstable : (prefixWord ++ tailWord_1395410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395410).length < 2 ^ (prefixWord ++ tailWord_1395410).sum := by decide
  have hdescent : baseEnd_1395410 < baseStart_1395410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395475 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5]
def baseStart_1395475 : Nat := 118140960795 + 1395475 * 2 ^ 59
def prefixEnd_1395475 : Nat := 4983230072969 + 3 ^ 40 * 1395475 * 2
def baseEnd_1395475 : Nat := 716549416333032931344833

theorem tailTrace_1395475 : CollatzResearch.WordTrace tailWord_1395475 prefixEnd_1395475 716549416333032931344833 := by
  unfold tailWord_1395475
  simp only [CollatzResearch.WordTrace]
  refine ⟨50897154619439878000835879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33931436412959918667223919 50897154619439878000835879)
  ·
    refine ⟨76345731929159817001253819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50897154619439878000835879 76345731929159817001253819)
    ·
      refine ⟨114518597893739725501880729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76345731929159817001253819 114518597893739725501880729)
      ·
        refine ⟨85888948420304794126410547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114518597893739725501880729 85888948420304794126410547)
        ·
          refine ⟨128833422630457191189615821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85888948420304794126410547 128833422630457191189615821)
          ·
            refine ⟨48312533486421446696105933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128833422630457191189615821 48312533486421446696105933)
            ·
              refine ⟨18117200057408042511039725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48312533486421446696105933 18117200057408042511039725)
              ·
                refine ⟨6793950021528015941639897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18117200057408042511039725 6793950021528015941639897)
                ·
                  refine ⟨5095462516146011956229923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793950021528015941639897 5095462516146011956229923)
                  ·
                    refine ⟨7643193774219017934344885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5095462516146011956229923 7643193774219017934344885)
                    ·
                      refine ⟨716549416333032931344833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7643193774219017934344885 716549416333032931344833)
                      ·
                        rfl

theorem cell23_1395475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_1395475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395475 prefixEnd_1395475 := by exact prefixLift 1395475
  have htrace : WordTrace (prefixWord ++ tailWord_1395475) baseStart_1395475 baseEnd_1395475 := by
    simpa [prefixWord, tailWord_1395475, baseEnd_1395475] using wordTrace_append hprefix tailTrace_1395475
  have hstable : (prefixWord ++ tailWord_1395475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395475).length < 2 ^ (prefixWord ++ tailWord_1395475).sum := by decide
  have hdescent : baseEnd_1395475 < baseStart_1395475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395506 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_1395506 : Nat := 118140960795 + 1395506 * 2 ^ 59
def prefixEnd_1395506 : Nat := 4983230072969 + 3 ^ 40 * 1395506 * 2
def baseEnd_1395506 : Nat := 716565334233322310057191

theorem tailTrace_1395506 : CollatzResearch.WordTrace tailWord_1395506 prefixEnd_1395506 716565334233322310057191 := by
  unfold tailWord_1395506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12724571320581892573803593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33932190188218380196809581 12724571320581892573803593)
  ·
    refine ⟨9543428490436419430352695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12724571320581892573803593 9543428490436419430352695)
    ·
      refine ⟨14315142735654629145529043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9543428490436419430352695 14315142735654629145529043)
      ·
        refine ⟨21472714103481943718293565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14315142735654629145529043 21472714103481943718293565)
        ·
          refine ⟨8052267788805728894360087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21472714103481943718293565 8052267788805728894360087)
          ·
            refine ⟨12078401683208593341540131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8052267788805728894360087 12078401683208593341540131)
            ·
              refine ⟨18117602524812890012310197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12078401683208593341540131 18117602524812890012310197)
              ·
                refine ⟨1698525236701208438654081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18117602524812890012310197 1698525236701208438654081)
                ·
                  refine ⟨1273893927525906328990561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698525236701208438654081 1273893927525906328990561)
                  ·
                    refine ⟨955420445644429746742921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1273893927525906328990561 955420445644429746742921)
                    ·
                      refine ⟨716565334233322310057191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955420445644429746742921 716565334233322310057191)
                      ·
                        rfl

theorem cell23_1395506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_1395506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395506 prefixEnd_1395506 := by exact prefixLift 1395506
  have htrace : WordTrace (prefixWord ++ tailWord_1395506) baseStart_1395506 baseEnd_1395506 := by
    simpa [prefixWord, tailWord_1395506, baseEnd_1395506] using wordTrace_append hprefix tailTrace_1395506
  have hstable : (prefixWord ++ tailWord_1395506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395506).length < 2 ^ (prefixWord ++ tailWord_1395506).sum := by decide
  have hdescent : baseEnd_1395506 < baseStart_1395506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395529 : List Nat := [1, 2, 1, 1, 2, 6, 2, 3, 5]
def baseStart_1395529 : Nat := 118140960795 + 1395529 * 2 ^ 59
def prefixEnd_1395529 : Nat := 4983230072969 + 3 ^ 40 * 1395529 * 2
def baseEnd_1395529 : Nat := 79619682698708413341065

theorem tailTrace_1395529 : CollatzResearch.WordTrace tailWord_1395529 prefixEnd_1395529 79619682698708413341065 := by
  unfold tailWord_1395529
  simp only [CollatzResearch.WordTrace]
  refine ⟨50899124161244245223301641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33932749440829496815534427 50899124161244245223301641)
  ·
    refine ⟨38174343120933183917476231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50899124161244245223301641 38174343120933183917476231)
    ·
      refine ⟨57261514681399775876214347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38174343120933183917476231 57261514681399775876214347)
      ·
        refine ⟨85892272022099663814321521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57261514681399775876214347 85892272022099663814321521)
        ·
          refine ⟨64419204016574747860741141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85892272022099663814321521 64419204016574747860741141)
          ·
            refine ⟨3019650188276941305972241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64419204016574747860741141 3019650188276941305972241)
            ·
              refine ⟨2264737641207705979479181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019650188276941305972241 2264737641207705979479181)
              ·
                refine ⟨849276615452889742304693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264737641207705979479181 849276615452889742304693)
                ·
                  refine ⟨79619682698708413341065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 849276615452889742304693 79619682698708413341065)
                  ·
                    rfl

theorem cell23_1395529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 5].length) (baseStart_1395529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395529 prefixEnd_1395529 := by exact prefixLift 1395529
  have htrace : WordTrace (prefixWord ++ tailWord_1395529) baseStart_1395529 baseEnd_1395529 := by
    simpa [prefixWord, tailWord_1395529, baseEnd_1395529] using wordTrace_append hprefix tailTrace_1395529
  have hstable : (prefixWord ++ tailWord_1395529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395529).length < 2 ^ (prefixWord ++ tailWord_1395529).sum := by decide
  have hdescent : baseEnd_1395529 < baseStart_1395529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395540 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_1395540 : Nat := 118140960795 + 1395540 * 2 ^ 59
def prefixEnd_1395540 : Nat := 4983230072969 + 3 ^ 40 * 1395540 * 2
def baseEnd_1395540 : Nat := 716582792575575177032035

theorem tailTrace_1395540 : CollatzResearch.WordTrace tailWord_1395540 prefixEnd_1395540 716582792575575177032035 := by
  unfold tailWord_1395540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25449762682102197050976037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33933016909469596067968049 25449762682102197050976037)
  ·
    refine ⟨4771830502894161947058007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25449762682102197050976037 4771830502894161947058007)
    ·
      refine ⟨7157745754341242920587011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771830502894161947058007 7157745754341242920587011)
      ·
        refine ⟨10736618631511864380880517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157745754341242920587011 10736618631511864380880517)
        ·
          refine ⟨2013115993408474571415097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10736618631511864380880517 2013115993408474571415097)
          ·
            refine ⟨1509836995056355928561323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2013115993408474571415097 1509836995056355928561323)
            ·
              refine ⟨2264755492584533892841985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509836995056355928561323 2264755492584533892841985)
              ·
                refine ⟨1698566619438400419631489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2264755492584533892841985 1698566619438400419631489)
                ·
                  refine ⟨1273924964578800314723617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698566619438400419631489 1273924964578800314723617)
                  ·
                    refine ⟨955443723434100236042713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1273924964578800314723617 955443723434100236042713)
                    ·
                      refine ⟨716582792575575177032035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955443723434100236042713 716582792575575177032035)
                      ·
                        rfl

theorem cell23_1395540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_1395540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395540 prefixEnd_1395540 := by exact prefixLift 1395540
  have htrace : WordTrace (prefixWord ++ tailWord_1395540) baseStart_1395540 baseEnd_1395540 := by
    simpa [prefixWord, tailWord_1395540, baseEnd_1395540] using wordTrace_append hprefix tailTrace_1395540
  have hstable : (prefixWord ++ tailWord_1395540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395540).length < 2 ^ (prefixWord ++ tailWord_1395540).sum := by decide
  have hdescent : baseEnd_1395540 < baseStart_1395540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395619 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 6]
def baseStart_1395619 : Nat := 118140960795 + 1395619 * 2 ^ 59
def prefixEnd_1395619 : Nat := 4983230072969 + 3 ^ 40 * 1395619 * 2
def baseEnd_1395619 : Nat := 79624817505253374216019

theorem tailTrace_1395619 : CollatzResearch.WordTrace tailWord_1395619 prefixEnd_1395619 79624817505253374216019 := by
  unfold tailWord_1395619
  simp only [CollatzResearch.WordTrace]
  refine ⟨50902406730918190594077911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33934937820612127062718607 50902406730918190594077911)
  ·
    refine ⟨76353610096377285891116867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50902406730918190594077911 76353610096377285891116867)
    ·
      refine ⟨114530415144565928836675301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76353610096377285891116867 114530415144565928836675301)
      ·
        refine ⟨21474452839606111656876619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114530415144565928836675301 21474452839606111656876619)
        ·
          refine ⟨32211679259409167485314929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21474452839606111656876619 32211679259409167485314929)
          ·
            refine ⟨24158759444556875613986197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32211679259409167485314929 24158759444556875613986197)
            ·
              refine ⟨1132441848963603544405603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24158759444556875613986197 1132441848963603544405603)
              ·
                refine ⟨1698662773445405316608405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132441848963603544405603 1698662773445405316608405)
                ·
                  refine ⟨79624817505253374216019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1698662773445405316608405 79624817505253374216019)
                  ·
                    rfl

theorem cell23_1395619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 6].length) (baseStart_1395619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395619 prefixEnd_1395619 := by exact prefixLift 1395619
  have htrace : WordTrace (prefixWord ++ tailWord_1395619) baseStart_1395619 baseEnd_1395619 := by
    simpa [prefixWord, tailWord_1395619, baseEnd_1395619] using wordTrace_append hprefix tailTrace_1395619
  have hstable : (prefixWord ++ tailWord_1395619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395619).length < 2 ^ (prefixWord ++ tailWord_1395619).sum := by decide
  have hdescent : baseEnd_1395619 < baseStart_1395619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395639 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 1, 5, 2]
def baseStart_1395639 : Nat := 118140960795 + 1395639 * 2 ^ 59
def prefixEnd_1395639 : Nat := 4983230072969 + 3 ^ 40 * 1395639 * 2
def baseEnd_1395639 : Nat := 716633627160370289694079

theorem tailTrace_1395639 : CollatzResearch.WordTrace tailWord_1395639 prefixEnd_1395639 716633627160370289694079 := by
  unfold tailWord_1395639
  simp only [CollatzResearch.WordTrace]
  refine ⟨50903136190845734009805971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33935424127230489339870647 50903136190845734009805971)
  ·
    refine ⟨76354704286268601014708957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50903136190845734009805971 76354704286268601014708957)
    ·
      refine ⟨28633014107350725380515859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76354704286268601014708957 28633014107350725380515859)
      ·
        refine ⟨42949521161026088070773789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28633014107350725380515859 42949521161026088070773789)
        ·
          refine ⟨16106070435384783026540171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42949521161026088070773789 16106070435384783026540171)
          ·
            refine ⟨24159105653077174539810257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16106070435384783026540171 24159105653077174539810257)
            ·
              refine ⟨18119329239807880904857693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24159105653077174539810257 18119329239807880904857693)
              ·
                refine ⟨6794748464927955339321635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18119329239807880904857693 6794748464927955339321635)
                ·
                  refine ⟨10192122697391933008982453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6794748464927955339321635 10192122697391933008982453)
                  ·
                    refine ⟨955511502880493719592105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10192122697391933008982453 955511502880493719592105)
                    ·
                      refine ⟨716633627160370289694079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955511502880493719592105 716633627160370289694079)
                      ·
                        rfl

theorem cell23_1395639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 5, 2].length) (baseStart_1395639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395639 prefixEnd_1395639 := by exact prefixLift 1395639
  have htrace : WordTrace (prefixWord ++ tailWord_1395639) baseStart_1395639 baseEnd_1395639 := by
    simpa [prefixWord, tailWord_1395639, baseEnd_1395639] using wordTrace_append hprefix tailTrace_1395639
  have hstable : (prefixWord ++ tailWord_1395639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395639).length < 2 ^ (prefixWord ++ tailWord_1395639).sum := by decide
  have hdescent : baseEnd_1395639 < baseStart_1395639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395663 : List Nat := [1, 1, 2, 1, 1, 7, 1, 4, 1, 1, 3]
def baseStart_1395663 : Nat := 118140960795 + 1395663 * 2 ^ 59
def prefixEnd_1395663 : Nat := 4983230072969 + 3 ^ 40 * 1395663 * 2
def baseEnd_1395663 : Nat := 716645950696078195793969

theorem tailTrace_1395663 : CollatzResearch.WordTrace tailWord_1395663 prefixEnd_1395663 716645950696078195793969 := by
  unfold tailWord_1395663
  simp only [CollatzResearch.WordTrace]
  refine ⟨50904011542758786108679643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33936007695172524072453095 50904011542758786108679643)
  ·
    refine ⟨76356017314138179163019465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50904011542758786108679643 76356017314138179163019465)
    ·
      refine ⟨57267012985603634372264599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76356017314138179163019465 57267012985603634372264599)
      ·
        refine ⟨85900519478405451558396899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57267012985603634372264599 85900519478405451558396899)
        ·
          refine ⟨128850779217608177337595349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85900519478405451558396899 128850779217608177337595349)
          ·
            refine ⟨3019940137912691656349891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128850779217608177337595349 3019940137912691656349891)
            ·
              refine ⟨4529910206869037484524837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019940137912691656349891 4529910206869037484524837)
              ·
                refine ⟨849358163787944528348407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4529910206869037484524837 849358163787944528348407)
                ·
                  refine ⟨1274037245681916792522611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849358163787944528348407 1274037245681916792522611)
                  ·
                    refine ⟨1911055868522875188783917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274037245681916792522611 1911055868522875188783917)
                    ·
                      refine ⟨716645950696078195793969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911055868522875188783917 716645950696078195793969)
                      ·
                        rfl

theorem cell23_1395663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 1, 3].length) (baseStart_1395663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395663 prefixEnd_1395663 := by exact prefixLift 1395663
  have htrace : WordTrace (prefixWord ++ tailWord_1395663) baseStart_1395663 baseEnd_1395663 := by
    simpa [prefixWord, tailWord_1395663, baseEnd_1395663] using wordTrace_append hprefix tailTrace_1395663
  have hstable : (prefixWord ++ tailWord_1395663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395663).length < 2 ^ (prefixWord ++ tailWord_1395663).sum := by decide
  have hdescent : baseEnd_1395663 < baseStart_1395663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395713 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1395713 : Nat := 118140960795 + 1395713 * 2 ^ 59
def prefixEnd_1395713 : Nat := 4983230072969 + 3 ^ 40 * 1395713 * 2
def baseEnd_1395713 : Nat := 238890541576267666722913

theorem tailTrace_1395713 : CollatzResearch.WordTrace tailWord_1395713 prefixEnd_1395713 238890541576267666722913 := by
  unfold tailWord_1395713
  simp only [CollatzResearch.WordTrace]
  refine ⟨50905835192577644647999793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33937223461718429765333195 50905835192577644647999793)
  ·
    refine ⟨38179376394433233485999845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50905835192577644647999793 38179376394433233485999845)
    ·
      refine ⟨7158633073956231278624971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38179376394433233485999845 7158633073956231278624971)
      ·
        refine ⟨10737949610934346917937457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7158633073956231278624971 10737949610934346917937457)
        ·
          refine ⟨8053462208200760188453093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10737949610934346917937457 8053462208200760188453093)
          ·
            refine ⟨1510024164037642535334955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8053462208200760188453093 1510024164037642535334955)
            ·
              refine ⟨2265036246056463803002433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510024164037642535334955 2265036246056463803002433)
              ·
                refine ⟨1698777184542347852251825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265036246056463803002433 1698777184542347852251825)
                ·
                  refine ⟨1274082888406760889188869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1698777184542347852251825 1274082888406760889188869)
                  ·
                    refine ⟨238890541576267666722913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1274082888406760889188869 238890541576267666722913)
                    ·
                      rfl

theorem cell23_1395713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1395713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395713 prefixEnd_1395713 := by exact prefixLift 1395713
  have htrace : WordTrace (prefixWord ++ tailWord_1395713) baseStart_1395713 baseEnd_1395713 := by
    simpa [prefixWord, tailWord_1395713, baseEnd_1395713] using wordTrace_append hprefix tailTrace_1395713
  have hstable : (prefixWord ++ tailWord_1395713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395713).length < 2 ^ (prefixWord ++ tailWord_1395713).sum := by decide
  have hdescent : baseEnd_1395713 < baseStart_1395713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395720 : List Nat := [2, 1, 3, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_1395720 : Nat := 118140960795 + 1395720 * 2 ^ 59
def prefixEnd_1395720 : Nat := 4983230072969 + 3 ^ 40 * 1395720 * 2
def baseEnd_1395720 : Nat := 716675219093384472781207

theorem tailTrace_1395720 : CollatzResearch.WordTrace tailWord_1395720 prefixEnd_1395720 716675219093384472781207 := by
  unfold tailWord_1395720
  simp only [CollatzResearch.WordTrace]
  refine ⟨25453045251776142421752307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33937393669034856562336409 25453045251776142421752307)
  ·
    refine ⟨38179567877664213632628461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25453045251776142421752307 38179567877664213632628461)
    ·
      refine ⟨14317337954124080112235673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38179567877664213632628461 14317337954124080112235673)
      ·
        refine ⟨10738003465593060084176755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14317337954124080112235673 10738003465593060084176755)
        ·
          refine ⟨16107005198389590126265133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10738003465593060084176755 16107005198389590126265133)
          ·
            refine ⟨6040126949396096297349425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16107005198389590126265133 6040126949396096297349425)
            ·
              refine ⟨4530095212047072223012069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6040126949396096297349425 4530095212047072223012069)
              ·
                refine ⟨849392852258826041814763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4530095212047072223012069 849392852258826041814763)
                ·
                  refine ⟨1274089278388239062722145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849392852258826041814763 1274089278388239062722145)
                  ·
                    refine ⟨955566958791179297041609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1274089278388239062722145 955566958791179297041609)
                    ·
                      refine ⟨716675219093384472781207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955566958791179297041609 716675219093384472781207)
                      ·
                        rfl

theorem cell23_1395720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_1395720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395720 prefixEnd_1395720 := by exact prefixLift 1395720
  have htrace : WordTrace (prefixWord ++ tailWord_1395720) baseStart_1395720 baseEnd_1395720 := by
    simpa [prefixWord, tailWord_1395720, baseEnd_1395720] using wordTrace_append hprefix tailTrace_1395720
  have hstable : (prefixWord ++ tailWord_1395720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395720).length < 2 ^ (prefixWord ++ tailWord_1395720).sum := by decide
  have hdescent : baseEnd_1395720 < baseStart_1395720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395736 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1395736 : Nat := 118140960795 + 1395736 * 2 ^ 59
def prefixEnd_1395736 : Nat := 4983230072969 + 3 ^ 40 * 1395736 * 2
def baseEnd_1395736 : Nat := 716683434783856410181133

theorem tailTrace_1395736 : CollatzResearch.WordTrace tailWord_1395736 prefixEnd_1395736 716683434783856410181133 := by
  unfold tailWord_1395736
  simp only [CollatzResearch.WordTrace]
  refine ⟨25453337035747159788043531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33937782714329546384058041 25453337035747159788043531)
  ·
    refine ⟨38180005553620739682065297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25453337035747159788043531 38180005553620739682065297)
    ·
      refine ⟨28635004165215554761548973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38180005553620739682065297 28635004165215554761548973)
      ·
        refine ⟨10738126561955833035580865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28635004165215554761548973 10738126561955833035580865)
        ·
          refine ⟨8053594921466874776685649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10738126561955833035580865 8053594921466874776685649)
          ·
            refine ⟨6040196191100156082514237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8053594921466874776685649 6040196191100156082514237)
            ·
              refine ⟨2265073571662558530942839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6040196191100156082514237 2265073571662558530942839)
              ·
                refine ⟨3397610357493837796414259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265073571662558530942839 3397610357493837796414259)
                ·
                  refine ⟨5096415536240756694621389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397610357493837796414259 5096415536240756694621389)
                  ·
                    refine ⟨1911155826090283760483021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5096415536240756694621389 1911155826090283760483021)
                    ·
                      refine ⟨716683434783856410181133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911155826090283760483021 716683434783856410181133)
                      ·
                        rfl

theorem cell23_1395736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1395736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395736 prefixEnd_1395736 := by exact prefixLift 1395736
  have htrace : WordTrace (prefixWord ++ tailWord_1395736) baseStart_1395736 baseEnd_1395736 := by
    simpa [prefixWord, tailWord_1395736, baseEnd_1395736] using wordTrace_append hprefix tailTrace_1395736
  have hstable : (prefixWord ++ tailWord_1395736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395736).length < 2 ^ (prefixWord ++ tailWord_1395736).sum := by decide
  have hdescent : baseEnd_1395736 < baseStart_1395736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395754 : List Nat := [3, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_1395754 : Nat := 118140960795 + 1395754 * 2 ^ 59
def prefixEnd_1395754 : Nat := 4983230072969 + 3 ^ 40 * 1395754 * 2
def baseEnd_1395754 : Nat := 716692677435637339756051

theorem tailTrace_1395754 : CollatzResearch.WordTrace tailWord_1395754 prefixEnd_1395754 716692677435637339756051 := by
  unfold tailWord_1395754
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726832646357277162560579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33938220390286072433494877 12726832646357277162560579)
  ·
    refine ⟨19090248969535915743840869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12726832646357277162560579 19090248969535915743840869)
    ·
      refine ⟨3579421681787984201970163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19090248969535915743840869 3579421681787984201970163)
      ·
        refine ⟨5369132522681976302955245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579421681787984201970163 5369132522681976302955245)
        ·
          refine ⟨2013424696005741113608217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5369132522681976302955245 2013424696005741113608217)
          ·
            refine ⟨1510068522004305835206163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2013424696005741113608217 1510068522004305835206163)
            ·
              refine ⟨2265102783006458752809245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510068522004305835206163 2265102783006458752809245)
              ·
                refine ⟨849413543627422032303467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2265102783006458752809245 849413543627422032303467)
                ·
                  refine ⟨1274120315441133048455201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849413543627422032303467 1274120315441133048455201)
                  ·
                    refine ⟨955590236580849786341401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1274120315441133048455201 955590236580849786341401)
                    ·
                      refine ⟨716692677435637339756051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955590236580849786341401 716692677435637339756051)
                      ·
                        rfl

theorem cell23_1395754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_1395754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395754 prefixEnd_1395754 := by exact prefixLift 1395754
  have htrace : WordTrace (prefixWord ++ tailWord_1395754) baseStart_1395754 baseEnd_1395754 := by
    simpa [prefixWord, tailWord_1395754, baseEnd_1395754] using wordTrace_append hprefix tailTrace_1395754
  have hstable : (prefixWord ++ tailWord_1395754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395754).length < 2 ^ (prefixWord ++ tailWord_1395754).sum := by decide
  have hdescent : baseEnd_1395754 < baseStart_1395754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395779 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 3]
def baseStart_1395779 : Nat := 118140960795 + 1395779 * 2 ^ 59
def prefixEnd_1395779 : Nat := 4983230072969 + 3 ^ 40 * 1395779 * 2
def baseEnd_1395779 : Nat := 716705514451999741943435

theorem tailTrace_1395779 : CollatzResearch.WordTrace tailWord_1395779 prefixEnd_1395779 716705514451999741943435 := by
  unfold tailWord_1395779
  simp only [CollatzResearch.WordTrace]
  refine ⟨50908242410338537919902391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33938828273559025279934927 50908242410338537919902391)
  ·
    refine ⟨76362363615507806879853587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50908242410338537919902391 76362363615507806879853587)
    ·
      refine ⟨114543545423261710319780381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76362363615507806879853587 114543545423261710319780381)
      ·
        refine ⟨42953829533723141369917643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114543545423261710319780381 42953829533723141369917643)
        ·
          refine ⟨64430744300584712054876465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42953829533723141369917643 64430744300584712054876465)
          ·
            refine ⟨48323058225438534041157349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64430744300584712054876465 48323058225438534041157349)
            ·
              refine ⟨9060573417269725132717003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48323058225438534041157349 9060573417269725132717003)
              ·
                refine ⟨13590860125904587699075505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9060573417269725132717003 13590860125904587699075505)
                ·
                  refine ⟨10193145094428440774306629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13590860125904587699075505 10193145094428440774306629)
                  ·
                    refine ⟨1911214705205332645182493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10193145094428440774306629 1911214705205332645182493)
                    ·
                      refine ⟨716705514451999741943435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911214705205332645182493 716705514451999741943435)
                      ·
                        rfl

theorem cell23_1395779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_1395779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395779 prefixEnd_1395779 := by exact prefixLift 1395779
  have htrace : WordTrace (prefixWord ++ tailWord_1395779) baseStart_1395779 baseEnd_1395779 := by
    simpa [prefixWord, tailWord_1395779, baseEnd_1395779] using wordTrace_append hprefix tailTrace_1395779
  have hstable : (prefixWord ++ tailWord_1395779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395779).length < 2 ^ (prefixWord ++ tailWord_1395779).sum := by decide
  have hdescent : baseEnd_1395779 < baseStart_1395779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395810 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1395810 : Nat := 118140960795 + 1395810 * 2 ^ 59
def prefixEnd_1395810 : Nat := 4983230072969 + 3 ^ 40 * 1395810 * 2
def baseEnd_1395810 : Nat := 716721432352289120655793

theorem tailTrace_1395810 : CollatzResearch.WordTrace tailWord_1395810 prefixEnd_1395810 716721432352289120655793 := by
  unfold tailWord_1395810
  simp only [CollatzResearch.WordTrace]
  refine ⟨12727343268306557553570221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33939582048817486809520589 12727343268306557553570221)
  ·
    refine ⟨4772753725614959082588833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12727343268306557553570221 4772753725614959082588833)
    ·
      refine ⟨3579565294211219311941625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4772753725614959082588833 3579565294211219311941625)
      ·
        refine ⟨2684673970658414483956219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3579565294211219311941625 2684673970658414483956219)
        ·
          refine ⟨4027010955987621725934329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684673970658414483956219 4027010955987621725934329)
          ·
            refine ⟨3020258216990716294450747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027010955987621725934329 3020258216990716294450747)
            ·
              refine ⟨4530387325486074441676121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020258216990716294450747 4530387325486074441676121)
              ·
                refine ⟨3397790494114555831257091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4530387325486074441676121 3397790494114555831257091)
                ·
                  refine ⟨5096685741171833746885637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397790494114555831257091 5096685741171833746885637)
                  ·
                    refine ⟨955628576469718827541057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5096685741171833746885637 955628576469718827541057)
                    ·
                      refine ⟨716721432352289120655793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955628576469718827541057 716721432352289120655793)
                      ·
                        rfl

theorem cell23_1395810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1395810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395810 prefixEnd_1395810 := by exact prefixLift 1395810
  have htrace : WordTrace (prefixWord ++ tailWord_1395810) baseStart_1395810 baseEnd_1395810 := by
    simpa [prefixWord, tailWord_1395810, baseEnd_1395810] using wordTrace_append hprefix tailTrace_1395810
  have hstable : (prefixWord ++ tailWord_1395810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395810).length < 2 ^ (prefixWord ++ tailWord_1395810).sum := by decide
  have hdescent : baseEnd_1395810 < baseStart_1395810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395826 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1395826 : Nat := 118140960795 + 1395826 * 2 ^ 59
def prefixEnd_1395826 : Nat := 4983230072969 + 3 ^ 40 * 1395826 * 2
def baseEnd_1395826 : Nat := 716729648042761058055719

theorem tailTrace_1395826 : CollatzResearch.WordTrace tailWord_1395826 prefixEnd_1395826 716729648042761058055719 := by
  unfold tailWord_1395826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12727489160292066236715833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33939971094112176631242221 12727489160292066236715833)
  ·
    refine ⟨9545616870219049677536875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12727489160292066236715833 9545616870219049677536875)
    ·
      refine ⟨14318425305328574516305313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545616870219049677536875 14318425305328574516305313)
      ·
        refine ⟨10738818978996430887228985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14318425305328574516305313 10738818978996430887228985)
        ·
          refine ⟨8054114234247323165421739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10738818978996430887228985 8054114234247323165421739)
          ·
            refine ⟨12081171351370984748132609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8054114234247323165421739 12081171351370984748132609)
            ·
              refine ⟨9060878513528238561099457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12081171351370984748132609 9060878513528238561099457)
              ·
                refine ⟨6795658885146178920824593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9060878513528238561099457 6795658885146178920824593)
                ·
                  refine ⟨5096744163859634190618445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6795658885146178920824593 5096744163859634190618445)
                  ·
                    refine ⟨1911279061447362821481917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5096744163859634190618445 1911279061447362821481917)
                    ·
                      refine ⟨716729648042761058055719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911279061447362821481917 716729648042761058055719)
                      ·
                        rfl

theorem cell23_1395826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1395826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395826 prefixEnd_1395826 := by exact prefixLift 1395826
  have htrace : WordTrace (prefixWord ++ tailWord_1395826) baseStart_1395826 baseEnd_1395826 := by
    simpa [prefixWord, tailWord_1395826, baseEnd_1395826] using wordTrace_append hprefix tailTrace_1395826
  have hstable : (prefixWord ++ tailWord_1395826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395826).length < 2 ^ (prefixWord ++ tailWord_1395826).sum := by decide
  have hdescent : baseEnd_1395826 < baseStart_1395826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395833 : List Nat := [1, 2, 1, 3, 5, 1, 1, 4, 5]
def baseStart_1395833 : Nat := 118140960795 + 1395833 * 2 ^ 59
def prefixEnd_1395833 : Nat := 4983230072969 + 3 ^ 40 * 1395833 * 2
def baseEnd_1395833 : Nat := 79637026934149170074243

theorem tailTrace_1395833 : CollatzResearch.WordTrace tailWord_1395833 prefixEnd_1395833 79637026934149170074243 := by
  unfold tailWord_1395833
  simp only [CollatzResearch.WordTrace]
  refine ⟨50910211952142905142368153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33940141301428603428245435 50910211952142905142368153)
  ·
    refine ⟨38182658964107178856776115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50910211952142905142368153 38182658964107178856776115)
    ·
      refine ⟨57273988446160768285164173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38182658964107178856776115 57273988446160768285164173)
      ·
        refine ⟨21477745667310288106936565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57273988446160768285164173 21477745667310288106936565)
        ·
          refine ⟨2013538656310339510025303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21477745667310288106936565 2013538656310339510025303)
          ·
            refine ⟨3020307984465509265037955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013538656310339510025303 3020307984465509265037955)
            ·
              refine ⟨4530461976698263897556933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020307984465509265037955 4530461976698263897556933)
              ·
                refine ⟨849461620630924480791925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4530461976698263897556933 849461620630924480791925)
                ·
                  refine ⟨79637026934149170074243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 849461620630924480791925 79637026934149170074243)
                  ·
                    rfl

theorem cell23_1395833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 5].length) (baseStart_1395833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395833 prefixEnd_1395833 := by exact prefixLift 1395833
  have htrace : WordTrace (prefixWord ++ tailWord_1395833) baseStart_1395833 baseEnd_1395833 := by
    simpa [prefixWord, tailWord_1395833, baseEnd_1395833] using wordTrace_append hprefix tailTrace_1395833
  have hstable : (prefixWord ++ tailWord_1395833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395833).length < 2 ^ (prefixWord ++ tailWord_1395833).sum := by decide
  have hdescent : baseEnd_1395833 < baseStart_1395833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395836 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 7, 2]
def baseStart_1395836 : Nat := 118140960795 + 1395836 * 2 ^ 59
def prefixEnd_1395836 : Nat := 4983230072969 + 3 ^ 40 * 1395836 * 2
def baseEnd_1395836 : Nat := 716734782849306018930673

theorem tailTrace_1395836 : CollatzResearch.WordTrace tailWord_1395836 prefixEnd_1395836 716734782849306018930673 := by
  unfold tailWord_1395836
  simp only [CollatzResearch.WordTrace]
  refine ⟨25455160685566018327363681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33940214247421357769818241 25455160685566018327363681)
  ·
    refine ⟨19091370514174513745522761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25455160685566018327363681 19091370514174513745522761)
    ·
      refine ⟨14318527885630885309142071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19091370514174513745522761 14318527885630885309142071)
      ·
        refine ⟨21477791828446327963713107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14318527885630885309142071 21477791828446327963713107)
        ·
          refine ⟨32216687742669491945569661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21477791828446327963713107 32216687742669491945569661)
          ·
            refine ⟨12081257903501059479588623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32216687742669491945569661 12081257903501059479588623)
            ·
              refine ⟨18121886855251589219382935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12081257903501059479588623 18121886855251589219382935)
              ·
                refine ⟨27182830282877383829074403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18121886855251589219382935 27182830282877383829074403)
                ·
                  refine ⟨40774245424316075743611605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27182830282877383829074403 40774245424316075743611605)
                  ·
                    refine ⟨955646377132408025240897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40774245424316075743611605 955646377132408025240897)
                    ·
                      refine ⟨716734782849306018930673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 955646377132408025240897 716734782849306018930673)
                      ·
                        rfl

theorem cell23_1395836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_1395836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395836 prefixEnd_1395836 := by exact prefixLift 1395836
  have htrace : WordTrace (prefixWord ++ tailWord_1395836) baseStart_1395836 baseEnd_1395836 := by
    simpa [prefixWord, tailWord_1395836, baseEnd_1395836] using wordTrace_append hprefix tailTrace_1395836
  have hstable : (prefixWord ++ tailWord_1395836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395836).length < 2 ^ (prefixWord ++ tailWord_1395836).sum := by decide
  have hdescent : baseEnd_1395836 < baseStart_1395836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395863 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 2, 5]
def baseStart_1395863 : Nat := 118140960795 + 1395863 * 2 ^ 59
def prefixEnd_1395863 : Nat := 4983230072969 + 3 ^ 40 * 1395863 * 2
def baseEnd_1395863 : Nat := 238916215608992471097683

theorem tailTrace_1395863 : CollatzResearch.WordTrace tailWord_1395863 prefixEnd_1395863 238916215608992471097683 := by
  unfold tailWord_1395863
  simp only [CollatzResearch.WordTrace]
  refine ⟨50911306142034220265960243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33940870761356146843973495 50911306142034220265960243)
  ·
    refine ⟨76366959213051330398940365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50911306142034220265960243 76366959213051330398940365)
    ·
      refine ⟨28637609704894248899602637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76366959213051330398940365 28637609704894248899602637)
      ·
        refine ⟨10739103639335343337350989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28637609704894248899602637 10739103639335343337350989)
        ·
          refine ⟨4027163864750753751506621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10739103639335343337350989 4027163864750753751506621)
          ·
            refine ⟨1510186449281532656814983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4027163864750753751506621 1510186449281532656814983)
            ·
              refine ⟨2265279673922298985222475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510186449281532656814983 2265279673922298985222475)
              ·
                refine ⟨3397919510883448477833713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265279673922298985222475 3397919510883448477833713)
                ·
                  refine ⟨2548439633162586358375285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3397919510883448477833713 2548439633162586358375285)
                  ·
                    refine ⟨238916215608992471097683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2548439633162586358375285 238916215608992471097683)
                    ·
                      rfl

theorem cell23_1395863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_1395863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395863 prefixEnd_1395863 := by exact prefixLift 1395863
  have htrace : WordTrace (prefixWord ++ tailWord_1395863) baseStart_1395863 baseEnd_1395863 := by
    simpa [prefixWord, tailWord_1395863, baseEnd_1395863] using wordTrace_append hprefix tailTrace_1395863
  have hstable : (prefixWord ++ tailWord_1395863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395863).length < 2 ^ (prefixWord ++ tailWord_1395863).sum := by decide
  have hdescent : baseEnd_1395863 < baseStart_1395863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395909 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_1395909 : Nat := 118140960795 + 1395909 * 2 ^ 59
def prefixEnd_1395909 : Nat := 4983230072969 + 3 ^ 40 * 1395909 * 2
def baseEnd_1395909 : Nat := 716772266937084233317837

theorem tailTrace_1395909 : CollatzResearch.WordTrace tailWord_1395909 prefixEnd_1395909 716772266937084233317837 := by
  unfold tailWord_1395909
  simp only [CollatzResearch.WordTrace]
  refine ⟨50912983899867570122134781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33941989266578380081423187 50912983899867570122134781)
  ·
    refine ⟨19092368962450338795800543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50912983899867570122134781 19092368962450338795800543)
    ·
      refine ⟨28638553443675508193700815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19092368962450338795800543 28638553443675508193700815)
      ·
        refine ⟨42957830165513262290551223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28638553443675508193700815 42957830165513262290551223)
        ·
          refine ⟨64436745248269893435826835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42957830165513262290551223 64436745248269893435826835)
          ·
            refine ⟨96655117872404840153740253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64436745248269893435826835 96655117872404840153740253)
            ·
              refine ⟨36245669202151815057652595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96655117872404840153740253 36245669202151815057652595)
              ·
                refine ⟨54368503803227722586478893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36245669202151815057652595 54368503803227722586478893)
                ·
                  refine ⟨20388188926210395969929585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54368503803227722586478893 20388188926210395969929585)
                  ·
                    refine ⟨15291141694657796977447189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20388188926210395969929585 15291141694657796977447189)
                    ·
                      refine ⟨716772266937084233317837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15291141694657796977447189 716772266937084233317837)
                      ·
                        rfl

theorem cell23_1395909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_1395909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395909 prefixEnd_1395909 := by exact prefixLift 1395909
  have htrace : WordTrace (prefixWord ++ tailWord_1395909) baseStart_1395909 baseEnd_1395909 := by
    simpa [prefixWord, tailWord_1395909, baseEnd_1395909] using wordTrace_append hprefix tailTrace_1395909
  have hstable : (prefixWord ++ tailWord_1395909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395909).length < 2 ^ (prefixWord ++ tailWord_1395909).sum := by decide
  have hdescent : baseEnd_1395909 < baseStart_1395909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395950 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_1395950 : Nat := 118140960795 + 1395950 * 2 ^ 59
def prefixEnd_1395950 : Nat := 4983230072969 + 3 ^ 40 * 1395950 * 2
def baseEnd_1395950 : Nat := 716793319643918572905149

theorem tailTrace_1395950 : CollatzResearch.WordTrace tailWord_1395950 prefixEnd_1395950 716793319643918572905149 := by
  unfold tailWord_1395950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6364309911589879265547163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33942986195146022749584869 6364309911589879265547163)
  ·
    refine ⟨9546464867384818898320745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6364309911589879265547163 9546464867384818898320745)
    ·
      refine ⟨7159848650538614173740559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9546464867384818898320745 7159848650538614173740559)
      ·
        refine ⟨10739772975807921260610839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7159848650538614173740559 10739772975807921260610839)
        ·
          refine ⟨16109659463711881890916259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10739772975807921260610839 16109659463711881890916259)
          ·
            refine ⟨24164489195567822836374389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16109659463711881890916259 24164489195567822836374389)
            ·
              refine ⟨2265420862084483390910099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24164489195567822836374389 2265420862084483390910099)
              ·
                refine ⟨3398131293126725086365149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265420862084483390910099 3398131293126725086365149)
                ·
                  refine ⟨1274299234922521907386931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3398131293126725086365149 1274299234922521907386931)
                  ·
                    refine ⟨1911448852383782861080397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274299234922521907386931 1911448852383782861080397)
                    ·
                      refine ⟨716793319643918572905149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911448852383782861080397 716793319643918572905149)
                      ·
                        rfl

theorem cell23_1395950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_1395950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395950 prefixEnd_1395950 := by exact prefixLift 1395950
  have htrace : WordTrace (prefixWord ++ tailWord_1395950) baseStart_1395950 baseEnd_1395950 := by
    simpa [prefixWord, tailWord_1395950, baseEnd_1395950] using wordTrace_append hprefix tailTrace_1395950
  have hstable : (prefixWord ++ tailWord_1395950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395950).length < 2 ^ (prefixWord ++ tailWord_1395950).sum := by decide
  have hdescent : baseEnd_1395950 < baseStart_1395950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1395970 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1395970 : Nat := 118140960795 + 1395970 * 2 ^ 59
def prefixEnd_1395970 : Nat := 4983230072969 + 3 ^ 40 * 1395970 * 2
def baseEnd_1395970 : Nat := 238934529752336164885019

theorem tailTrace_1395970 : CollatzResearch.WordTrace tailWord_1395970 prefixEnd_1395970 238934529752336164885019 := by
  unfold tailWord_1395970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12728802188161644385026341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33943472501764385026736909 12728802188161644385026341)
  ·
    refine ⟨2386650410280308322192439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12728802188161644385026341 2386650410280308322192439)
    ·
      refine ⟨3579975615420462483288659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386650410280308322192439 3579975615420462483288659)
      ·
        refine ⟨5369963423130693724932989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579975615420462483288659 5369963423130693724932989)
        ·
          refine ⟨2013736283674010146849871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5369963423130693724932989 2013736283674010146849871)
          ·
            refine ⟨3020604425511015220274807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013736283674010146849871 3020604425511015220274807)
            ·
              refine ⟨4530906638266522830412211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3020604425511015220274807 4530906638266522830412211)
              ·
                refine ⟨6796359957399784245618317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4530906638266522830412211 6796359957399784245618317)
                ·
                  refine ⟨2548634984024919092106869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6796359957399784245618317 2548634984024919092106869)
                  ·
                    refine ⟨238934529752336164885019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2548634984024919092106869 238934529752336164885019)
                    ·
                      rfl

theorem cell23_1395970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1395970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1395970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1395970 prefixEnd_1395970 := by exact prefixLift 1395970
  have htrace : WordTrace (prefixWord ++ tailWord_1395970) baseStart_1395970 baseEnd_1395970 := by
    simpa [prefixWord, tailWord_1395970, baseEnd_1395970] using wordTrace_append hprefix tailTrace_1395970
  have hstable : (prefixWord ++ tailWord_1395970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1395970).length < 2 ^ (prefixWord ++ tailWord_1395970).sum := by decide
  have hdescent : baseEnd_1395970 < baseStart_1395970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1395970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396010 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1396010 : Nat := 118140960795 + 1396010 * 2 ^ 59
def prefixEnd_1396010 : Nat := 4983230072969 + 3 ^ 40 * 1396010 * 2
def baseEnd_1396010 : Nat := 716824128483188338154873

theorem tailTrace_1396010 : CollatzResearch.WordTrace tailWord_1396010 prefixEnd_1396010 716824128483188338154873 := by
  unfold tailWord_1396010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729166918125416092890371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33944445115001109581040989 12729166918125416092890371)
  ·
    refine ⟨19093750377188124139335557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12729166918125416092890371 19093750377188124139335557)
    ·
      refine ⟨3580078195722773276125417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19093750377188124139335557 3580078195722773276125417)
      ·
        refine ⟨2685058646792079957094063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3580078195722773276125417 2685058646792079957094063)
        ·
          refine ⟨4027587970188119935641095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685058646792079957094063 4027587970188119935641095)
          ·
            refine ⟨6041381955282179903461643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4027587970188119935641095 6041381955282179903461643)
            ·
              refine ⟨9062072932923269855192465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6041381955282179903461643 9062072932923269855192465)
              ·
                refine ⟨6796554699692452391394349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9062072932923269855192465 6796554699692452391394349)
                ·
                  refine ⟨2548708012384669646772881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6796554699692452391394349 2548708012384669646772881)
                  ·
                    refine ⟨1911531009288502235079661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2548708012384669646772881 1911531009288502235079661)
                    ·
                      refine ⟨716824128483188338154873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911531009288502235079661 716824128483188338154873)
                      ·
                        rfl

theorem cell23_1396010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1396010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396010 prefixEnd_1396010 := by exact prefixLift 1396010
  have htrace : WordTrace (prefixWord ++ tailWord_1396010) baseStart_1396010 baseEnd_1396010 := by
    simpa [prefixWord, tailWord_1396010, baseEnd_1396010] using wordTrace_append hprefix tailTrace_1396010
  have hstable : (prefixWord ++ tailWord_1396010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396010).length < 2 ^ (prefixWord ++ tailWord_1396010).sum := by decide
  have hdescent : baseEnd_1396010 < baseStart_1396010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396020 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1396020 : Nat := 118140960795 + 1396020 * 2 ^ 59
def prefixEnd_1396020 : Nat := 4983230072969 + 3 ^ 40 * 1396020 * 2
def baseEnd_1396020 : Nat := 716829263289733299029827

theorem tailTrace_1396020 : CollatzResearch.WordTrace tailWord_1396020 prefixEnd_1396020 716829263289733299029827 := by
  unfold tailWord_1396020
  simp only [CollatzResearch.WordTrace]
  refine ⟨25458516201232718039712757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33944688268310290719617009 25458516201232718039712757)
  ·
    refine ⟨2386735893865567316223071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25458516201232718039712757 2386735893865567316223071)
    ·
      refine ⟨3580103840798350974334607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386735893865567316223071 3580103840798350974334607)
      ·
        refine ⟨5370155761197526461501911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580103840798350974334607 5370155761197526461501911)
        ·
          refine ⟨8055233641796289692252867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5370155761197526461501911 8055233641796289692252867)
          ·
            refine ⟨12082850462694434538379301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8055233641796289692252867 12082850462694434538379301)
            ·
              refine ⟨2265534461755206475946119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12082850462694434538379301 2265534461755206475946119)
              ·
                refine ⟨3398301692632809713919179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265534461755206475946119 3398301692632809713919179)
                ·
                  refine ⟨5097452538949214570878769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398301692632809713919179 5097452538949214570878769)
                  ·
                    refine ⟨3823089404211910928159077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5097452538949214570878769 3823089404211910928159077)
                    ·
                      refine ⟨716829263289733299029827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3823089404211910928159077 716829263289733299029827)
                      ·
                        rfl

theorem cell23_1396020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1396020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396020 prefixEnd_1396020 := by exact prefixLift 1396020
  have htrace : WordTrace (prefixWord ++ tailWord_1396020) baseStart_1396020 baseEnd_1396020 := by
    simpa [prefixWord, tailWord_1396020, baseEnd_1396020] using wordTrace_append hprefix tailTrace_1396020
  have hstable : (prefixWord ++ tailWord_1396020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396020).length < 2 ^ (prefixWord ++ tailWord_1396020).sum := by decide
  have hdescent : baseEnd_1396020 < baseStart_1396020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396023 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_1396023 : Nat := 118140960795 + 1396023 * 2 ^ 59
def prefixEnd_1396023 : Nat := 4983230072969 + 3 ^ 40 * 1396023 * 2
def baseEnd_1396023 : Nat := 716830803731696787292313

theorem tailTrace_1396023 : CollatzResearch.WordTrace tailWord_1396023 prefixEnd_1396023 716830803731696787292313 := by
  unfold tailWord_1396023
  simp only [CollatzResearch.WordTrace]
  refine ⟨50917141821454567591784723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33944761214303045061189815 50917141821454567591784723)
  ·
    refine ⟨76375712732181851387677085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50917141821454567591784723 76375712732181851387677085)
    ·
      refine ⟨28640892274568194270378907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76375712732181851387677085 28640892274568194270378907)
      ·
        refine ⟨42961338411852291405568361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28640892274568194270378907 42961338411852291405568361)
        ·
          refine ⟨32221003808889218554176271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42961338411852291405568361 32221003808889218554176271)
          ·
            refine ⟨48331505713333827831264407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32221003808889218554176271 48331505713333827831264407)
            ·
              refine ⟨72497258570000741746896611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48331505713333827831264407 72497258570000741746896611)
              ·
                refine ⟨108745887855001112620344917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72497258570000741746896611 108745887855001112620344917)
                ·
                  refine ⟨1274365873300794288519667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 108745887855001112620344917 1274365873300794288519667)
                  ·
                    refine ⟨1911548809951191432779501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274365873300794288519667 1911548809951191432779501)
                    ·
                      refine ⟨716830803731696787292313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911548809951191432779501 716830803731696787292313)
                      ·
                        rfl

theorem cell23_1396023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_1396023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396023 prefixEnd_1396023 := by exact prefixLift 1396023
  have htrace : WordTrace (prefixWord ++ tailWord_1396023) baseStart_1396023 baseEnd_1396023 := by
    simpa [prefixWord, tailWord_1396023, baseEnd_1396023] using wordTrace_append hprefix tailTrace_1396023
  have hstable : (prefixWord ++ tailWord_1396023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396023).length < 2 ^ (prefixWord ++ tailWord_1396023).sum := by decide
  have hdescent : baseEnd_1396023 < baseStart_1396023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396026 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_1396026 : Nat := 118140960795 + 1396026 * 2 ^ 59
def prefixEnd_1396026 : Nat := 4983230072969 + 3 ^ 40 * 1396026 * 2
def baseEnd_1396026 : Nat := 238944114724553425184933

theorem tailTrace_1396026 : CollatzResearch.WordTrace tailWord_1396026 prefixEnd_1396026 238944114724553425184933 := by
  unfold tailWord_1396026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729312810110924776035983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33944834160295799402762621 12729312810110924776035983)
  ·
    refine ⟨19093969215166387164053975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12729312810110924776035983 19093969215166387164053975)
    ·
      refine ⟨28640953822749580746080963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19093969215166387164053975 28640953822749580746080963)
      ·
        refine ⟨42961430734124371119121445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28640953822749580746080963 42961430734124371119121445)
        ·
          refine ⟨8055268262648319584835271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42961430734124371119121445 8055268262648319584835271)
          ·
            refine ⟨12082902393972479377252907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8055268262648319584835271 12082902393972479377252907)
            ·
              refine ⟨18124353590958719065879361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12082902393972479377252907 18124353590958719065879361)
              ·
                refine ⟨13593265193219039299409521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18124353590958719065879361 13593265193219039299409521)
                ·
                  refine ⟨10194948894914279474557141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13593265193219039299409521 10194948894914279474557141)
                  ·
                    refine ⟨238944114724553425184933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10194948894914279474557141 238944114724553425184933)
                    ·
                      rfl

theorem cell23_1396026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_1396026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396026 prefixEnd_1396026 := by exact prefixLift 1396026
  have htrace : WordTrace (prefixWord ++ tailWord_1396026) baseStart_1396026 baseEnd_1396026 := by
    simpa [prefixWord, tailWord_1396026, baseEnd_1396026] using wordTrace_append hprefix tailTrace_1396026
  have hstable : (prefixWord ++ tailWord_1396026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396026).length < 2 ^ (prefixWord ++ tailWord_1396026).sum := by decide
  have hdescent : baseEnd_1396026 < baseStart_1396026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396038 : List Nat := [6, 1, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1396038 : Nat := 118140960795 + 1396038 * 2 ^ 59
def prefixEnd_1396038 : Nat := 4983230072969 + 3 ^ 40 * 1396038 * 2
def baseEnd_1396038 : Nat := 238946168647171409534915

theorem tailTrace_1396038 : CollatzResearch.WordTrace tailWord_1396038 prefixEnd_1396038 238946168647171409534915 := by
  unfold tailWord_1396038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591177778637507036049399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33945125944266816769053845 1591177778637507036049399)
  ·
    refine ⟨2386766667956260554074099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1591177778637507036049399 2386766667956260554074099)
    ·
      refine ⟨3580150001934390831111149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386766667956260554074099 3580150001934390831111149)
      ·
        refine ⟨1342556250725396561666681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3580150001934390831111149 1342556250725396561666681)
        ·
          refine ⟨1006917188044047421250011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342556250725396561666681 1006917188044047421250011)
          ·
            refine ⟨1510375782066071131875017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006917188044047421250011 1510375782066071131875017)
            ·
              refine ⟨1132781836549553348906263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510375782066071131875017 1132781836549553348906263)
              ·
                refine ⟨1699172754824330023359395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132781836549553348906263 1699172754824330023359395)
                ·
                  refine ⟨2548759132236495035039093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699172754824330023359395 2548759132236495035039093)
                  ·
                    refine ⟨238946168647171409534915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2548759132236495035039093 238946168647171409534915)
                    ·
                      rfl

theorem cell23_1396038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1396038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396038 prefixEnd_1396038 := by exact prefixLift 1396038
  have htrace : WordTrace (prefixWord ++ tailWord_1396038) baseStart_1396038 baseEnd_1396038 := by
    simpa [prefixWord, tailWord_1396038, baseEnd_1396038] using wordTrace_append hprefix tailTrace_1396038
  have hstable : (prefixWord ++ tailWord_1396038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396038).length < 2 ^ (prefixWord ++ tailWord_1396038).sum := by decide
  have hdescent : baseEnd_1396038 < baseStart_1396038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396056 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 4, 6]
def baseStart_1396056 : Nat := 118140960795 + 1396056 * 2 ^ 59
def prefixEnd_1396056 : Nat := 4983230072969 + 3 ^ 40 * 1396056 * 2
def baseEnd_1396056 : Nat := 238949249531098386059887

theorem tailTrace_1396056 : CollatzResearch.WordTrace tailWord_1396056 prefixEnd_1396056 238949249531098386059887 := by
  unfold tailWord_1396056
  simp only [CollatzResearch.WordTrace]
  refine ⟨25459172715167507113868011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33945563620223342818490681 25459172715167507113868011)
  ·
    refine ⟨38188759072751260670802017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25459172715167507113868011 38188759072751260670802017)
    ·
      refine ⟨28641569304563445503101513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38188759072751260670802017 28641569304563445503101513)
      ·
        refine ⟨21481176978422584127326135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28641569304563445503101513 21481176978422584127326135)
        ·
          refine ⟨32221765467633876190989203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21481176978422584127326135 32221765467633876190989203)
          ·
            refine ⟨48332648201450814286483805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32221765467633876190989203 48332648201450814286483805)
            ·
              refine ⟨18124743075544055357431427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48332648201450814286483805 18124743075544055357431427)
              ·
                refine ⟨27187114613316083036147141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18124743075544055357431427 27187114613316083036147141)
                ·
                  refine ⟨5097583989996765569277589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27187114613316083036147141 5097583989996765569277589)
                  ·
                    refine ⟨238949249531098386059887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5097583989996765569277589 238949249531098386059887)
                    ·
                      rfl

theorem cell23_1396056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_1396056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396056 prefixEnd_1396056 := by exact prefixLift 1396056
  have htrace : WordTrace (prefixWord ++ tailWord_1396056) baseStart_1396056 baseEnd_1396056 := by
    simpa [prefixWord, tailWord_1396056, baseEnd_1396056] using wordTrace_append hprefix tailTrace_1396056
  have hstable : (prefixWord ++ tailWord_1396056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396056).length < 2 ^ (prefixWord ++ tailWord_1396056).sum := by decide
  have hdescent : baseEnd_1396056 < baseStart_1396056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396074 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1396074 : Nat := 118140960795 + 1396074 * 2 ^ 59
def prefixEnd_1396074 : Nat := 4983230072969 + 3 ^ 40 * 1396074 * 2
def baseEnd_1396074 : Nat := 716856991245076087754579

theorem tailTrace_1396074 : CollatzResearch.WordTrace tailWord_1396074 prefixEnd_1396074 716856991245076087754579 := by
  unfold tailWord_1396074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12729750486067450825472819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33946001296179868867927517 12729750486067450825472819)
  ·
    refine ⟨19094625729101176238209229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12729750486067450825472819 19094625729101176238209229)
    ·
      refine ⟨7160484648412941089328461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19094625729101176238209229 7160484648412941089328461)
      ·
        refine ⟨2685181743154852908498173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7160484648412941089328461 2685181743154852908498173)
        ·
          refine ⟨1006943153683069840686815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2685181743154852908498173 1006943153683069840686815)
          ·
            refine ⟨1510414730524604761030223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006943153683069840686815 1510414730524604761030223)
            ·
              refine ⟨2265622095786907141545335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510414730524604761030223 2265622095786907141545335)
              ·
                refine ⟨3398433143680360712318003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265622095786907141545335 3398433143680360712318003)
                ·
                  refine ⟨5097649715520541068477005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398433143680360712318003 5097649715520541068477005)
                  ·
                    refine ⟨1911618643320202900678877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5097649715520541068477005 1911618643320202900678877)
                    ·
                      refine ⟨716856991245076087754579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911618643320202900678877 716856991245076087754579)
                      ·
                        rfl

theorem cell23_1396074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1396074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396074 prefixEnd_1396074 := by exact prefixLift 1396074
  have htrace : WordTrace (prefixWord ++ tailWord_1396074) baseStart_1396074 baseEnd_1396074 := by
    simpa [prefixWord, tailWord_1396074, baseEnd_1396074] using wordTrace_append hprefix tailTrace_1396074
  have hstable : (prefixWord ++ tailWord_1396074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396074).length < 2 ^ (prefixWord ++ tailWord_1396074).sum := by decide
  have hdescent : baseEnd_1396074 < baseStart_1396074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396170 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1396170 : Nat := 118140960795 + 1396170 * 2 ^ 59
def prefixEnd_1396170 : Nat := 4983230072969 + 3 ^ 40 * 1396170 * 2
def baseEnd_1396170 : Nat := 716906285387907712154137

theorem tailTrace_1396170 : CollatzResearch.WordTrace tailWord_1396170 prefixEnd_1396170 716906285387907712154137 := by
  unfold tailWord_1396170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12730625837980502924346491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33948335567948007798257309 12730625837980502924346491)
  ·
    refine ⟨19095938756970754386519737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12730625837980502924346491 19095938756970754386519737)
    ·
      refine ⟨14321954067728065789889803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19095938756970754386519737 14321954067728065789889803)
      ·
        refine ⟨21482931101592098684834705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14321954067728065789889803 21482931101592098684834705)
        ·
          refine ⟨16112198326194074013626029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21482931101592098684834705 16112198326194074013626029)
          ·
            refine ⟨6042074372322777755109761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16112198326194074013626029 6042074372322777755109761)
            ·
              refine ⟨4531555779242083316332321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6042074372322777755109761 4531555779242083316332321)
              ·
                refine ⟨3398666834431562487249241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4531555779242083316332321 3398666834431562487249241)
                ·
                  refine ⟨2549000125823671865436931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3398666834431562487249241 2549000125823671865436931)
                  ·
                    refine ⟨3823500188735507798155397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549000125823671865436931 3823500188735507798155397)
                    ·
                      refine ⟨716906285387907712154137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3823500188735507798155397 716906285387907712154137)
                      ·
                        rfl

theorem cell23_1396170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1396170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396170 prefixEnd_1396170 := by exact prefixLift 1396170
  have htrace : WordTrace (prefixWord ++ tailWord_1396170) baseStart_1396170 baseEnd_1396170 := by
    simpa [prefixWord, tailWord_1396170, baseEnd_1396170] using wordTrace_append hprefix tailTrace_1396170
  have hstable : (prefixWord ++ tailWord_1396170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396170).length < 2 ^ (prefixWord ++ tailWord_1396170).sum := by decide
  have hdescent : baseEnd_1396170 < baseStart_1396170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396197 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_1396197 : Nat := 118140960795 + 1396197 * 2 ^ 59
def prefixEnd_1396197 : Nat := 4983230072969 + 3 ^ 40 * 1396197 * 2
def baseEnd_1396197 : Nat := 238973383121859702172171

theorem tailTrace_1396197 : CollatzResearch.WordTrace tailWord_1396197 prefixEnd_1396197 238973383121859702172171 := by
  unfold tailWord_1396197
  simp only [CollatzResearch.WordTrace]
  refine ⟨50923488122824195308618845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33948992081882796872412563 50923488122824195308618845)
  ·
    refine ⟨19096308046059073240732067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50923488122824195308618845 19096308046059073240732067)
    ·
      refine ⟨28644462069088609861098101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19096308046059073240732067 28644462069088609861098101)
      ·
        refine ⟨2685418318977057174477947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28644462069088609861098101 2685418318977057174477947)
        ·
          refine ⟨4028127478465585761716921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685418318977057174477947 4028127478465585761716921)
          ·
            refine ⟨3021095608849189321287691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4028127478465585761716921 3021095608849189321287691)
            ·
              refine ⟨4531643413273783981931537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3021095608849189321287691 4531643413273783981931537)
              ·
                refine ⟨3398732559955337986448653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4531643413273783981931537 3398732559955337986448653)
                ·
                  refine ⟨1274524709983251744918245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3398732559955337986448653 1274524709983251744918245)
                  ·
                    refine ⟨238973383121859702172171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1274524709983251744918245 238973383121859702172171)
                    ·
                      rfl

theorem cell23_1396197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_1396197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396197 prefixEnd_1396197 := by exact prefixLift 1396197
  have htrace : WordTrace (prefixWord ++ tailWord_1396197) baseStart_1396197 baseEnd_1396197 := by
    simpa [prefixWord, tailWord_1396197, baseEnd_1396197] using wordTrace_append hprefix tailTrace_1396197
  have hstable : (prefixWord ++ tailWord_1396197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396197).length < 2 ^ (prefixWord ++ tailWord_1396197).sum := by decide
  have hdescent : baseEnd_1396197 < baseStart_1396197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396203 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 3]
def baseStart_1396203 : Nat := 118140960795 + 1396203 * 2 ^ 59
def prefixEnd_1396203 : Nat := 4983230072969 + 3 ^ 40 * 1396203 * 2
def baseEnd_1396203 : Nat := 716923230249506083041485

theorem tailTrace_1396203 : CollatzResearch.WordTrace tailWord_1396203 prefixEnd_1396203 716923230249506083041485 := by
  unfold tailWord_1396203
  simp only [CollatzResearch.WordTrace]
  refine ⟨50923706960802458333337263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33949137973868305555558175 50923706960802458333337263)
  ·
    refine ⟨76385560441203687500005895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50923706960802458333337263 76385560441203687500005895)
    ·
      refine ⟨114578340661805531250008843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76385560441203687500005895 114578340661805531250008843)
      ·
        refine ⟨171867510992708296875013265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114578340661805531250008843 171867510992708296875013265)
        ·
          refine ⟨128900633244531222656259949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171867510992708296875013265 128900633244531222656259949)
          ·
            refine ⟨48337737466699208496097481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128900633244531222656259949 48337737466699208496097481)
            ·
              refine ⟨36253303100024406372073111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48337737466699208496097481 36253303100024406372073111)
              ·
                refine ⟨54379954650036609558109667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36253303100024406372073111 54379954650036609558109667)
                ·
                  refine ⟨81569931975054914337164501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54379954650036609558109667 81569931975054914337164501)
                  ·
                    refine ⟨1911795280665349554777293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 81569931975054914337164501 1911795280665349554777293)
                    ·
                      refine ⟨716923230249506083041485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911795280665349554777293 716923230249506083041485)
                      ·
                        rfl

theorem cell23_1396203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 3].length) (baseStart_1396203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396203 prefixEnd_1396203 := by exact prefixLift 1396203
  have htrace : WordTrace (prefixWord ++ tailWord_1396203) baseStart_1396203 baseEnd_1396203 := by
    simpa [prefixWord, tailWord_1396203, baseEnd_1396203] using wordTrace_append hprefix tailTrace_1396203
  have hstable : (prefixWord ++ tailWord_1396203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396203).length < 2 ^ (prefixWord ++ tailWord_1396203).sum := by decide
  have hdescent : baseEnd_1396203 < baseStart_1396203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396214 : List Nat := [5, 1, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_1396214 : Nat := 118140960795 + 1396214 * 2 ^ 59
def prefixEnd_1396214 : Nat := 4983230072969 + 3 ^ 40 * 1396214 * 2
def baseEnd_1396214 : Nat := 238976292845568513334645

theorem tailTrace_1396214 : CollatzResearch.WordTrace tailWord_1396214 prefixEnd_1396214 238976292845568513334645 := by
  unfold tailWord_1396214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182756760235162950749231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33949405442508404807991797 3182756760235162950749231)
  ·
    refine ⟨4774135140352744426123847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3182756760235162950749231 4774135140352744426123847)
    ·
      refine ⟨7161202710529116639185771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4774135140352744426123847 7161202710529116639185771)
      ·
        refine ⟨10741804065793674958778657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7161202710529116639185771 10741804065793674958778657)
        ·
          refine ⟨8056353049345256219083993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10741804065793674958778657 8056353049345256219083993)
          ·
            refine ⟨6042264787008942164312995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056353049345256219083993 6042264787008942164312995)
            ·
              refine ⟨9063397180513413246469493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042264787008942164312995 9063397180513413246469493)
              ·
                refine ⟨849693485673132491856515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9063397180513413246469493 849693485673132491856515)
                ·
                  refine ⟨1274540228509698737784773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849693485673132491856515 1274540228509698737784773)
                  ·
                    refine ⟨238976292845568513334645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1274540228509698737784773 238976292845568513334645)
                    ·
                      rfl

theorem cell23_1396214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_1396214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396214 prefixEnd_1396214 := by exact prefixLift 1396214
  have htrace : WordTrace (prefixWord ++ tailWord_1396214) baseStart_1396214 baseEnd_1396214 := by
    simpa [prefixWord, tailWord_1396214, baseEnd_1396214] using wordTrace_append hprefix tailTrace_1396214
  have hstable : (prefixWord ++ tailWord_1396214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396214).length < 2 ^ (prefixWord ++ tailWord_1396214).sum := by decide
  have hdescent : baseEnd_1396214 < baseStart_1396214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396223 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 5, 5]
def baseStart_1396223 : Nat := 118140960795 + 1396223 * 2 ^ 59
def prefixEnd_1396223 : Nat := 4983230072969 + 3 ^ 40 * 1396223 * 2
def baseEnd_1396223 : Nat := 238977833287532001597131

theorem tailTrace_1396223 : CollatzResearch.WordTrace tailWord_1396223 prefixEnd_1396223 238977833287532001597131 := by
  unfold tailWord_1396223
  simp only [CollatzResearch.WordTrace]
  refine ⟨50924436420730001749065323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33949624280486667832710215 50924436420730001749065323)
  ·
    refine ⟨76386654631095002623597985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50924436420730001749065323 76386654631095002623597985)
    ·
      refine ⟨57289990973321251967698489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76386654631095002623597985 57289990973321251967698489)
      ·
        refine ⟨42967493229990938975773867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57289990973321251967698489 42967493229990938975773867)
        ·
          refine ⟨64451239844986408463660801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42967493229990938975773867 64451239844986408463660801)
          ·
            refine ⟨48338429883739806347745601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64451239844986408463660801 48338429883739806347745601)
            ·
              refine ⟨36253822412804854760809201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48338429883739806347745601 36253822412804854760809201)
              ·
                refine ⟨27190366809603641070606901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36253822412804854760809201 27190366809603641070606901)
                ·
                  refine ⟨2549096888400341350369397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27190366809603641070606901 2549096888400341350369397)
                  ·
                    refine ⟨238977833287532001597131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2549096888400341350369397 238977833287532001597131)
                    ·
                      rfl

theorem cell23_1396223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_1396223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396223 prefixEnd_1396223 := by exact prefixLift 1396223
  have htrace : WordTrace (prefixWord ++ tailWord_1396223) baseStart_1396223 baseEnd_1396223 := by
    simpa [prefixWord, tailWord_1396223, baseEnd_1396223] using wordTrace_append hprefix tailTrace_1396223
  have hstable : (prefixWord ++ tailWord_1396223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396223).length < 2 ^ (prefixWord ++ tailWord_1396223).sum := by decide
  have hdescent : baseEnd_1396223 < baseStart_1396223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396257 : List Nat := [1, 2, 3, 2, 2, 3, 2, 2, 1, 5]
def baseStart_1396257 : Nat := 118140960795 + 1396257 * 2 ^ 59
def prefixEnd_1396257 : Nat := 4983230072969 + 3 ^ 40 * 1396257 * 2
def baseEnd_1396257 : Nat := 238983652734949623922079

theorem tailTrace_1396257 : CollatzResearch.WordTrace tailWord_1396257 prefixEnd_1396257 238983652734949623922079 := by
  unfold tailWord_1396257
  simp only [CollatzResearch.WordTrace]
  refine ⟨50925676502606825555803025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33950451001737883703868683 50925676502606825555803025)
  ·
    refine ⟨38194257376955119166852269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50925676502606825555803025 38194257376955119166852269)
    ·
      refine ⟨14322846516358169687569601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38194257376955119166852269 14322846516358169687569601)
      ·
        refine ⟨10742134887268627265677201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14322846516358169687569601 10742134887268627265677201)
        ·
          refine ⟨8056601165451470449257901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10742134887268627265677201 8056601165451470449257901)
          ·
            refine ⟨3021225437044301418471713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8056601165451470449257901 3021225437044301418471713)
            ·
              refine ⟨2265919077783226063853785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021225437044301418471713 2265919077783226063853785)
              ·
                refine ⟨1699439308337419547890339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265919077783226063853785 1699439308337419547890339)
                ·
                  refine ⟨2549158962506129321835509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699439308337419547890339 2549158962506129321835509)
                  ·
                    refine ⟨238983652734949623922079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2549158962506129321835509 238983652734949623922079)
                    ·
                      rfl

theorem cell23_1396257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_1396257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396257 prefixEnd_1396257 := by exact prefixLift 1396257
  have htrace : WordTrace (prefixWord ++ tailWord_1396257) baseStart_1396257 baseEnd_1396257 := by
    simpa [prefixWord, tailWord_1396257, baseEnd_1396257] using wordTrace_append hprefix tailTrace_1396257
  have hstable : (prefixWord ++ tailWord_1396257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396257).length < 2 ^ (prefixWord ++ tailWord_1396257).sum := by decide
  have hdescent : baseEnd_1396257 < baseStart_1396257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396277 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1396277 : Nat := 118140960795 + 1396277 * 2 ^ 59
def prefixEnd_1396277 : Nat := 4983230072969 + 3 ^ 40 * 1396277 * 2
def baseEnd_1396277 : Nat := 716961227817938793516145

theorem tailTrace_1396277 : CollatzResearch.WordTrace tailWord_1396277 prefixEnd_1396277 716961227817938793516145 := by
  unfold tailWord_1396277
  simp only [CollatzResearch.WordTrace]
  refine ⟨50926405962534368971531085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33950937308356245981020723 50926405962534368971531085)
  ·
    refine ⟨19097402235950388364324157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50926405962534368971531085 19097402235950388364324157)
    ·
      refine ⟨7161525838481395636621559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19097402235950388364324157 7161525838481395636621559)
      ·
        refine ⟨10742288757722093454932339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7161525838481395636621559 10742288757722093454932339)
        ·
          refine ⟨16113433136583140182398509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10742288757722093454932339 16113433136583140182398509)
          ·
            refine ⟨6042537426218677568399441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16113433136583140182398509 6042537426218677568399441)
            ·
              refine ⟨4531903069664008176299581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6042537426218677568399441 4531903069664008176299581)
              ·
                refine ⟨1699463651124003066112343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4531903069664008176299581 1699463651124003066112343)
                ·
                  refine ⟨2549195476686004599168515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699463651124003066112343 2549195476686004599168515)
                  ·
                    refine ⟨3823793215029006898752773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2549195476686004599168515 3823793215029006898752773)
                    ·
                      refine ⟨716961227817938793516145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3823793215029006898752773 716961227817938793516145)
                      ·
                        rfl

theorem cell23_1396277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1396277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396277 prefixEnd_1396277 := by exact prefixLift 1396277
  have htrace : WordTrace (prefixWord ++ tailWord_1396277) baseStart_1396277 baseEnd_1396277 := by
    simpa [prefixWord, tailWord_1396277, baseEnd_1396277] using wordTrace_append hprefix tailTrace_1396277
  have hstable : (prefixWord ++ tailWord_1396277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396277).length < 2 ^ (prefixWord ++ tailWord_1396277).sum := by decide
  have hdescent : baseEnd_1396277 < baseStart_1396277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396280 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_1396280 : Nat := 118140960795 + 1396280 * 2 ^ 59
def prefixEnd_1396280 : Nat := 4983230072969 + 3 ^ 40 * 1396280 * 2
def baseEnd_1396280 : Nat := 716962768259902281778631

theorem tailTrace_1396280 : CollatzResearch.WordTrace tailWord_1396280 prefixEnd_1396280 716962768259902281778631 := by
  unfold tailWord_1396280
  simp only [CollatzResearch.WordTrace]
  refine ⟨25463257690761750241945147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33951010254349000322593529 25463257690761750241945147)
  ·
    refine ⟨38194886536142625362917721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25463257690761750241945147 38194886536142625362917721)
    ·
      refine ⟨28646164902106969022188291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38194886536142625362917721 28646164902106969022188291)
      ·
        refine ⟨42969247353160453533282437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28646164902106969022188291 42969247353160453533282437)
        ·
          refine ⟨8056733878717585037490457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42969247353160453533282437 8056733878717585037490457)
          ·
            refine ⟨6042550409038188778117843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056733878717585037490457 6042550409038188778117843)
            ·
              refine ⟨9063825613557283167176765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6042550409038188778117843 9063825613557283167176765)
              ·
                refine ⟨3398934605083981187691287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9063825613557283167176765 3398934605083981187691287)
                ·
                  refine ⟨5098401907625971781536931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3398934605083981187691287 5098401907625971781536931)
                  ·
                    refine ⟨7647602861438957672305397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5098401907625971781536931 7647602861438957672305397)
                    ·
                      refine ⟨716962768259902281778631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7647602861438957672305397 716962768259902281778631)
                      ·
                        rfl

theorem cell23_1396280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_1396280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396280 prefixEnd_1396280 := by exact prefixLift 1396280
  have htrace : WordTrace (prefixWord ++ tailWord_1396280) baseStart_1396280 baseEnd_1396280 := by
    simpa [prefixWord, tailWord_1396280, baseEnd_1396280] using wordTrace_append hprefix tailTrace_1396280
  have hstable : (prefixWord ++ tailWord_1396280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396280).length < 2 ^ (prefixWord ++ tailWord_1396280).sum := by decide
  have hdescent : baseEnd_1396280 < baseStart_1396280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396300 : List Nat := [2, 2, 1, 3, 1, 4, 2, 8]
def baseStart_1396300 : Nat := 118140960795 + 1396300 * 2 ^ 59
def prefixEnd_1396300 : Nat := 4983230072969 + 3 ^ 40 * 1396300 * 2
def baseEnd_1396300 : Nat := 26554556958258970501057

theorem tailTrace_1396300 : CollatzResearch.WordTrace tailWord_1396300 prefixEnd_1396300 26554556958258970501057 := by
  unfold tailWord_1396300
  simp only [CollatzResearch.WordTrace]
  refine ⟨25463622420725521949809177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33951496560967362599745569 25463622420725521949809177)
  ·
    refine ⟨19097716815544141462356883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25463622420725521949809177 19097716815544141462356883)
    ·
      refine ⟨28646575223316212193535325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19097716815544141462356883 28646575223316212193535325)
      ·
        refine ⟨10742465708743579572575747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28646575223316212193535325 10742465708743579572575747)
        ·
          refine ⟨16113698563115369358863621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10742465708743579572575747 16113698563115369358863621)
          ·
            refine ⟨3021318480584131754786929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16113698563115369358863621 3021318480584131754786929)
            ·
              refine ⟨2265988860438098816090197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021318480584131754786929 2265988860438098816090197)
              ·
                refine ⟨26554556958258970501057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2265988860438098816090197 26554556958258970501057)
                ·
                  rfl

theorem cell23_1396300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 8].length) (baseStart_1396300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396300 prefixEnd_1396300 := by exact prefixLift 1396300
  have htrace : WordTrace (prefixWord ++ tailWord_1396300) baseStart_1396300 baseEnd_1396300 := by
    simpa [prefixWord, tailWord_1396300, baseEnd_1396300] using wordTrace_append hprefix tailTrace_1396300
  have hstable : (prefixWord ++ tailWord_1396300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396300).length < 2 ^ (prefixWord ++ tailWord_1396300).sum := by decide
  have hdescent : baseEnd_1396300 < baseStart_1396300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396303 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_1396303 : Nat := 118140960795 + 1396303 * 2 ^ 59
def prefixEnd_1396303 : Nat := 4983230072969 + 3 ^ 40 * 1396303 * 2
def baseEnd_1396303 : Nat := 716974578314955691791025

theorem tailTrace_1396303 : CollatzResearch.WordTrace tailWord_1396303 prefixEnd_1396303 716974578314955691791025 := by
  unfold tailWord_1396303
  simp only [CollatzResearch.WordTrace]
  refine ⟨50927354260440175411977563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33951569506960116941318375 50927354260440175411977563)
  ·
    refine ⟨76391031390660263117966345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50927354260440175411977563 76391031390660263117966345)
    ·
      refine ⟨57293273542995197338474759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76391031390660263117966345 57293273542995197338474759)
      ·
        refine ⟨85939910314492796007712139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57293273542995197338474759 85939910314492796007712139)
        ·
          refine ⟨128909865471739194011568209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85939910314492796007712139 128909865471739194011568209)
          ·
            refine ⟨96682399103804395508676157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128909865471739194011568209 96682399103804395508676157)
            ·
              refine ⟨36255899663926648315753559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96682399103804395508676157 36255899663926648315753559)
              ·
                refine ⟨54383849495889972473630339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36255899663926648315753559 54383849495889972473630339)
                ·
                  refine ⟨81575774243834958710445509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54383849495889972473630339 81575774243834958710445509)
                  ·
                    refine ⟨15295457670719054758208533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81575774243834958710445509 15295457670719054758208533)
                    ·
                      refine ⟨716974578314955691791025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15295457670719054758208533 716974578314955691791025)
                      ·
                        rfl

theorem cell23_1396303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_1396303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396303 prefixEnd_1396303 := by exact prefixLift 1396303
  have htrace : WordTrace (prefixWord ++ tailWord_1396303) baseStart_1396303 baseEnd_1396303 := by
    simpa [prefixWord, tailWord_1396303, baseEnd_1396303] using wordTrace_append hprefix tailTrace_1396303
  have hstable : (prefixWord ++ tailWord_1396303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396303).length < 2 ^ (prefixWord ++ tailWord_1396303).sum := by decide
  have hdescent : baseEnd_1396303 < baseStart_1396303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396327 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1396327 : Nat := 118140960795 + 1396327 * 2 ^ 59
def prefixEnd_1396327 : Nat := 4983230072969 + 3 ^ 40 * 1396327 * 2
def baseEnd_1396327 : Nat := 716986901850663597890915

theorem tailTrace_1396327 : CollatzResearch.WordTrace tailWord_1396327 prefixEnd_1396327 716986901850663597890915 := by
  unfold tailWord_1396327
  simp only [CollatzResearch.WordTrace]
  refine ⟨50928229612353227510851235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33952153074902151673900823 50928229612353227510851235)
  ·
    refine ⟨76392344418529841266276853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50928229612353227510851235 76392344418529841266276853)
    ·
      refine ⟨7161782289237172618713455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76392344418529841266276853 7161782289237172618713455)
      ·
        refine ⟨10742673433855758928070183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7161782289237172618713455 10742673433855758928070183)
        ·
          refine ⟨16114010150783638392105275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10742673433855758928070183 16114010150783638392105275)
          ·
            refine ⟨24171015226175457588157913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16114010150783638392105275 24171015226175457588157913)
            ·
              refine ⟨18128261419631593191118435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24171015226175457588157913 18128261419631593191118435)
              ·
                refine ⟨27192392129447389786677653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18128261419631593191118435 27192392129447389786677653)
                ·
                  refine ⟨1274643381067846396250515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27192392129447389786677653 1274643381067846396250515)
                  ·
                    refine ⟨1911965071601769594375773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274643381067846396250515 1911965071601769594375773)
                    ·
                      refine ⟨716986901850663597890915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1911965071601769594375773 716986901850663597890915)
                      ·
                        rfl

theorem cell23_1396327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1396327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396327 prefixEnd_1396327 := by exact prefixLift 1396327
  have htrace : WordTrace (prefixWord ++ tailWord_1396327) baseStart_1396327 baseEnd_1396327 := by
    simpa [prefixWord, tailWord_1396327, baseEnd_1396327] using wordTrace_append hprefix tailTrace_1396327
  have hstable : (prefixWord ++ tailWord_1396327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396327).length < 2 ^ (prefixWord ++ tailWord_1396327).sum := by decide
  have hdescent : baseEnd_1396327 < baseStart_1396327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
