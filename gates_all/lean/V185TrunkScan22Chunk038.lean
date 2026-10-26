import V185TrunkScan22Chunk037

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_339709 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_339709 : Nat := 118140960795 + 339709 * 2 ^ 59
def prefixEnd_339709 : Nat := 4983230072969 + 3 ^ 40 * 339709 * 2
def baseEnd_339709 : Nat := 116289333105544413783475

theorem tailTrace_339709 : CollatzResearch.WordTrace tailWord_339709 prefixEnd_339709 116289333105544413783475 := by
  unfold tailWord_339709
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390205126299785523286181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8260136750866523682190787 12390205126299785523286181)
  ·
    refine ⟨2323163461181209785616159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12390205126299785523286181 2323163461181209785616159)
    ·
      refine ⟨3484745191771814678424239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323163461181209785616159 3484745191771814678424239)
      ·
        refine ⟨5227117787657722017636359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484745191771814678424239 5227117787657722017636359)
        ·
          refine ⟨7840676681486583026454539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227117787657722017636359 7840676681486583026454539)
          ·
            refine ⟨11761015022229874539681809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7840676681486583026454539 11761015022229874539681809)
            ·
              refine ⟨8820761266672405904761357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11761015022229874539681809 8820761266672405904761357)
              ·
                refine ⟨3307785475002152214285509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8820761266672405904761357 3307785475002152214285509)
                ·
                  refine ⟨620209776562903540178533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3307785475002152214285509 620209776562903540178533)
                  ·
                    refine ⟨116289333105544413783475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 620209776562903540178533 116289333105544413783475)
                    ·
                      rfl

theorem cell22_339709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_339709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339709 prefixEnd_339709 := by exact prefixLift 339709
  have htrace : WordTrace (prefixWord ++ tailWord_339709) baseStart_339709 baseEnd_339709 := by
    simpa [prefixWord, tailWord_339709, baseEnd_339709] using wordTrace_append hprefix tailTrace_339709
  have hstable : (prefixWord ++ tailWord_339709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339709).length < 2 ^ (prefixWord ++ tailWord_339709).sum := by decide
  have hdescent : baseEnd_339709 < baseStart_339709 := by decide
  rcases family_descends (prefixWord ++ tailWord_339709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339711 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 2, 3]
def baseStart_339711 : Nat := 118140960795 + 339711 * 2 ^ 59
def prefixEnd_339711 : Nat := 4983230072969 + 3 ^ 40 * 339711 * 2
def baseEnd_339711 : Nat := 116290017746417075233469

theorem tailTrace_339711 : CollatzResearch.WordTrace tailWord_339711 prefixEnd_339711 116290017746417075233469 := by
  unfold tailWord_339711
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390278072292539864858987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8260185381528359909905991 12390278072292539864858987)
  ·
    refine ⟨18585417108438809797288481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12390278072292539864858987 18585417108438809797288481)
    ·
      refine ⟨13939062831329107347966361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18585417108438809797288481 13939062831329107347966361)
      ·
        refine ⟨10454297123496830510974771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13939062831329107347966361 10454297123496830510974771)
        ·
          refine ⟨15681445685245245766462157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10454297123496830510974771 15681445685245245766462157)
          ·
            refine ⟨5880542131966967162423309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15681445685245245766462157 5880542131966967162423309)
            ·
              refine ⟨2205203299487612685908741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5880542131966967162423309 2205203299487612685908741)
              ·
                refine ⟨413475618653927378607889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2205203299487612685908741 413475618653927378607889)
                ·
                  refine ⟨310106713990445533955917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413475618653927378607889 310106713990445533955917)
                  ·
                    refine ⟨116290017746417075233469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 310106713990445533955917 116290017746417075233469)
                    ·
                      rfl

theorem cell22_339711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_339711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339711 prefixEnd_339711 := by exact prefixLift 339711
  have htrace : WordTrace (prefixWord ++ tailWord_339711) baseStart_339711 baseEnd_339711 := by
    simpa [prefixWord, tailWord_339711, baseEnd_339711] using wordTrace_append hprefix tailTrace_339711
  have hstable : (prefixWord ++ tailWord_339711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339711).length < 2 ^ (prefixWord ++ tailWord_339711).sum := by decide
  have hdescent : baseEnd_339711 < baseStart_339711 := by decide
  rcases family_descends (prefixWord ++ tailWord_339711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339713 : List Nat := [1, 2, 4, 1, 1, 1, 6, 2, 4]
def baseStart_339713 : Nat := 118140960795 + 339713 * 2 ^ 59
def prefixEnd_339713 : Nat := 4983230072969 + 3 ^ 40 * 339713 * 2
def baseEnd_339713 : Nat := 38763567462429912227821

theorem tailTrace_339713 : CollatzResearch.WordTrace tailWord_339713 prefixEnd_339713 38763567462429912227821 := by
  unfold tailWord_339713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12390351018285294206431793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8260234012190196137621195 12390351018285294206431793)
  ·
    refine ⟨9292763263713970654823845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12390351018285294206431793 9292763263713970654823845)
    ·
      refine ⟨1742393111946369497779471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9292763263713970654823845 1742393111946369497779471)
      ·
        refine ⟨2613589667919554246669207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742393111946369497779471 2613589667919554246669207)
        ·
          refine ⟨3920384501879331370003811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613589667919554246669207 3920384501879331370003811)
          ·
            refine ⟨5880576752818997055005717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920384501879331370003811 5880576752818997055005717)
            ·
              refine ⟨275652035288390486953393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5880576752818997055005717 275652035288390486953393)
              ·
                refine ⟨206739026466292865215045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275652035288390486953393 206739026466292865215045)
                ·
                  refine ⟨38763567462429912227821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206739026466292865215045 38763567462429912227821)
                  ·
                    rfl

theorem cell22_339713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 4].length) (baseStart_339713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339713 prefixEnd_339713 := by exact prefixLift 339713
  have htrace : WordTrace (prefixWord ++ tailWord_339713) baseStart_339713 baseEnd_339713 := by
    simpa [prefixWord, tailWord_339713, baseEnd_339713] using wordTrace_append hprefix tailTrace_339713
  have hstable : (prefixWord ++ tailWord_339713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339713).length < 2 ^ (prefixWord ++ tailWord_339713).sum := by decide
  have hdescent : baseEnd_339713 < baseStart_339713 := by decide
  rcases family_descends (prefixWord ++ tailWord_339713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339724 : List Nat := [2, 2, 1, 2, 2, 1, 5, 7]
def baseStart_339724 : Nat := 118140960795 + 339724 * 2 ^ 59
def prefixEnd_339724 : Nat := 4983230072969 + 3 ^ 40 * 339724 * 2
def baseEnd_339724 : Nat := 12921607545787708295381

theorem tailTrace_339724 : CollatzResearch.WordTrace tailWord_339724 prefixEnd_339724 12921607545787708295381 := by
  unfold tailWord_339724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6195376110622721542541113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8260501480830295390054817 6195376110622721542541113)
  ·
    refine ⟨4646532082967041156905835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6195376110622721542541113 4646532082967041156905835)
    ·
      refine ⟨6969798124450561735358753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4646532082967041156905835 6969798124450561735358753)
      ·
        refine ⟨5227348593337921301519065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6969798124450561735358753 5227348593337921301519065)
        ·
          refine ⟨3920511445003440976139299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5227348593337921301519065 3920511445003440976139299)
          ·
            refine ⟨5880767167505161464208949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920511445003440976139299 5880767167505161464208949)
            ·
              refine ⟨551321921953608887269589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5880767167505161464208949 551321921953608887269589)
              ·
                refine ⟨12921607545787708295381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 551321921953608887269589 12921607545787708295381)
                ·
                  rfl

theorem cell22_339724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 7].length) (baseStart_339724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339724 prefixEnd_339724 := by exact prefixLift 339724
  have htrace : WordTrace (prefixWord ++ tailWord_339724) baseStart_339724 baseEnd_339724 := by
    simpa [prefixWord, tailWord_339724, baseEnd_339724] using wordTrace_append hprefix tailTrace_339724
  have hstable : (prefixWord ++ tailWord_339724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339724).length < 2 ^ (prefixWord ++ tailWord_339724).sum := by decide
  have hdescent : baseEnd_339724 < baseStart_339724 := by decide
  rcases family_descends (prefixWord ++ tailWord_339724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339773 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_339773 : Nat := 118140960795 + 339773 * 2 ^ 59
def prefixEnd_339773 : Nat := 4983230072969 + 3 ^ 40 * 339773 * 2
def baseEnd_339773 : Nat := 116311241613469580183279

theorem tailTrace_339773 : CollatzResearch.WordTrace tailWord_339773 prefixEnd_339773 116311241613469580183279 := by
  unfold tailWord_339773
  simp only [CollatzResearch.WordTrace]
  refine ⟨12392539398067924453615973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8261692932045282969077315 12392539398067924453615973)
  ·
    refine ⟨2323601137137735835052995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12392539398067924453615973 2323601137137735835052995)
    ·
      refine ⟨3485401705706603752579493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323601137137735835052995 3485401705706603752579493)
      ·
        refine ⟨653512819819988203608655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3485401705706603752579493 653512819819988203608655)
        ·
          refine ⟨980269229729982305412983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653512819819988203608655 980269229729982305412983)
          ·
            refine ⟨1470403844594973458119475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980269229729982305412983 1470403844594973458119475)
            ·
              refine ⟨2205605766892460187179213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470403844594973458119475 2205605766892460187179213)
              ·
                refine ⟨827102162584672570192205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2205605766892460187179213 827102162584672570192205)
                ·
                  refine ⟨310163310969252213822077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827102162584672570192205 310163310969252213822077)
                  ·
                    refine ⟨116311241613469580183279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 310163310969252213822077 116311241613469580183279)
                    ·
                      rfl

theorem cell22_339773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_339773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339773 prefixEnd_339773 := by exact prefixLift 339773
  have htrace : WordTrace (prefixWord ++ tailWord_339773) baseStart_339773 baseEnd_339773 := by
    simpa [prefixWord, tailWord_339773, baseEnd_339773] using wordTrace_append hprefix tailTrace_339773
  have hstable : (prefixWord ++ tailWord_339773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339773).length < 2 ^ (prefixWord ++ tailWord_339773).sum := by decide
  have hdescent : baseEnd_339773 < baseStart_339773 := by decide
  rcases family_descends (prefixWord ++ tailWord_339773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339893 : List Nat := [1, 3, 3, 2, 1, 4, 1, 7]
def baseStart_339893 : Nat := 118140960795 + 339893 * 2 ^ 59
def prefixEnd_339893 : Nat := 4983230072969 + 3 ^ 40 * 339893 * 2
def baseEnd_339893 : Nat := 12928035562869918575879

theorem tailTrace_339893 : CollatzResearch.WordTrace tailWord_339893 prefixEnd_339893 12928035562869918575879 := by
  unfold tailWord_339893
  simp only [CollatzResearch.WordTrace]
  refine ⟨12396916157633184947984333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8264610771755456631989555 12396916157633184947984333)
  ·
    refine ⟨4648843559112444355494125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12396916157633184947984333 4648843559112444355494125)
    ·
      refine ⟨1743316334667166633310297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4648843559112444355494125 1743316334667166633310297)
      ·
        refine ⟨1307487251000374974982723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1743316334667166633310297 1307487251000374974982723)
        ·
          refine ⟨1961230876500562462474085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307487251000374974982723 1961230876500562462474085)
          ·
            refine ⟨367730789343855461713891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1961230876500562462474085 367730789343855461713891)
            ·
              refine ⟨551596184015783192570837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367730789343855461713891 551596184015783192570837)
              ·
                refine ⟨12928035562869918575879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 551596184015783192570837 12928035562869918575879)
                ·
                  rfl

theorem cell22_339893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 7].length) (baseStart_339893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_339893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_339893 prefixEnd_339893 := by exact prefixLift 339893
  have htrace : WordTrace (prefixWord ++ tailWord_339893) baseStart_339893 baseEnd_339893 := by
    simpa [prefixWord, tailWord_339893, baseEnd_339893] using wordTrace_append hprefix tailTrace_339893
  have hstable : (prefixWord ++ tailWord_339893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339893).length < 2 ^ (prefixWord ++ tailWord_339893).sum := by decide
  have hdescent : baseEnd_339893 < baseStart_339893 := by decide
  rcases family_descends (prefixWord ++ tailWord_339893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340043 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 5, 3]
def baseStart_340043 : Nat := 118140960795 + 340043 * 2 ^ 59
def prefixEnd_340043 : Nat := 4983230072969 + 3 ^ 40 * 340043 * 2
def baseEnd_340043 : Nat := 116403668131278875932451

theorem tailTrace_340043 : CollatzResearch.WordTrace tailWord_340043 prefixEnd_340043 116403668131278875932451 := by
  unfold tailWord_340043
  simp only [CollatzResearch.WordTrace]
  refine ⟨12402387107089760565944783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8268258071393173710629855 12402387107089760565944783)
  ·
    refine ⟨18603580660634640848917175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12402387107089760565944783 18603580660634640848917175)
    ·
      refine ⟨27905370990951961273375763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18603580660634640848917175 27905370990951961273375763)
      ·
        refine ⟨41858056486427941910063645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27905370990951961273375763 41858056486427941910063645)
        ·
          refine ⟨15696771182410478216273867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41858056486427941910063645 15696771182410478216273867)
          ·
            refine ⟨23545156773615717324410801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15696771182410478216273867 23545156773615717324410801)
            ·
              refine ⟨17658867580211787993308101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23545156773615717324410801 17658867580211787993308101)
              ·
                refine ⟨3311037671289710248745269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17658867580211787993308101 3311037671289710248745269)
                ·
                  refine ⟨310409781683410335819869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3311037671289710248745269 310409781683410335819869)
                  ·
                    refine ⟨116403668131278875932451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 310409781683410335819869 116403668131278875932451)
                    ·
                      rfl

theorem cell22_340043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 3].length) (baseStart_340043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340043 prefixEnd_340043 := by exact prefixLift 340043
  have htrace : WordTrace (prefixWord ++ tailWord_340043) baseStart_340043 baseEnd_340043 := by
    simpa [prefixWord, tailWord_340043, baseEnd_340043] using wordTrace_append hprefix tailTrace_340043
  have hstable : (prefixWord ++ tailWord_340043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340043).length < 2 ^ (prefixWord ++ tailWord_340043).sum := by decide
  have hdescent : baseEnd_340043 < baseStart_340043 := by decide
  rcases family_descends (prefixWord ++ tailWord_340043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340073 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 5]
def baseStart_340073 : Nat := 118140960795 + 340073 * 2 ^ 59
def prefixEnd_340073 : Nat := 4983230072969 + 3 ^ 40 * 340073 * 2
def baseEnd_340073 : Nat := 38804645914789599227453

theorem tailTrace_340073 : CollatzResearch.WordTrace tailWord_340073 prefixEnd_340073 38804645914789599227453 := by
  unfold tailWord_340073
  simp only [CollatzResearch.WordTrace]
  refine ⟨12403481296981075689536873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8268987531320717126357915 12403481296981075689536873)
  ·
    refine ⟨9302610972735806767152655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12403481296981075689536873 9302610972735806767152655)
    ·
      refine ⟨13953916459103710150728983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9302610972735806767152655 13953916459103710150728983)
      ·
        refine ⟨20930874688655565226093475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13953916459103710150728983 20930874688655565226093475)
        ·
          refine ⟨31396312032983347839140213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20930874688655565226093475 31396312032983347839140213)
          ·
            refine ⟨2943404253092188859919395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31396312032983347839140213 2943404253092188859919395)
            ·
              refine ⟨4415106379638283289879093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943404253092188859919395 4415106379638283289879093)
              ·
                refine ⟨413916223091089058426165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4415106379638283289879093 413916223091089058426165)
                ·
                  refine ⟨38804645914789599227453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 413916223091089058426165 38804645914789599227453)
                  ·
                    rfl

theorem cell22_340073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_340073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340073 prefixEnd_340073 := by exact prefixLift 340073
  have htrace : WordTrace (prefixWord ++ tailWord_340073) baseStart_340073 baseEnd_340073 := by
    simpa [prefixWord, tailWord_340073, baseEnd_340073] using wordTrace_append hprefix tailTrace_340073
  have hstable : (prefixWord ++ tailWord_340073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340073).length < 2 ^ (prefixWord ++ tailWord_340073).sum := by decide
  have hdescent : baseEnd_340073 < baseStart_340073 := by decide
  rcases family_descends (prefixWord ++ tailWord_340073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340184 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 2, 3]
def baseStart_340184 : Nat := 118140960795 + 340184 * 2 ^ 59
def prefixEnd_340184 : Nat := 4983230072969 + 3 ^ 40 * 340184 * 2
def baseEnd_340184 : Nat := 116451935312801508157019

theorem tailTrace_340184 : CollatzResearch.WordTrace tailWord_340184 prefixEnd_340184 116451935312801508157019 := by
  unfold tailWord_340184
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203764899789470823413803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8271686533052627764551737 6203764899789470823413803)
  ·
    refine ⟨9305647349684206235120705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6203764899789470823413803 9305647349684206235120705)
    ·
      refine ⟨6979235512263154676340529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9305647349684206235120705 6979235512263154676340529)
      ·
        refine ⟨5234426634197366007255397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6979235512263154676340529 5234426634197366007255397)
        ·
          refine ⟨981454993912006126360387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5234426634197366007255397 981454993912006126360387)
          ·
            refine ⟨1472182490868009189540581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981454993912006126360387 1472182490868009189540581)
            ·
              refine ⟨276034217037751723038859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1472182490868009189540581 276034217037751723038859)
              ·
                refine ⟨414051325556627584558289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276034217037751723038859 414051325556627584558289)
                ·
                  refine ⟨310538494167470688418717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414051325556627584558289 310538494167470688418717)
                  ·
                    refine ⟨116451935312801508157019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 310538494167470688418717 116451935312801508157019)
                    ·
                      rfl

theorem cell22_340184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_340184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340184 prefixEnd_340184 := by exact prefixLift 340184
  have htrace : WordTrace (prefixWord ++ tailWord_340184) baseStart_340184 baseEnd_340184 := by
    simpa [prefixWord, tailWord_340184, baseEnd_340184] using wordTrace_append hprefix tailTrace_340184
  have hstable : (prefixWord ++ tailWord_340184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340184).length < 2 ^ (prefixWord ++ tailWord_340184).sum := by decide
  have hdescent : baseEnd_340184 < baseStart_340184 := by decide
  rcases family_descends (prefixWord ++ tailWord_340184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340188 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_340188 : Nat := 118140960795 + 340188 * 2 ^ 59
def prefixEnd_340188 : Nat := 4983230072969 + 3 ^ 40 * 340188 * 2
def baseEnd_340188 : Nat := 116453304594546831057007

theorem tailTrace_340188 : CollatzResearch.WordTrace tailWord_340188 prefixEnd_340188 116453304594546831057007 := by
  unfold tailWord_340188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203837845782225164986609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8271783794376300219982145 6203837845782225164986609)
  ·
    refine ⟨4652878384336668873739957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6203837845782225164986609 4652878384336668873739957)
    ·
      refine ⟨436207348531562706913121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4652878384336668873739957 436207348531562706913121)
      ·
        refine ⟨327155511398672030184841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436207348531562706913121 327155511398672030184841)
        ·
          refine ⟨245366633549004022638631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327155511398672030184841 245366633549004022638631)
          ·
            refine ⟨368049950323506033957947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245366633549004022638631 368049950323506033957947)
            ·
              refine ⟨552074925485259050936921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368049950323506033957947 552074925485259050936921)
              ·
                refine ⟨414056194113944288202691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552074925485259050936921 414056194113944288202691)
                ·
                  refine ⟨621084291170916432304037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414056194113944288202691 621084291170916432304037)
                  ·
                    refine ⟨116453304594546831057007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 621084291170916432304037 116453304594546831057007)
                    ·
                      rfl

theorem cell22_340188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_340188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340188 prefixEnd_340188 := by exact prefixLift 340188
  have htrace : WordTrace (prefixWord ++ tailWord_340188) baseStart_340188 baseEnd_340188 := by
    simpa [prefixWord, tailWord_340188, baseEnd_340188] using wordTrace_append hprefix tailTrace_340188
  have hstable : (prefixWord ++ tailWord_340188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340188).length < 2 ^ (prefixWord ++ tailWord_340188).sum := by decide
  have hdescent : baseEnd_340188 < baseStart_340188 := by decide
  rcases family_descends (prefixWord ++ tailWord_340188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340208 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 9]
def baseStart_340208 : Nat := 118140960795 + 340208 * 2 ^ 59
def prefixEnd_340208 : Nat := 4983230072969 + 3 ^ 40 * 340208 * 2
def baseEnd_340208 : Nat := 38820050334424481852315

theorem tailTrace_340208 : CollatzResearch.WordTrace tailWord_340208 prefixEnd_340208 38820050334424481852315 := by
  unfold tailWord_340208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204202575745996872850639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8272270100994662497134185 6204202575745996872850639)
  ·
    refine ⟨9306303863618995309275959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6204202575745996872850639 9306303863618995309275959)
    ·
      refine ⟨13959455795428492963913939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9306303863618995309275959 13959455795428492963913939)
      ·
        refine ⟨20939183693142739445870909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13959455795428492963913939 20939183693142739445870909)
        ·
          refine ⟨7852193884928527292201591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20939183693142739445870909 7852193884928527292201591)
          ·
            refine ⟨11778290827392790938302387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7852193884928527292201591 11778290827392790938302387)
            ·
              refine ⟨17667436241089186407453581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11778290827392790938302387 17667436241089186407453581)
              ·
                refine ⟨6625288590408444902795093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17667436241089186407453581 6625288590408444902795093)
                ·
                  refine ⟨38820050334424481852315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6625288590408444902795093 38820050334424481852315)
                  ·
                    rfl

theorem cell22_340208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_340208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340208 prefixEnd_340208 := by exact prefixLift 340208
  have htrace : WordTrace (prefixWord ++ tailWord_340208) baseStart_340208 baseEnd_340208 := by
    simpa [prefixWord, tailWord_340208, baseEnd_340208] using wordTrace_append hprefix tailTrace_340208
  have hstable : (prefixWord ++ tailWord_340208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340208).length < 2 ^ (prefixWord ++ tailWord_340208).sum := by decide
  have hdescent : baseEnd_340208 < baseStart_340208 := by decide
  rcases family_descends (prefixWord ++ tailWord_340208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340287 : List Nat := [1, 1, 2, 2, 4, 1, 1, 6, 4]
def baseStart_340287 : Nat := 118140960795 + 340287 * 2 ^ 59
def prefixEnd_340287 : Nat := 4983230072969 + 3 ^ 40 * 340287 * 2
def baseEnd_340287 : Nat := 38829064772581190943901

theorem tailTrace_340287 : CollatzResearch.WordTrace tailWord_340287 prefixEnd_340287 38829064772581190943901 := by
  unfold tailWord_340287
  simp only [CollatzResearch.WordTrace]
  refine ⟨12411286518205790237827115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8274191012137193491884743 12411286518205790237827115)
  ·
    refine ⟨18616929777308685356740673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12411286518205790237827115 18616929777308685356740673)
    ·
      refine ⟨13962697332981514017555505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18616929777308685356740673 13962697332981514017555505)
      ·
        refine ⟨10472022999736135513166629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13962697332981514017555505 10472022999736135513166629)
        ·
          refine ⟨1963504312450525408718743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10472022999736135513166629 1963504312450525408718743)
          ·
            refine ⟨2945256468675788113078115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963504312450525408718743 2945256468675788113078115)
            ·
              refine ⟨4417884703013682169617173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945256468675788113078115 4417884703013682169617173)
              ·
                refine ⟨207088345453766351700805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4417884703013682169617173 207088345453766351700805)
                ·
                  refine ⟨38829064772581190943901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207088345453766351700805 38829064772581190943901)
                  ·
                    rfl

theorem cell22_340287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 4].length) (baseStart_340287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340287 prefixEnd_340287 := by exact prefixLift 340287
  have htrace : WordTrace (prefixWord ++ tailWord_340287) baseStart_340287 baseEnd_340287 := by
    simpa [prefixWord, tailWord_340287, baseEnd_340287] using wordTrace_append hprefix tailTrace_340287
  have hstable : (prefixWord ++ tailWord_340287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340287).length < 2 ^ (prefixWord ++ tailWord_340287).sum := by decide
  have hdescent : baseEnd_340287 < baseStart_340287 := by decide
  rcases family_descends (prefixWord ++ tailWord_340287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340300 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_340300 : Nat := 118140960795 + 340300 * 2 ^ 59
def prefixEnd_340300 : Nat := 4983230072969 + 3 ^ 40 * 340300 * 2
def baseEnd_340300 : Nat := 116491644483415872256663

theorem tailTrace_340300 : CollatzResearch.WordTrace tailWord_340300 prefixEnd_340300 116491644483415872256663 := by
  unfold tailWord_340300
  simp only [CollatzResearch.WordTrace]
  refine ⟨6205880333579346729025177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8274507111439128972033569 6205880333579346729025177)
  ·
    refine ⟨4654410250184510046768883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6205880333579346729025177 4654410250184510046768883)
    ·
      refine ⟨6981615375276765070153325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654410250184510046768883 6981615375276765070153325)
      ·
        refine ⟨2618105765728786901307497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6981615375276765070153325 2618105765728786901307497)
        ·
          refine ⟨1963579324296590175980623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2618105765728786901307497 1963579324296590175980623)
          ·
            refine ⟨2945368986444885263970935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963579324296590175980623 2945368986444885263970935)
            ·
              refine ⟨4418053479667327895956403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945368986444885263970935 4418053479667327895956403)
              ·
                refine ⟨6627080219500991843934605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418053479667327895956403 6627080219500991843934605)
                ·
                  refine ⟨2485155082312871941475477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6627080219500991843934605 2485155082312871941475477)
                  ·
                    refine ⟨116491644483415872256663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2485155082312871941475477 116491644483415872256663)
                    ·
                      rfl

theorem cell22_340300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_340300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340300 prefixEnd_340300 := by exact prefixLift 340300
  have htrace : WordTrace (prefixWord ++ tailWord_340300) baseStart_340300 baseEnd_340300 := by
    simpa [prefixWord, tailWord_340300, baseEnd_340300] using wordTrace_append hprefix tailTrace_340300
  have hstable : (prefixWord ++ tailWord_340300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340300).length < 2 ^ (prefixWord ++ tailWord_340300).sum := by decide
  have hdescent : baseEnd_340300 < baseStart_340300 := by decide
  rcases family_descends (prefixWord ++ tailWord_340300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340332 : List Nat := [2, 2, 1, 1, 6, 2, 8]
def baseStart_340332 : Nat := 118140960795 + 340332 * 2 ^ 59
def prefixEnd_340332 : Nat := 4983230072969 + 3 ^ 40 * 340332 * 2
def baseEnd_340332 : Nat := 4314911064347350202095

theorem tailTrace_340332 : CollatzResearch.WordTrace tailWord_340332 prefixEnd_340332 4314911064347350202095 := by
  unfold tailWord_340332
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206463901521381461607625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8275285202028508615476833 6206463901521381461607625)
  ·
    refine ⟨4654847926141036096205719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6206463901521381461607625 4654847926141036096205719)
    ·
      refine ⟨6982271889211554144308579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654847926141036096205719 6982271889211554144308579)
      ·
        refine ⟨10473407833817331216462869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982271889211554144308579 10473407833817331216462869)
        ·
          refine ⟨490940992210187400771697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10473407833817331216462869 490940992210187400771697)
          ·
            refine ⟨368205744157640550578773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490940992210187400771697 368205744157640550578773)
            ·
              refine ⟨4314911064347350202095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 368205744157640550578773 4314911064347350202095)
              ·
                rfl

theorem cell22_340332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 8].length) (baseStart_340332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340332 prefixEnd_340332 := by exact prefixLift 340332
  have htrace : WordTrace (prefixWord ++ tailWord_340332) baseStart_340332 baseEnd_340332 := by
    simpa [prefixWord, tailWord_340332, baseEnd_340332] using wordTrace_append hprefix tailTrace_340332
  have hstable : (prefixWord ++ tailWord_340332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340332).length < 2 ^ (prefixWord ++ tailWord_340332).sum := by decide
  have hdescent : baseEnd_340332 < baseStart_340332 := by decide
  rcases family_descends (prefixWord ++ tailWord_340332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340345 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_340345 : Nat := 118140960795 + 340345 * 2 ^ 59
def prefixEnd_340345 : Nat := 4983230072969 + 3 ^ 40 * 340345 * 2
def baseEnd_340345 : Nat := 116507048903050754881525

theorem tailTrace_340345 : CollatzResearch.WordTrace tailWord_340345 prefixEnd_340345 116507048903050754881525 := by
  unfold tailWord_340345
  simp only [CollatzResearch.WordTrace]
  refine ⟨12413401951995666143438489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8275601301330444095625659 12413401951995666143438489)
  ·
    refine ⟨9310051463996749607578867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12413401951995666143438489 9310051463996749607578867)
    ·
      refine ⟨13965077195995124411368301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9310051463996749607578867 13965077195995124411368301)
      ·
        refine ⟨5236903948498171654263113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13965077195995124411368301 5236903948498171654263113)
        ·
          refine ⟨3927677961373628740697335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5236903948498171654263113 3927677961373628740697335)
          ·
            refine ⟨5891516942060443111046003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927677961373628740697335 5891516942060443111046003)
            ·
              refine ⟨8837275413090664666569005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891516942060443111046003 8837275413090664666569005)
              ·
                refine ⟨3313978279908999249963377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8837275413090664666569005 3313978279908999249963377)
                ·
                  refine ⟨2485483709931749437472533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3313978279908999249963377 2485483709931749437472533)
                  ·
                    refine ⟨116507048903050754881525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2485483709931749437472533 116507048903050754881525)
                    ·
                      rfl

theorem cell22_340345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_340345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340345 prefixEnd_340345 := by exact prefixLift 340345
  have htrace : WordTrace (prefixWord ++ tailWord_340345) baseStart_340345 baseEnd_340345 := by
    simpa [prefixWord, tailWord_340345, baseEnd_340345] using wordTrace_append hprefix tailTrace_340345
  have hstable : (prefixWord ++ tailWord_340345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340345).length < 2 ^ (prefixWord ++ tailWord_340345).sum := by decide
  have hdescent : baseEnd_340345 < baseStart_340345 := by decide
  rcases family_descends (prefixWord ++ tailWord_340345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340353 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 2, 3]
def baseStart_340353 : Nat := 118140960795 + 340353 * 2 ^ 59
def prefixEnd_340353 : Nat := 4983230072969 + 3 ^ 40 * 340353 * 2
def baseEnd_340353 : Nat := 116509787466541400681501

theorem tailTrace_340353 : CollatzResearch.WordTrace tailWord_340353 prefixEnd_340353 116509787466541400681501 := by
  unfold tailWord_340353
  simp only [CollatzResearch.WordTrace]
  refine ⟨12413693735966683509729713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8275795823977789006486475 12413693735966683509729713)
  ·
    refine ⟨9310270301975012632297285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12413693735966683509729713 9310270301975012632297285)
    ·
      refine ⟨1745675681620314868555741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9310270301975012632297285 1745675681620314868555741)
      ·
        refine ⟨654628380607618075708403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1745675681620314868555741 654628380607618075708403)
        ·
          refine ⟨981942570911427113562605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654628380607618075708403 981942570911427113562605)
          ·
            refine ⟨368228464091785167585977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 981942570911427113562605 368228464091785167585977)
            ·
              refine ⟨276171348068838875689483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368228464091785167585977 276171348068838875689483)
              ·
                refine ⟨414257022103258313534225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276171348068838875689483 414257022103258313534225)
                ·
                  refine ⟨310692766577443735150669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414257022103258313534225 310692766577443735150669)
                  ·
                    refine ⟨116509787466541400681501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 310692766577443735150669 116509787466541400681501)
                    ·
                      rfl

theorem cell22_340353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_340353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340353 prefixEnd_340353 := by exact prefixLift 340353
  have htrace : WordTrace (prefixWord ++ tailWord_340353) baseStart_340353 baseEnd_340353 := by
    simpa [prefixWord, tailWord_340353, baseEnd_340353] using wordTrace_append hprefix tailTrace_340353
  have hstable : (prefixWord ++ tailWord_340353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340353).length < 2 ^ (prefixWord ++ tailWord_340353).sum := by decide
  have hdescent : baseEnd_340353 < baseStart_340353 := by decide
  rcases family_descends (prefixWord ++ tailWord_340353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340407 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 3, 4]
def baseStart_340407 : Nat := 118140960795 + 340407 * 2 ^ 59
def prefixEnd_340407 : Nat := 4983230072969 + 3 ^ 40 * 340407 * 2
def baseEnd_340407 : Nat := 116528272770103259831335

theorem tailTrace_340407 : CollatzResearch.WordTrace tailWord_340407 prefixEnd_340407 116528272770103259831335 := by
  unfold tailWord_340407
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415663277771050732195475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8277108851847367154796983 12415663277771050732195475)
  ·
    refine ⟨18623494916656576098293213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12415663277771050732195475 18623494916656576098293213)
    ·
      refine ⟨6983810593746216036859955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18623494916656576098293213 6983810593746216036859955)
      ·
        refine ⟨10475715890619324055289933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6983810593746216036859955 10475715890619324055289933)
        ·
          refine ⟨3928393458982246520733725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10475715890619324055289933 3928393458982246520733725)
          ·
            refine ⟨1473147547118342445275147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3928393458982246520733725 1473147547118342445275147)
            ·
              refine ⟨2209721320677513667912721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473147547118342445275147 2209721320677513667912721)
              ·
                refine ⟨1657290990508135250934541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2209721320677513667912721 1657290990508135250934541)
                ·
                  refine ⟨621484121440550719100453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1657290990508135250934541 621484121440550719100453)
                  ·
                    refine ⟨116528272770103259831335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 621484121440550719100453 116528272770103259831335)
                    ·
                      rfl

theorem cell22_340407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_340407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340407 prefixEnd_340407 := by exact prefixLift 340407
  have htrace : WordTrace (prefixWord ++ tailWord_340407) baseStart_340407 baseEnd_340407 := by
    simpa [prefixWord, tailWord_340407, baseEnd_340407] using wordTrace_append hprefix tailTrace_340407
  have hstable : (prefixWord ++ tailWord_340407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340407).length < 2 ^ (prefixWord ++ tailWord_340407).sum := by decide
  have hdescent : baseEnd_340407 < baseStart_340407 := by decide
  rcases family_descends (prefixWord ++ tailWord_340407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340484 : List Nat := [2, 3, 2, 3, 1, 2, 1, 8]
def baseStart_340484 : Nat := 118140960795 + 340484 * 2 ^ 59
def prefixEnd_340484 : Nat := 4983230072969 + 3 ^ 40 * 340484 * 2
def baseEnd_340484 : Nat := 12950514604855636184011

theorem tailTrace_340484 : CollatzResearch.WordTrace tailWord_340484 prefixEnd_340484 12950514604855636184011 := by
  unfold tailWord_340484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209235849246046441374253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8278981132328061921832337 6209235849246046441374253)
  ·
    refine ⟨2328463443467267415515345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6209235849246046441374253 2328463443467267415515345)
    ·
      refine ⟨1746347582600450561636509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2328463443467267415515345 1746347582600450561636509)
      ·
        refine ⟨654880343475168960613691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1746347582600450561636509 654880343475168960613691)
        ·
          refine ⟨982320515212753440920537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654880343475168960613691 982320515212753440920537)
          ·
            refine ⟨736740386409565080690403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 982320515212753440920537 736740386409565080690403)
            ·
              refine ⟨1105110579614347621035605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736740386409565080690403 1105110579614347621035605)
              ·
                refine ⟨12950514604855636184011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1105110579614347621035605 12950514604855636184011)
                ·
                  rfl

theorem cell22_340484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 8].length) (baseStart_340484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340484 prefixEnd_340484 := by exact prefixLift 340484
  have htrace : WordTrace (prefixWord ++ tailWord_340484) baseStart_340484 baseEnd_340484 := by
    simpa [prefixWord, tailWord_340484, baseEnd_340484] using wordTrace_append hprefix tailTrace_340484
  have hstable : (prefixWord ++ tailWord_340484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340484).length < 2 ^ (prefixWord ++ tailWord_340484).sum := by decide
  have hdescent : baseEnd_340484 < baseStart_340484 := by decide
  rcases family_descends (prefixWord ++ tailWord_340484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340559 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 1, 4]
def baseStart_340559 : Nat := 118140960795 + 340559 * 2 ^ 59
def prefixEnd_340559 : Nat := 4983230072969 + 3 ^ 40 * 340559 * 2
def baseEnd_340559 : Nat := 116580305476425530030869

theorem tailTrace_340559 : CollatzResearch.WordTrace tailWord_340559 prefixEnd_340559 116580305476425530030869 := by
  unfold tailWord_340559
  simp only [CollatzResearch.WordTrace]
  refine ⟨12421207173220380691728731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8280804782146920461152487 12421207173220380691728731)
  ·
    refine ⟨18631810759830571037593097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12421207173220380691728731 18631810759830571037593097)
    ·
      refine ⟨13973858069872928278194823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18631810759830571037593097 13973858069872928278194823)
      ·
        refine ⟨20960787104809392417292235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13973858069872928278194823 20960787104809392417292235)
        ·
          refine ⟨31441180657214088625938353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20960787104809392417292235 31441180657214088625938353)
          ·
            refine ⟨23580885492910566469453765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31441180657214088625938353 23580885492910566469453765)
            ·
              refine ⟨4421416029920731213022581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23580885492910566469453765 4421416029920731213022581)
              ·
                refine ⟨414507752805068551220867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4421416029920731213022581 414507752805068551220867)
                ·
                  refine ⟨621761629207602826831301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414507752805068551220867 621761629207602826831301)
                  ·
                    refine ⟨116580305476425530030869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 621761629207602826831301 116580305476425530030869)
                    ·
                      rfl

theorem cell22_340559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_340559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340559 prefixEnd_340559 := by exact prefixLift 340559
  have htrace : WordTrace (prefixWord ++ tailWord_340559) baseStart_340559 baseEnd_340559 := by
    simpa [prefixWord, tailWord_340559, baseEnd_340559] using wordTrace_append hprefix tailTrace_340559
  have hstable : (prefixWord ++ tailWord_340559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340559).length < 2 ^ (prefixWord ++ tailWord_340559).sum := by decide
  have hdescent : baseEnd_340559 < baseStart_340559 := by decide
  rcases family_descends (prefixWord ++ tailWord_340559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340578 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_340578 : Nat := 118140960795 + 340578 * 2 ^ 59
def prefixEnd_340578 : Nat := 4983230072969 + 3 ^ 40 * 340578 * 2
def baseEnd_340578 : Nat := 116586809564715813805811

theorem tailTrace_340578 : CollatzResearch.WordTrace tailWord_340578 prefixEnd_340578 116586809564715813805811 := by
  unfold tailWord_340578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105475040037886734167597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8281266773434364624446925 3105475040037886734167597)
  ·
    refine ⟨1164553140014207525312849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3105475040037886734167597 1164553140014207525312849)
    ·
      refine ⟨873414855010655643984637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164553140014207525312849 873414855010655643984637)
      ·
        refine ⟨327530570628995866494239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 873414855010655643984637 327530570628995866494239)
        ·
          refine ⟨491295855943493799741359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327530570628995866494239 491295855943493799741359)
          ·
            refine ⟨736943783915240699612039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491295855943493799741359 736943783915240699612039)
            ·
              refine ⟨1105415675872861049418059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736943783915240699612039 1105415675872861049418059)
              ·
                refine ⟨1658123513809291574127089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1105415675872861049418059 1658123513809291574127089)
                ·
                  refine ⟨1243592635356968680595317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1658123513809291574127089 1243592635356968680595317)
                  ·
                    refine ⟨116586809564715813805811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1243592635356968680595317 116586809564715813805811)
                    ·
                      rfl

theorem cell22_340578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_340578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340578 prefixEnd_340578 := by exact prefixLift 340578
  have htrace : WordTrace (prefixWord ++ tailWord_340578) baseStart_340578 baseEnd_340578 := by
    simpa [prefixWord, tailWord_340578, baseEnd_340578] using wordTrace_append hprefix tailTrace_340578
  have hstable : (prefixWord ++ tailWord_340578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340578).length < 2 ^ (prefixWord ++ tailWord_340578).sum := by decide
  have hdescent : baseEnd_340578 < baseStart_340578 := by decide
  rcases family_descends (prefixWord ++ tailWord_340578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340640 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 2, 3]
def baseStart_340640 : Nat := 118140960795 + 340640 * 2 ^ 59
def prefixEnd_340640 : Nat := 4983230072969 + 3 ^ 40 * 340640 * 2
def baseEnd_340640 : Nat := 116608033431768318755621

theorem tailTrace_340640 : CollatzResearch.WordTrace tailWord_340640 prefixEnd_340640 116608033431768318755621 := by
  unfold tailWord_340640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212080742963465762713687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8282774323951287683618249 6212080742963465762713687)
  ·
    refine ⟨9318121114445198644070531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6212080742963465762713687 9318121114445198644070531)
    ·
      refine ⟨13977181671667797966105797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9318121114445198644070531 13977181671667797966105797)
      ·
        refine ⟨2620721563437712118644837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13977181671667797966105797 2620721563437712118644837)
        ·
          refine ⟨491385293144571022245907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2620721563437712118644837 491385293144571022245907)
          ·
            refine ⟨737077939716856533368861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491385293144571022245907 737077939716856533368861)
            ·
              refine ⟨276404227393821200013323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 737077939716856533368861 276404227393821200013323)
              ·
                refine ⟨414606341090731800019985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276404227393821200013323 414606341090731800019985)
                ·
                  refine ⟨310954755818048850014989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414606341090731800019985 310954755818048850014989)
                  ·
                    refine ⟨116608033431768318755621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 310954755818048850014989 116608033431768318755621)
                    ·
                      rfl

theorem cell22_340640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_340640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340640 prefixEnd_340640 := by exact prefixLift 340640
  have htrace : WordTrace (prefixWord ++ tailWord_340640) baseStart_340640 baseEnd_340640 := by
    simpa [prefixWord, tailWord_340640, baseEnd_340640] using wordTrace_append hprefix tailTrace_340640
  have hstable : (prefixWord ++ tailWord_340640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340640).length < 2 ^ (prefixWord ++ tailWord_340640).sum := by decide
  have hdescent : baseEnd_340640 < baseStart_340640 := by decide
  rcases family_descends (prefixWord ++ tailWord_340640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340653 : List Nat := [1, 5, 2, 1, 1, 4, 2, 6]
def baseStart_340653 : Nat := 118140960795 + 340653 * 2 ^ 59
def prefixEnd_340653 : Nat := 4983230072969 + 3 ^ 40 * 340653 * 2
def baseEnd_340653 : Nat := 12956942621937846464509

theorem tailTrace_340653 : CollatzResearch.WordTrace tailWord_340653 prefixEnd_340653 12956942621937846464509 := by
  unfold tailWord_340653
  simp only [CollatzResearch.WordTrace]
  refine ⟨12424635634879834745650613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8283090423253223163767075 12424635634879834745650613)
  ·
    refine ⟨1164809590769984507404745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12424635634879834745650613 1164809590769984507404745)
    ·
      refine ⟨873607193077488380553559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164809590769984507404745 873607193077488380553559)
      ·
        refine ⟨1310410789616232570830339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873607193077488380553559 1310410789616232570830339)
        ·
          refine ⟨1965616184424348856245509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310410789616232570830339 1965616184424348856245509)
          ·
            refine ⟨368553034579565410546033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1965616184424348856245509 368553034579565410546033)
            ·
              refine ⟨276414775934674057909525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368553034579565410546033 276414775934674057909525)
              ·
                refine ⟨12956942621937846464509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 276414775934674057909525 12956942621937846464509)
                ·
                  rfl

theorem cell22_340653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 6].length) (baseStart_340653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340653 prefixEnd_340653 := by exact prefixLift 340653
  have htrace : WordTrace (prefixWord ++ tailWord_340653) baseStart_340653 baseEnd_340653 := by
    simpa [prefixWord, tailWord_340653, baseEnd_340653] using wordTrace_append hprefix tailTrace_340653
  have hstable : (prefixWord ++ tailWord_340653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340653).length < 2 ^ (prefixWord ++ tailWord_340653).sum := by decide
  have hdescent : baseEnd_340653 < baseStart_340653 := by decide
  rcases family_descends (prefixWord ++ tailWord_340653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340679 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 2, 5]
def baseStart_340679 : Nat := 118140960795 + 340679 * 2 ^ 59
def prefixEnd_340679 : Nat := 4983230072969 + 3 ^ 40 * 340679 * 2
def baseEnd_340679 : Nat := 116621383928785217030501

theorem tailTrace_340679 : CollatzResearch.WordTrace tailWord_340679 prefixEnd_340679 116621383928785217030501 := by
  unfold tailWord_340679
  simp only [CollatzResearch.WordTrace]
  refine ⟨12425583932785641186097091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8283722621857094124064727 12425583932785641186097091)
  ·
    refine ⟨18638375899178461779145637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12425583932785641186097091 18638375899178461779145637)
    ·
      refine ⟨3494695481095961583589807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18638375899178461779145637 3494695481095961583589807)
      ·
        refine ⟨5242043221643942375384711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494695481095961583589807 5242043221643942375384711)
        ·
          refine ⟨7863064832465913563077067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5242043221643942375384711 7863064832465913563077067)
          ·
            refine ⟨11794597248698870344615601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7863064832465913563077067 11794597248698870344615601)
            ·
              refine ⟨8845947936524152758461701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11794597248698870344615601 8845947936524152758461701)
              ·
                refine ⟨1658615238098278642211569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8845947936524152758461701 1658615238098278642211569)
                ·
                  refine ⟨1243961428573708981658677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1658615238098278642211569 1243961428573708981658677)
                  ·
                    refine ⟨116621383928785217030501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1243961428573708981658677 116621383928785217030501)
                    ·
                      rfl

theorem cell22_340679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_340679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340679 prefixEnd_340679 := by exact prefixLift 340679
  have htrace : WordTrace (prefixWord ++ tailWord_340679) baseStart_340679 baseEnd_340679 := by
    simpa [prefixWord, tailWord_340679, baseEnd_340679] using wordTrace_append hprefix tailTrace_340679
  have hstable : (prefixWord ++ tailWord_340679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340679).length < 2 ^ (prefixWord ++ tailWord_340679).sum := by decide
  have hdescent : baseEnd_340679 < baseStart_340679 := by decide
  rcases family_descends (prefixWord ++ tailWord_340679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340728 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 1, 4]
def baseStart_340728 : Nat := 118140960795 + 340728 * 2 ^ 59
def prefixEnd_340728 : Nat := 4983230072969 + 3 ^ 40 * 340728 * 2
def baseEnd_340728 : Nat := 116638157630165422555351

theorem tailTrace_340728 : CollatzResearch.WordTrace tailWord_340728 prefixEnd_340728 116638157630165422555351 := by
  unfold tailWord_340728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213685554804061277315419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8284914073072081703087225 6213685554804061277315419)
  ·
    refine ⟨9320528332206091915973129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213685554804061277315419 9320528332206091915973129)
    ·
      refine ⟨6990396249154568936979847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9320528332206091915973129 6990396249154568936979847)
      ·
        refine ⟨10485594373731853405469771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990396249154568936979847 10485594373731853405469771)
        ·
          refine ⟨15728391560597780108204657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10485594373731853405469771 15728391560597780108204657)
          ·
            refine ⟨11796293670448335081153493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15728391560597780108204657 11796293670448335081153493)
            ·
              refine ⟨276475632901132853464535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11796293670448335081153493 276475632901132853464535)
              ·
                refine ⟨414713449351699280196803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276475632901132853464535 414713449351699280196803)
                ·
                  refine ⟨622070174027548920295205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414713449351699280196803 622070174027548920295205)
                  ·
                    refine ⟨116638157630165422555351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 622070174027548920295205 116638157630165422555351)
                    ·
                      rfl

theorem cell22_340728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_340728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340728 prefixEnd_340728 := by exact prefixLift 340728
  have htrace : WordTrace (prefixWord ++ tailWord_340728) baseStart_340728 baseEnd_340728 := by
    simpa [prefixWord, tailWord_340728, baseEnd_340728] using wordTrace_append hprefix tailTrace_340728
  have hstable : (prefixWord ++ tailWord_340728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340728).length < 2 ^ (prefixWord ++ tailWord_340728).sum := by decide
  have hdescent : baseEnd_340728 < baseStart_340728 := by decide
  rcases family_descends (prefixWord ++ tailWord_340728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340739 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 3, 6]
def baseStart_340739 : Nat := 118140960795 + 340739 * 2 ^ 59
def prefixEnd_340739 : Nat := 4983230072969 + 3 ^ 40 * 340739 * 2
def baseEnd_340739 : Nat := 116641923154965060530317

theorem tailTrace_340739 : CollatzResearch.WordTrace tailWord_340739 prefixEnd_340739 116641923154965060530317 := by
  unfold tailWord_340739
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427772312568271433281271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8285181541712180955520847 12427772312568271433281271)
  ·
    refine ⟨18641658468852407149921907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12427772312568271433281271 18641658468852407149921907)
    ·
      refine ⟨27962487703278610724882861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18641658468852407149921907 27962487703278610724882861)
      ·
        refine ⟨10485932888729479021831073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27962487703278610724882861 10485932888729479021831073)
        ·
          refine ⟨7864449666547109266373305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10485932888729479021831073 7864449666547109266373305)
          ·
            refine ⟨5898337249910331949779979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7864449666547109266373305 5898337249910331949779979)
            ·
              refine ⟨8847505874865497924669969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898337249910331949779979 8847505874865497924669969)
              ·
                refine ⟨6635629406149123443502477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8847505874865497924669969 6635629406149123443502477)
                ·
                  refine ⟨2488361027305921291313429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6635629406149123443502477 2488361027305921291313429)
                  ·
                    refine ⟨116641923154965060530317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2488361027305921291313429 116641923154965060530317)
                    ·
                      rfl

theorem cell22_340739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_340739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340739 prefixEnd_340739 := by exact prefixLift 340739
  have htrace : WordTrace (prefixWord ++ tailWord_340739) baseStart_340739 baseEnd_340739 := by
    simpa [prefixWord, tailWord_340739, baseEnd_340739] using wordTrace_append hprefix tailTrace_340739
  have hstable : (prefixWord ++ tailWord_340739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340739).length < 2 ^ (prefixWord ++ tailWord_340739).sum := by decide
  have hdescent : baseEnd_340739 < baseStart_340739 := by decide
  rcases family_descends (prefixWord ++ tailWord_340739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340741 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_340741 : Nat := 118140960795 + 340741 * 2 ^ 59
def prefixEnd_340741 : Nat := 4983230072969 + 3 ^ 40 * 340741 * 2
def baseEnd_340741 : Nat := 116642607795837721980311

theorem tailTrace_340741 : CollatzResearch.WordTrace tailWord_340741 prefixEnd_340741 116642607795837721980311 := by
  unfold tailWord_340741
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427845258561025774854077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8285230172374017183236051 12427845258561025774854077)
  ·
    refine ⟨4660441971960384665570279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12427845258561025774854077 4660441971960384665570279)
    ·
      refine ⟨6990662957940576998355419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4660441971960384665570279 6990662957940576998355419)
      ·
        refine ⟨10485994436910865497533129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990662957940576998355419 10485994436910865497533129)
        ·
          refine ⟨7864495827683149123149847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10485994436910865497533129 7864495827683149123149847)
          ·
            refine ⟨11796743741524723684724771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7864495827683149123149847 11796743741524723684724771)
            ·
              refine ⟨17695115612287085527087157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11796743741524723684724771 17695115612287085527087157)
              ·
                refine ⟨1658917088651914268164421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17695115612287085527087157 1658917088651914268164421)
                ·
                  refine ⟨311046954122233925280829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658917088651914268164421 311046954122233925280829)
                  ·
                    refine ⟨116642607795837721980311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 311046954122233925280829 116642607795837721980311)
                    ·
                      rfl

theorem cell22_340741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_340741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340741 prefixEnd_340741 := by exact prefixLift 340741
  have htrace : WordTrace (prefixWord ++ tailWord_340741) baseStart_340741 baseEnd_340741 := by
    simpa [prefixWord, tailWord_340741, baseEnd_340741] using wordTrace_append hprefix tailTrace_340741
  have hstable : (prefixWord ++ tailWord_340741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340741).length < 2 ^ (prefixWord ++ tailWord_340741).sum := by decide
  have hdescent : baseEnd_340741 < baseStart_340741 := by decide
  rcases family_descends (prefixWord ++ tailWord_340741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340788 : List Nat := [2, 5, 1, 1, 3, 1, 9]
def baseStart_340788 : Nat := 118140960795 + 340788 * 2 ^ 59
def prefixEnd_340788 : Nat := 4983230072969 + 3 ^ 40 * 340788 * 2
def baseEnd_340788 : Nat := 4320692476160935779821

theorem tailTrace_340788 : CollatzResearch.WordTrace tailWord_340788 prefixEnd_340788 4320692476160935779821 := by
  unfold tailWord_340788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214779744695376400907509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8286372992927168534543345 6214779744695376400907509)
  ·
    refine ⟨582635601065191537585079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6214779744695376400907509 582635601065191537585079)
    ·
      refine ⟨873953401597787306377619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582635601065191537585079 873953401597787306377619)
      ·
        refine ⟨1310930102396680959566429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873953401597787306377619 1310930102396680959566429)
        ·
          refine ⟨491598788398755359837411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1310930102396680959566429 491598788398755359837411)
          ·
            refine ⟨737398182598133039756117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491598788398755359837411 737398182598133039756117)
            ·
              refine ⟨4320692476160935779821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 737398182598133039756117 4320692476160935779821)
              ·
                rfl

theorem cell22_340788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 9].length) (baseStart_340788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340788 prefixEnd_340788 := by exact prefixLift 340788
  have htrace : WordTrace (prefixWord ++ tailWord_340788) baseStart_340788 baseEnd_340788 := by
    simpa [prefixWord, tailWord_340788, baseEnd_340788] using wordTrace_append hprefix tailTrace_340788
  have hstable : (prefixWord ++ tailWord_340788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340788).length < 2 ^ (prefixWord ++ tailWord_340788).sum := by decide
  have hdescent : baseEnd_340788 < baseStart_340788 := by decide
  rcases family_descends (prefixWord ++ tailWord_340788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340803 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 3, 3]
def baseStart_340803 : Nat := 118140960795 + 340803 * 2 ^ 59
def prefixEnd_340803 : Nat := 4983230072969 + 3 ^ 40 * 340803 * 2
def baseEnd_340803 : Nat := 116663831662890226930121

theorem tailTrace_340803 : CollatzResearch.WordTrace tailWord_340803 prefixEnd_340803 116663831662890226930121 := by
  unfold tailWord_340803
  simp only [CollatzResearch.WordTrace]
  refine ⟨12430106584336410363611063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8286737722890940242407375 12430106584336410363611063)
  ·
    refine ⟨18645159876504615545416595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12430106584336410363611063 18645159876504615545416595)
    ·
      refine ⟨27967739814756923318124893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18645159876504615545416595 27967739814756923318124893)
      ·
        refine ⟨10487902430533846244296835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27967739814756923318124893 10487902430533846244296835)
        ·
          refine ⟨15731853645800769366445253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10487902430533846244296835 15731853645800769366445253)
          ·
            refine ⟨2949722558587644256208485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15731853645800769366445253 2949722558587644256208485)
            ·
              refine ⟨553072979735183298039091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2949722558587644256208485 553072979735183298039091)
              ·
                refine ⟨829609469602774947058637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553072979735183298039091 829609469602774947058637)
                ·
                  refine ⟨311103551101040605146989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 829609469602774947058637 311103551101040605146989)
                  ·
                    refine ⟨116663831662890226930121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 311103551101040605146989 116663831662890226930121)
                    ·
                      rfl

theorem cell22_340803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 3].length) (baseStart_340803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340803 prefixEnd_340803 := by exact prefixLift 340803
  have htrace : WordTrace (prefixWord ++ tailWord_340803) baseStart_340803 baseEnd_340803 := by
    simpa [prefixWord, tailWord_340803, baseEnd_340803] using wordTrace_append hprefix tailTrace_340803
  have hstable : (prefixWord ++ tailWord_340803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340803).length < 2 ^ (prefixWord ++ tailWord_340803).sum := by decide
  have hdescent : baseEnd_340803 < baseStart_340803 := by decide
  rcases family_descends (prefixWord ++ tailWord_340803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340816 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 5]
def baseStart_340816 : Nat := 118140960795 + 340816 * 2 ^ 59
def prefixEnd_340816 : Nat := 4983230072969 + 3 ^ 40 * 340816 * 2
def baseEnd_340816 : Nat := 38889427276187508785027

theorem tailTrace_340816 : CollatzResearch.WordTrace tailWord_340816 prefixEnd_340816 38889427276187508785027 := by
  unfold tailWord_340816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215290366644656791917151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8287053822192875722556201 6215290366644656791917151)
  ·
    refine ⟨9322935549966985187875727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215290366644656791917151 9322935549966985187875727)
    ·
      refine ⟨13984403324950477781813591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9322935549966985187875727 13984403324950477781813591)
      ·
        refine ⟨20976604987425716672720387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13984403324950477781813591 20976604987425716672720387)
        ·
          refine ⟨31464907481138575009080581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20976604987425716672720387 31464907481138575009080581)
          ·
            refine ⟨5899670152713482814202609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31464907481138575009080581 5899670152713482814202609)
            ·
              refine ⟨4424752614535112110651957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5899670152713482814202609 4424752614535112110651957)
              ·
                refine ⟨414820557612666760373621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4424752614535112110651957 414820557612666760373621)
                ·
                  refine ⟨38889427276187508785027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 414820557612666760373621 38889427276187508785027)
                  ·
                    rfl

theorem cell22_340816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_340816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340816 prefixEnd_340816 := by exact prefixLift 340816
  have htrace : WordTrace (prefixWord ++ tailWord_340816) baseStart_340816 baseEnd_340816 := by
    simpa [prefixWord, tailWord_340816, baseEnd_340816] using wordTrace_append hprefix tailTrace_340816
  have hstable : (prefixWord ++ tailWord_340816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340816).length < 2 ^ (prefixWord ++ tailWord_340816).sum := by decide
  have hdescent : baseEnd_340816 < baseStart_340816 := by decide
  rcases family_descends (prefixWord ++ tailWord_340816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340893 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_340893 : Nat := 118140960795 + 340893 * 2 ^ 59
def prefixEnd_340893 : Nat := 4983230072969 + 3 ^ 40 * 340893 * 2
def baseEnd_340893 : Nat := 116694640502159992179845

theorem tailTrace_340893 : CollatzResearch.WordTrace tailWord_340893 prefixEnd_340893 116694640502159992179845 := by
  unfold tailWord_340893
  simp only [CollatzResearch.WordTrace]
  refine ⟨12433389154010355734387333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8288926102673570489591555 12433389154010355734387333)
  ·
    refine ⟨2331260466376941700197625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12433389154010355734387333 2331260466376941700197625)
    ·
      refine ⟨1748445349782706275148219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2331260466376941700197625 1748445349782706275148219)
      ·
        refine ⟨2622668024674059412722329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748445349782706275148219 2622668024674059412722329)
        ·
          refine ⟨1967001018505544559541747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2622668024674059412722329 1967001018505544559541747)
          ·
            refine ⟨2950501527758316839312621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1967001018505544559541747 2950501527758316839312621)
            ·
              refine ⟨1106438072909368814742233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2950501527758316839312621 1106438072909368814742233)
              ·
                refine ⟨829828554682026611056675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106438072909368814742233 829828554682026611056675)
                ·
                  refine ⟨1244742832023039916585013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829828554682026611056675 1244742832023039916585013)
                  ·
                    refine ⟨116694640502159992179845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1244742832023039916585013 116694640502159992179845)
                    ·
                      rfl

theorem cell22_340893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_340893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340893 prefixEnd_340893 := by exact prefixLift 340893
  have htrace : WordTrace (prefixWord ++ tailWord_340893) baseStart_340893 baseEnd_340893 := by
    simpa [prefixWord, tailWord_340893, baseEnd_340893] using wordTrace_append hprefix tailTrace_340893
  have hstable : (prefixWord ++ tailWord_340893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340893).length < 2 ^ (prefixWord ++ tailWord_340893).sum := by decide
  have hdescent : baseEnd_340893 < baseStart_340893 := by decide
  rcases family_descends (prefixWord ++ tailWord_340893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340897 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 1, 4]
def baseStart_340897 : Nat := 118140960795 + 340897 * 2 ^ 59
def prefixEnd_340897 : Nat := 4983230072969 + 3 ^ 40 * 340897 * 2
def baseEnd_340897 : Nat := 116696009783905315079833

theorem tailTrace_340897 : CollatzResearch.WordTrace tailWord_340897 prefixEnd_340897 116696009783905315079833 := by
  unfold tailWord_340897
  simp only [CollatzResearch.WordTrace]
  refine ⟨12433535045995864417532945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8289023363997242945021963 12433535045995864417532945)
  ·
    refine ⟨9325151284496898313149709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12433535045995864417532945 9325151284496898313149709)
    ·
      refine ⟨3496931731686336867431141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9325151284496898313149709 3496931731686336867431141)
      ·
        refine ⟨655674699691188162643339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3496931731686336867431141 655674699691188162643339)
        ·
          refine ⟨983512049536782243965009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655674699691188162643339 983512049536782243965009)
          ·
            refine ⟨737634037152586682973757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983512049536782243965009 737634037152586682973757)
            ·
              refine ⟨276612763932220006115159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 737634037152586682973757 276612763932220006115159)
              ·
                refine ⟨414919145898330009172739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276612763932220006115159 414919145898330009172739)
                ·
                  refine ⟨622378718847495013759109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414919145898330009172739 622378718847495013759109)
                  ·
                    refine ⟨116696009783905315079833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 622378718847495013759109 116696009783905315079833)
                    ·
                      rfl

theorem cell22_340897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_340897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340897 prefixEnd_340897 := by exact prefixLift 340897
  have htrace : WordTrace (prefixWord ++ tailWord_340897) baseStart_340897 baseEnd_340897 := by
    simpa [prefixWord, tailWord_340897, baseEnd_340897] using wordTrace_append hprefix tailTrace_340897
  have hstable : (prefixWord ++ tailWord_340897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340897).length < 2 ^ (prefixWord ++ tailWord_340897).sum := by decide
  have hdescent : baseEnd_340897 < baseStart_340897 := by decide
  rcases family_descends (prefixWord ++ tailWord_340897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340985 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 5]
def baseStart_340985 : Nat := 118140960795 + 340985 * 2 ^ 59
def prefixEnd_340985 : Nat := 4983230072969 + 3 ^ 40 * 340985 * 2
def baseEnd_340985 : Nat := 38908711327434139626521

theorem tailTrace_340985 : CollatzResearch.WordTrace tailWord_340985 prefixEnd_340985 38908711327434139626521 := by
  unfold tailWord_340985
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436744669677055446736409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8291163113118036964490939 12436744669677055446736409)
  ·
    refine ⟨9327558502257791585052307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12436744669677055446736409 9327558502257791585052307)
    ·
      refine ⟨13991337753386687377578461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9327558502257791585052307 13991337753386687377578461)
      ·
        refine ⟨5246751657520007766591923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13991337753386687377578461 5246751657520007766591923)
        ·
          refine ⟨7870127486280011649887885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5246751657520007766591923 7870127486280011649887885)
          ·
            refine ⟨2951297807355004368707957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7870127486280011649887885 2951297807355004368707957)
            ·
              refine ⟨276684169439531659566371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2951297807355004368707957 276684169439531659566371)
              ·
                refine ⟨415026254159297489349557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276684169439531659566371 415026254159297489349557)
                ·
                  refine ⟨38908711327434139626521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415026254159297489349557 38908711327434139626521)
                  ·
                    rfl

theorem cell22_340985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 5].length) (baseStart_340985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_340985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_340985 prefixEnd_340985 := by exact prefixLift 340985
  have htrace : WordTrace (prefixWord ++ tailWord_340985) baseStart_340985 baseEnd_340985 := by
    simpa [prefixWord, tailWord_340985, baseEnd_340985] using wordTrace_append hprefix tailTrace_340985
  have hstable : (prefixWord ++ tailWord_340985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340985).length < 2 ^ (prefixWord ++ tailWord_340985).sum := by decide
  have hdescent : baseEnd_340985 < baseStart_340985 := by decide
  rcases family_descends (prefixWord ++ tailWord_340985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341043 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 6, 4]
def baseStart_341043 : Nat := 118140960795 + 341043 * 2 ^ 59
def prefixEnd_341043 : Nat := 4983230072969 + 3 ^ 40 * 341043 * 2
def baseEnd_341043 : Nat := 116745988567609600929385

theorem tailTrace_341043 : CollatzResearch.WordTrace tailWord_341043 prefixEnd_341043 116745988567609600929385 := by
  unfold tailWord_341043
  simp only [CollatzResearch.WordTrace]
  refine ⟨12438860103466931352347783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8292573402311287568231855 12438860103466931352347783)
  ·
    refine ⟨18658290155200397028521675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12438860103466931352347783 18658290155200397028521675)
    ·
      refine ⟨27987435232800595542782513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18658290155200397028521675 27987435232800595542782513)
      ·
        refine ⟨20990576424600446657086885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27987435232800595542782513 20990576424600446657086885)
        ·
          refine ⟨3935733079612583748203791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20990576424600446657086885 3935733079612583748203791)
          ·
            refine ⟨5903599619418875622305687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3935733079612583748203791 5903599619418875622305687)
            ·
              refine ⟨8855399429128313433458531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5903599619418875622305687 8855399429128313433458531)
              ·
                refine ⟨13283099143692470150187797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8855399429128313433458531 13283099143692470150187797)
                ·
                  refine ⟨622645272360584538290053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13283099143692470150187797 622645272360584538290053)
                  ·
                    refine ⟨116745988567609600929385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 622645272360584538290053 116745988567609600929385)
                    ·
                      rfl

theorem cell22_341043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_341043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341043 prefixEnd_341043 := by exact prefixLift 341043
  have htrace : WordTrace (prefixWord ++ tailWord_341043) baseStart_341043 baseEnd_341043 := by
    simpa [prefixWord, tailWord_341043, baseEnd_341043] using wordTrace_append hprefix tailTrace_341043
  have hstable : (prefixWord ++ tailWord_341043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341043).length < 2 ^ (prefixWord ++ tailWord_341043).sum := by decide
  have hdescent : baseEnd_341043 < baseStart_341043 := by decide
  rcases family_descends (prefixWord ++ tailWord_341043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341062 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_341062 : Nat := 118140960795 + 341062 * 2 ^ 59
def prefixEnd_341062 : Nat := 4983230072969 + 3 ^ 40 * 341062 * 2
def baseEnd_341062 : Nat := 116752492655899884704327

theorem tailTrace_341062 : CollatzResearch.WordTrace tailWord_341062 prefixEnd_341062 116752492655899884704327 := by
  unfold tailWord_341062
  simp only [CollatzResearch.WordTrace]
  refine ⟨388736034074940549915295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8293035393598731731526293 388736034074940549915295)
  ·
    refine ⟨583104051112410824872943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388736034074940549915295 583104051112410824872943)
    ·
      refine ⟨874656076668616237309415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583104051112410824872943 874656076668616237309415)
      ·
        refine ⟨1311984115002924355964123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874656076668616237309415 1311984115002924355964123)
        ·
          refine ⟨1967976172504386533946185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1311984115002924355964123 1967976172504386533946185)
          ·
            refine ⟨1475982129378289900459639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1967976172504386533946185 1475982129378289900459639)
            ·
              refine ⟨2213973194067434850689459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475982129378289900459639 2213973194067434850689459)
              ·
                refine ⟨3320959791101152276034189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2213973194067434850689459 3320959791101152276034189)
                ·
                  refine ⟨1245359921662932103512821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3320959791101152276034189 1245359921662932103512821)
                  ·
                    refine ⟨116752492655899884704327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1245359921662932103512821 116752492655899884704327)
                    ·
                      rfl

theorem cell22_341062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_341062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341062 prefixEnd_341062 := by exact prefixLift 341062
  have htrace : WordTrace (prefixWord ++ tailWord_341062) baseStart_341062 baseEnd_341062 := by
    simpa [prefixWord, tailWord_341062, baseEnd_341062] using wordTrace_append hprefix tailTrace_341062
  have hstable : (prefixWord ++ tailWord_341062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341062).length < 2 ^ (prefixWord ++ tailWord_341062).sum := by decide
  have hdescent : baseEnd_341062 < baseStart_341062 := by decide
  rcases family_descends (prefixWord ++ tailWord_341062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341088 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_341088 : Nat := 118140960795 + 341088 * 2 ^ 59
def prefixEnd_341088 : Nat := 4983230072969 + 3 ^ 40 * 341088 * 2
def baseEnd_341088 : Nat := 116761392987244483554247

theorem tailTrace_341088 : CollatzResearch.WordTrace tailWord_341088 prefixEnd_341088 116761392987244483554247 := by
  unfold tailWord_341088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6220250694151952018867959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8293667592202602691823945 6220250694151952018867959)
  ·
    refine ⟨9330376041227928028301939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6220250694151952018867959 9330376041227928028301939)
    ·
      refine ⟨13995564061841892042452909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9330376041227928028301939 13995564061841892042452909)
      ·
        refine ⟨5248336523190709515919841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13995564061841892042452909 5248336523190709515919841)
        ·
          refine ⟨3936252392393032136939881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5248336523190709515919841 3936252392393032136939881)
          ·
            refine ⟨2952189294294774102704911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3936252392393032136939881 2952189294294774102704911)
            ·
              refine ⟨4428283941442161154057367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2952189294294774102704911 4428283941442161154057367)
              ·
                refine ⟨6642425912163241731086051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428283941442161154057367 6642425912163241731086051)
                ·
                  refine ⟨9963638868244862596629077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642425912163241731086051 9963638868244862596629077)
                  ·
                    refine ⟨116761392987244483554247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9963638868244862596629077 116761392987244483554247)
                    ·
                      rfl

theorem cell22_341088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_341088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341088 prefixEnd_341088 := by exact prefixLift 341088
  have htrace : WordTrace (prefixWord ++ tailWord_341088) baseStart_341088 baseEnd_341088 := by
    simpa [prefixWord, tailWord_341088, baseEnd_341088] using wordTrace_append hprefix tailTrace_341088
  have hstable : (prefixWord ++ tailWord_341088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341088).length < 2 ^ (prefixWord ++ tailWord_341088).sum := by decide
  have hdescent : baseEnd_341088 < baseStart_341088 := by decide
  rcases family_descends (prefixWord ++ tailWord_341088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341109 : List Nat := [1, 3, 4, 3, 1, 1, 3, 6]
def baseStart_341109 : Nat := 118140960795 + 341109 * 2 ^ 59
def prefixEnd_341109 : Nat := 4983230072969 + 3 ^ 40 * 341109 * 2
def baseEnd_341109 : Nat := 12974286857378603197687

theorem tailTrace_341109 : CollatzResearch.WordTrace tailWord_341109 prefixEnd_341109 12974286857378603197687 := by
  unfold tailWord_341109
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441267321227824624250381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8294178214151883082833587 12441267321227824624250381)
  ·
    refine ⟨4665475245460434234093893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12441267321227824624250381 4665475245460434234093893)
    ·
      refine ⟨874776608523831418892605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4665475245460434234093893 874776608523831418892605)
      ·
        refine ⟨328041228196436782084727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 874776608523831418892605 328041228196436782084727)
        ·
          refine ⟨492061842294655173127091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328041228196436782084727 492061842294655173127091)
          ·
            refine ⟨738092763441982759690637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492061842294655173127091 738092763441982759690637)
            ·
              refine ⟨276784786290743534883989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 738092763441982759690637 276784786290743534883989)
              ·
                refine ⟨12974286857378603197687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 276784786290743534883989 12974286857378603197687)
                ·
                  rfl

theorem cell22_341109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 6].length) (baseStart_341109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341109 prefixEnd_341109 := by exact prefixLift 341109
  have htrace : WordTrace (prefixWord ++ tailWord_341109) baseStart_341109 baseEnd_341109 := by
    simpa [prefixWord, tailWord_341109, baseEnd_341109] using wordTrace_append hprefix tailTrace_341109
  have hstable : (prefixWord ++ tailWord_341109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341109).length < 2 ^ (prefixWord ++ tailWord_341109).sum := by decide
  have hdescent : baseEnd_341109 < baseStart_341109 := by decide
  rcases family_descends (prefixWord ++ tailWord_341109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341124 : List Nat := [2, 3, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_341124 : Nat := 118140960795 + 341124 * 2 ^ 59
def prefixEnd_341124 : Nat := 4983230072969 + 3 ^ 40 * 341124 * 2
def baseEnd_341124 : Nat := 116773716522952389654137

theorem tailTrace_341124 : CollatzResearch.WordTrace tailWord_341124 prefixEnd_341124 116773716522952389654137 := by
  unfold tailWord_341124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6220907208086741093023213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8294542944115654790697617 6220907208086741093023213)
  ·
    refine ⟨2332840203032527909883705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6220907208086741093023213 2332840203032527909883705)
    ·
      refine ⟨1749630152274395932412779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2332840203032527909883705 1749630152274395932412779)
      ·
        refine ⟨2624445228411593898619169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749630152274395932412779 2624445228411593898619169)
        ·
          refine ⟨1968333921308695423964377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2624445228411593898619169 1968333921308695423964377)
          ·
            refine ⟨1476250440981521567973283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1968333921308695423964377 1476250440981521567973283)
            ·
              refine ⟨2214375661472282351959925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476250440981521567973283 2214375661472282351959925)
              ·
                refine ⟨207597718263026470496243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2214375661472282351959925 207597718263026470496243)
                ·
                  refine ⟨311396577394539705744365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207597718263026470496243 311396577394539705744365)
                  ·
                    refine ⟨116773716522952389654137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 311396577394539705744365 116773716522952389654137)
                    ·
                      rfl

theorem cell22_341124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_341124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341124 prefixEnd_341124 := by exact prefixLift 341124
  have htrace : WordTrace (prefixWord ++ tailWord_341124) baseStart_341124 baseEnd_341124 := by
    simpa [prefixWord, tailWord_341124, baseEnd_341124] using wordTrace_append hprefix tailTrace_341124
  have hstable : (prefixWord ++ tailWord_341124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341124).length < 2 ^ (prefixWord ++ tailWord_341124).sum := by decide
  have hdescent : baseEnd_341124 < baseStart_341124 := by decide
  rcases family_descends (prefixWord ++ tailWord_341124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341229 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_341229 : Nat := 118140960795 + 341229 * 2 ^ 59
def prefixEnd_341229 : Nat := 4983230072969 + 3 ^ 40 * 341229 * 2
def baseEnd_341229 : Nat := 116809660168767115778815

theorem tailTrace_341229 : CollatzResearch.WordTrace tailWord_341229 prefixEnd_341229 116809660168767115778815 := by
  unfold tailWord_341229
  simp only [CollatzResearch.WordTrace]
  refine ⟨12445644080793085118618741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8297096053862056745745827 12445644080793085118618741)
  ·
    refine ⟨1166779132574351729870507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12445644080793085118618741 1166779132574351729870507)
    ·
      refine ⟨1750168698861527594805761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166779132574351729870507 1750168698861527594805761)
      ·
        refine ⟨1312626524146145696104321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1750168698861527594805761 1312626524146145696104321)
        ·
          refine ⟨984469893109609272078241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312626524146145696104321 984469893109609272078241)
          ·
            refine ⟨738352419832206954058681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984469893109609272078241 738352419832206954058681)
            ·
              refine ⟨553764314874155215544011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738352419832206954058681 553764314874155215544011)
              ·
                refine ⟨830646472311232823316017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553764314874155215544011 830646472311232823316017)
                ·
                  refine ⟨622984854233424617487013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 830646472311232823316017 622984854233424617487013)
                  ·
                    refine ⟨116809660168767115778815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 622984854233424617487013 116809660168767115778815)
                    ·
                      rfl

theorem cell22_341229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_341229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341229 prefixEnd_341229 := by exact prefixLift 341229
  have htrace : WordTrace (prefixWord ++ tailWord_341229) baseStart_341229 baseEnd_341229 := by
    simpa [prefixWord, tailWord_341229, baseEnd_341229] using wordTrace_append hprefix tailTrace_341229
  have hstable : (prefixWord ++ tailWord_341229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341229).length < 2 ^ (prefixWord ++ tailWord_341229).sum := by decide
  have hdescent : baseEnd_341229 < baseStart_341229 := by decide
  rcases family_descends (prefixWord ++ tailWord_341229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341250 : List Nat := [3, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_341250 : Nat := 118140960795 + 341250 * 2 ^ 59
def prefixEnd_341250 : Nat := 4983230072969 + 3 ^ 40 * 341250 * 2
def baseEnd_341250 : Nat := 38938949632643353667917

theorem tailTrace_341250 : CollatzResearch.WordTrace tailWord_341250 prefixEnd_341250 38938949632643353667917 := by
  unfold tailWord_341250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111602503429251426283301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8297606675811337136755469 3111602503429251426283301)
  ·
    refine ⟨583425469392984642428119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3111602503429251426283301 583425469392984642428119)
    ·
      refine ⟨875138204089476963642179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583425469392984642428119 875138204089476963642179)
      ·
        refine ⟨1312707306134215445463269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875138204089476963642179 1312707306134215445463269)
        ·
          refine ⟨246132619900165396024363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1312707306134215445463269 246132619900165396024363)
          ·
            refine ⟨369198929850248094036545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246132619900165396024363 369198929850248094036545)
            ·
              refine ⟨276899197387686070527409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369198929850248094036545 276899197387686070527409)
              ·
                refine ⟨207674398040764552895557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276899197387686070527409 207674398040764552895557)
                ·
                  refine ⟨38938949632643353667917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207674398040764552895557 38938949632643353667917)
                  ·
                    rfl

theorem cell22_341250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_341250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341250 prefixEnd_341250 := by exact prefixLift 341250
  have htrace : WordTrace (prefixWord ++ tailWord_341250) baseStart_341250 baseEnd_341250 := by
    simpa [prefixWord, tailWord_341250, baseEnd_341250] using wordTrace_append hprefix tailTrace_341250
  have hstable : (prefixWord ++ tailWord_341250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341250).length < 2 ^ (prefixWord ++ tailWord_341250).sum := by decide
  have hdescent : baseEnd_341250 < baseStart_341250 := by decide
  rcases family_descends (prefixWord ++ tailWord_341250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341272 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 5]
def baseStart_341272 : Nat := 118140960795 + 341272 * 2 ^ 59
def prefixEnd_341272 : Nat := 4983230072969 + 3 ^ 40 * 341272 * 2
def baseEnd_341272 : Nat := 38941459982509778984561

theorem tailTrace_341272 : CollatzResearch.WordTrace tailWord_341272 prefixEnd_341272 38941459982509778984561 := by
  unfold tailWord_341272
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223606209818651731217035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8298141613091535641622713 6223606209818651731217035)
  ·
    refine ⟨9335409314727977596825553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6223606209818651731217035 9335409314727977596825553)
    ·
      refine ⟨7001556986045983197619165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9335409314727977596825553 7001556986045983197619165)
      ·
        refine ⟨2625583869767243699107187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7001556986045983197619165 2625583869767243699107187)
        ·
          refine ⟨3938375804650865548660781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2625583869767243699107187 3938375804650865548660781)
          ·
            refine ⟨1476890926744074580747793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3938375804650865548660781 1476890926744074580747793)
            ·
              refine ⟨1107668195058055935560845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476890926744074580747793 1107668195058055935560845)
              ·
                refine ⟨415375573146770975835317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1107668195058055935560845 415375573146770975835317)
                ·
                  refine ⟨38941459982509778984561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415375573146770975835317 38941459982509778984561)
                  ·
                    rfl

theorem cell22_341272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_341272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341272 prefixEnd_341272 := by exact prefixLift 341272
  have htrace : WordTrace (prefixWord ++ tailWord_341272) baseStart_341272 baseEnd_341272 := by
    simpa [prefixWord, tailWord_341272, baseEnd_341272] using wordTrace_append hprefix tailTrace_341272
  have hstable : (prefixWord ++ tailWord_341272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341272).length < 2 ^ (prefixWord ++ tailWord_341272).sum := by decide
  have hdescent : baseEnd_341272 < baseStart_341272 := by decide
  rcases family_descends (prefixWord ++ tailWord_341272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341293 : List Nat := [1, 5, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_341293 : Nat := 118140960795 + 341293 * 2 ^ 59
def prefixEnd_341293 : Nat := 4983230072969 + 3 ^ 40 * 341293 * 2
def baseEnd_341293 : Nat := 116831568676692282178619

theorem tailTrace_341293 : CollatzResearch.WordTrace tailWord_341293 prefixEnd_341293 116831568676692282178619 := by
  unfold tailWord_341293
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447978352561224048948533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8298652235040816032632355 12447978352561224048948533)
  ·
    refine ⟨1166997970552614754588925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12447978352561224048948533 1166997970552614754588925)
    ·
      refine ⟨437624238957230532970847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1166997970552614754588925 437624238957230532970847)
      ·
        refine ⟨656436358435845799456271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437624238957230532970847 656436358435845799456271)
        ·
          refine ⟨984654537653768699184407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656436358435845799456271 984654537653768699184407)
          ·
            refine ⟨1476981806480653048776611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984654537653768699184407 1476981806480653048776611)
            ·
              refine ⟨2215472709720979573164917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476981806480653048776611 2215472709720979573164917)
              ·
                refine ⟨207700566536341834984211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2215472709720979573164917 207700566536341834984211)
                ·
                  refine ⟨311550849804512752476317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207700566536341834984211 311550849804512752476317)
                  ·
                    refine ⟨116831568676692282178619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 311550849804512752476317 116831568676692282178619)
                    ·
                      rfl

theorem cell22_341293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_341293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341293 prefixEnd_341293 := by exact prefixLift 341293
  have htrace : WordTrace (prefixWord ++ tailWord_341293) baseStart_341293 baseEnd_341293 := by
    simpa [prefixWord, tailWord_341293, baseEnd_341293] using wordTrace_append hprefix tailTrace_341293
  have hstable : (prefixWord ++ tailWord_341293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341293).length < 2 ^ (prefixWord ++ tailWord_341293).sum := by decide
  have hdescent : baseEnd_341293 < baseStart_341293 := by decide
  rcases family_descends (prefixWord ++ tailWord_341293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341347 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 1, 6]
def baseStart_341347 : Nat := 118140960795 + 341347 * 2 ^ 59
def prefixEnd_341347 : Nat := 4983230072969 + 3 ^ 40 * 341347 * 2
def baseEnd_341347 : Nat := 116850053980254141328453

theorem tailTrace_341347 : CollatzResearch.WordTrace tailWord_341347 prefixEnd_341347 116850053980254141328453 := by
  unfold tailWord_341347
  simp only [CollatzResearch.WordTrace]
  refine ⟨12449947894365591271414295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8299965262910394180942863 12449947894365591271414295)
  ·
    refine ⟨18674921841548386907121443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12449947894365591271414295 18674921841548386907121443)
    ·
      refine ⟨28012382762322580360682165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18674921841548386907121443 28012382762322580360682165)
      ·
        refine ⟨2626160883967741908813953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28012382762322580360682165 2626160883967741908813953)
        ·
          refine ⟨1969620662975806431610465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2626160883967741908813953 1969620662975806431610465)
          ·
            refine ⟨1477215497231854823707849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1969620662975806431610465 1477215497231854823707849)
            ·
              refine ⟨1107911622923891117780887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477215497231854823707849 1107911622923891117780887)
              ·
                refine ⟨1661867434385836676671331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107911622923891117780887 1661867434385836676671331)
                ·
                  refine ⟨2492801151578755015006997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661867434385836676671331 2492801151578755015006997)
                  ·
                    refine ⟨116850053980254141328453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2492801151578755015006997 116850053980254141328453)
                    ·
                      rfl

theorem cell22_341347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_341347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341347 prefixEnd_341347 := by exact prefixLift 341347
  have htrace : WordTrace (prefixWord ++ tailWord_341347) baseStart_341347 baseEnd_341347 := by
    simpa [prefixWord, tailWord_341347, baseEnd_341347] using wordTrace_append hprefix tailTrace_341347
  have hstable : (prefixWord ++ tailWord_341347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341347).length < 2 ^ (prefixWord ++ tailWord_341347).sum := by decide
  have hdescent : baseEnd_341347 < baseStart_341347 := by decide
  rcases family_descends (prefixWord ++ tailWord_341347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341383 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 2, 3]
def baseStart_341383 : Nat := 118140960795 + 341383 * 2 ^ 59
def prefixEnd_341383 : Nat := 4983230072969 + 3 ^ 40 * 341383 * 2
def baseEnd_341383 : Nat := 116862377515962047428343

theorem tailTrace_341383 : CollatzResearch.WordTrace tailWord_341383 prefixEnd_341383 116862377515962047428343 := by
  unfold tailWord_341383
  simp only [CollatzResearch.WordTrace]
  refine ⟨12451260922235169419724803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8300840614823446279816535 12451260922235169419724803)
  ·
    refine ⟨18676891383352754129587205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12451260922235169419724803 18676891383352754129587205)
    ·
      refine ⟨3501917134378641399297601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18676891383352754129587205 3501917134378641399297601)
      ·
        refine ⟨2626437850783981049473201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3501917134378641399297601 2626437850783981049473201)
        ·
          refine ⟨1969828388087985787104901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2626437850783981049473201 1969828388087985787104901)
          ·
            refine ⟨369342822766497335082169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1969828388087985787104901 369342822766497335082169)
            ·
              refine ⟨277007117074873001311627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369342822766497335082169 277007117074873001311627)
              ·
                refine ⟨415510675612309501967441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277007117074873001311627 415510675612309501967441)
                ·
                  refine ⟨311633006709232126475581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415510675612309501967441 311633006709232126475581)
                  ·
                    refine ⟨116862377515962047428343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 311633006709232126475581 116862377515962047428343)
                    ·
                      rfl

theorem cell22_341383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_341383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341383 prefixEnd_341383 := by exact prefixLift 341383
  have htrace : WordTrace (prefixWord ++ tailWord_341383) baseStart_341383 baseEnd_341383 := by
    simpa [prefixWord, tailWord_341383, baseEnd_341383] using wordTrace_append hprefix tailTrace_341383
  have hstable : (prefixWord ++ tailWord_341383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341383).length < 2 ^ (prefixWord ++ tailWord_341383).sum := by decide
  have hdescent : baseEnd_341383 < baseStart_341383 := by decide
  rcases family_descends (prefixWord ++ tailWord_341383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341411 : List Nat := [1, 1, 1, 4, 1, 3, 2, 5, 1, 3]
def baseStart_341411 : Nat := 118140960795 + 341411 * 2 ^ 59
def prefixEnd_341411 : Nat := 4983230072969 + 3 ^ 40 * 341411 * 2
def baseEnd_341411 : Nat := 116871962488179307728257

theorem tailTrace_341411 : CollatzResearch.WordTrace tailWord_341411 prefixEnd_341411 116871962488179307728257 := by
  unfold tailWord_341411
  simp only [CollatzResearch.WordTrace]
  refine ⟨12452282166133730201744087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8301521444089153467829391 12452282166133730201744087)
  ·
    refine ⟨18678423249200595302616131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12452282166133730201744087 18678423249200595302616131)
    ·
      refine ⟨28017634873800892953924197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18678423249200595302616131 28017634873800892953924197)
      ·
        refine ⟨5253306538837667428860787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28017634873800892953924197 5253306538837667428860787)
        ·
          refine ⟨7879959808256501143291181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5253306538837667428860787 7879959808256501143291181)
          ·
            refine ⟨2954984928096187928734193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7879959808256501143291181 2954984928096187928734193)
            ·
              refine ⟨2216238696072140946550645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2954984928096187928734193 2216238696072140946550645)
              ·
                refine ⟨207772377756763213739123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2216238696072140946550645 207772377756763213739123)
                ·
                  refine ⟨311658566635144820608685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207772377756763213739123 311658566635144820608685)
                  ·
                    refine ⟨116871962488179307728257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 311658566635144820608685 116871962488179307728257)
                    ·
                      rfl

theorem cell22_341411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 3].length) (baseStart_341411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341411 prefixEnd_341411 := by exact prefixLift 341411
  have htrace : WordTrace (prefixWord ++ tailWord_341411) baseStart_341411 baseEnd_341411 := by
    simpa [prefixWord, tailWord_341411, baseEnd_341411] using wordTrace_append hprefix tailTrace_341411
  have hstable : (prefixWord ++ tailWord_341411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341411).length < 2 ^ (prefixWord ++ tailWord_341411).sum := by decide
  have hdescent : baseEnd_341411 < baseStart_341411 := by decide
  rcases family_descends (prefixWord ++ tailWord_341411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341454 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_341454 : Nat := 118140960795 + 341454 * 2 ^ 59
def prefixEnd_341454 : Nat := 4983230072969 + 3 ^ 40 * 341454 * 2
def baseEnd_341454 : Nat := 116886682266941528903125

theorem tailTrace_341454 : CollatzResearch.WordTrace tailWord_341454 prefixEnd_341454 116886682266941528903125 := by
  unfold tailWord_341454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556731313122243568194927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8302567003318632363706277 1556731313122243568194927)
  ·
    refine ⟨2335096969683365352292391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556731313122243568194927 2335096969683365352292391)
    ·
      refine ⟨3502645454525048028438587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2335096969683365352292391 3502645454525048028438587)
      ·
        refine ⟨5253968181787572042657881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3502645454525048028438587 5253968181787572042657881)
        ·
          refine ⟨3940476136340679031993411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253968181787572042657881 3940476136340679031993411)
          ·
            refine ⟨5910714204511018547990117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940476136340679031993411 5910714204511018547990117)
            ·
              refine ⟨1108258913345815977748147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5910714204511018547990117 1108258913345815977748147)
              ·
                refine ⟨1662388370018723966622221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108258913345815977748147 1662388370018723966622221)
                ·
                  refine ⟨623395638757021487483333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1662388370018723966622221 623395638757021487483333)
                  ·
                    refine ⟨116886682266941528903125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 623395638757021487483333 116886682266941528903125)
                    ·
                      rfl

theorem cell22_341454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_341454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341454 prefixEnd_341454 := by exact prefixLift 341454
  have htrace : WordTrace (prefixWord ++ tailWord_341454) baseStart_341454 baseEnd_341454 := by
    simpa [prefixWord, tailWord_341454, baseEnd_341454] using wordTrace_append hprefix tailTrace_341454
  have hstable : (prefixWord ++ tailWord_341454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341454).length < 2 ^ (prefixWord ++ tailWord_341454).sum := by decide
  have hdescent : baseEnd_341454 < baseStart_341454 := by decide
  rcases family_descends (prefixWord ++ tailWord_341454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341486 : List Nat := [4, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_341486 : Nat := 118140960795 + 341486 * 2 ^ 59
def prefixEnd_341486 : Nat := 4983230072969 + 3 ^ 40 * 341486 * 2
def baseEnd_341486 : Nat := 38965878840301370701009

theorem tailTrace_341486 : CollatzResearch.WordTrace tailWord_341486 prefixEnd_341486 38965878840301370701009 := by
  unfold tailWord_341486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556877205107752251340539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8303345093908012007149541 1556877205107752251340539)
  ·
    refine ⟨2335315807661628377010809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556877205107752251340539 2335315807661628377010809)
    ·
      refine ⟨1751486855746221282758107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2335315807661628377010809 1751486855746221282758107)
      ·
        refine ⟨2627230283619331924137161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751486855746221282758107 2627230283619331924137161)
        ·
          refine ⟨1970422712714498943102871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627230283619331924137161 1970422712714498943102871)
          ·
            refine ⟨2955634069071748414654307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970422712714498943102871 2955634069071748414654307)
            ·
              refine ⟨4433451103607622621981461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2955634069071748414654307 4433451103607622621981461)
              ·
                refine ⟨207818020481607310405381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4433451103607622621981461 207818020481607310405381)
                ·
                  refine ⟨38965878840301370701009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 207818020481607310405381 38965878840301370701009)
                  ·
                    rfl

theorem cell22_341486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_341486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341486 prefixEnd_341486 := by exact prefixLift 341486
  have htrace : WordTrace (prefixWord ++ tailWord_341486) baseStart_341486 baseEnd_341486 := by
    simpa [prefixWord, tailWord_341486, baseEnd_341486] using wordTrace_append hprefix tailTrace_341486
  have hstable : (prefixWord ++ tailWord_341486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341486).length < 2 ^ (prefixWord ++ tailWord_341486).sum := by decide
  have hdescent : baseEnd_341486 < baseStart_341486 := by decide
  rcases family_descends (prefixWord ++ tailWord_341486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341497 : List Nat := [1, 2, 1, 3, 1, 2, 1, 11]
def baseStart_341497 : Nat := 118140960795 + 341497 * 2 ^ 59
def prefixEnd_341497 : Nat := 4983230072969 + 3 ^ 40 * 341497 * 2
def baseEnd_341497 : Nat := 12989044671744861119777

theorem tailTrace_341497 : CollatzResearch.WordTrace tailWord_341497 prefixEnd_341497 12989044671744861119777 := by
  unfold tailWord_341497
  simp only [CollatzResearch.WordTrace]
  refine ⟨12455418843822166889374745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8303612562548111259583163 12455418843822166889374745)
  ·
    refine ⟨9341564132866625167031059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12455418843822166889374745 9341564132866625167031059)
    ·
      refine ⟨14012346199299937750546589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9341564132866625167031059 14012346199299937750546589)
      ·
        refine ⟨5254629824737476656454971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14012346199299937750546589 5254629824737476656454971)
        ·
          refine ⟨7881944737106214984682457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5254629824737476656454971 7881944737106214984682457)
          ·
            refine ⟨5911458552829661238511843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7881944737106214984682457 5911458552829661238511843)
            ·
              refine ⟨8867187829244491857767765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5911458552829661238511843 8867187829244491857767765)
              ·
                refine ⟨12989044671744861119777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 8867187829244491857767765 12989044671744861119777)
                ·
                  rfl

theorem cell22_341497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 11].length) (baseStart_341497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341497 prefixEnd_341497 := by exact prefixLift 341497
  have htrace : WordTrace (prefixWord ++ tailWord_341497) baseStart_341497 baseEnd_341497 := by
    simpa [prefixWord, tailWord_341497, baseEnd_341497] using wordTrace_append hprefix tailTrace_341497
  have hstable : (prefixWord ++ tailWord_341497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341497).length < 2 ^ (prefixWord ++ tailWord_341497).sum := by decide
  have hdescent : baseEnd_341497 < baseStart_341497 := by decide
  rcases family_descends (prefixWord ++ tailWord_341497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341501 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_341501 : Nat := 118140960795 + 341501 * 2 ^ 59
def prefixEnd_341501 : Nat := 4983230072969 + 3 ^ 40 * 341501 * 2
def baseEnd_341501 : Nat := 116902771327449072977981

theorem tailTrace_341501 : CollatzResearch.WordTrace tailWord_341501 prefixEnd_341501 116902771327449072977981 := by
  unfold tailWord_341501
  simp only [CollatzResearch.WordTrace]
  refine ⟨12455564735807675572520357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8303709823871783715013571 12455564735807675572520357)
  ·
    refine ⟨2335418387963939169847567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12455564735807675572520357 2335418387963939169847567)
    ·
      refine ⟨3503127581945908754771351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2335418387963939169847567 3503127581945908754771351)
      ·
        refine ⟨5254691372918863132157027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3503127581945908754771351 5254691372918863132157027)
        ·
          refine ⟨7882037059378294698235541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5254691372918863132157027 7882037059378294698235541)
          ·
            refine ⟨369470487158357563979791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7882037059378294698235541 369470487158357563979791)
            ·
              refine ⟨554205730737536345969687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369470487158357563979791 554205730737536345969687)
              ·
                refine ⟨831308596106304518954531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554205730737536345969687 831308596106304518954531)
                ·
                  refine ⟨1246962894159456778431797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831308596106304518954531 1246962894159456778431797)
                  ·
                    refine ⟨116902771327449072977981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1246962894159456778431797 116902771327449072977981)
                    ·
                      rfl

theorem cell22_341501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_341501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341501 prefixEnd_341501 := by exact prefixLift 341501
  have htrace : WordTrace (prefixWord ++ tailWord_341501) baseStart_341501 baseEnd_341501 := by
    simpa [prefixWord, tailWord_341501, baseEnd_341501] using wordTrace_append hprefix tailTrace_341501
  have hstable : (prefixWord ++ tailWord_341501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341501).length < 2 ^ (prefixWord ++ tailWord_341501).sum := by decide
  have hdescent : baseEnd_341501 < baseStart_341501 := by decide
  rcases family_descends (prefixWord ++ tailWord_341501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341514 : List Nat := [3, 1, 2, 2, 2, 3, 1, 8]
def baseStart_341514 : Nat := 118140960795 + 341514 * 2 ^ 59
def prefixEnd_341514 : Nat := 4983230072969 + 3 ^ 40 * 341514 * 2
def baseEnd_341514 : Nat := 12989691277013485822549

theorem tailTrace_341514 : CollatzResearch.WordTrace tailWord_341514 prefixEnd_341514 12989691277013485822549 := by
  unfold tailWord_341514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114009721190144698185899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8304025923173719195162397 3114009721190144698185899)
  ·
    refine ⟨4671014581785217047278849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3114009721190144698185899 4671014581785217047278849)
    ·
      refine ⟨3503260936338912785459137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4671014581785217047278849 3503260936338912785459137)
      ·
        refine ⟨2627445702254184589094353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3503260936338912785459137 2627445702254184589094353)
        ·
          refine ⟨1970584276690638441820765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2627445702254184589094353 1970584276690638441820765)
          ·
            refine ⟨738969103758989415682787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1970584276690638441820765 738969103758989415682787)
            ·
              refine ⟨1108453655638484123524181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738969103758989415682787 1108453655638484123524181)
              ·
                refine ⟨12989691277013485822549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1108453655638484123524181 12989691277013485822549)
                ·
                  rfl

theorem cell22_341514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_341514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341514 prefixEnd_341514 := by exact prefixLift 341514
  have htrace : WordTrace (prefixWord ++ tailWord_341514) baseStart_341514 baseEnd_341514 := by
    simpa [prefixWord, tailWord_341514, baseEnd_341514] using wordTrace_append hprefix tailTrace_341514
  have hstable : (prefixWord ++ tailWord_341514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341514).length < 2 ^ (prefixWord ++ tailWord_341514).sum := by decide
  have hdescent : baseEnd_341514 < baseStart_341514 := by decide
  rcases family_descends (prefixWord ++ tailWord_341514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341621 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 8]
def baseStart_341621 : Nat := 118140960795 + 341621 * 2 ^ 59
def prefixEnd_341621 : Nat := 4983230072969 + 3 ^ 40 * 341621 * 2
def baseEnd_341621 : Nat := 38981283259936253325871

theorem tailTrace_341621 : CollatzResearch.WordTrace tailWord_341621 prefixEnd_341621 38981283259936253325871 := by
  unfold tailWord_341621
  simp only [CollatzResearch.WordTrace]
  refine ⟨12459941495372936066888717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8306627663581957377925811 12459941495372936066888717)
  ·
    refine ⟨4672478060764851025083269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12459941495372936066888717 4672478060764851025083269)
    ·
      refine ⟨876089636393409567203113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4672478060764851025083269 876089636393409567203113)
      ·
        refine ⟨657067227295057175402335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 876089636393409567203113 657067227295057175402335)
        ·
          refine ⟨985600840942585763103503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657067227295057175402335 985600840942585763103503)
          ·
            refine ⟨1478401261413878644655255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985600840942585763103503 1478401261413878644655255)
            ·
              refine ⟨2217601892120817966982883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478401261413878644655255 2217601892120817966982883)
              ·
                refine ⟨3326402838181226950474325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217601892120817966982883 3326402838181226950474325)
                ·
                  refine ⟨38981283259936253325871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3326402838181226950474325 38981283259936253325871)
                  ·
                    rfl

theorem cell22_341621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_341621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341621 prefixEnd_341621 := by exact prefixLift 341621
  have htrace : WordTrace (prefixWord ++ tailWord_341621) baseStart_341621 baseEnd_341621 := by
    simpa [prefixWord, tailWord_341621, baseEnd_341621] using wordTrace_append hprefix tailTrace_341621
  have hstable : (prefixWord ++ tailWord_341621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341621).length < 2 ^ (prefixWord ++ tailWord_341621).sum := by decide
  have hdescent : baseEnd_341621 < baseStart_341621 := by decide
  rcases family_descends (prefixWord ++ tailWord_341621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341640 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 1, 4]
def baseStart_341640 : Nat := 118140960795 + 341640 * 2 ^ 59
def prefixEnd_341640 : Nat := 4983230072969 + 3 ^ 40 * 341640 * 2
def baseEnd_341640 : Nat := 116950353868099043752555

theorem tailTrace_341640 : CollatzResearch.WordTrace tailWord_341640 prefixEnd_341640 116950353868099043752555 := by
  unfold tailWord_341640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6230317241152051155915187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8307089654869401541220249 6230317241152051155915187)
  ·
    refine ⟨9345475861728076733872781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6230317241152051155915187 9345475861728076733872781)
    ·
      refine ⟨3504553448148028775202293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9345475861728076733872781 3504553448148028775202293)
      ·
        refine ⟨328551885763877697675215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3504553448148028775202293 328551885763877697675215)
        ·
          refine ⟨492827828645816546512823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328551885763877697675215 492827828645816546512823)
          ·
            refine ⟨739241742968724819769235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492827828645816546512823 739241742968724819769235)
            ·
              refine ⟨1108862614453087229653853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739241742968724819769235 1108862614453087229653853)
              ·
                refine ⟨415823480419907711120195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1108862614453087229653853 415823480419907711120195)
                ·
                  refine ⟨623735220629861566680293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415823480419907711120195 623735220629861566680293)
                  ·
                    refine ⟨116950353868099043752555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 623735220629861566680293 116950353868099043752555)
                    ·
                      rfl

theorem cell22_341640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_341640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341640 prefixEnd_341640 := by exact prefixLift 341640
  have htrace : WordTrace (prefixWord ++ tailWord_341640) baseStart_341640 baseEnd_341640 := by
    simpa [prefixWord, tailWord_341640, baseEnd_341640] using wordTrace_append hprefix tailTrace_341640
  have hstable : (prefixWord ++ tailWord_341640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341640).length < 2 ^ (prefixWord ++ tailWord_341640).sum := by decide
  have hdescent : baseEnd_341640 < baseStart_341640 := by decide
  rcases family_descends (prefixWord ++ tailWord_341640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341702 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_341702 : Nat := 118140960795 + 341702 * 2 ^ 59
def prefixEnd_341702 : Nat := 4983230072969 + 3 ^ 40 * 341702 * 2
def baseEnd_341702 : Nat := 116971577735151548702365

theorem tailTrace_341702 : CollatzResearch.WordTrace tailWord_341702 prefixEnd_341702 116971577735151548702365 := by
  unfold tailWord_341702
  simp only [CollatzResearch.WordTrace]
  refine ⟨389465494002483965643355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8308597205386324600391573 389465494002483965643355)
  ·
    refine ⟨584198241003725948465033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 389465494002483965643355 584198241003725948465033)
    ·
      refine ⟨438148680752794461348775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 584198241003725948465033 438148680752794461348775)
      ·
        refine ⟨657223021129191692023163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438148680752794461348775 657223021129191692023163)
        ·
          refine ⟨985834531693787538034745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657223021129191692023163 985834531693787538034745)
          ·
            refine ⟨739375898770340653526059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 985834531693787538034745 739375898770340653526059)
            ·
              refine ⟨1109063848155510980289089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739375898770340653526059 1109063848155510980289089)
              ·
                refine ⟨831797886116633235216817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109063848155510980289089 831797886116633235216817)
                ·
                  refine ⟨623848414587474926412613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 831797886116633235216817 623848414587474926412613)
                  ·
                    refine ⟨116971577735151548702365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 623848414587474926412613 116971577735151548702365)
                    ·
                      rfl

theorem cell22_341702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_341702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341702 prefixEnd_341702 := by exact prefixLift 341702
  have htrace : WordTrace (prefixWord ++ tailWord_341702) baseStart_341702 baseEnd_341702 := by
    simpa [prefixWord, tailWord_341702, baseEnd_341702] using wordTrace_append hprefix tailTrace_341702
  have hstable : (prefixWord ++ tailWord_341702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341702).length < 2 ^ (prefixWord ++ tailWord_341702).sum := by decide
  have hdescent : baseEnd_341702 < baseStart_341702 := by decide
  rcases family_descends (prefixWord ++ tailWord_341702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341728 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 5]
def baseStart_341728 : Nat := 118140960795 + 341728 * 2 ^ 59
def prefixEnd_341728 : Nat := 4983230072969 + 3 ^ 40 * 341728 * 2
def baseEnd_341728 : Nat := 38993492688832049184095

theorem tailTrace_341728 : CollatzResearch.WordTrace tailWord_341728 prefixEnd_341728 38993492688832049184095 := by
  unfold tailWord_341728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231922052992646670516919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8309229403990195560689225 6231922052992646670516919)
  ·
    refine ⟨9347883079488970005775379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6231922052992646670516919 9347883079488970005775379)
    ·
      refine ⟨14021824619233455008663069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9347883079488970005775379 14021824619233455008663069)
      ·
        refine ⟨5258184232212545628248651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14021824619233455008663069 5258184232212545628248651)
        ·
          refine ⟨7887276348318818442372977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258184232212545628248651 7887276348318818442372977)
          ·
            refine ⟨5915457261239113831779733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7887276348318818442372977 5915457261239113831779733)
            ·
              refine ⟨277287059120583460864675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5915457261239113831779733 277287059120583460864675)
              ·
                refine ⟨415930588680875191297013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277287059120583460864675 415930588680875191297013)
                ·
                  refine ⟨38993492688832049184095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 415930588680875191297013 38993492688832049184095)
                  ·
                    rfl

theorem cell22_341728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_341728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341728 prefixEnd_341728 := by exact prefixLift 341728
  have htrace : WordTrace (prefixWord ++ tailWord_341728) baseStart_341728 baseEnd_341728 := by
    simpa [prefixWord, tailWord_341728, baseEnd_341728] using wordTrace_append hprefix tailTrace_341728
  have hstable : (prefixWord ++ tailWord_341728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341728).length < 2 ^ (prefixWord ++ tailWord_341728).sum := by decide
  have hdescent : baseEnd_341728 < baseStart_341728 := by decide
  rcases family_descends (prefixWord ++ tailWord_341728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341788 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_341788 : Nat := 118140960795 + 341788 * 2 ^ 59
def prefixEnd_341788 : Nat := 4983230072969 + 3 ^ 40 * 341788 * 2
def baseEnd_341788 : Nat := 117001017292675991052101

theorem tailTrace_341788 : CollatzResearch.WordTrace tailWord_341788 prefixEnd_341788 117001017292675991052101 := by
  unfold tailWord_341788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233016242883961794109009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8310688323845282392145345 6233016242883961794109009)
  ·
    refine ⟨4674762182162971345581757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6233016242883961794109009 4674762182162971345581757)
    ·
      refine ⟨1753035818311114254593159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4674762182162971345581757 1753035818311114254593159)
      ·
        refine ⟨2629553727466671381889739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753035818311114254593159 2629553727466671381889739)
        ·
          refine ⟨3944330591200007072834609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2629553727466671381889739 3944330591200007072834609)
          ·
            refine ⟨2958247943400005304625957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3944330591200007072834609 2958247943400005304625957)
            ·
              refine ⟨554671489387500994617367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2958247943400005304625957 554671489387500994617367)
              ·
                refine ⟨832007234081251491926051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554671489387500994617367 832007234081251491926051)
                ·
                  refine ⟨1248010851121877237889077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832007234081251491926051 1248010851121877237889077)
                  ·
                    refine ⟨117001017292675991052101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1248010851121877237889077 117001017292675991052101)
                    ·
                      rfl

theorem cell22_341788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_341788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341788 prefixEnd_341788 := by exact prefixLift 341788
  have htrace : WordTrace (prefixWord ++ tailWord_341788) baseStart_341788 baseEnd_341788 := by
    simpa [prefixWord, tailWord_341788, baseEnd_341788] using wordTrace_append hprefix tailTrace_341788
  have hstable : (prefixWord ++ tailWord_341788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341788).length < 2 ^ (prefixWord ++ tailWord_341788).sum := by decide
  have hdescent : baseEnd_341788 < baseStart_341788 := by decide
  rcases family_descends (prefixWord ++ tailWord_341788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341822 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_341822 : Nat := 118140960795 + 341822 * 2 ^ 59
def prefixEnd_341822 : Nat := 4983230072969 + 3 ^ 40 * 341822 * 2
def baseEnd_341822 : Nat := 117012656187511235701997

theorem tailTrace_341822 : CollatzResearch.WordTrace tailWord_341822 prefixEnd_341822 117012656187511235701997 := by
  unfold tailWord_341822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558409070955593424369465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8311515045096498263303813 1558409070955593424369465)
  ·
    refine ⟨1168806803216695068277099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1558409070955593424369465 1168806803216695068277099)
    ·
      refine ⟨1753210204825042602415649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1168806803216695068277099 1753210204825042602415649)
      ·
        refine ⟨1314907653618781951811737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1753210204825042602415649 1314907653618781951811737)
        ·
          refine ⟨986180740214086463858803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1314907653618781951811737 986180740214086463858803)
          ·
            refine ⟨1479271110321129695788205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986180740214086463858803 1479271110321129695788205)
            ·
              refine ⟨554726666370423635920577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1479271110321129695788205 554726666370423635920577)
              ·
                refine ⟨416044999777817726940433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554726666370423635920577 416044999777817726940433)
                ·
                  refine ⟨312033749833363295205325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416044999777817726940433 312033749833363295205325)
                  ·
                    refine ⟨117012656187511235701997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312033749833363295205325 117012656187511235701997)
                    ·
                      rfl

theorem cell22_341822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_341822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341822 prefixEnd_341822 := by exact prefixLift 341822
  have htrace : WordTrace (prefixWord ++ tailWord_341822) baseStart_341822 baseEnd_341822 := by
    simpa [prefixWord, tailWord_341822, baseEnd_341822] using wordTrace_append hprefix tailTrace_341822
  have hstable : (prefixWord ++ tailWord_341822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341822).length < 2 ^ (prefixWord ++ tailWord_341822).sum := by decide
  have hdescent : baseEnd_341822 < baseStart_341822 := by decide
  rcases family_descends (prefixWord ++ tailWord_341822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341831 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 8]
def baseStart_341831 : Nat := 118140960795 + 341831 * 2 ^ 59
def prefixEnd_341831 : Nat := 4983230072969 + 3 ^ 40 * 341831 * 2
def baseEnd_341831 : Nat := 117015737071438212226969

theorem tailTrace_341831 : CollatzResearch.WordTrace tailWord_341831 prefixEnd_341831 117015737071438212226969 := by
  unfold tailWord_341831
  simp only [CollatzResearch.WordTrace]
  refine ⟨12467600824612141932033347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8311733883074761288022231 12467600824612141932033347)
  ·
    refine ⟨18701401236918212898050021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12467600824612141932033347 18701401236918212898050021)
    ·
      refine ⟨3506512731922164918384379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18701401236918212898050021 3506512731922164918384379)
      ·
        refine ⟨5259769097883247377576569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506512731922164918384379 5259769097883247377576569)
        ·
          refine ⟨3944826823412435533182427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5259769097883247377576569 3944826823412435533182427)
          ·
            refine ⟨5917240235118653299773641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3944826823412435533182427 5917240235118653299773641)
            ·
              refine ⟨4437930176338989974830231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5917240235118653299773641 4437930176338989974830231)
              ·
                refine ⟨6656895264508484962245347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4437930176338989974830231 6656895264508484962245347)
                ·
                  refine ⟨9985342896762727443368021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6656895264508484962245347 9985342896762727443368021)
                  ·
                    refine ⟨117015737071438212226969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9985342896762727443368021 117015737071438212226969)
                    ·
                      rfl

theorem cell22_341831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_341831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341831 prefixEnd_341831 := by exact prefixLift 341831
  have htrace : WordTrace (prefixWord ++ tailWord_341831) baseStart_341831 baseEnd_341831 := by
    simpa [prefixWord, tailWord_341831, baseEnd_341831] using wordTrace_append hprefix tailTrace_341831
  have hstable : (prefixWord ++ tailWord_341831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341831).length < 2 ^ (prefixWord ++ tailWord_341831).sum := by decide
  have hdescent : baseEnd_341831 < baseStart_341831 := by decide
  rcases family_descends (prefixWord ++ tailWord_341831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341852 : List Nat := [2, 2, 4, 2, 2, 2, 2, 6]
def baseStart_341852 : Nat := 118140960795 + 341852 * 2 ^ 59
def prefixEnd_341852 : Nat := 4983230072969 + 3 ^ 40 * 341852 * 2
def baseEnd_341852 : Nat := 13002547311177906383545

theorem tailTrace_341852 : CollatzResearch.WordTrace tailWord_341852 prefixEnd_341852 13002547311177906383545 := by
  unfold tailWord_341852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234183378768031259273905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8312244505024041679031873 6234183378768031259273905)
  ·
    refine ⟨4675637534076023444455429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6234183378768031259273905 4675637534076023444455429)
    ·
      refine ⟨876682037639254395835393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4675637534076023444455429 876682037639254395835393)
      ·
        refine ⟨657511528229440796876545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 876682037639254395835393 657511528229440796876545)
        ·
          refine ⟨493133646172080597657409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657511528229440796876545 493133646172080597657409)
          ·
            refine ⟨369850234629060448243057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493133646172080597657409 369850234629060448243057)
            ·
              refine ⟨277387675971795336182293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369850234629060448243057 277387675971795336182293)
              ·
                refine ⟨13002547311177906383545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 277387675971795336182293 13002547311177906383545)
                ·
                  rfl

theorem cell22_341852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 6].length) (baseStart_341852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341852 prefixEnd_341852 := by exact prefixLift 341852
  have htrace : WordTrace (prefixWord ++ tailWord_341852) baseStart_341852 baseEnd_341852 := by
    simpa [prefixWord, tailWord_341852, baseEnd_341852] using wordTrace_append hprefix tailTrace_341852
  have hstable : (prefixWord ++ tailWord_341852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341852).length < 2 ^ (prefixWord ++ tailWord_341852).sum := by decide
  have hdescent : baseEnd_341852 < baseStart_341852 := by decide
  rcases family_descends (prefixWord ++ tailWord_341852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341893 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_341893 : Nat := 118140960795 + 341893 * 2 ^ 59
def prefixEnd_341893 : Nat := 4983230072969 + 3 ^ 40 * 341893 * 2
def baseEnd_341893 : Nat := 117036960938490717176779

theorem tailTrace_341893 : CollatzResearch.WordTrace tailWord_341893 prefixEnd_341893 117036960938490717176779 := by
  unfold tailWord_341893
  simp only [CollatzResearch.WordTrace]
  refine ⟨12469862150387526520790333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8313241433591684347193555 12469862150387526520790333)
  ·
    refine ⟨4676198306395322445296375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12469862150387526520790333 4676198306395322445296375)
    ·
      refine ⟨7014297459592983667944563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4676198306395322445296375 7014297459592983667944563)
      ·
        refine ⟨10521446189389475501916845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7014297459592983667944563 10521446189389475501916845)
        ·
          refine ⟨3945542321021053313218817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10521446189389475501916845 3945542321021053313218817)
          ·
            refine ⟨2959156740765789984914113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3945542321021053313218817 2959156740765789984914113)
            ·
              refine ⟨2219367555574342488685585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959156740765789984914113 2219367555574342488685585)
              ·
                refine ⟨1664525666680756866514189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2219367555574342488685585 1664525666680756866514189)
                ·
                  refine ⟨624197125005283824942821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1664525666680756866514189 624197125005283824942821)
                  ·
                    refine ⟨117036960938490717176779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 624197125005283824942821 117036960938490717176779)
                    ·
                      rfl

theorem cell22_341893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_341893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341893 prefixEnd_341893 := by exact prefixLift 341893
  have htrace : WordTrace (prefixWord ++ tailWord_341893) baseStart_341893 baseEnd_341893 := by
    simpa [prefixWord, tailWord_341893, baseEnd_341893] using wordTrace_append hprefix tailTrace_341893
  have hstable : (prefixWord ++ tailWord_341893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341893).length < 2 ^ (prefixWord ++ tailWord_341893).sum := by decide
  have hdescent : baseEnd_341893 < baseStart_341893 := by decide
  rcases family_descends (prefixWord ++ tailWord_341893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341991 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 2, 3]
def baseStart_341991 : Nat := 118140960795 + 341991 * 2 ^ 59
def prefixEnd_341991 : Nat := 4983230072969 + 3 ^ 40 * 341991 * 2
def baseEnd_341991 : Nat := 117070508341251128226479

theorem tailTrace_341991 : CollatzResearch.WordTrace tailWord_341991 prefixEnd_341991 117070508341251128226479 := by
  unfold tailWord_341991
  simp only [CollatzResearch.WordTrace]
  refine ⟨12473436504032489257857827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8315624336021659505238551 12473436504032489257857827)
  ·
    refine ⟨18710154756048733886786741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12473436504032489257857827 18710154756048733886786741)
    ·
      refine ⟨1754077008379568801886257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18710154756048733886786741 1754077008379568801886257)
      ·
        refine ⟨1315557756284676601414693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1754077008379568801886257 1315557756284676601414693)
        ·
          refine ⟨246667079303376862765255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1315557756284676601414693 246667079303376862765255)
          ·
            refine ⟨370000618955065294147883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246667079303376862765255 370000618955065294147883)
            ·
              refine ⟨555000928432597941221825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370000618955065294147883 555000928432597941221825)
              ·
                refine ⟨416250696324448455916369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555000928432597941221825 416250696324448455916369)
                ·
                  refine ⟨312188022243336341937277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416250696324448455916369 312188022243336341937277)
                  ·
                    refine ⟨117070508341251128226479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312188022243336341937277 117070508341251128226479)
                    ·
                      rfl

theorem cell22_341991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_341991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_341991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_341991 prefixEnd_341991 := by exact prefixLift 341991
  have htrace : WordTrace (prefixWord ++ tailWord_341991) baseStart_341991 baseEnd_341991 := by
    simpa [prefixWord, tailWord_341991, baseEnd_341991] using wordTrace_append hprefix tailTrace_341991
  have hstable : (prefixWord ++ tailWord_341991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341991).length < 2 ^ (prefixWord ++ tailWord_341991).sum := by decide
  have hdescent : baseEnd_341991 < baseStart_341991 := by decide
  rcases family_descends (prefixWord ++ tailWord_341991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342137 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 5, 3]
def baseStart_342137 : Nat := 118140960795 + 342137 * 2 ^ 59
def prefixEnd_342137 : Nat := 4983230072969 + 3 ^ 40 * 342137 * 2
def baseEnd_342137 : Nat := 117120487124955414076031

theorem tailTrace_342137 : CollatzResearch.WordTrace tailWord_342137 prefixEnd_342137 117120487124955414076031 := by
  unfold tailWord_342137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12478761561503556192672665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8319174374335704128448443 12478761561503556192672665)
  ·
    refine ⟨9359071171127667144504499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12478761561503556192672665 9359071171127667144504499)
    ·
      refine ⟨14038606756691500716756749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9359071171127667144504499 14038606756691500716756749)
      ·
        refine ⟨5264477533759312768783781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14038606756691500716756749 5264477533759312768783781)
        ·
          refine ⟨987089537579871144146959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5264477533759312768783781 987089537579871144146959)
          ·
            refine ⟨1480634306369806716220439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987089537579871144146959 1480634306369806716220439)
            ·
              refine ⟨2220951459554710074330659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480634306369806716220439 2220951459554710074330659)
              ·
                refine ⟨3331427189332065111495989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220951459554710074330659 3331427189332065111495989)
                ·
                  refine ⟨312321298999881104202749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3331427189332065111495989 312321298999881104202749)
                  ·
                    refine ⟨117120487124955414076031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312321298999881104202749 117120487124955414076031)
                    ·
                      rfl

theorem cell22_342137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_342137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342137 prefixEnd_342137 := by exact prefixLift 342137
  have htrace : WordTrace (prefixWord ++ tailWord_342137) baseStart_342137 baseEnd_342137 := by
    simpa [prefixWord, tailWord_342137, baseEnd_342137] using wordTrace_append hprefix tailTrace_342137
  have hstable : (prefixWord ++ tailWord_342137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342137).length < 2 ^ (prefixWord ++ tailWord_342137).sum := by decide
  have hdescent : baseEnd_342137 < baseStart_342137 := by decide
  rcases family_descends (prefixWord ++ tailWord_342137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342165 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_342165 : Nat := 118140960795 + 342165 * 2 ^ 59
def prefixEnd_342165 : Nat := 4983230072969 + 3 ^ 40 * 342165 * 2
def baseEnd_342165 : Nat := 117130072097172674375945

theorem tailTrace_342165 : CollatzResearch.WordTrace tailWord_342165 prefixEnd_342165 117130072097172674375945 := by
  unfold tailWord_342165
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479782805402116974691949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8319855203601411316461299 12479782805402116974691949)
  ·
    refine ⟨4679918552025793865509481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12479782805402116974691949 4679918552025793865509481)
    ·
      refine ⟨3509938914019345399132111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4679918552025793865509481 3509938914019345399132111)
      ·
        refine ⟨5264908371029018098698167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509938914019345399132111 5264908371029018098698167)
        ·
          refine ⟨7897362556543527148047251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264908371029018098698167 7897362556543527148047251)
          ·
            refine ⟨11846043834815290722070877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897362556543527148047251 11846043834815290722070877)
            ·
              refine ⟨4442266438055734020776579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11846043834815290722070877 4442266438055734020776579)
              ·
                refine ⟨6663399657083601031164869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442266438055734020776579 6663399657083601031164869)
                ·
                  refine ⟨1249387435703175193343413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6663399657083601031164869 1249387435703175193343413)
                  ·
                    refine ⟨117130072097172674375945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1249387435703175193343413 117130072097172674375945)
                    ·
                      rfl

theorem cell22_342165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_342165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342165 prefixEnd_342165 := by exact prefixLift 342165
  have htrace : WordTrace (prefixWord ++ tailWord_342165) baseStart_342165 baseEnd_342165 := by
    simpa [prefixWord, tailWord_342165, baseEnd_342165] using wordTrace_append hprefix tailTrace_342165
  have hstable : (prefixWord ++ tailWord_342165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342165).length < 2 ^ (prefixWord ++ tailWord_342165).sum := by decide
  have hdescent : baseEnd_342165 < baseStart_342165 := by decide
  rcases family_descends (prefixWord ++ tailWord_342165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342167 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 7]
def baseStart_342167 : Nat := 118140960795 + 342167 * 2 ^ 59
def prefixEnd_342167 : Nat := 4983230072969 + 3 ^ 40 * 342167 * 2
def baseEnd_342167 : Nat := 39043585579348445275313

theorem tailTrace_342167 : CollatzResearch.WordTrace tailWord_342167 prefixEnd_342167 39043585579348445275313 := by
  unfold tailWord_342167
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479855751394871316264755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8319903834263247544176503 12479855751394871316264755)
  ·
    refine ⟨18719783627092306974397133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12479855751394871316264755 18719783627092306974397133)
    ·
      refine ⟨7019918860159615115398925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18719783627092306974397133 7019918860159615115398925)
      ·
        refine ⟨2632469572559855668274597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7019918860159615115398925 2632469572559855668274597)
        ·
          refine ⟨493588044854972937801487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2632469572559855668274597 493588044854972937801487)
          ·
            refine ⟨740382067282459406702231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493588044854972937801487 740382067282459406702231)
            ·
              refine ⟨1110573100923689110053347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740382067282459406702231 1110573100923689110053347)
              ·
                refine ⟨1665859651385533665080021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110573100923689110053347 1665859651385533665080021)
                ·
                  refine ⟨39043585579348445275313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1665859651385533665080021 39043585579348445275313)
                  ·
                    rfl

theorem cell22_342167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 7].length) (baseStart_342167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342167 prefixEnd_342167 := by exact prefixLift 342167
  have htrace : WordTrace (prefixWord ++ tailWord_342167) baseStart_342167 baseEnd_342167 := by
    simpa [prefixWord, tailWord_342167, baseEnd_342167] using wordTrace_append hprefix tailTrace_342167
  have hstable : (prefixWord ++ tailWord_342167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342167).length < 2 ^ (prefixWord ++ tailWord_342167).sum := by decide
  have hdescent : baseEnd_342167 < baseStart_342167 := by decide
  rcases family_descends (prefixWord ++ tailWord_342167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342306 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_342306 : Nat := 118140960795 + 342306 * 2 ^ 59
def prefixEnd_342306 : Nat := 4983230072969 + 3 ^ 40 * 342306 * 2
def baseEnd_342306 : Nat := 117178339278695306600513

theorem tailTrace_342306 : CollatzResearch.WordTrace tailWord_342306 prefixEnd_342306 117178339278695306600513 := by
  unfold tailWord_342306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121231374472824513893693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8323283665260865370383181 3121231374472824513893693)
  ·
    refine ⟨1170461765427309192710135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3121231374472824513893693 1170461765427309192710135)
    ·
      refine ⟨1755692648140963789065203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170461765427309192710135 1755692648140963789065203)
      ·
        refine ⟨2633538972211445683597805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755692648140963789065203 2633538972211445683597805)
        ·
          refine ⟨987577114579292131349177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2633538972211445683597805 987577114579292131349177)
          ·
            refine ⟨740682835934469098511883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987577114579292131349177 740682835934469098511883)
            ·
              refine ⟨1111024253901703647767825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740682835934469098511883 1111024253901703647767825)
              ·
                refine ⟨833268190426277735825869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111024253901703647767825 833268190426277735825869)
                ·
                  refine ⟨312475571409854150934701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 833268190426277735825869 312475571409854150934701)
                  ·
                    refine ⟨117178339278695306600513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312475571409854150934701 117178339278695306600513)
                    ·
                      rfl

theorem cell22_342306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_342306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342306 prefixEnd_342306 := by exact prefixLift 342306
  have htrace : WordTrace (prefixWord ++ tailWord_342306) baseStart_342306 baseEnd_342306 := by
    simpa [prefixWord, tailWord_342306, baseEnd_342306] using wordTrace_append hprefix tailTrace_342306
  have hstable : (prefixWord ++ tailWord_342306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342306).length < 2 ^ (prefixWord ++ tailWord_342306).sum := by decide
  have hdescent : baseEnd_342306 < baseStart_342306 := by decide
  rcases family_descends (prefixWord ++ tailWord_342306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342334 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_342334 : Nat := 118140960795 + 342334 * 2 ^ 59
def prefixEnd_342334 : Nat := 4983230072969 + 3 ^ 40 * 342334 * 2
def baseEnd_342334 : Nat := 117187924250912566900427

theorem tailTrace_342334 : CollatzResearch.WordTrace tailWord_342334 prefixEnd_342334 117187924250912566900427 := by
  unfold tailWord_342334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1560743342723732354699257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8323964494526572558396037 1560743342723732354699257)
  ·
    refine ⟨1170557507042799266024443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1560743342723732354699257 1170557507042799266024443)
    ·
      refine ⟨1755836260564198899036665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1170557507042799266024443 1755836260564198899036665)
      ·
        refine ⟨1316877195423149174277499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1755836260564198899036665 1316877195423149174277499)
        ·
          refine ⟨1975315793134723761416249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316877195423149174277499 1975315793134723761416249)
          ·
            refine ⟨1481486844851042821062187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1975315793134723761416249 1481486844851042821062187)
            ·
              refine ⟨2222230267276564231593281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481486844851042821062187 2222230267276564231593281)
              ·
                refine ⟨1666672700457423173694961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222230267276564231593281 1666672700457423173694961)
                ·
                  refine ⟨1250004525343067380271221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1666672700457423173694961 1250004525343067380271221)
                  ·
                    refine ⟨117187924250912566900427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1250004525343067380271221 117187924250912566900427)
                    ·
                      rfl

theorem cell22_342334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_342334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342334 prefixEnd_342334 := by exact prefixLift 342334
  have htrace : WordTrace (prefixWord ++ tailWord_342334) baseStart_342334 baseEnd_342334 := by
    simpa [prefixWord, tailWord_342334, baseEnd_342334] using wordTrace_append hprefix tailTrace_342334
  have hstable : (prefixWord ++ tailWord_342334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342334).length < 2 ^ (prefixWord ++ tailWord_342334).sum := by decide
  have hdescent : baseEnd_342334 < baseStart_342334 := by decide
  rcases family_descends (prefixWord ++ tailWord_342334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342377 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_342377 : Nat := 118140960795 + 342377 * 2 ^ 59
def prefixEnd_342377 : Nat := 4983230072969 + 3 ^ 40 * 342377 * 2
def baseEnd_342377 : Nat := 117202644029674788075295

theorem tailTrace_342377 : CollatzResearch.WordTrace tailWord_342377 prefixEnd_342377 117202644029674788075295 := by
  unfold tailWord_342377
  simp only [CollatzResearch.WordTrace]
  refine ⟨12487515080634077181409385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8325010053756051454272923 12487515080634077181409385)
  ·
    refine ⟨9365636310475557886057039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12487515080634077181409385 9365636310475557886057039)
    ·
      refine ⟨14048454465713336829085559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9365636310475557886057039 14048454465713336829085559)
      ·
        refine ⟨21072681698570005243628339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14048454465713336829085559 21072681698570005243628339)
        ·
          refine ⟨31609022547855007865442509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21072681698570005243628339 31609022547855007865442509)
          ·
            refine ⟨11853383455445627949540941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31609022547855007865442509 11853383455445627949540941)
            ·
              refine ⟨4445018795792110481077853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11853383455445627949540941 4445018795792110481077853)
              ·
                refine ⟨1666882048422041430404195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4445018795792110481077853 1666882048422041430404195)
                ·
                  refine ⟨2500323072633062145606293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1666882048422041430404195 2500323072633062145606293)
                  ·
                    refine ⟨117202644029674788075295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2500323072633062145606293 117202644029674788075295)
                    ·
                      rfl

theorem cell22_342377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_342377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342377 prefixEnd_342377 := by exact prefixLift 342377
  have htrace : WordTrace (prefixWord ++ tailWord_342377) baseStart_342377 baseEnd_342377 := by
    simpa [prefixWord, tailWord_342377, baseEnd_342377] using wordTrace_append hprefix tailTrace_342377
  have hstable : (prefixWord ++ tailWord_342377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342377).length < 2 ^ (prefixWord ++ tailWord_342377).sum := by decide
  have hdescent : baseEnd_342377 < baseStart_342377 := by decide
  rcases family_descends (prefixWord ++ tailWord_342377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342409 : List Nat := [1, 2, 1, 1, 6, 2, 2, 7]
def baseStart_342409 : Nat := 118140960795 + 342409 * 2 ^ 59
def prefixEnd_342409 : Nat := 4983230072969 + 3 ^ 40 * 342409 * 2
def baseEnd_342409 : Nat := 13023733142626374586133

theorem tailTrace_342409 : CollatzResearch.WordTrace tailWord_342409 prefixEnd_342409 13023733142626374586133 := by
  unfold tailWord_342409
  simp only [CollatzResearch.WordTrace]
  refine ⟨12488682216518146646574281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8325788144345431097716187 12488682216518146646574281)
  ·
    refine ⟨9366511662388609984930711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12488682216518146646574281 9366511662388609984930711)
    ·
      refine ⟨14049767493582914977396067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9366511662388609984930711 14049767493582914977396067)
      ·
        refine ⟨21074651240374372466094101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14049767493582914977396067 21074651240374372466094101)
        ·
          refine ⟨987874276892548709348161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21074651240374372466094101 987874276892548709348161)
          ·
            refine ⟨740905707669411532011121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987874276892548709348161 740905707669411532011121)
            ·
              refine ⟨555679280752058649008341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740905707669411532011121 555679280752058649008341)
              ·
                refine ⟨13023733142626374586133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 555679280752058649008341 13023733142626374586133)
                ·
                  rfl

theorem cell22_342409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 7].length) (baseStart_342409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342409 prefixEnd_342409 := by exact prefixLift 342409
  have htrace : WordTrace (prefixWord ++ tailWord_342409) baseStart_342409 baseEnd_342409 := by
    simpa [prefixWord, tailWord_342409, baseEnd_342409] using wordTrace_append hprefix tailTrace_342409
  have hstable : (prefixWord ++ tailWord_342409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342409).length < 2 ^ (prefixWord ++ tailWord_342409).sum := by decide
  have hdescent : baseEnd_342409 < baseStart_342409 := by decide
  rcases family_descends (prefixWord ++ tailWord_342409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342486 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_342486 : Nat := 118140960795 + 342486 * 2 ^ 59
def prefixEnd_342486 : Nat := 4983230072969 + 3 ^ 40 * 342486 * 2
def baseEnd_342486 : Nat := 117239956957234837099961

theorem tailTrace_342486 : CollatzResearch.WordTrace tailWord_342486 prefixEnd_342486 117239956957234837099961 := by
  unfold tailWord_342486
  simp only [CollatzResearch.WordTrace]
  refine ⟨780718164827449299820457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8327660424826125864751541 780718164827449299820457)
  ·
    refine ⟨585538623620586974865343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 780718164827449299820457 585538623620586974865343)
    ·
      refine ⟨878307935430880462298015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585538623620586974865343 878307935430880462298015)
      ·
        refine ⟨1317461903146320693447023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878307935430880462298015 1317461903146320693447023)
        ·
          refine ⟨1976192854719481040170535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1317461903146320693447023 1976192854719481040170535)
          ·
            refine ⟨2964289282079221560255803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976192854719481040170535 2964289282079221560255803)
            ·
              refine ⟨4446433923118832340383705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2964289282079221560255803 4446433923118832340383705)
              ·
                refine ⟨3334825442339124255287779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446433923118832340383705 3334825442339124255287779)
                ·
                  refine ⟨5002238163508686382931669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334825442339124255287779 5002238163508686382931669)
                  ·
                    refine ⟨117239956957234837099961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5002238163508686382931669 117239956957234837099961)
                    ·
                      rfl

theorem cell22_342486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_342486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342486 prefixEnd_342486 := by exact prefixLift 342486
  have htrace : WordTrace (prefixWord ++ tailWord_342486) baseStart_342486 baseEnd_342486 := by
    simpa [prefixWord, tailWord_342486, baseEnd_342486] using wordTrace_append hprefix tailTrace_342486
  have hstable : (prefixWord ++ tailWord_342486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342486).length < 2 ^ (prefixWord ++ tailWord_342486).sum := by decide
  have hdescent : baseEnd_342486 < baseStart_342486 := by decide
  rcases family_descends (prefixWord ++ tailWord_342486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342567 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 6]
def baseStart_342567 : Nat := 118140960795 + 342567 * 2 ^ 59
def prefixEnd_342567 : Nat := 4983230072969 + 3 ^ 40 * 342567 * 2
def baseEnd_342567 : Nat := 39089228304192541941571

theorem tailTrace_342567 : CollatzResearch.WordTrace tailWord_342567 prefixEnd_342567 39089228304192541941571 := by
  unfold tailWord_342567
  simp only [CollatzResearch.WordTrace]
  refine ⟨12494444949945739630825955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8329629966630493087217303 12494444949945739630825955)
  ·
    refine ⟨18741667424918609446238933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12494444949945739630825955 18741667424918609446238933)
    ·
      refine ⟨439257830271529908896225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18741667424918609446238933 439257830271529908896225)
      ·
        refine ⟨329443372703647431672169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439257830271529908896225 329443372703647431672169)
        ·
          refine ⟨247082529527735573754127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329443372703647431672169 247082529527735573754127)
          ·
            refine ⟨370623794291603360631191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247082529527735573754127 370623794291603360631191)
            ·
              refine ⟨555935691437405040946787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370623794291603360631191 555935691437405040946787)
              ·
                refine ⟨833903537156107561420181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555935691437405040946787 833903537156107561420181)
                ·
                  refine ⟨39089228304192541941571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 833903537156107561420181 39089228304192541941571)
                  ·
                    rfl

theorem cell22_342567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 6].length) (baseStart_342567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342567 prefixEnd_342567 := by exact prefixLift 342567
  have htrace : WordTrace (prefixWord ++ tailWord_342567) baseStart_342567 baseEnd_342567 := by
    simpa [prefixWord, tailWord_342567, baseEnd_342567] using wordTrace_append hprefix tailTrace_342567
  have hstable : (prefixWord ++ tailWord_342567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342567).length < 2 ^ (prefixWord ++ tailWord_342567).sum := by decide
  have hdescent : baseEnd_342567 < baseStart_342567 := by decide
  rcases family_descends (prefixWord ++ tailWord_342567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342582 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_342582 : Nat := 118140960795 + 342582 * 2 ^ 59
def prefixEnd_342582 : Nat := 4983230072969 + 3 ^ 40 * 342582 * 2
def baseEnd_342582 : Nat := 117272819719122586699667

theorem tailTrace_342582 : CollatzResearch.WordTrace tailWord_342582 prefixEnd_342582 117272819719122586699667 := by
  unfold tailWord_342582
  simp only [CollatzResearch.WordTrace]
  refine ⟨780937002805712324538875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8329994696594264795081333 780937002805712324538875)
  ·
    refine ⟨1171405504208568486808313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 780937002805712324538875 1171405504208568486808313)
    ·
      refine ⟨878554128156426365106235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1171405504208568486808313 878554128156426365106235)
      ·
        refine ⟨1317831192234639547659353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878554128156426365106235 1317831192234639547659353)
        ·
          refine ⟨988373394175979660744515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1317831192234639547659353 988373394175979660744515)
          ·
            refine ⟨1482560091263969491116773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988373394175979660744515 1482560091263969491116773)
            ·
              refine ⟨277980017111994279584395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1482560091263969491116773 277980017111994279584395)
              ·
                refine ⟨416970025667991419376593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277980017111994279584395 416970025667991419376593)
                ·
                  refine ⟨312727519250993564532445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416970025667991419376593 312727519250993564532445)
                  ·
                    refine ⟨117272819719122586699667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312727519250993564532445 117272819719122586699667)
                    ·
                      rfl

theorem cell22_342582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_342582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342582 prefixEnd_342582 := by exact prefixLift 342582
  have htrace : WordTrace (prefixWord ++ tailWord_342582) baseStart_342582 baseEnd_342582 := by
    simpa [prefixWord, tailWord_342582, baseEnd_342582] using wordTrace_append hprefix tailTrace_342582
  have hstable : (prefixWord ++ tailWord_342582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342582).length < 2 ^ (prefixWord ++ tailWord_342582).sum := by decide
  have hdescent : baseEnd_342582 < baseStart_342582 := by decide
  rcases family_descends (prefixWord ++ tailWord_342582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342610 : List Nat := [3, 2, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_342610 : Nat := 118140960795 + 342610 * 2 ^ 59
def prefixEnd_342610 : Nat := 4983230072969 + 3 ^ 40 * 342610 * 2
def baseEnd_342610 : Nat := 117282404691339846999581

theorem tailTrace_342610 : CollatzResearch.WordTrace tailWord_342610 prefixEnd_342610 117282404691339846999581 := by
  unfold tailWord_342610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124003322197489493660321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8330675525859971983094189 3124003322197489493660321)
  ·
    refine ⟨2343002491648117120245241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3124003322197489493660321 2343002491648117120245241)
    ·
      refine ⟨1757251868736087840183931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2343002491648117120245241 1757251868736087840183931)
      ·
        refine ⟨2635877803104131760275897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757251868736087840183931 2635877803104131760275897)
        ·
          refine ⟨1976908352328098820206923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2635877803104131760275897 1976908352328098820206923)
          ·
            refine ⟨2965362528492148230310385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976908352328098820206923 2965362528492148230310385)
            ·
              refine ⟨2224021896369111172732789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2965362528492148230310385 2224021896369111172732789)
              ·
                refine ⟨208502052784604172443699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2224021896369111172732789 208502052784604172443699)
                ·
                  refine ⟨312753079176906258665549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208502052784604172443699 312753079176906258665549)
                  ·
                    refine ⟨117282404691339846999581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312753079176906258665549 117282404691339846999581)
                    ·
                      rfl

theorem cell22_342610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_342610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342610 prefixEnd_342610 := by exact prefixLift 342610
  have htrace : WordTrace (prefixWord ++ tailWord_342610) baseStart_342610 baseEnd_342610 := by
    simpa [prefixWord, tailWord_342610, baseEnd_342610] using wordTrace_append hprefix tailTrace_342610
  have hstable : (prefixWord ++ tailWord_342610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342610).length < 2 ^ (prefixWord ++ tailWord_342610).sum := by decide
  have hdescent : baseEnd_342610 < baseStart_342610 := by decide
  rcases family_descends (prefixWord ++ tailWord_342610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342636 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_342636 : Nat := 118140960795 + 342636 * 2 ^ 59
def prefixEnd_342636 : Nat := 4983230072969 + 3 ^ 40 * 342636 * 2
def baseEnd_342636 : Nat := 117291305022684445849501

theorem tailTrace_342636 : CollatzResearch.WordTrace tailWord_342636 prefixEnd_342636 117291305022684445849501 := by
  unfold tailWord_342636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6248480793347882207543881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8331307724463842943391841 6248480793347882207543881)
  ·
    refine ⟨4686360595010911655657911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6248480793347882207543881 4686360595010911655657911)
    ·
      refine ⟨7029540892516367483486867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4686360595010911655657911 7029540892516367483486867)
      ·
        refine ⟨10544311338774551225230301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029540892516367483486867 10544311338774551225230301)
        ·
          refine ⟨3954116752040456709461363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10544311338774551225230301 3954116752040456709461363)
          ·
            refine ⟨5931175128060685064192045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3954116752040456709461363 5931175128060685064192045)
            ·
              refine ⟨2224190673022756899072017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5931175128060685064192045 2224190673022756899072017)
              ·
                refine ⟨1668143004767067674304013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2224190673022756899072017 1668143004767067674304013)
                ·
                  refine ⟨625553626787650377864005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1668143004767067674304013 625553626787650377864005)
                  ·
                    refine ⟨117291305022684445849501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625553626787650377864005 117291305022684445849501)
                    ·
                      rfl

theorem cell22_342636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_342636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342636 prefixEnd_342636 := by exact prefixLift 342636
  have htrace : WordTrace (prefixWord ++ tailWord_342636) baseStart_342636 baseEnd_342636 := by
    simpa [prefixWord, tailWord_342636, baseEnd_342636] using wordTrace_append hprefix tailTrace_342636
  have hstable : (prefixWord ++ tailWord_342636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342636).length < 2 ^ (prefixWord ++ tailWord_342636).sum := by decide
  have hdescent : baseEnd_342636 < baseStart_342636 := by decide
  rcases family_descends (prefixWord ++ tailWord_342636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342638 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_342638 : Nat := 118140960795 + 342638 * 2 ^ 59
def prefixEnd_342638 : Nat := 4983230072969 + 3 ^ 40 * 342638 * 2
def baseEnd_342638 : Nat := 117291989663557107299495

theorem tailTrace_342638 : CollatzResearch.WordTrace tailWord_342638 prefixEnd_342638 117291989663557107299495 := by
  unfold tailWord_342638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562129316586064844582571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8331356355125679171107045 1562129316586064844582571)
  ·
    refine ⟨2343193974879097266873857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1562129316586064844582571 2343193974879097266873857)
    ·
      refine ⟨1757395481159322950155393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2343193974879097266873857 1757395481159322950155393)
      ·
        refine ⟨1318046610869492212616545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1757395481159322950155393 1318046610869492212616545)
        ·
          refine ⟨988534958152119159462409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1318046610869492212616545 988534958152119159462409)
          ·
            refine ⟨741401218614089369596807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 988534958152119159462409 741401218614089369596807)
            ·
              refine ⟨1112101827921134054395211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741401218614089369596807 1112101827921134054395211)
              ·
                refine ⟨1668152741881701081592817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112101827921134054395211 1668152741881701081592817)
                ·
                  refine ⟨1251114556411275811194613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668152741881701081592817 1251114556411275811194613)
                  ·
                    refine ⟨117291989663557107299495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1251114556411275811194613 117291989663557107299495)
                    ·
                      rfl

theorem cell22_342638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_342638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342638 prefixEnd_342638 := by exact prefixLift 342638
  have htrace : WordTrace (prefixWord ++ tailWord_342638) baseStart_342638 baseEnd_342638 := by
    simpa [prefixWord, tailWord_342638, baseEnd_342638] using wordTrace_append hprefix tailTrace_342638
  have hstable : (prefixWord ++ tailWord_342638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342638).length < 2 ^ (prefixWord ++ tailWord_342638).sum := by decide
  have hdescent : baseEnd_342638 < baseStart_342638 := by decide
  rcases family_descends (prefixWord ++ tailWord_342638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342681 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_342681 : Nat := 118140960795 + 342681 * 2 ^ 59
def prefixEnd_342681 : Nat := 4983230072969 + 3 ^ 40 * 342681 * 2
def baseEnd_342681 : Nat := 117306709442319328474363

theorem tailTrace_342681 : CollatzResearch.WordTrace tailWord_342681 prefixEnd_342681 117306709442319328474363 := by
  unfold tailWord_342681
  simp only [CollatzResearch.WordTrace]
  refine ⟨12498602871532737100475897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8332401914355158066983931 12498602871532737100475897)
  ·
    refine ⟨9373952153649552825356923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12498602871532737100475897 9373952153649552825356923)
    ·
      refine ⟨14060928230474329238035385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9373952153649552825356923 14060928230474329238035385)
      ·
        refine ⟨10545696172855746928526539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14060928230474329238035385 10545696172855746928526539)
        ·
          refine ⟨15818544259283620392789809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10545696172855746928526539 15818544259283620392789809)
          ·
            refine ⟨11863908194462715294592357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15818544259283620392789809 11863908194462715294592357)
            ·
              refine ⟨2224482786461759117736067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11863908194462715294592357 2224482786461759117736067)
              ·
                refine ⟨3336724179692638676604101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2224482786461759117736067 3336724179692638676604101)
                ·
                  refine ⟨625635783692369751863269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3336724179692638676604101 625635783692369751863269)
                  ·
                    refine ⟨117306709442319328474363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 625635783692369751863269 117306709442319328474363)
                    ·
                      rfl

theorem cell22_342681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_342681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342681 prefixEnd_342681 := by exact prefixLift 342681
  have htrace : WordTrace (prefixWord ++ tailWord_342681) baseStart_342681 baseEnd_342681 := by
    simpa [prefixWord, tailWord_342681, baseEnd_342681] using wordTrace_append hprefix tailTrace_342681
  have hstable : (prefixWord ++ tailWord_342681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342681).length < 2 ^ (prefixWord ++ tailWord_342681).sum := by decide
  have hdescent : baseEnd_342681 < baseStart_342681 := by decide
  rcases family_descends (prefixWord ++ tailWord_342681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342820 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 6]
def baseStart_342820 : Nat := 118140960795 + 342820 * 2 ^ 59
def prefixEnd_342820 : Nat := 4983230072969 + 3 ^ 40 * 342820 * 2
def baseEnd_342820 : Nat := 39118097327656433082979

theorem tailTrace_342820 : CollatzResearch.WordTrace tailWord_342820 prefixEnd_342820 39118097327656433082979 := by
  unfold tailWord_342820
  simp only [CollatzResearch.WordTrace]
  refine ⟨6251836309014581919892957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8335781745352775893190609 6251836309014581919892957)
  ·
    refine ⟨2344438615880468219959859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6251836309014581919892957 2344438615880468219959859)
    ·
      refine ⟨3516657923820702329939789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2344438615880468219959859 3516657923820702329939789)
      ·
        refine ⟨1318746721432763373727421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3516657923820702329939789 1318746721432763373727421)
        ·
          refine ⟨494530020537286265147783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1318746721432763373727421 494530020537286265147783)
          ·
            refine ⟨741795030805929397721675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494530020537286265147783 741795030805929397721675)
            ·
              refine ⟨1112692546208894096582513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741795030805929397721675 1112692546208894096582513)
              ·
                refine ⟨834519409656670572436885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112692546208894096582513 834519409656670572436885)
                ·
                  refine ⟨39118097327656433082979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 834519409656670572436885 39118097327656433082979)
                  ·
                    rfl

theorem cell22_342820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_342820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342820 prefixEnd_342820 := by exact prefixLift 342820
  have htrace : WordTrace (prefixWord ++ tailWord_342820) baseStart_342820 baseEnd_342820 := by
    simpa [prefixWord, tailWord_342820, baseEnd_342820] using wordTrace_append hprefix tailTrace_342820
  have hstable : (prefixWord ++ tailWord_342820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342820).length < 2 ^ (prefixWord ++ tailWord_342820).sum := by decide
  have hdescent : baseEnd_342820 < baseStart_342820 := by decide
  rcases family_descends (prefixWord ++ tailWord_342820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342833 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_342833 : Nat := 118140960795 + 342833 * 2 ^ 59
def prefixEnd_342833 : Nat := 4983230072969 + 3 ^ 40 * 342833 * 2
def baseEnd_342833 : Nat := 117358742148641598673897

theorem tailTrace_342833 : CollatzResearch.WordTrace tailWord_342833 prefixEnd_342833 117358742148641598673897 := by
  unfold tailWord_342833
  simp only [CollatzResearch.WordTrace]
  refine ⟨12504146766982067060009153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8336097844654711373339435 12504146766982067060009153)
  ·
    refine ⟨9378110075236550295006865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12504146766982067060009153 9378110075236550295006865)
    ·
      refine ⟨7033582556427412721255149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9378110075236550295006865 7033582556427412721255149)
      ·
        refine ⟨2637593458660279770470681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7033582556427412721255149 2637593458660279770470681)
        ·
          refine ⟨1978195093995209827853011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2637593458660279770470681 1978195093995209827853011)
          ·
            refine ⟨2967292640992814741779517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978195093995209827853011 2967292640992814741779517)
            ·
              refine ⟨1112734740372305528167319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2967292640992814741779517 1112734740372305528167319)
              ·
                refine ⟨1669102110558458292250979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112734740372305528167319 1669102110558458292250979)
                ·
                  refine ⟨2503653165837687438376469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669102110558458292250979 2503653165837687438376469)
                  ·
                    refine ⟨117358742148641598673897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2503653165837687438376469 117358742148641598673897)
                    ·
                      rfl

theorem cell22_342833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_342833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342833 prefixEnd_342833 := by exact prefixLift 342833
  have htrace : WordTrace (prefixWord ++ tailWord_342833) baseStart_342833 baseEnd_342833 := by
    simpa [prefixWord, tailWord_342833, baseEnd_342833] using wordTrace_append hprefix tailTrace_342833
  have hstable : (prefixWord ++ tailWord_342833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342833).length < 2 ^ (prefixWord ++ tailWord_342833).sum := by decide
  have hdescent : baseEnd_342833 < baseStart_342833 := by decide
  rcases family_descends (prefixWord ++ tailWord_342833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342837 : List Nat := [1, 3, 3, 1, 3, 2, 2, 3, 4]
def baseStart_342837 : Nat := 118140960795 + 342837 * 2 ^ 59
def prefixEnd_342837 : Nat := 4983230072969 + 3 ^ 40 * 342837 * 2
def baseEnd_342837 : Nat := 39120037143462307191295

theorem tailTrace_342837 : CollatzResearch.WordTrace tailWord_342837 prefixEnd_342837 39120037143462307191295 := by
  unfold tailWord_342837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12504292658967575743154765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8336195105978383828769843 12504292658967575743154765)
  ·
    refine ⟨4689109747112840903683037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12504292658967575743154765 4689109747112840903683037)
    ·
      refine ⟨1758416155167315338881139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4689109747112840903683037 1758416155167315338881139)
      ·
        refine ⟨2637624232750973008321709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758416155167315338881139 2637624232750973008321709)
        ·
          refine ⟨989109087281614878120641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2637624232750973008321709 989109087281614878120641)
          ·
            refine ⟨741831815461211158590481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989109087281614878120641 741831815461211158590481)
            ·
              refine ⟨556373861595908368942861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741831815461211158590481 556373861595908368942861)
              ·
                refine ⟨208640198098465638353573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 556373861595908368942861 208640198098465638353573)
                ·
                  refine ⟨39120037143462307191295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208640198098465638353573 39120037143462307191295)
                  ·
                    rfl

theorem cell22_342837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_342837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342837 prefixEnd_342837 := by exact prefixLift 342837
  have htrace : WordTrace (prefixWord ++ tailWord_342837) baseStart_342837 baseEnd_342837 := by
    simpa [prefixWord, tailWord_342837, baseEnd_342837] using wordTrace_append hprefix tailTrace_342837
  have hstable : (prefixWord ++ tailWord_342837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342837).length < 2 ^ (prefixWord ++ tailWord_342837).sum := by decide
  have hdescent : baseEnd_342837 < baseStart_342837 := by decide
  rcases family_descends (prefixWord ++ tailWord_342837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342854 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_342854 : Nat := 118140960795 + 342854 * 2 ^ 59
def prefixEnd_342854 : Nat := 4983230072969 + 3 ^ 40 * 342854 * 2
def baseEnd_342854 : Nat := 39121976959268181299611

theorem tailTrace_342854 : CollatzResearch.WordTrace tailWord_342854 prefixEnd_342854 39121976959268181299611 := by
  unfold tailWord_342854
  simp only [CollatzResearch.WordTrace]
  refine ⟨390778521872062113953863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8336608466603991764349077 390778521872062113953863)
  ·
    refine ⟨586167782808093170930795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 390778521872062113953863 586167782808093170930795)
    ·
      refine ⟨879251674212139756396193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586167782808093170930795 879251674212139756396193)
      ·
        refine ⟨659438755659104817297145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 879251674212139756396193 659438755659104817297145)
        ·
          refine ⟨494579066744328612972859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 659438755659104817297145 494579066744328612972859)
          ·
            refine ⟨741868600116492919459289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494579066744328612972859 741868600116492919459289)
            ·
              refine ⟨556401450087369689594467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741868600116492919459289 556401450087369689594467)
              ·
                refine ⟨834602175131054534391701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556401450087369689594467 834602175131054534391701)
                ·
                  refine ⟨39121976959268181299611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 834602175131054534391701 39121976959268181299611)
                  ·
                    rfl

theorem cell22_342854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_342854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342854 prefixEnd_342854 := by exact prefixLift 342854
  have htrace : WordTrace (prefixWord ++ tailWord_342854) baseStart_342854 baseEnd_342854 := by
    simpa [prefixWord, tailWord_342854, baseEnd_342854] using wordTrace_append hprefix tailTrace_342854
  have hstable : (prefixWord ++ tailWord_342854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342854).length < 2 ^ (prefixWord ++ tailWord_342854).sum := by decide
  have hdescent : baseEnd_342854 < baseStart_342854 := by decide
  rcases family_descends (prefixWord ++ tailWord_342854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342880 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 3, 3]
def baseStart_342880 : Nat := 118140960795 + 342880 * 2 ^ 59
def prefixEnd_342880 : Nat := 4983230072969 + 3 ^ 40 * 342880 * 2
def baseEnd_342880 : Nat := 117374831209149142748753

theorem tailTrace_342880 : CollatzResearch.WordTrace tailWord_342880 prefixEnd_342880 117374831209149142748753 := by
  unfold tailWord_342880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252930498905897043485047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8337240665207862724646729 6252930498905897043485047)
  ·
    refine ⟨9379395748358845565227571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6252930498905897043485047 9379395748358845565227571)
    ·
      refine ⟨14069093622538268347841357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9379395748358845565227571 14069093622538268347841357)
      ·
        refine ⟨5275910108451850630440509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14069093622538268347841357 5275910108451850630440509)
        ·
          refine ⟨1978466290669443986415191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5275910108451850630440509 1978466290669443986415191)
          ·
            refine ⟨2967699436004165979622787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978466290669443986415191 2967699436004165979622787)
            ·
              refine ⟨4451549154006248969434181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2967699436004165979622787 4451549154006248969434181)
              ·
                refine ⟨834665466376171681768909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4451549154006248969434181 834665466376171681768909)
                ·
                  refine ⟨312999549891064380663341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 834665466376171681768909 312999549891064380663341)
                  ·
                    refine ⟨117374831209149142748753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312999549891064380663341 117374831209149142748753)
                    ·
                      rfl

theorem cell22_342880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_342880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342880 prefixEnd_342880 := by exact prefixLift 342880
  have htrace : WordTrace (prefixWord ++ tailWord_342880) baseStart_342880 baseEnd_342880 := by
    simpa [prefixWord, tailWord_342880, baseEnd_342880] using wordTrace_append hprefix tailTrace_342880
  have hstable : (prefixWord ++ tailWord_342880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342880).length < 2 ^ (prefixWord ++ tailWord_342880).sum := by decide
  have hdescent : baseEnd_342880 < baseStart_342880 := by decide
  rcases family_descends (prefixWord ++ tailWord_342880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342908 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_342908 : Nat := 118140960795 + 342908 * 2 ^ 59
def prefixEnd_342908 : Nat := 4983230072969 + 3 ^ 40 * 342908 * 2
def baseEnd_342908 : Nat := 117384416181366403048667

theorem tailTrace_342908 : CollatzResearch.WordTrace tailWord_342908 prefixEnd_342908 117384416181366403048667 := by
  unfold tailWord_342908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253441120855177434494689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8337921494473569912659585 6253441120855177434494689)
  ·
    refine ⟨4690080840641383075871017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6253441120855177434494689 4690080840641383075871017)
    ·
      refine ⟨3517560630481037306903263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4690080840641383075871017 3517560630481037306903263)
      ·
        refine ⟨5276340945721555960354895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3517560630481037306903263 5276340945721555960354895)
        ·
          refine ⟨7914511418582333940532343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5276340945721555960354895 7914511418582333940532343)
          ·
            refine ⟨11871767127873500910798515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7914511418582333940532343 11871767127873500910798515)
            ·
              refine ⟨17807650691810251366197773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11871767127873500910798515 17807650691810251366197773)
              ·
                refine ⟨6677869009428844262324165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17807650691810251366197773 6677869009428844262324165)
                ·
                  refine ⟨1252100439267908299185781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6677869009428844262324165 1252100439267908299185781)
                  ·
                    refine ⟨117384416181366403048667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1252100439267908299185781 117384416181366403048667)
                    ·
                      rfl

theorem cell22_342908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_342908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342908 prefixEnd_342908 := by exact prefixLift 342908
  have htrace : WordTrace (prefixWord ++ tailWord_342908) baseStart_342908 baseEnd_342908 := by
    simpa [prefixWord, tailWord_342908, baseEnd_342908] using wordTrace_append hprefix tailTrace_342908
  have hstable : (prefixWord ++ tailWord_342908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342908).length < 2 ^ (prefixWord ++ tailWord_342908).sum := by decide
  have hdescent : baseEnd_342908 < baseStart_342908 := by decide
  rcases family_descends (prefixWord ++ tailWord_342908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342987 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 2, 3]
def baseStart_342987 : Nat := 118140960795 + 342987 * 2 ^ 59
def prefixEnd_342987 : Nat := 4983230072969 + 3 ^ 40 * 342987 * 2
def baseEnd_342987 : Nat := 117411459495836530323425

theorem tailTrace_342987 : CollatzResearch.WordTrace tailWord_342987 prefixEnd_342987 117411459495836530323425 := by
  unfold tailWord_342987
  simp only [CollatzResearch.WordTrace]
  refine ⟨12509763608424151361115215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8339842405616100907410143 12509763608424151361115215)
  ·
    refine ⟨18764645412636227041672823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12509763608424151361115215 18764645412636227041672823)
    ·
      refine ⟨28146968118954340562509235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18764645412636227041672823 28146968118954340562509235)
      ·
        refine ⟨42220452178431510843763853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28146968118954340562509235 42220452178431510843763853)
        ·
          refine ⟨15832669566911816566411445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42220452178431510843763853 15832669566911816566411445)
          ·
            refine ⟨1484312771897982803101073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15832669566911816566411445 1484312771897982803101073)
            ·
              refine ⟨1113234578923487102325805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1484312771897982803101073 1113234578923487102325805)
              ·
                refine ⟨417462967096307663372177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1113234578923487102325805 417462967096307663372177)
                ·
                  refine ⟨313097225322230747529133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417462967096307663372177 313097225322230747529133)
                  ·
                    refine ⟨117411459495836530323425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313097225322230747529133 117411459495836530323425)
                    ·
                      rfl

theorem cell22_342987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 3].length) (baseStart_342987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_342987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_342987 prefixEnd_342987 := by exact prefixLift 342987
  have htrace : WordTrace (prefixWord ++ tailWord_342987) baseStart_342987 baseEnd_342987 := by
    simpa [prefixWord, tailWord_342987, baseEnd_342987] using wordTrace_append hprefix tailTrace_342987
  have hstable : (prefixWord ++ tailWord_342987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342987).length < 2 ^ (prefixWord ++ tailWord_342987).sum := by decide
  have hdescent : baseEnd_342987 < baseStart_342987 := by decide
  rcases family_descends (prefixWord ++ tailWord_342987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343002 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_343002 : Nat := 118140960795 + 343002 * 2 ^ 59
def prefixEnd_343002 : Nat := 4983230072969 + 3 ^ 40 * 343002 * 2
def baseEnd_343002 : Nat := 117416594302381491198379

theorem tailTrace_343002 : CollatzResearch.WordTrace tailWord_343002 prefixEnd_343002 117416594302381491198379 := by
  unfold tailWord_343002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3127577675842452230727815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8340207135579872615274173 3127577675842452230727815)
  ·
    refine ⟨4691366513763678346091723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3127577675842452230727815 4691366513763678346091723)
    ·
      refine ⟨7037049770645517519137585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4691366513763678346091723 7037049770645517519137585)
      ·
        refine ⟨5277787327984138139353189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7037049770645517519137585 5277787327984138139353189)
        ·
          refine ⟨989585123997025901128723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5277787327984138139353189 989585123997025901128723)
          ·
            refine ⟨1484377685995538851693085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989585123997025901128723 1484377685995538851693085)
            ·
              refine ⟨556641632248327069384907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1484377685995538851693085 556641632248327069384907)
              ·
                refine ⟨834962448372490604077361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556641632248327069384907 834962448372490604077361)
                ·
                  refine ⟨626221836279367953058021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 834962448372490604077361 626221836279367953058021)
                  ·
                    refine ⟨117416594302381491198379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626221836279367953058021 117416594302381491198379)
                    ·
                      rfl

theorem cell22_343002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_343002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343002 prefixEnd_343002 := by exact prefixLift 343002
  have htrace : WordTrace (prefixWord ++ tailWord_343002) baseStart_343002 baseEnd_343002 := by
    simpa [prefixWord, tailWord_343002, baseEnd_343002] using wordTrace_append hprefix tailTrace_343002
  have hstable : (prefixWord ++ tailWord_343002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343002).length < 2 ^ (prefixWord ++ tailWord_343002).sum := by decide
  have hdescent : baseEnd_343002 < baseStart_343002 := by decide
  rcases family_descends (prefixWord ++ tailWord_343002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343038 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_343038 : Nat := 118140960795 + 343038 * 2 ^ 59
def prefixEnd_343038 : Nat := 4983230072969 + 3 ^ 40 * 343038 * 2
def baseEnd_343038 : Nat := 117428917838089397298269

theorem tailTrace_343038 : CollatzResearch.WordTrace tailWord_343038 prefixEnd_343038 117428917838089397298269 := by
  unfold tailWord_343038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563952966404923383902721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8341082487492924714147845 1563952966404923383902721)
  ·
    refine ⟨1172964724803692537927041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1563952966404923383902721 1172964724803692537927041)
    ·
      refine ⟨879723543602769403445281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1172964724803692537927041 879723543602769403445281)
      ·
        refine ⟨659792657702077052583961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 879723543602769403445281 659792657702077052583961)
        ·
          refine ⟨494844493276557789437971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 659792657702077052583961 494844493276557789437971)
          ·
            refine ⟨742266739914836684156957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494844493276557789437971 742266739914836684156957)
            ·
              refine ⟨278350027468063756558859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742266739914836684156957 278350027468063756558859)
              ·
                refine ⟨417525041202095634838289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278350027468063756558859 417525041202095634838289)
                ·
                  refine ⟨313143780901571726128717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417525041202095634838289 313143780901571726128717)
                  ·
                    refine ⟨117428917838089397298269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313143780901571726128717 117428917838089397298269)
                    ·
                      rfl

theorem cell22_343038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_343038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343038 prefixEnd_343038 := by exact prefixLift 343038
  have htrace : WordTrace (prefixWord ++ tailWord_343038) baseStart_343038 baseEnd_343038 := by
    simpa [prefixWord, tailWord_343038, baseEnd_343038] using wordTrace_append hprefix tailTrace_343038
  have hstable : (prefixWord ++ tailWord_343038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343038).length < 2 ^ (prefixWord ++ tailWord_343038).sum := by decide
  have hdescent : baseEnd_343038 < baseStart_343038 := by decide
  rcases family_descends (prefixWord ++ tailWord_343038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343120 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_343120 : Nat := 118140960795 + 343120 * 2 ^ 59
def prefixEnd_343120 : Nat := 4983230072969 + 3 ^ 40 * 343120 * 2
def baseEnd_343120 : Nat := 117456988113868516748017

theorem tailTrace_343120 : CollatzResearch.WordTrace tailWord_343120 prefixEnd_343120 117456988113868516748017 := by
  unfold tailWord_343120
  simp only [CollatzResearch.WordTrace]
  refine ⟨6257307258471157537853407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8343076344628210050471209 6257307258471157537853407)
  ·
    refine ⟨9385960887706736306780111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6257307258471157537853407 9385960887706736306780111)
    ·
      refine ⟨14078941331560104460170167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9385960887706736306780111 14078941331560104460170167)
      ·
        refine ⟨21118411997340156690255251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14078941331560104460170167 21118411997340156690255251)
        ·
          refine ⟨31677617996010235035382877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21118411997340156690255251 31677617996010235035382877)
          ·
            refine ⟨11879106748503838138268579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31677617996010235035382877 11879106748503838138268579)
            ·
              refine ⟨17818660122755757207402869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11879106748503838138268579 17818660122755757207402869)
              ·
                refine ⟨1670499386508352238194019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17818660122755757207402869 1670499386508352238194019)
                ·
                  refine ⟨2505749079762528357291029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670499386508352238194019 2505749079762528357291029)
                  ·
                    refine ⟨117456988113868516748017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2505749079762528357291029 117456988113868516748017)
                    ·
                      rfl

theorem cell22_343120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_343120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343120 prefixEnd_343120 := by exact prefixLift 343120
  have htrace : WordTrace (prefixWord ++ tailWord_343120) baseStart_343120 baseEnd_343120 := by
    simpa [prefixWord, tailWord_343120, baseEnd_343120] using wordTrace_append hprefix tailTrace_343120
  have hstable : (prefixWord ++ tailWord_343120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343120).length < 2 ^ (prefixWord ++ tailWord_343120).sum := by decide
  have hdescent : baseEnd_343120 < baseStart_343120 := by decide
  rcases family_descends (prefixWord ++ tailWord_343120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343122 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_343122 : Nat := 118140960795 + 343122 * 2 ^ 59
def prefixEnd_343122 : Nat := 4983230072969 + 3 ^ 40 * 343122 * 2
def baseEnd_343122 : Nat := 117457672754741178198011

theorem tailTrace_343122 : CollatzResearch.WordTrace tailWord_343122 prefixEnd_343122 117457672754741178198011 := by
  unfold tailWord_343122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128671865733767354319905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8343124975290046278186413 3128671865733767354319905)
  ·
    refine ⟨2346503899300325515739929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3128671865733767354319905 2346503899300325515739929)
    ·
      refine ⟨1759877924475244136804947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2346503899300325515739929 1759877924475244136804947)
      ·
        refine ⟨2639816886712866205207421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759877924475244136804947 2639816886712866205207421)
        ·
          refine ⟨989931332517324826952783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2639816886712866205207421 989931332517324826952783)
          ·
            refine ⟨1484896998775987240429175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989931332517324826952783 1484896998775987240429175)
            ·
              refine ⟨2227345498163980860643763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484896998775987240429175 2227345498163980860643763)
              ·
                refine ⟨3341018247245971290965645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227345498163980860643763 3341018247245971290965645)
                ·
                  refine ⟨1252881842717239234112117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3341018247245971290965645 1252881842717239234112117)
                  ·
                    refine ⟨117457672754741178198011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1252881842717239234112117 117457672754741178198011)
                    ·
                      rfl

theorem cell22_343122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_343122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343122 prefixEnd_343122 := by exact prefixLift 343122
  have htrace : WordTrace (prefixWord ++ tailWord_343122) baseStart_343122 baseEnd_343122 := by
    simpa [prefixWord, tailWord_343122, baseEnd_343122] using wordTrace_append hprefix tailTrace_343122
  have hstable : (prefixWord ++ tailWord_343122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343122).length < 2 ^ (prefixWord ++ tailWord_343122).sum := by decide
  have hdescent : baseEnd_343122 < baseStart_343122 := by decide
  rcases family_descends (prefixWord ++ tailWord_343122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343137 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_343137 : Nat := 118140960795 + 343137 * 2 ^ 59
def prefixEnd_343137 : Nat := 4983230072969 + 3 ^ 40 * 343137 * 2
def baseEnd_343137 : Nat := 117462807561286139072965

theorem tailTrace_343137 : CollatzResearch.WordTrace tailWord_343137 prefixEnd_343137 117462807561286139072965 := by
  unfold tailWord_343137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515234557880726979075665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8343489705253817986050443 12515234557880726979075665)
  ·
    refine ⟨9386425918410545234306749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12515234557880726979075665 9386425918410545234306749)
    ·
      refine ⟨3519909719403954462865031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9386425918410545234306749 3519909719403954462865031)
      ·
        refine ⟨5279864579105931694297547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519909719403954462865031 5279864579105931694297547)
        ·
          refine ⟨7919796868658897541446321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5279864579105931694297547 7919796868658897541446321)
          ·
            refine ⟨5939847651494173156084741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7919796868658897541446321 5939847651494173156084741)
            ·
              refine ⟨1113721434655157466765889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5939847651494173156084741 1113721434655157466765889)
              ·
                refine ⟨835291075991368100074417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113721434655157466765889 835291075991368100074417)
                ·
                  refine ⟨626468306993526075055813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 835291075991368100074417 626468306993526075055813)
                  ·
                    refine ⟨117462807561286139072965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626468306993526075055813 117462807561286139072965)
                    ·
                      rfl

theorem cell22_343137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_343137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343137 prefixEnd_343137 := by exact prefixLift 343137
  have htrace : WordTrace (prefixWord ++ tailWord_343137) baseStart_343137 baseEnd_343137 := by
    simpa [prefixWord, tailWord_343137, baseEnd_343137] using wordTrace_append hprefix tailTrace_343137
  have hstable : (prefixWord ++ tailWord_343137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343137).length < 2 ^ (prefixWord ++ tailWord_343137).sum := by decide
  have hdescent : baseEnd_343137 < baseStart_343137 := by decide
  rcases family_descends (prefixWord ++ tailWord_343137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343169 : List Nat := [1, 2, 4, 2, 2, 2, 3, 6]
def baseStart_343169 : Nat := 118140960795 + 343169 * 2 ^ 59
def prefixEnd_343169 : Nat := 4983230072969 + 3 ^ 40 * 343169 * 2
def baseEnd_343169 : Nat := 13052640201694302474763

theorem tailTrace_343169 : CollatzResearch.WordTrace tailWord_343169 prefixEnd_343169 13052640201694302474763 := by
  unfold tailWord_343169
  simp only [CollatzResearch.WordTrace]
  refine ⟨12516401693764796444240561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8344267795843197629493707 12516401693764796444240561)
  ·
    refine ⟨9387301270323597333180421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12516401693764796444240561 9387301270323597333180421)
    ·
      refine ⟨1760118988185674499971329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9387301270323597333180421 1760118988185674499971329)
      ·
        refine ⟨1320089241139255874978497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1760118988185674499971329 1320089241139255874978497)
        ·
          refine ⟨990066930854441906233873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320089241139255874978497 990066930854441906233873)
          ·
            refine ⟨742550198140831429675405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990066930854441906233873 742550198140831429675405)
            ·
              refine ⟨278456324302811786128277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742550198140831429675405 278456324302811786128277)
              ·
                refine ⟨13052640201694302474763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 278456324302811786128277 13052640201694302474763)
                ·
                  rfl

theorem cell22_343169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 6].length) (baseStart_343169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343169 prefixEnd_343169 := by exact prefixLift 343169
  have htrace : WordTrace (prefixWord ++ tailWord_343169) baseStart_343169 baseEnd_343169 := by
    simpa [prefixWord, tailWord_343169, baseEnd_343169] using wordTrace_append hprefix tailTrace_343169
  have hstable : (prefixWord ++ tailWord_343169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343169).length < 2 ^ (prefixWord ++ tailWord_343169).sum := by decide
  have hdescent : baseEnd_343169 < baseStart_343169 := by decide
  rcases family_descends (prefixWord ++ tailWord_343169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343197 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 7]
def baseStart_343197 : Nat := 118140960795 + 343197 * 2 ^ 59
def prefixEnd_343197 : Nat := 4983230072969 + 3 ^ 40 * 343197 * 2
def baseEnd_343197 : Nat := 39161115595821994190927

theorem tailTrace_343197 : CollatzResearch.WordTrace tailWord_343197 prefixEnd_343197 39161115595821994190927 := by
  unfold tailWord_343197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517422937663357226259845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8344948625108904817506563 12517422937663357226259845)
  ·
    refine ⟨2347016800811879479923721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12517422937663357226259845 2347016800811879479923721)
    ·
      refine ⟨1760262600608909609942791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2347016800811879479923721 1760262600608909609942791)
      ·
        refine ⟨2640393900913364414914187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760262600608909609942791 2640393900913364414914187)
        ·
          refine ⟨3960590851370046622371281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640393900913364414914187 3960590851370046622371281)
          ·
            refine ⟨2970443138527534966778461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3960590851370046622371281 2970443138527534966778461)
            ·
              refine ⟨1113916176947825612541923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2970443138527534966778461 1113916176947825612541923)
              ·
                refine ⟨1670874265421738418812885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113916176947825612541923 1670874265421738418812885)
                ·
                  refine ⟨39161115595821994190927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1670874265421738418812885 39161115595821994190927)
                  ·
                    rfl

theorem cell22_343197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_343197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343197 prefixEnd_343197 := by exact prefixLift 343197
  have htrace : WordTrace (prefixWord ++ tailWord_343197) baseStart_343197 baseEnd_343197 := by
    simpa [prefixWord, tailWord_343197, baseEnd_343197] using wordTrace_append hprefix tailTrace_343197
  have hstable : (prefixWord ++ tailWord_343197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343197).length < 2 ^ (prefixWord ++ tailWord_343197).sum := by decide
  have hdescent : baseEnd_343197 < baseStart_343197 := by decide
  rcases family_descends (prefixWord ++ tailWord_343197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343201 : List Nat := [1, 2, 3, 3, 1, 1, 1, 6, 1, 3]
def baseStart_343201 : Nat := 118140960795 + 343201 * 2 ^ 59
def prefixEnd_343201 : Nat := 4983230072969 + 3 ^ 40 * 343201 * 2
def baseEnd_343201 : Nat := 117484716069211305472769

theorem tailTrace_343201 : CollatzResearch.WordTrace tailWord_343201 prefixEnd_343201 117484716069211305472769 := by
  unfold tailWord_343201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517568829648865909405457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8345045886432577272936971 12517568829648865909405457)
  ·
    refine ⟨9388176622236649432054093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12517568829648865909405457 9388176622236649432054093)
    ·
      refine ⟨3520566233338743537020285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9388176622236649432054093 3520566233338743537020285)
      ·
        refine ⟨1320212337502028826382607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3520566233338743537020285 1320212337502028826382607)
        ·
          refine ⟨1980318506253043239573911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320212337502028826382607 1980318506253043239573911)
          ·
            refine ⟨2970477759379564859360867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980318506253043239573911 2970477759379564859360867)
            ·
              refine ⟨4455716639069347289041301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970477759379564859360867 4455716639069347289041301)
              ·
                refine ⟨208861717456375654173811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4455716639069347289041301 208861717456375654173811)
                ·
                  refine ⟨313292576184563481260717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208861717456375654173811 313292576184563481260717)
                  ·
                    refine ⟨117484716069211305472769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313292576184563481260717 117484716069211305472769)
                    ·
                      rfl

theorem cell22_343201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_343201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343201 prefixEnd_343201 := by exact prefixLift 343201
  have htrace : WordTrace (prefixWord ++ tailWord_343201) baseStart_343201 baseEnd_343201 := by
    simpa [prefixWord, tailWord_343201, baseEnd_343201] using wordTrace_append hprefix tailTrace_343201
  have hstable : (prefixWord ++ tailWord_343201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343201).length < 2 ^ (prefixWord ++ tailWord_343201).sum := by decide
  have hdescent : baseEnd_343201 < baseStart_343201 := by decide
  rcases family_descends (prefixWord ++ tailWord_343201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343252 : List Nat := [2, 4, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_343252 : Nat := 118140960795 + 343252 * 2 ^ 59
def prefixEnd_343252 : Nat := 4983230072969 + 3 ^ 40 * 343252 * 2
def baseEnd_343252 : Nat := 117502174411464172447613

theorem tailTrace_343252 : CollatzResearch.WordTrace tailWord_343252 prefixEnd_343252 117502174411464172447613 := by
  unfold tailWord_343252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259714476232050809756005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8346285968309401079674673 6259714476232050809756005)
  ·
    refine ⟨1173696464293509526829251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6259714476232050809756005 1173696464293509526829251)
    ·
      refine ⟨1760544696440264290243877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1173696464293509526829251 1760544696440264290243877)
      ·
        refine ⟨330102130582549554420727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1760544696440264290243877 330102130582549554420727)
        ·
          refine ⟨495153195873824331631091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330102130582549554420727 495153195873824331631091)
          ·
            refine ⟨742729793810736497446637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495153195873824331631091 742729793810736497446637)
            ·
              refine ⟨278523672679026186542489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742729793810736497446637 278523672679026186542489)
              ·
                refine ⟨208892754509269639906867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278523672679026186542489 208892754509269639906867)
                ·
                  refine ⟨313339131763904459860301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208892754509269639906867 313339131763904459860301)
                  ·
                    refine ⟨117502174411464172447613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313339131763904459860301 117502174411464172447613)
                    ·
                      rfl

theorem cell22_343252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_343252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343252 prefixEnd_343252 := by exact prefixLift 343252
  have htrace : WordTrace (prefixWord ++ tailWord_343252) baseStart_343252 baseEnd_343252 := by
    simpa [prefixWord, tailWord_343252, baseEnd_343252] using wordTrace_append hprefix tailTrace_343252
  have hstable : (prefixWord ++ tailWord_343252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343252).length < 2 ^ (prefixWord ++ tailWord_343252).sum := by decide
  have hdescent : baseEnd_343252 < baseStart_343252 := by decide
  rcases family_descends (prefixWord ++ tailWord_343252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343289 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_343289 : Nat := 118140960795 + 343289 * 2 ^ 59
def prefixEnd_343289 : Nat := 4983230072969 + 3 ^ 40 * 343289 * 2
def baseEnd_343289 : Nat := 117514840267608409272499

theorem tailTrace_343289 : CollatzResearch.WordTrace tailWord_343289 prefixEnd_343289 117514840267608409272499 := by
  unfold tailWord_343289
  simp only [CollatzResearch.WordTrace]
  refine ⟨12520778453330056938608921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8347185635553371292405947 12520778453330056938608921)
  ·
    refine ⟨9390583839997542703956691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12520778453330056938608921 9390583839997542703956691)
    ·
      refine ⟨14085875759996314055935037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9390583839997542703956691 14085875759996314055935037)
      ·
        refine ⟨5282203409998617770975639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14085875759996314055935037 5282203409998617770975639)
        ·
          refine ⟨7923305114997926656463459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5282203409998617770975639 7923305114997926656463459)
          ·
            refine ⟨11884957672496889984695189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7923305114997926656463459 11884957672496889984695189)
            ·
              refine ⟨557107390898291718032587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11884957672496889984695189 557107390898291718032587)
              ·
                refine ⟨835661086347437577048881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557107390898291718032587 835661086347437577048881)
                ·
                  refine ⟨626745814760578182786661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 835661086347437577048881 626745814760578182786661)
                  ·
                    refine ⟨117514840267608409272499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626745814760578182786661 117514840267608409272499)
                    ·
                      rfl

theorem cell22_343289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_343289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343289 prefixEnd_343289 := by exact prefixLift 343289
  have htrace : WordTrace (prefixWord ++ tailWord_343289) baseStart_343289 baseEnd_343289 := by
    simpa [prefixWord, tailWord_343289, baseEnd_343289] using wordTrace_append hprefix tailTrace_343289
  have hstable : (prefixWord ++ tailWord_343289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343289).length < 2 ^ (prefixWord ++ tailWord_343289).sum := by decide
  have hdescent : baseEnd_343289 < baseStart_343289 := by decide
  rcases family_descends (prefixWord ++ tailWord_343289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343304 : List Nat := [2, 1, 3, 2, 5, 9]
def baseStart_343304 : Nat := 118140960795 + 343304 * 2 ^ 59
def prefixEnd_343304 : Nat := 4983230072969 + 3 ^ 40 * 343304 * 2
def baseEnd_343304 : Nat := 1450863889804362594413

theorem tailTrace_343304 : CollatzResearch.WordTrace tailWord_343304 prefixEnd_343304 1450863889804362594413 := by
  unfold tailWord_343304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260662774137857250202483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8347550365517143000269977 6260662774137857250202483)
  ·
    refine ⟨9390994161206785875303725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6260662774137857250202483 9390994161206785875303725)
    ·
      refine ⟨3521622810452544703238897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9390994161206785875303725 3521622810452544703238897)
      ·
        refine ⟨2641217107839408527429173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3521622810452544703238897 2641217107839408527429173)
        ·
          refine ⟨247614103859944549446485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2641217107839408527429173 247614103859944549446485)
          ·
            refine ⟨1450863889804362594413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 247614103859944549446485 1450863889804362594413)
            ·
              rfl

theorem cell22_343304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 9].length) (baseStart_343304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343304 prefixEnd_343304 := by exact prefixLift 343304
  have htrace : WordTrace (prefixWord ++ tailWord_343304) baseStart_343304 baseEnd_343304 := by
    simpa [prefixWord, tailWord_343304, baseEnd_343304] using wordTrace_append hprefix tailTrace_343304
  have hstable : (prefixWord ++ tailWord_343304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343304).length < 2 ^ (prefixWord ++ tailWord_343304).sum := by decide
  have hdescent : baseEnd_343304 < baseStart_343304 := by decide
  rcases family_descends (prefixWord ++ tailWord_343304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343336 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 5, 3]
def baseStart_343336 : Nat := 118140960795 + 343336 * 2 ^ 59
def prefixEnd_343336 : Nat := 4983230072969 + 3 ^ 40 * 343336 * 2
def baseEnd_343336 : Nat := 117530929328115953347355

theorem tailTrace_343336 : CollatzResearch.WordTrace tailWord_343336 prefixEnd_343336 117530929328115953347355 := by
  unfold tailWord_343336
  simp only [CollatzResearch.WordTrace]
  refine ⟨6261246342079891982784931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8348328456106522643713241 6261246342079891982784931)
  ·
    refine ⟨9391869513119837974177397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6261246342079891982784931 9391869513119837974177397)
    ·
      refine ⟨880487766854984810079131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9391869513119837974177397 880487766854984810079131)
      ·
        refine ⟨1320731650282477215118697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880487766854984810079131 1320731650282477215118697)
        ·
          refine ⟨990548737711857911339023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320731650282477215118697 990548737711857911339023)
          ·
            refine ⟨1485823106567786867008535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990548737711857911339023 1485823106567786867008535)
            ·
              refine ⟨2228734659851680300512803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485823106567786867008535 2228734659851680300512803)
              ·
                refine ⟨3343101989777520450769205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228734659851680300512803 3343101989777520450769205)
                ·
                  refine ⟨313415811541642542259613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3343101989777520450769205 313415811541642542259613)
                  ·
                    refine ⟨117530929328115953347355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313415811541642542259613 117530929328115953347355)
                    ·
                      rfl

theorem cell22_343336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_343336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343336 prefixEnd_343336 := by exact prefixLift 343336
  have htrace : WordTrace (prefixWord ++ tailWord_343336) baseStart_343336 baseEnd_343336 := by
    simpa [prefixWord, tailWord_343336, baseEnd_343336] using wordTrace_append hprefix tailTrace_343336
  have hstable : (prefixWord ++ tailWord_343336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343336).length < 2 ^ (prefixWord ++ tailWord_343336).sum := by decide
  have hdescent : baseEnd_343336 < baseStart_343336 := by decide
  rcases family_descends (prefixWord ++ tailWord_343336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343396 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_343396 : Nat := 118140960795 + 343396 * 2 ^ 59
def prefixEnd_343396 : Nat := 4983230072969 + 3 ^ 40 * 343396 * 2
def baseEnd_343396 : Nat := 117551468554295796847171

theorem tailTrace_343396 : CollatzResearch.WordTrace tailWord_343396 prefixEnd_343396 117551468554295796847171 := by
  unfold tailWord_343396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262340531971207106377021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8349787375961609475169361 6262340531971207106377021)
  ·
    refine ⟨2348377699489202664891383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6262340531971207106377021 2348377699489202664891383)
    ·
      refine ⟨3522566549233803997337075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348377699489202664891383 3522566549233803997337075)
      ·
        refine ⟨5283849823850705996005613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3522566549233803997337075 5283849823850705996005613)
        ·
          refine ⟨1981443683944014748502105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5283849823850705996005613 1981443683944014748502105)
          ·
            refine ⟨1486082762958011061376579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981443683944014748502105 1486082762958011061376579)
            ·
              refine ⟨2229124144437016592064869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486082762958011061376579 2229124144437016592064869)
              ·
                refine ⟨417960777081940611012163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2229124144437016592064869 417960777081940611012163)
                ·
                  refine ⟨626941165622910916518245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417960777081940611012163 626941165622910916518245)
                  ·
                    refine ⟨117551468554295796847171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626941165622910916518245 117551468554295796847171)
                    ·
                      rfl

theorem cell22_343396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_343396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343396 prefixEnd_343396 := by exact prefixLift 343396
  have htrace : WordTrace (prefixWord ++ tailWord_343396) baseStart_343396 baseEnd_343396 := by
    simpa [prefixWord, tailWord_343396, baseEnd_343396] using wordTrace_append hprefix tailTrace_343396
  have hstable : (prefixWord ++ tailWord_343396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343396).length < 2 ^ (prefixWord ++ tailWord_343396).sum := by decide
  have hdescent : baseEnd_343396 < baseStart_343396 := by decide
  rcases family_descends (prefixWord ++ tailWord_343396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343409 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_343409 : Nat := 118140960795 + 343409 * 2 ^ 59
def prefixEnd_343409 : Nat := 4983230072969 + 3 ^ 40 * 343409 * 2
def baseEnd_343409 : Nat := 117555918719968096272131

theorem tailTrace_343409 : CollatzResearch.WordTrace tailWord_343409 prefixEnd_343409 117555918719968096272131 := by
  unfold tailWord_343409
  simp only [CollatzResearch.WordTrace]
  refine ⟨12525155212895317432977281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8350103475263544955318187 12525155212895317432977281)
  ·
    refine ⟨9393866409671488074732961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12525155212895317432977281 9393866409671488074732961)
    ·
      refine ⟨7045399807253616056049721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9393866409671488074732961 7045399807253616056049721)
      ·
        refine ⟨5284049855440212042037291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7045399807253616056049721 5284049855440212042037291)
        ·
          refine ⟨7926074783160318063055937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5284049855440212042037291 7926074783160318063055937)
          ·
            refine ⟨5944556087370238547291953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7926074783160318063055937 5944556087370238547291953)
            ·
              refine ⟨4458417065527678910468965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5944556087370238547291953 4458417065527678910468965)
              ·
                refine ⟨835953199786439795712931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4458417065527678910468965 835953199786439795712931)
                ·
                  refine ⟨1253929799679659693569397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835953199786439795712931 1253929799679659693569397)
                  ·
                    refine ⟨117555918719968096272131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1253929799679659693569397 117555918719968096272131)
                    ·
                      rfl

theorem cell22_343409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_343409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343409 prefixEnd_343409 := by exact prefixLift 343409
  have htrace : WordTrace (prefixWord ++ tailWord_343409) baseStart_343409 baseEnd_343409 := by
    simpa [prefixWord, tailWord_343409, baseEnd_343409] using wordTrace_append hprefix tailTrace_343409
  have hstable : (prefixWord ++ tailWord_343409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343409).length < 2 ^ (prefixWord ++ tailWord_343409).sum := by decide
  have hdescent : baseEnd_343409 < baseStart_343409 := by decide
  rcases family_descends (prefixWord ++ tailWord_343409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343458 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_343458 : Nat := 118140960795 + 343458 * 2 ^ 59
def prefixEnd_343458 : Nat := 4983230072969 + 3 ^ 40 * 343458 * 2
def baseEnd_343458 : Nat := 117572692421348301796981

theorem tailTrace_343458 : CollatzResearch.WordTrace tailWord_343458 prefixEnd_343458 117572692421348301796981 := by
  unfold tailWord_343458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131735597429449700377757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8351294926478532534340685 3131735597429449700377757)
  ·
    refine ⟨1174400849036043637641659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3131735597429449700377757 1174400849036043637641659)
    ·
      refine ⟨1761601273554065456462489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174400849036043637641659 1761601273554065456462489)
      ·
        refine ⟨1321200955165549092346867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1761601273554065456462489 1321200955165549092346867)
        ·
          refine ⟨1981801432748323638520301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321200955165549092346867 1981801432748323638520301)
          ·
            refine ⟨743175537280621364445113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1981801432748323638520301 743175537280621364445113)
            ·
              refine ⟨557381652960466023333835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743175537280621364445113 557381652960466023333835)
              ·
                refine ⟨836072479440699035000753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557381652960466023333835 836072479440699035000753)
                ·
                  refine ⟨627054359580524276250565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 836072479440699035000753 627054359580524276250565)
                  ·
                    refine ⟨117572692421348301796981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 627054359580524276250565 117572692421348301796981)
                    ·
                      rfl

theorem cell22_343458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_343458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343458 prefixEnd_343458 := by exact prefixLift 343458
  have htrace : WordTrace (prefixWord ++ tailWord_343458) baseStart_343458 baseEnd_343458 := by
    simpa [prefixWord, tailWord_343458, baseEnd_343458] using wordTrace_append hprefix tailTrace_343458
  have hstable : (prefixWord ++ tailWord_343458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343458).length < 2 ^ (prefixWord ++ tailWord_343458).sum := by decide
  have hdescent : baseEnd_343458 < baseStart_343458 := by decide
  rcases family_descends (prefixWord ++ tailWord_343458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343499 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 1, 7]
def baseStart_343499 : Nat := 118140960795 + 343499 * 2 ^ 59
def prefixEnd_343499 : Nat := 4983230072969 + 3 ^ 40 * 343499 * 2
def baseEnd_343499 : Nat := 117586727559237861521855

theorem tailTrace_343499 : CollatzResearch.WordTrace tailWord_343499 prefixEnd_343499 117586727559237861521855 := by
  unfold tailWord_343499
  simp only [CollatzResearch.WordTrace]
  refine ⟨12528437782569262803753551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8352291855046175202502367 12528437782569262803753551)
  ·
    refine ⟨18792656673853894205630327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12528437782569262803753551 18792656673853894205630327)
    ·
      refine ⟨28188985010780841308445491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18792656673853894205630327 28188985010780841308445491)
      ·
        refine ⟨42283477516171261962668237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28188985010780841308445491 42283477516171261962668237)
        ·
          refine ⟨15856304068564223236000589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42283477516171261962668237 15856304068564223236000589)
          ·
            refine ⟨5946114025711583713500221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15856304068564223236000589 5946114025711583713500221)
            ·
              refine ⟨2229792759641843892562583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5946114025711583713500221 2229792759641843892562583)
              ·
                refine ⟨3344689139462765838843875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229792759641843892562583 3344689139462765838843875)
                ·
                  refine ⟨5017033709194148758265813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344689139462765838843875 5017033709194148758265813)
                  ·
                    refine ⟨117586727559237861521855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5017033709194148758265813 117586727559237861521855)
                    ·
                      rfl

theorem cell22_343499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_343499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343499 prefixEnd_343499 := by exact prefixLift 343499
  have htrace : WordTrace (prefixWord ++ tailWord_343499) baseStart_343499 baseEnd_343499 := by
    simpa [prefixWord, tailWord_343499, baseEnd_343499] using wordTrace_append hprefix tailTrace_343499
  have hstable : (prefixWord ++ tailWord_343499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343499).length < 2 ^ (prefixWord ++ tailWord_343499).sum := by decide
  have hdescent : baseEnd_343499 < baseStart_343499 := by decide
  rcases family_descends (prefixWord ++ tailWord_343499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343546 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_343546 : Nat := 118140960795 + 343546 * 2 ^ 59
def prefixEnd_343546 : Nat := 4983230072969 + 3 ^ 40 * 343546 * 2
def baseEnd_343546 : Nat := 39200938873248468532237

theorem tailTrace_343546 : CollatzResearch.WordTrace tailWord_343546 prefixEnd_343546 39200938873248468532237 := by
  unfold tailWord_343546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3132538003349747457678623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8353434675599326553809661 3132538003349747457678623)
  ·
    refine ⟨4698807005024621186517935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3132538003349747457678623 4698807005024621186517935)
    ·
      refine ⟨7048210507536931779776903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4698807005024621186517935 7048210507536931779776903)
      ·
        refine ⟨10572315761305397669665355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7048210507536931779776903 10572315761305397669665355)
        ·
          refine ⟨15858473641958096504498033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10572315761305397669665355 15858473641958096504498033)
          ·
            refine ⟨11893855231468572378373525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15858473641958096504498033 11893855231468572378373525)
            ·
              refine ⟨557524463975089330236259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11893855231468572378373525 557524463975089330236259)
              ·
                refine ⟨836286695962633995354389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557524463975089330236259 836286695962633995354389)
                ·
                  refine ⟨39200938873248468532237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 836286695962633995354389 39200938873248468532237)
                  ·
                    rfl

theorem cell22_343546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_343546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343546 prefixEnd_343546 := by exact prefixLift 343546
  have htrace : WordTrace (prefixWord ++ tailWord_343546) baseStart_343546 baseEnd_343546 := by
    simpa [prefixWord, tailWord_343546, baseEnd_343546] using wordTrace_append hprefix tailTrace_343546
  have hstable : (prefixWord ++ tailWord_343546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343546).length < 2 ^ (prefixWord ++ tailWord_343546).sum := by decide
  have hdescent : baseEnd_343546 < baseStart_343546 := by decide
  rcases family_descends (prefixWord ++ tailWord_343546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343640 : List Nat := [2, 1, 2, 2, 1, 2, 1, 7, 1, 3]
def baseStart_343640 : Nat := 118140960795 + 343640 * 2 ^ 59
def prefixEnd_343640 : Nat := 4983230072969 + 3 ^ 40 * 343640 * 2
def baseEnd_343640 : Nat := 117634994740760493746423

theorem tailTrace_343640 : CollatzResearch.WordTrace tailWord_343640 prefixEnd_343640 117634994740760493746423 := by
  unfold tailWord_343640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6266790237529221942318187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8355720316705629256424249 6266790237529221942318187)
  ·
    refine ⟨9400185356293832913477281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6266790237529221942318187 9400185356293832913477281)
    ·
      refine ⟨7050139017220374685107961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9400185356293832913477281 7050139017220374685107961)
      ·
        refine ⟨5287604262915281013830971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7050139017220374685107961 5287604262915281013830971)
        ·
          refine ⟨7931406394372921520746457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5287604262915281013830971 7931406394372921520746457)
          ·
            refine ⟨5948554795779691140559843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7931406394372921520746457 5948554795779691140559843)
            ·
              refine ⟨8922832193669536710839765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5948554795779691140559843 8922832193669536710839765)
              ·
                refine ⟨209128879539129766660307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8922832193669536710839765 209128879539129766660307)
                ·
                  refine ⟨313693319308694649990461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209128879539129766660307 313693319308694649990461)
                  ·
                    refine ⟨117634994740760493746423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313693319308694649990461 117634994740760493746423)
                    ·
                      rfl

theorem cell22_343640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_343640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343640 prefixEnd_343640 := by exact prefixLift 343640
  have htrace : WordTrace (prefixWord ++ tailWord_343640) baseStart_343640 baseEnd_343640 := by
    simpa [prefixWord, tailWord_343640, baseEnd_343640] using wordTrace_append hprefix tailTrace_343640
  have hstable : (prefixWord ++ tailWord_343640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343640).length < 2 ^ (prefixWord ++ tailWord_343640).sum := by decide
  have hdescent : baseEnd_343640 < baseStart_343640 := by decide
  rcases family_descends (prefixWord ++ tailWord_343640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343653 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 5]
def baseStart_343653 : Nat := 118140960795 + 343653 * 2 ^ 59
def prefixEnd_343653 : Nat := 4983230072969 + 3 ^ 40 * 343653 * 2
def baseEnd_343653 : Nat := 39213148302144264390461

theorem tailTrace_343653 : CollatzResearch.WordTrace tailWord_343653 prefixEnd_343653 39213148302144264390461 := by
  unfold tailWord_343653
  simp only [CollatzResearch.WordTrace]
  refine ⟨12534054624011347104859613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8356036416007564736573075 12534054624011347104859613)
  ·
    refine ⟨4700270484004255164322355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12534054624011347104859613 4700270484004255164322355)
    ·
      refine ⟨7050405726006382746483533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700270484004255164322355 7050405726006382746483533)
      ·
        refine ⟨2643902147252393529931325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7050405726006382746483533 2643902147252393529931325)
        ·
          refine ⟨991463305219647573724247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2643902147252393529931325 991463305219647573724247)
          ·
            refine ⟨1487194957829471360586371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991463305219647573724247 1487194957829471360586371)
            ·
              refine ⟨2230792436744207040879557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487194957829471360586371 2230792436744207040879557)
              ·
                refine ⟨418273581889538820164917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2230792436744207040879557 418273581889538820164917)
                ·
                  refine ⟨39213148302144264390461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418273581889538820164917 39213148302144264390461)
                  ·
                    rfl

theorem cell22_343653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_343653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343653 prefixEnd_343653 := by exact prefixLift 343653
  have htrace : WordTrace (prefixWord ++ tailWord_343653) baseStart_343653 baseEnd_343653 := by
    simpa [prefixWord, tailWord_343653, baseEnd_343653] using wordTrace_append hprefix tailTrace_343653
  have hstable : (prefixWord ++ tailWord_343653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343653).length < 2 ^ (prefixWord ++ tailWord_343653).sum := by decide
  have hdescent : baseEnd_343653 < baseStart_343653 := by decide
  rcases family_descends (prefixWord ++ tailWord_343653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343657 : List Nat := [1, 2, 1, 1, 1, 4, 6, 2, 1, 3]
def baseStart_343657 : Nat := 118140960795 + 343657 * 2 ^ 59
def prefixEnd_343657 : Nat := 4983230072969 + 3 ^ 40 * 343657 * 2
def baseEnd_343657 : Nat := 117640814188178116071371

theorem tailTrace_343657 : CollatzResearch.WordTrace tailWord_343657 prefixEnd_343657 117640814188178116071371 := by
  unfold tailWord_343657
  simp only [CollatzResearch.WordTrace]
  refine ⟨12534200515996855788005225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8356133677331237192003483 12534200515996855788005225)
  ·
    refine ⟨9400650386997641841003919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12534200515996855788005225 9400650386997641841003919)
    ·
      refine ⟨14100975580496462761505879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9400650386997641841003919 14100975580496462761505879)
      ·
        refine ⟨21151463370744694142258819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14100975580496462761505879 21151463370744694142258819)
        ·
          refine ⟨31727195056117041213388229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21151463370744694142258819 31727195056117041213388229)
          ·
            refine ⟨5948849073021945227510293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31727195056117041213388229 5948849073021945227510293)
            ·
              refine ⟨278852300297903682539545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5948849073021945227510293 278852300297903682539545)
              ·
                refine ⟨209139225223427761904659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278852300297903682539545 209139225223427761904659)
                ·
                  refine ⟨313708837835141642856989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209139225223427761904659 313708837835141642856989)
                  ·
                    refine ⟨117640814188178116071371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313708837835141642856989 117640814188178116071371)
                    ·
                      rfl

theorem cell22_343657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 1, 3].length) (baseStart_343657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343657 prefixEnd_343657 := by exact prefixLift 343657
  have htrace : WordTrace (prefixWord ++ tailWord_343657) baseStart_343657 baseEnd_343657 := by
    simpa [prefixWord, tailWord_343657, baseEnd_343657] using wordTrace_append hprefix tailTrace_343657
  have hstable : (prefixWord ++ tailWord_343657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343657).length < 2 ^ (prefixWord ++ tailWord_343657).sum := by decide
  have hdescent : baseEnd_343657 < baseStart_343657 := by decide
  rcases family_descends (prefixWord ++ tailWord_343657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343670 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_343670 : Nat := 118140960795 + 343670 * 2 ^ 59
def prefixEnd_343670 : Nat := 4983230072969 + 3 ^ 40 * 343670 * 2
def baseEnd_343670 : Nat := 39215088117950138498777

theorem tailTrace_343670 : CollatzResearch.WordTrace tailWord_343670 prefixEnd_343670 39215088117950138498777 := by
  unfold tailWord_343670
  simp only [CollatzResearch.WordTrace]
  refine ⟨783417166559359938014279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8356449776633172672152309 783417166559359938014279)
  ·
    refine ⟨1175125749839039907021419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783417166559359938014279 1175125749839039907021419)
    ·
      refine ⟨1762688624758559860532129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175125749839039907021419 1762688624758559860532129)
      ·
        refine ⟨1322016468568919895399097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1762688624758559860532129 1322016468568919895399097)
        ·
          refine ⟨991512351426689921549323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322016468568919895399097 991512351426689921549323)
          ·
            refine ⟨1487268527140034882323985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991512351426689921549323 1487268527140034882323985)
            ·
              refine ⟨1115451395355026161742989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487268527140034882323985 1115451395355026161742989)
              ·
                refine ⟨418294273258134810653621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1115451395355026161742989 418294273258134810653621)
                ·
                  refine ⟨39215088117950138498777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418294273258134810653621 39215088117950138498777)
                  ·
                    rfl

theorem cell22_343670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_343670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343670 prefixEnd_343670 := by exact prefixLift 343670
  have htrace : WordTrace (prefixWord ++ tailWord_343670) baseStart_343670 baseEnd_343670 := by
    simpa [prefixWord, tailWord_343670, baseEnd_343670] using wordTrace_append hprefix tailTrace_343670
  have hstable : (prefixWord ++ tailWord_343670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343670).length < 2 ^ (prefixWord ++ tailWord_343670).sum := by decide
  have hdescent : baseEnd_343670 < baseStart_343670 := by decide
  rcases family_descends (prefixWord ++ tailWord_343670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343683 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 1, 4]
def baseStart_343683 : Nat := 118140960795 + 343683 * 2 ^ 59
def prefixEnd_343683 : Nat := 4983230072969 + 3 ^ 40 * 343683 * 2
def baseEnd_343683 : Nat := 117649714519522714921291

theorem tailTrace_343683 : CollatzResearch.WordTrace tailWord_343683 prefixEnd_343683 117649714519522714921291 := by
  unfold tailWord_343683
  simp only [CollatzResearch.WordTrace]
  refine ⟨12535148813902662228451703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8356765875935108152301135 12535148813902662228451703)
  ·
    refine ⟨18802723220853993342677555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12535148813902662228451703 18802723220853993342677555)
    ·
      refine ⟨28204084831280990014016333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18802723220853993342677555 28204084831280990014016333)
      ·
        refine ⟨10576531811730371255256125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28204084831280990014016333 10576531811730371255256125)
        ·
          refine ⟨3966199429398889220721047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10576531811730371255256125 3966199429398889220721047)
          ·
            refine ⟨5949299144098333831081571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966199429398889220721047 5949299144098333831081571)
            ·
              refine ⟨8923948716147500746622357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949299144098333831081571 8923948716147500746622357)
              ·
                refine ⟨418310096069414097497923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8923948716147500746622357 418310096069414097497923)
                ·
                  refine ⟨627465144104121146246885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418310096069414097497923 627465144104121146246885)
                  ·
                    refine ⟨117649714519522714921291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 627465144104121146246885 117649714519522714921291)
                    ·
                      rfl

theorem cell22_343683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 4].length) (baseStart_343683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343683 prefixEnd_343683 := by exact prefixLift 343683
  have htrace : WordTrace (prefixWord ++ tailWord_343683) baseStart_343683 baseEnd_343683 := by
    simpa [prefixWord, tailWord_343683, baseEnd_343683] using wordTrace_append hprefix tailTrace_343683
  have hstable : (prefixWord ++ tailWord_343683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343683).length < 2 ^ (prefixWord ++ tailWord_343683).sum := by decide
  have hdescent : baseEnd_343683 < baseStart_343683 := by decide
  rcases family_descends (prefixWord ++ tailWord_343683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343730 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_343730 : Nat := 118140960795 + 343730 * 2 ^ 59
def prefixEnd_343730 : Nat := 4983230072969 + 3 ^ 40 * 343730 * 2
def baseEnd_343730 : Nat := 117665803580030258996147

theorem tailTrace_343730 : CollatzResearch.WordTrace tailWord_343730 prefixEnd_343730 117665803580030258996147 := by
  unfold tailWord_343730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3134215761183097313853161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8357908696488259503608429 3134215761183097313853161)
  ·
    refine ⟨2350661820887322985389871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3134215761183097313853161 2350661820887322985389871)
    ·
      refine ⟨3525992731330984478084807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2350661820887322985389871 3525992731330984478084807)
      ·
        refine ⟨5288989096996476717127211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3525992731330984478084807 5288989096996476717127211)
        ·
          refine ⟨7933483645494715075690817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5288989096996476717127211 7933483645494715075690817)
          ·
            refine ⟨5950112734121036306768113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7933483645494715075690817 5950112734121036306768113)
            ·
              refine ⟨4462584550590777230076085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5950112734121036306768113 4462584550590777230076085)
              ·
                refine ⟨418367301617885365319633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4462584550590777230076085 418367301617885365319633)
                ·
                  refine ⟨313775476213414023989725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418367301617885365319633 313775476213414023989725)
                  ·
                    refine ⟨117665803580030258996147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313775476213414023989725 117665803580030258996147)
                    ·
                      rfl

theorem cell22_343730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_343730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343730 prefixEnd_343730 := by exact prefixLift 343730
  have htrace : WordTrace (prefixWord ++ tailWord_343730) baseStart_343730 baseEnd_343730 := by
    simpa [prefixWord, tailWord_343730, baseEnd_343730] using wordTrace_append hprefix tailTrace_343730
  have hstable : (prefixWord ++ tailWord_343730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343730).length < 2 ^ (prefixWord ++ tailWord_343730).sum := by decide
  have hdescent : baseEnd_343730 < baseStart_343730 := by decide
  rcases family_descends (prefixWord ++ tailWord_343730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343734 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_343734 : Nat := 118140960795 + 343734 * 2 ^ 59
def prefixEnd_343734 : Nat := 4983230072969 + 3 ^ 40 * 343734 * 2
def baseEnd_343734 : Nat := 117667172861775581896135

theorem tailTrace_343734 : CollatzResearch.WordTrace tailWord_343734 prefixEnd_343734 117667172861775581896135 := by
  unfold tailWord_343734
  simp only [CollatzResearch.WordTrace]
  refine ⟨783563058544868621159891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8358005957811931959038837 783563058544868621159891)
  ·
    refine ⟨1175344587817302931739837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783563058544868621159891 1175344587817302931739837)
    ·
      refine ⟨440754220431488599402439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1175344587817302931739837 440754220431488599402439)
      ·
        refine ⟨661131330647232899103659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440754220431488599402439 661131330647232899103659)
        ·
          refine ⟨991696995970849348655489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661131330647232899103659 991696995970849348655489)
          ·
            refine ⟨743772746978137011491617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991696995970849348655489 743772746978137011491617)
            ·
              refine ⟨557829560233602758618713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743772746978137011491617 557829560233602758618713)
              ·
                refine ⟨418372170175202068964035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557829560233602758618713 418372170175202068964035)
                ·
                  refine ⟨627558255262803103446053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418372170175202068964035 627558255262803103446053)
                  ·
                    refine ⟨117667172861775581896135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 627558255262803103446053 117667172861775581896135)
                    ·
                      rfl

theorem cell22_343734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_343734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343734 prefixEnd_343734 := by exact prefixLift 343734
  have htrace : WordTrace (prefixWord ++ tailWord_343734) baseStart_343734 baseEnd_343734 := by
    simpa [prefixWord, tailWord_343734, baseEnd_343734] using wordTrace_append hprefix tailTrace_343734
  have hstable : (prefixWord ++ tailWord_343734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343734).length < 2 ^ (prefixWord ++ tailWord_343734).sum := by decide
  have hdescent : baseEnd_343734 < baseStart_343734 := by decide
  rcases family_descends (prefixWord ++ tailWord_343734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343766 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_343766 : Nat := 118140960795 + 343766 * 2 ^ 59
def prefixEnd_343766 : Nat := 4983230072969 + 3 ^ 40 * 343766 * 2
def baseEnd_343766 : Nat := 39226042371912721698679

theorem tailTrace_343766 : CollatzResearch.WordTrace tailWord_343766 prefixEnd_343766 39226042371912721698679 := by
  unfold tailWord_343766
  simp only [CollatzResearch.WordTrace]
  refine ⟨783636004537622962732697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8358784048401311602482101 783636004537622962732697)
  ·
    refine ⟨587727003403217222049523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 783636004537622962732697 587727003403217222049523)
    ·
      refine ⟨881590505104825833074285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587727003403217222049523 881590505104825833074285)
      ·
        refine ⟨330596439414309687402857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 881590505104825833074285 330596439414309687402857)
        ·
          refine ⟨247947329560732265552143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330596439414309687402857 247947329560732265552143)
          ·
            refine ⟨371920994341098398328215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247947329560732265552143 371920994341098398328215)
            ·
              refine ⟨557881491511647597492323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371920994341098398328215 557881491511647597492323)
              ·
                refine ⟨836822237267471396238485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557881491511647597492323 836822237267471396238485)
                ·
                  refine ⟨39226042371912721698679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 836822237267471396238485 39226042371912721698679)
                  ·
                    rfl

theorem cell22_343766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_343766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343766 prefixEnd_343766 := by exact prefixLift 343766
  have htrace : WordTrace (prefixWord ++ tailWord_343766) baseStart_343766 baseEnd_343766 := by
    simpa [prefixWord, tailWord_343766, baseEnd_343766] using wordTrace_append hprefix tailTrace_343766
  have hstable : (prefixWord ++ tailWord_343766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343766).length < 2 ^ (prefixWord ++ tailWord_343766).sum := by decide
  have hdescent : baseEnd_343766 < baseStart_343766 := by decide
  rcases family_descends (prefixWord ++ tailWord_343766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343826 : List Nat := [3, 2, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_343826 : Nat := 118140960795 + 343826 * 2 ^ 59
def prefixEnd_343826 : Nat := 4983230072969 + 3 ^ 40 * 343826 * 2
def baseEnd_343826 : Nat := 117698666341918008595853

theorem tailTrace_343826 : CollatzResearch.WordTrace tailWord_343826 prefixEnd_343826 117698666341918008595853 := by
  unfold tailWord_343826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135091113096149412726833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8360242968256398433938221 3135091113096149412726833)
  ·
    refine ⟨2351318334822112059545125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3135091113096149412726833 2351318334822112059545125)
    ·
      refine ⟨440872187779146011164711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2351318334822112059545125 440872187779146011164711)
      ·
        refine ⟨661308281668719016747067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440872187779146011164711 661308281668719016747067)
        ·
          refine ⟨991962422503078525120601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661308281668719016747067 991962422503078525120601)
          ·
            refine ⟨743971816877308893840451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991962422503078525120601 743971816877308893840451)
            ·
              refine ⟨1115957725315963340760677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743971816877308893840451 1115957725315963340760677)
              ·
                refine ⟨209242073496743126392627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1115957725315963340760677 209242073496743126392627)
                ·
                  refine ⟨313863110245114689588941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209242073496743126392627 313863110245114689588941)
                  ·
                    refine ⟨117698666341918008595853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313863110245114689588941 117698666341918008595853)
                    ·
                      rfl

theorem cell22_343826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_343826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343826 prefixEnd_343826 := by exact prefixLift 343826
  have htrace : WordTrace (prefixWord ++ tailWord_343826) baseStart_343826 baseEnd_343826 := by
    simpa [prefixWord, tailWord_343826, baseEnd_343826] using wordTrace_append hprefix tailTrace_343826
  have hstable : (prefixWord ++ tailWord_343826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343826).length < 2 ^ (prefixWord ++ tailWord_343826).sum := by decide
  have hdescent : baseEnd_343826 < baseStart_343826 := by decide
  rcases family_descends (prefixWord ++ tailWord_343826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343869 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_343869 : Nat := 118140960795 + 343869 * 2 ^ 59
def prefixEnd_343869 : Nat := 4983230072969 + 3 ^ 40 * 343869 * 2
def baseEnd_343869 : Nat := 117713386120680229770721

theorem tailTrace_343869 : CollatzResearch.WordTrace tailWord_343869 prefixEnd_343869 117713386120680229770721 := by
  unfold tailWord_343869
  simp only [CollatzResearch.WordTrace]
  refine ⟨12541932791228815994722661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8361288527485877329815107 12541932791228815994722661)
  ·
    refine ⟨2351612398355402999010499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12541932791228815994722661 2351612398355402999010499)
    ·
      refine ⟨3527418597533104498515749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2351612398355402999010499 3527418597533104498515749)
      ·
        refine ⟨661390987037457093471703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3527418597533104498515749 661390987037457093471703)
        ·
          refine ⟨992086480556185640207555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661390987037457093471703 992086480556185640207555)
          ·
            refine ⟨1488129720834278460311333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992086480556185640207555 1488129720834278460311333)
            ·
              refine ⟨279024322656427211308375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1488129720834278460311333 279024322656427211308375)
              ·
                refine ⟨418536483984640816962563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279024322656427211308375 418536483984640816962563)
                ·
                  refine ⟨627804725976961225443845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418536483984640816962563 627804725976961225443845)
                  ·
                    refine ⟨117713386120680229770721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 627804725976961225443845 117713386120680229770721)
                    ·
                      rfl

theorem cell22_343869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_343869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343869 prefixEnd_343869 := by exact prefixLift 343869
  have htrace : WordTrace (prefixWord ++ tailWord_343869) baseStart_343869 baseEnd_343869 := by
    simpa [prefixWord, tailWord_343869, baseEnd_343869] using wordTrace_append hprefix tailTrace_343869
  have hstable : (prefixWord ++ tailWord_343869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343869).length < 2 ^ (prefixWord ++ tailWord_343869).sum := by decide
  have hdescent : baseEnd_343869 < baseStart_343869 := by decide
  rcases family_descends (prefixWord ++ tailWord_343869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343940 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 7]
def baseStart_343940 : Nat := 118140960795 + 343940 * 2 ^ 59
def prefixEnd_343940 : Nat := 4983230072969 + 3 ^ 40 * 343940 * 2
def baseEnd_343940 : Nat := 39245896957219903748501

theorem tailTrace_343940 : CollatzResearch.WordTrace tailWord_343940 prefixEnd_343940 39245896957219903748501 := by
  unfold tailWord_343940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6272261186985797560278637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8363014915981063413704849 6272261186985797560278637)
  ·
    refine ⟨2352097945119674085104489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6272261186985797560278637 2352097945119674085104489)
    ·
      refine ⟨1764073458839755563828367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2352097945119674085104489 1764073458839755563828367)
      ·
        refine ⟨2646110188259633345742551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764073458839755563828367 2646110188259633345742551)
        ·
          refine ⟨3969165282389450018613827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646110188259633345742551 3969165282389450018613827)
          ·
            refine ⟨5953747923584175027920741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969165282389450018613827 5953747923584175027920741)
            ·
              refine ⟨1116327735672032817735139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5953747923584175027920741 1116327735672032817735139)
              ·
                refine ⟨1674491603508049226602709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116327735672032817735139 1674491603508049226602709)
                ·
                  refine ⟨39245896957219903748501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1674491603508049226602709 39245896957219903748501)
                  ·
                    rfl

theorem cell22_343940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_343940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343940 prefixEnd_343940 := by exact prefixLift 343940
  have htrace : WordTrace (prefixWord ++ tailWord_343940) baseStart_343940 baseEnd_343940 := by
    simpa [prefixWord, tailWord_343940, baseEnd_343940] using wordTrace_append hprefix tailTrace_343940
  have hstable : (prefixWord ++ tailWord_343940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343940).length < 2 ^ (prefixWord ++ tailWord_343940).sum := by decide
  have hdescent : baseEnd_343940 < baseStart_343940 := by decide
  rcases family_descends (prefixWord ++ tailWord_343940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343950 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_343950 : Nat := 118140960795 + 343950 * 2 ^ 59
def prefixEnd_343950 : Nat := 4983230072969 + 3 ^ 40 * 343950 * 2
def baseEnd_343950 : Nat := 117741114076023018495473

theorem tailTrace_343950 : CollatzResearch.WordTrace tailWord_343950 prefixEnd_343950 117741114076023018495473 := by
  unfold tailWord_343950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568110887991920853552663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8363258069290244552280869 1568110887991920853552663)
  ·
    refine ⟨2352166331987881280328995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1568110887991920853552663 2352166331987881280328995)
    ·
      refine ⟨3528249497981821920493493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2352166331987881280328995 3528249497981821920493493)
      ·
        refine ⟨330773390435795805046265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3528249497981821920493493 330773390435795805046265)
        ·
          refine ⟨248080042826846853784699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330773390435795805046265 248080042826846853784699)
          ·
            refine ⟨372120064240270280677049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248080042826846853784699 372120064240270280677049)
            ·
              refine ⟨279090048180202710507787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372120064240270280677049 279090048180202710507787)
              ·
                refine ⟨418635072270304065761681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279090048180202710507787 418635072270304065761681)
                ·
                  refine ⟨313976304202728049321261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418635072270304065761681 313976304202728049321261)
                  ·
                    refine ⟨117741114076023018495473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313976304202728049321261 117741114076023018495473)
                    ·
                      rfl

theorem cell22_343950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_343950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_343950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_343950 prefixEnd_343950 := by exact prefixLift 343950
  have htrace : WordTrace (prefixWord ++ tailWord_343950) baseStart_343950 baseEnd_343950 := by
    simpa [prefixWord, tailWord_343950, baseEnd_343950] using wordTrace_append hprefix tailTrace_343950
  have hstable : (prefixWord ++ tailWord_343950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343950).length < 2 ^ (prefixWord ++ tailWord_343950).sum := by decide
  have hdescent : baseEnd_343950 < baseStart_343950 := by decide
  rcases family_descends (prefixWord ++ tailWord_343950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344000 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_344000 : Nat := 118140960795 + 344000 * 2 ^ 59
def prefixEnd_344000 : Nat := 4983230072969 + 3 ^ 40 * 344000 * 2
def baseEnd_344000 : Nat := 117758230097839554745319

theorem tailTrace_344000 : CollatzResearch.WordTrace tailWord_344000 prefixEnd_344000 117758230097839554745319 := by
  unfold tailWord_344000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6273355376877112683870727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8364473835836150245160969 6273355376877112683870727)
  ·
    refine ⟨9410033065315669025806091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6273355376877112683870727 9410033065315669025806091)
    ·
      refine ⟨14115049597973503538709137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9410033065315669025806091 14115049597973503538709137)
      ·
        refine ⟨10586287198480127654031853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14115049597973503538709137 10586287198480127654031853)
        ·
          refine ⟨3969857699430047870261945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10586287198480127654031853 3969857699430047870261945)
          ·
            refine ⟨2977393274572535902696459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3969857699430047870261945 2977393274572535902696459)
            ·
              refine ⟨4466089911858803854044689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2977393274572535902696459 4466089911858803854044689)
              ·
                refine ⟨3349567433894102890533517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4466089911858803854044689 3349567433894102890533517)
                ·
                  refine ⟨1256087787710288583950069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3349567433894102890533517 1256087787710288583950069)
                  ·
                    refine ⟨117758230097839554745319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1256087787710288583950069 117758230097839554745319)
                    ·
                      rfl

theorem cell22_344000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_344000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344000 prefixEnd_344000 := by exact prefixLift 344000
  have htrace : WordTrace (prefixWord ++ tailWord_344000) baseStart_344000 baseEnd_344000 := by
    simpa [prefixWord, tailWord_344000, baseEnd_344000] using wordTrace_append hprefix tailTrace_344000
  have hstable : (prefixWord ++ tailWord_344000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344000).length < 2 ^ (prefixWord ++ tailWord_344000).sum := by decide
  have hdescent : baseEnd_344000 < baseStart_344000 := by decide
  rcases family_descends (prefixWord ++ tailWord_344000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344015 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 1, 6]
def baseStart_344015 : Nat := 118140960795 + 344015 * 2 ^ 59
def prefixEnd_344015 : Nat := 4983230072969 + 3 ^ 40 * 344015 * 2
def baseEnd_344015 : Nat := 117763364904384515620273

theorem tailTrace_344015 : CollatzResearch.WordTrace tailWord_344015 prefixEnd_344015 117763364904384515620273 := by
  unfold tailWord_344015
  simp only [CollatzResearch.WordTrace]
  refine ⟨12547257848699882929537499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8364838565799921953024999 12547257848699882929537499)
  ·
    refine ⟨18820886773049824394306249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12547257848699882929537499 18820886773049824394306249)
    ·
      refine ⟨14115665079787368295729687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18820886773049824394306249 14115665079787368295729687)
      ·
        refine ⟨21173497619681052443594531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14115665079787368295729687 21173497619681052443594531)
        ·
          refine ⟨31760246429521578665391797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21173497619681052443594531 31760246429521578665391797)
          ·
            refine ⟨2977523102767647999880481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31760246429521578665391797 2977523102767647999880481)
            ·
              refine ⟨2233142327075735999910361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2977523102767647999880481 2233142327075735999910361)
              ·
                refine ⟨1674856745306801999932771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233142327075735999910361 1674856745306801999932771)
                ·
                  refine ⟨2512285117960202999899157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674856745306801999932771 2512285117960202999899157)
                  ·
                    refine ⟨117763364904384515620273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2512285117960202999899157 117763364904384515620273)
                    ·
                      rfl

theorem cell22_344015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_344015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344015 prefixEnd_344015 := by exact prefixLift 344015
  have htrace : WordTrace (prefixWord ++ tailWord_344015) baseStart_344015 baseEnd_344015 := by
    simpa [prefixWord, tailWord_344015, baseEnd_344015] using wordTrace_append hprefix tailTrace_344015
  have hstable : (prefixWord ++ tailWord_344015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344015).length < 2 ^ (prefixWord ++ tailWord_344015).sum := by decide
  have hdescent : baseEnd_344015 < baseStart_344015 := by decide
  rcases family_descends (prefixWord ++ tailWord_344015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344068 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_344068 : Nat := 118140960795 + 344068 * 2 ^ 59
def prefixEnd_344068 : Nat := 4983230072969 + 3 ^ 40 * 344068 * 2
def baseEnd_344068 : Nat := 117781507887510044045111

theorem tailTrace_344068 : CollatzResearch.WordTrace tailWord_344068 prefixEnd_344068 117781507887510044045111 := by
  unfold tailWord_344068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274595458753936490608429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8366127278338581987477905 6274595458753936490608429)
  ·
    refine ⟨2352973297032726183978161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6274595458753936490608429 2352973297032726183978161)
    ·
      refine ⟨1764729972774544637983621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2352973297032726183978161 1764729972774544637983621)
      ·
        refine ⟨330886869895227119621929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1764729972774544637983621 330886869895227119621929)
        ·
          refine ⟨248165152421420339716447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330886869895227119621929 248165152421420339716447)
          ·
            refine ⟨372247728632130509574671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248165152421420339716447 372247728632130509574671)
            ·
              refine ⟨558371592948195764362007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372247728632130509574671 558371592948195764362007)
              ·
                refine ⟨837557389422293646543011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558371592948195764362007 837557389422293646543011)
                ·
                  refine ⟨1256336084133440469814517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837557389422293646543011 1256336084133440469814517)
                  ·
                    refine ⟨117781507887510044045111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1256336084133440469814517 117781507887510044045111)
                    ·
                      rfl

theorem cell22_344068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_344068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344068 prefixEnd_344068 := by exact prefixLift 344068
  have htrace : WordTrace (prefixWord ++ tailWord_344068) baseStart_344068 baseEnd_344068 := by
    simpa [prefixWord, tailWord_344068, baseEnd_344068] using wordTrace_append hprefix tailTrace_344068
  have hstable : (prefixWord ++ tailWord_344068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344068).length < 2 ^ (prefixWord ++ tailWord_344068).sum := by decide
  have hdescent : baseEnd_344068 < baseStart_344068 := by decide
  rcases family_descends (prefixWord ++ tailWord_344068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344092 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 7]
def baseStart_344092 : Nat := 118140960795 + 344092 * 2 ^ 59
def prefixEnd_344092 : Nat := 4983230072969 + 3 ^ 40 * 344092 * 2
def baseEnd_344092 : Nat := 39263241192660660481679

theorem tailTrace_344092 : CollatzResearch.WordTrace tailWord_344092 prefixEnd_344092 39263241192660660481679 := by
  unfold tailWord_344092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275033134710462540045265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8366710846280616720060353 6275033134710462540045265)
  ·
    refine ⟨4706274851032846905033949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6275033134710462540045265 4706274851032846905033949)
    ·
      refine ⟨1764853069137317589387731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4706274851032846905033949 1764853069137317589387731)
      ·
        refine ⟨2647279603705976384081597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764853069137317589387731 2647279603705976384081597)
        ·
          refine ⟨992729851389741144030599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2647279603705976384081597 992729851389741144030599)
          ·
            refine ⟨1489094777084611716045899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992729851389741144030599 1489094777084611716045899)
            ·
              refine ⟨2233642165626917574068849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489094777084611716045899 2233642165626917574068849)
              ·
                refine ⟨1675231624220188180551637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233642165626917574068849 1675231624220188180551637)
                ·
                  refine ⟨39263241192660660481679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1675231624220188180551637 39263241192660660481679)
                  ·
                    rfl

theorem cell22_344092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_344092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344092 prefixEnd_344092 := by exact prefixLift 344092
  have htrace : WordTrace (prefixWord ++ tailWord_344092) baseStart_344092 baseEnd_344092 := by
    simpa [prefixWord, tailWord_344092, baseEnd_344092] using wordTrace_append hprefix tailTrace_344092
  have hstable : (prefixWord ++ tailWord_344092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344092).length < 2 ^ (prefixWord ++ tailWord_344092).sum := by decide
  have hdescent : baseEnd_344092 < baseStart_344092 := by decide
  rcases family_descends (prefixWord ++ tailWord_344092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_344105 : Nat := 118140960795 + 344105 * 2 ^ 59
def prefixEnd_344105 : Nat := 4983230072969 + 3 ^ 40 * 344105 * 2
def baseEnd_344105 : Nat := 117794173743654280869997

theorem tailTrace_344105 : CollatzResearch.WordTrace tailWord_344105 prefixEnd_344105 117794173743654280869997 := by
  unfold tailWord_344105
  simp only [CollatzResearch.WordTrace]
  refine ⟨12550540418373828300313769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8367026945582552200209179 12550540418373828300313769)
  ·
    refine ⟨9412905313780371225235327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12550540418373828300313769 9412905313780371225235327)
    ·
      refine ⟨14119357970670556837852991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9412905313780371225235327 14119357970670556837852991)
      ·
        refine ⟨21179036956005835256779487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14119357970670556837852991 21179036956005835256779487)
        ·
          refine ⟨31768555434008752885169231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21179036956005835256779487 31768555434008752885169231)
          ·
            refine ⟨47652833151013129327753847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31768555434008752885169231 47652833151013129327753847)
            ·
              refine ⟨71479249726519693991630771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47652833151013129327753847 71479249726519693991630771)
              ·
                refine ⟨107218874589779540987446157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71479249726519693991630771 107218874589779540987446157)
                ·
                  refine ⟨40207077971167327870292309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107218874589779540987446157 40207077971167327870292309)
                  ·
                    refine ⟨117794173743654280869997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 40207077971167327870292309 117794173743654280869997)
                    ·
                      rfl

theorem cell22_344105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_344105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344105 prefixEnd_344105 := by exact prefixLift 344105
  have htrace : WordTrace (prefixWord ++ tailWord_344105) baseStart_344105 baseEnd_344105 := by
    simpa [prefixWord, tailWord_344105, baseEnd_344105] using wordTrace_append hprefix tailTrace_344105
  have hstable : (prefixWord ++ tailWord_344105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344105).length < 2 ^ (prefixWord ++ tailWord_344105).sum := by decide
  have hdescent : baseEnd_344105 < baseStart_344105 := by decide
  rcases family_descends (prefixWord ++ tailWord_344105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344113 : List Nat := [1, 2, 2, 3, 1, 4, 3, 2, 1, 3]
def baseStart_344113 : Nat := 118140960795 + 344113 * 2 ^ 59
def prefixEnd_344113 : Nat := 4983230072969 + 3 ^ 40 * 344113 * 2
def baseEnd_344113 : Nat := 117796912307144926669973

theorem tailTrace_344113 : CollatzResearch.WordTrace tailWord_344113 prefixEnd_344113 117796912307144926669973 := by
  unfold tailWord_344113
  simp only [CollatzResearch.WordTrace]
  refine ⟨12550832202344845666604993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8367221468229897111069995 12550832202344845666604993)
  ·
    refine ⟨9413124151758634249953745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12550832202344845666604993 9413124151758634249953745)
    ·
      refine ⟨7059843113818975687465309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9413124151758634249953745 7059843113818975687465309)
      ·
        refine ⟨2647441167682115882799491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7059843113818975687465309 2647441167682115882799491)
        ·
          refine ⟨3971161751523173824199237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647441167682115882799491 3971161751523173824199237)
          ·
            refine ⟨744592828410595092037357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3971161751523173824199237 744592828410595092037357)
            ·
              refine ⟨279222310653973159514009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 744592828410595092037357 279222310653973159514009)
              ·
                refine ⟨209416732990479869635507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279222310653973159514009 209416732990479869635507)
                ·
                  refine ⟨314125099485719804453261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209416732990479869635507 314125099485719804453261)
                  ·
                    refine ⟨117796912307144926669973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 314125099485719804453261 117796912307144926669973)
                    ·
                      rfl

theorem cell22_344113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_344113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344113 prefixEnd_344113 := by exact prefixLift 344113
  have htrace : WordTrace (prefixWord ++ tailWord_344113) baseStart_344113 baseEnd_344113 := by
    simpa [prefixWord, tailWord_344113, baseEnd_344113] using wordTrace_append hprefix tailTrace_344113
  have hstable : (prefixWord ++ tailWord_344113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344113).length < 2 ^ (prefixWord ++ tailWord_344113).sum := by decide
  have hdescent : baseEnd_344113 < baseStart_344113 := by decide
  rcases family_descends (prefixWord ++ tailWord_344113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344122 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_344122 : Nat := 118140960795 + 344122 * 2 ^ 59
def prefixEnd_344122 : Nat := 4983230072969 + 3 ^ 40 * 344122 * 2
def baseEnd_344122 : Nat := 117799993191071903194945

theorem tailTrace_344122 : CollatzResearch.WordTrace tailWord_344122 prefixEnd_344122 117799993191071903194945 := by
  unfold tailWord_344122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137790114828060050920655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8367440306208160135788413 3137790114828060050920655)
  ·
    refine ⟨4706685172242090076380983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3137790114828060050920655 4706685172242090076380983)
    ·
      refine ⟨7060027758363135114571475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4706685172242090076380983 7060027758363135114571475)
      ·
        refine ⟨10590041637544702671857213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7060027758363135114571475 10590041637544702671857213)
        ·
          refine ⟨3971265614079263501946455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10590041637544702671857213 3971265614079263501946455)
          ·
            refine ⟨5956898421118895252919683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971265614079263501946455 5956898421118895252919683)
            ·
              refine ⟨8935347631678342879379525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5956898421118895252919683 8935347631678342879379525)
              ·
                refine ⟨1675377680939689289883661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8935347631678342879379525 1675377680939689289883661)
                ·
                  refine ⟨628266630352383483706373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1675377680939689289883661 628266630352383483706373)
                  ·
                    refine ⟨117799993191071903194945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628266630352383483706373 117799993191071903194945)
                    ·
                      rfl

theorem cell22_344122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_344122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344122 prefixEnd_344122 := by exact prefixLift 344122
  have htrace : WordTrace (prefixWord ++ tailWord_344122) baseStart_344122 baseEnd_344122 := by
    simpa [prefixWord, tailWord_344122, baseEnd_344122] using wordTrace_append hprefix tailTrace_344122
  have hstable : (prefixWord ++ tailWord_344122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344122).length < 2 ^ (prefixWord ++ tailWord_344122).sum := by decide
  have hdescent : baseEnd_344122 < baseStart_344122 := by decide
  rcases family_descends (prefixWord ++ tailWord_344122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344126 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_344126 : Nat := 118140960795 + 344126 * 2 ^ 59
def prefixEnd_344126 : Nat := 4983230072969 + 3 ^ 40 * 344126 * 2
def baseEnd_344126 : Nat := 39267120824272408698311

theorem tailTrace_344126 : CollatzResearch.WordTrace tailWord_344126 prefixEnd_344126 39267120824272408698311 := by
  unfold tailWord_344126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568913293912218610853529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8367537567531832591218821 1568913293912218610853529)
  ·
    refine ⟨1176684970434163958140147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1568913293912218610853529 1176684970434163958140147)
    ·
      refine ⟨1765027455651245937210221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1176684970434163958140147 1765027455651245937210221)
      ·
        refine ⟨661885295869217226453833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1765027455651245937210221 661885295869217226453833)
        ·
          refine ⟨496413971901912919840375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661885295869217226453833 496413971901912919840375)
          ·
            refine ⟨744620957852869379760563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496413971901912919840375 744620957852869379760563)
            ·
              refine ⟨1116931436779304069640845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744620957852869379760563 1116931436779304069640845)
              ·
                refine ⟨418849288792239026115317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1116931436779304069640845 418849288792239026115317)
                ·
                  refine ⟨39267120824272408698311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418849288792239026115317 39267120824272408698311)
                  ·
                    rfl

theorem cell22_344126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_344126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344126 prefixEnd_344126 := by exact prefixLift 344126
  have htrace : WordTrace (prefixWord ++ tailWord_344126) baseStart_344126 baseEnd_344126 := by
    simpa [prefixWord, tailWord_344126, baseEnd_344126] using wordTrace_append hprefix tailTrace_344126
  have hstable : (prefixWord ++ tailWord_344126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344126).length < 2 ^ (prefixWord ++ tailWord_344126).sum := by decide
  have hdescent : baseEnd_344126 < baseStart_344126 := by decide
  rcases family_descends (prefixWord ++ tailWord_344126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344152 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_344152 : Nat := 118140960795 + 344152 * 2 ^ 59
def prefixEnd_344152 : Nat := 4983230072969 + 3 ^ 40 * 344152 * 2
def baseEnd_344152 : Nat := 117810262804161824944853

theorem tailTrace_344152 : CollatzResearch.WordTrace tailWord_344152 prefixEnd_344152 117810262804161824944853 := by
  unfold tailWord_344152
  simp only [CollatzResearch.WordTrace]
  refine ⟨6276127324601777663637355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8368169766135703551516473 6276127324601777663637355)
  ·
    refine ⟨9414190986902666495456033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6276127324601777663637355 9414190986902666495456033)
    ·
      refine ⟨7060643240176999871592025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9414190986902666495456033 7060643240176999871592025)
      ·
        refine ⟨5295482430132749903694019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7060643240176999871592025 5295482430132749903694019)
        ·
          refine ⟨7943223645199124855541029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295482430132749903694019 7943223645199124855541029)
          ·
            refine ⟨1489354433474835910413943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7943223645199124855541029 1489354433474835910413943)
            ·
              refine ⟨2234031650212253865620915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489354433474835910413943 2234031650212253865620915)
              ·
                refine ⟨3351047475318380798431373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234031650212253865620915 3351047475318380798431373)
                ·
                  refine ⟨1256642803244392799411765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3351047475318380798431373 1256642803244392799411765)
                  ·
                    refine ⟨117810262804161824944853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1256642803244392799411765 117810262804161824944853)
                    ·
                      rfl

theorem cell22_344152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_344152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344152 prefixEnd_344152 := by exact prefixLift 344152
  have htrace : WordTrace (prefixWord ++ tailWord_344152) baseStart_344152 baseEnd_344152 := by
    simpa [prefixWord, tailWord_344152, baseEnd_344152] using wordTrace_append hprefix tailTrace_344152
  have hstable : (prefixWord ++ tailWord_344152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344152).length < 2 ^ (prefixWord ++ tailWord_344152).sum := by decide
  have hdescent : baseEnd_344152 < baseStart_344152 := by decide
  rcases family_descends (prefixWord ++ tailWord_344152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344154 : List Nat := [3, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_344154 : Nat := 118140960795 + 344154 * 2 ^ 59
def prefixEnd_344154 : Nat := 4983230072969 + 3 ^ 40 * 344154 * 2
def baseEnd_344154 : Nat := 39270315815011495464949

theorem tailTrace_344154 : CollatzResearch.WordTrace tailWord_344154 prefixEnd_344154 39270315815011495464949 := by
  unfold tailWord_344154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138081898799077417211879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8368218396797539779231677 3138081898799077417211879)
  ·
    refine ⟨4707122848198616125817819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3138081898799077417211879 4707122848198616125817819)
    ·
      refine ⟨7060684272297924188726729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4707122848198616125817819 7060684272297924188726729)
      ·
        refine ⟨5295513204223443141545047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7060684272297924188726729 5295513204223443141545047)
        ·
          refine ⟨7943269806335164712317571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295513204223443141545047 7943269806335164712317571)
          ·
            refine ⟨11914904709502747068476357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943269806335164712317571 11914904709502747068476357)
            ·
              refine ⟨2234044633031765075339317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11914904709502747068476357 2234044633031765075339317)
              ·
                refine ⟨209441684346727975813061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2234044633031765075339317 209441684346727975813061)
                ·
                  refine ⟨39270315815011495464949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209441684346727975813061 39270315815011495464949)
                  ·
                    rfl

theorem cell22_344154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_344154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344154 prefixEnd_344154 := by exact prefixLift 344154
  have htrace : WordTrace (prefixWord ++ tailWord_344154) baseStart_344154 baseEnd_344154 := by
    simpa [prefixWord, tailWord_344154, baseEnd_344154] using wordTrace_append hprefix tailTrace_344154
  have hstable : (prefixWord ++ tailWord_344154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344154).length < 2 ^ (prefixWord ++ tailWord_344154).sum := by decide
  have hdescent : baseEnd_344154 < baseStart_344154 := by decide
  rcases family_descends (prefixWord ++ tailWord_344154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344351 : List Nat := [1, 1, 2, 4, 3, 3, 1, 7]
def baseStart_344351 : Nat := 118140960795 + 344351 * 2 ^ 59
def prefixEnd_344351 : Nat := 4983230072969 + 3 ^ 40 * 344351 * 2
def baseEnd_344351 : Nat := 13097598285665737691027

theorem tailTrace_344351 : CollatzResearch.WordTrace tailWord_344351 prefixEnd_344351 13097598285665737691027 := by
  unfold tailWord_344351
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559512775482612313768907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8373008516988408209179271 12559512775482612313768907)
  ·
    refine ⟨18839269163223918470653361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12559512775482612313768907 18839269163223918470653361)
    ·
      refine ⟨14129451872417938852990021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18839269163223918470653361 14129451872417938852990021)
      ·
        refine ⟨2649272226078363534935629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14129451872417938852990021 2649272226078363534935629)
        ·
          refine ⟨993477084779386325600861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2649272226078363534935629 993477084779386325600861)
          ·
            refine ⟨372553906792269872100323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 993477084779386325600861 372553906792269872100323)
            ·
              refine ⟨558830860188404808150485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372553906792269872100323 558830860188404808150485)
              ·
                refine ⟨13097598285665737691027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 558830860188404808150485 13097598285665737691027)
                ·
                  rfl

theorem cell22_344351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 7].length) (baseStart_344351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344351 prefixEnd_344351 := by exact prefixLift 344351
  have htrace : WordTrace (prefixWord ++ tailWord_344351) baseStart_344351 baseEnd_344351 := by
    simpa [prefixWord, tailWord_344351, baseEnd_344351] using wordTrace_append hprefix tailTrace_344351
  have hstable : (prefixWord ++ tailWord_344351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344351).length < 2 ^ (prefixWord ++ tailWord_344351).sum := by decide
  have hdescent : baseEnd_344351 < baseStart_344351 := by decide
  rcases family_descends (prefixWord ++ tailWord_344351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344370 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_344370 : Nat := 118140960795 + 344370 * 2 ^ 59
def prefixEnd_344370 : Nat := 4983230072969 + 3 ^ 40 * 344370 * 2
def baseEnd_344370 : Nat := 117884888659281922994185

theorem tailTrace_344370 : CollatzResearch.WordTrace tailWord_344370 prefixEnd_344370 117884888659281922994185 := by
  unfold tailWord_344370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140051440603444639677641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8373470508275852372473709 3140051440603444639677641)
  ·
    refine ⟨2355038580452583479758231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3140051440603444639677641 2355038580452583479758231)
    ·
      refine ⟨3532557870678875219637347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2355038580452583479758231 3532557870678875219637347)
      ·
        refine ⟨5298836806018312829456021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3532557870678875219637347 5298836806018312829456021)
        ·
          refine ⟨248382975282108413880751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5298836806018312829456021 248382975282108413880751)
          ·
            refine ⟨372574462923162620821127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248382975282108413880751 372574462923162620821127)
            ·
              refine ⟨558861694384743931231691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372574462923162620821127 558861694384743931231691)
              ·
                refine ⟨838292541577115896847537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558861694384743931231691 838292541577115896847537)
                ·
                  refine ⟨628719406182836922635653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 838292541577115896847537 628719406182836922635653)
                  ·
                    refine ⟨117884888659281922994185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628719406182836922635653 117884888659281922994185)
                    ·
                      rfl

theorem cell22_344370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_344370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344370 prefixEnd_344370 := by exact prefixLift 344370
  have htrace : WordTrace (prefixWord ++ tailWord_344370) baseStart_344370 baseEnd_344370 := by
    simpa [prefixWord, tailWord_344370, baseEnd_344370] using wordTrace_append hprefix tailTrace_344370
  have hstable : (prefixWord ++ tailWord_344370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344370).length < 2 ^ (prefixWord ++ tailWord_344370).sum := by decide
  have hdescent : baseEnd_344370 < baseStart_344370 := by decide
  rcases family_descends (prefixWord ++ tailWord_344370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344473 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 2, 3]
def baseStart_344473 : Nat := 118140960795 + 344473 * 2 ^ 59
def prefixEnd_344473 : Nat := 4983230072969 + 3 ^ 40 * 344473 * 2
def baseEnd_344473 : Nat := 117920147664223987668869

theorem tailTrace_344473 : CollatzResearch.WordTrace tailWord_344473 prefixEnd_344473 117920147664223987668869 := by
  unfold tailWord_344473
  simp only [CollatzResearch.WordTrace]
  refine ⟨12563962481040627149710073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8375974987360418099806715 12563962481040627149710073)
  ·
    refine ⟨9422971860780470362282555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12563962481040627149710073 9422971860780470362282555)
    ·
      refine ⟨14134457791170705543423833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9422971860780470362282555 14134457791170705543423833)
      ·
        refine ⟨10600843343378029157567875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14134457791170705543423833 10600843343378029157567875)
        ·
          refine ⟨15901265015067043736351813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10600843343378029157567875 15901265015067043736351813)
          ·
            refine ⟨2981487190325070700565965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15901265015067043736351813 2981487190325070700565965)
            ·
              refine ⟨1118057696371901512712237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2981487190325070700565965 1118057696371901512712237)
              ·
                refine ⟨419271636139463067267089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1118057696371901512712237 419271636139463067267089)
                ·
                  refine ⟨314453727104597300450317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419271636139463067267089 314453727104597300450317)
                  ·
                    refine ⟨117920147664223987668869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 314453727104597300450317 117920147664223987668869)
                    ·
                      rfl

theorem cell22_344473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_344473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344473 prefixEnd_344473 := by exact prefixLift 344473
  have htrace : WordTrace (prefixWord ++ tailWord_344473) baseStart_344473 baseEnd_344473 := by
    simpa [prefixWord, tailWord_344473, baseEnd_344473] using wordTrace_append hprefix tailTrace_344473
  have hstable : (prefixWord ++ tailWord_344473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344473).length < 2 ^ (prefixWord ++ tailWord_344473).sum := by decide
  have hdescent : baseEnd_344473 < baseStart_344473 := by decide
  rcases family_descends (prefixWord ++ tailWord_344473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344477 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_344477 : Nat := 118140960795 + 344477 * 2 ^ 59
def prefixEnd_344477 : Nat := 4983230072969 + 3 ^ 40 * 344477 * 2
def baseEnd_344477 : Nat := 117921516945969310568857

theorem tailTrace_344477 : CollatzResearch.WordTrace tailWord_344477 prefixEnd_344477 117921516945969310568857 := by
  unfold tailWord_344477
  simp only [CollatzResearch.WordTrace]
  refine ⟨12564108373026135832855685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8376072248684090555237123 12564108373026135832855685)
  ·
    refine ⟨2355770319942400468660441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12564108373026135832855685 2355770319942400468660441)
    ·
      refine ⟨1766827739956800351495331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2355770319942400468660441 1766827739956800351495331)
      ·
        refine ⟨2650241609935200527242997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766827739956800351495331 2650241609935200527242997)
        ·
          refine ⟨248460150931425049429031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2650241609935200527242997 248460150931425049429031)
          ·
            refine ⟨372690226397137574143547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248460150931425049429031 372690226397137574143547)
            ·
              refine ⟨559035339595706361215321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372690226397137574143547 559035339595706361215321)
              ·
                refine ⟨419276504696779770911491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559035339595706361215321 419276504696779770911491)
                ·
                  refine ⟨628914757045169656367237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419276504696779770911491 628914757045169656367237)
                  ·
                    refine ⟨117921516945969310568857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628914757045169656367237 117921516945969310568857)
                    ·
                      rfl

theorem cell22_344477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_344477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344477 prefixEnd_344477 := by exact prefixLift 344477
  have htrace : WordTrace (prefixWord ++ tailWord_344477) baseStart_344477 baseEnd_344477 := by
    simpa [prefixWord, tailWord_344477, baseEnd_344477] using wordTrace_append hprefix tailTrace_344477
  have hstable : (prefixWord ++ tailWord_344477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344477).length < 2 ^ (prefixWord ++ tailWord_344477).sum := by decide
  have hdescent : baseEnd_344477 < baseStart_344477 := by decide
  rcases family_descends (prefixWord ++ tailWord_344477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344552 : List Nat := [2, 1, 4, 1, 1, 4, 2, 3, 1, 3]
def baseStart_344552 : Nat := 118140960795 + 344552 * 2 ^ 59
def prefixEnd_344552 : Nat := 4983230072969 + 3 ^ 40 * 344552 * 2
def baseEnd_344552 : Nat := 117947190978694114943627

theorem tailTrace_344552 : CollatzResearch.WordTrace tailWord_344552 prefixEnd_344552 117947190978694114943627 := by
  unfold tailWord_344552
  simp only [CollatzResearch.WordTrace]
  refine ⟨6283421923877211820917955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8377895898502949094557273 6283421923877211820917955)
  ·
    refine ⟨9425132885815817731376933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6283421923877211820917955 9425132885815817731376933)
    ·
      refine ⟨1767212416090465824633175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9425132885815817731376933 1767212416090465824633175)
      ·
        refine ⟨2650818624135698736949763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767212416090465824633175 2650818624135698736949763)
        ·
          refine ⟨3976227936203548105424645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650818624135698736949763 3976227936203548105424645)
          ·
            refine ⟨745542738038165269767121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3976227936203548105424645 745542738038165269767121)
            ·
              refine ⟨559157053528623952325341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745542738038165269767121 559157053528623952325341)
              ·
                refine ⟨209683895073233982122003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559157053528623952325341 209683895073233982122003)
                ·
                  refine ⟨314525842609850973183005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209683895073233982122003 314525842609850973183005)
                  ·
                    refine ⟨117947190978694114943627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 314525842609850973183005 117947190978694114943627)
                    ·
                      rfl

theorem cell22_344552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_344552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344552 prefixEnd_344552 := by exact prefixLift 344552
  have htrace : WordTrace (prefixWord ++ tailWord_344552) baseStart_344552 baseEnd_344552 := by
    simpa [prefixWord, tailWord_344552, baseEnd_344552] using wordTrace_append hprefix tailTrace_344552
  have hstable : (prefixWord ++ tailWord_344552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344552).length < 2 ^ (prefixWord ++ tailWord_344552).sum := by decide
  have hdescent : baseEnd_344552 < baseStart_344552 := by decide
  rcases family_descends (prefixWord ++ tailWord_344552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344565 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 7]
def baseStart_344565 : Nat := 118140960795 + 344565 * 2 ^ 59
def prefixEnd_344565 : Nat := 4983230072969 + 3 ^ 40 * 344565 * 2
def baseEnd_344565 : Nat := 39317213714788804789529

theorem tailTrace_344565 : CollatzResearch.WordTrace tailWord_344565 prefixEnd_344565 39317213714788804789529 := by
  unfold tailWord_344565
  simp only [CollatzResearch.WordTrace]
  refine ⟨12567317996707326862059149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8378211997804884574706099 12567317996707326862059149)
  ·
    refine ⟨4712744248765247573272181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12567317996707326862059149 4712744248765247573272181)
    ·
      refine ⟨441819773321741959994267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4712744248765247573272181 441819773321741959994267)
      ·
        refine ⟨662729659982612939991401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441819773321741959994267 662729659982612939991401)
        ·
          refine ⟨497047244986959704993551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662729659982612939991401 497047244986959704993551)
          ·
            refine ⟨745570867480439557490327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497047244986959704993551 745570867480439557490327)
            ·
              refine ⟨1118356301220659336235491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745570867480439557490327 1118356301220659336235491)
              ·
                refine ⟨1677534451830989004353237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118356301220659336235491 1677534451830989004353237)
                ·
                  refine ⟨39317213714788804789529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1677534451830989004353237 39317213714788804789529)
                  ·
                    rfl

theorem cell22_344565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_344565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344565 prefixEnd_344565 := by exact prefixLift 344565
  have htrace : WordTrace (prefixWord ++ tailWord_344565) baseStart_344565 baseEnd_344565 := by
    simpa [prefixWord, tailWord_344565, baseEnd_344565] using wordTrace_append hprefix tailTrace_344565
  have hstable : (prefixWord ++ tailWord_344565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344565).length < 2 ^ (prefixWord ++ tailWord_344565).sum := by decide
  have hdescent : baseEnd_344565 < baseStart_344565 := by decide
  rcases family_descends (prefixWord ++ tailWord_344565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344706 : List Nat := [3, 4, 3, 1, 1, 1, 3, 6]
def baseStart_344706 : Nat := 118140960795 + 344706 * 2 ^ 59
def prefixEnd_344706 : Nat := 4983230072969 + 3 ^ 40 * 344706 * 2
def baseEnd_344706 : Nat := 13111100925098782954795

theorem tailTrace_344706 : CollatzResearch.WordTrace tailWord_344706 prefixEnd_344706 13111100925098782954795 := by
  unfold tailWord_344706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143115172299126985735493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8381640459464338628627981 3143115172299126985735493)
  ·
    refine ⟨589334094806086309825405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3143115172299126985735493 589334094806086309825405)
    ·
      refine ⟨221000285552282366184527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 589334094806086309825405 221000285552282366184527)
      ·
        refine ⟨331500428328423549276791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221000285552282366184527 331500428328423549276791)
        ·
          refine ⟨497250642492635323915187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331500428328423549276791 497250642492635323915187)
          ·
            refine ⟨745875963738952985872781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497250642492635323915187 745875963738952985872781)
            ·
              refine ⟨279703486402107369702293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 745875963738952985872781 279703486402107369702293)
              ·
                refine ⟨13111100925098782954795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 279703486402107369702293 13111100925098782954795)
                ·
                  rfl

theorem cell22_344706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_344706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344706 prefixEnd_344706 := by exact prefixLift 344706
  have htrace : WordTrace (prefixWord ++ tailWord_344706) baseStart_344706 baseEnd_344706 := by
    simpa [prefixWord, tailWord_344706, baseEnd_344706] using wordTrace_append hprefix tailTrace_344706
  have hstable : (prefixWord ++ tailWord_344706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344706).length < 2 ^ (prefixWord ++ tailWord_344706).sum := by decide
  have hdescent : baseEnd_344706 < baseStart_344706 := by decide
  rcases family_descends (prefixWord ++ tailWord_344706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344728 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 8]
def baseStart_344728 : Nat := 118140960795 + 344728 * 2 ^ 59
def prefixEnd_344728 : Nat := 4983230072969 + 3 ^ 40 * 344728 * 2
def baseEnd_344728 : Nat := 39335813125162774181029

theorem tailTrace_344728 : CollatzResearch.WordTrace tailWord_344728 prefixEnd_344728 39335813125162774181029 := by
  unfold tailWord_344728
  simp only [CollatzResearch.WordTrace]
  refine ⟨6286631547558402850121419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8382175396744537133495225 6286631547558402850121419)
  ·
    refine ⟨9429947321337604275182129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6286631547558402850121419 9429947321337604275182129)
    ·
      refine ⟨7072460491003203206386597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9429947321337604275182129 7072460491003203206386597)
      ·
        refine ⟨1326086342063100601197487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7072460491003203206386597 1326086342063100601197487)
        ·
          refine ⟨1989129513094650901796231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326086342063100601197487 1989129513094650901796231)
          ·
            refine ⟨2983694269641976352694347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1989129513094650901796231 2983694269641976352694347)
            ·
              refine ⟨4475541404462964529041521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983694269641976352694347 4475541404462964529041521)
              ·
                refine ⟨3356656053347223396781141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475541404462964529041521 3356656053347223396781141)
                ·
                  refine ⟨39335813125162774181029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3356656053347223396781141 39335813125162774181029)
                  ·
                    rfl

theorem cell22_344728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_344728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344728 prefixEnd_344728 := by exact prefixLift 344728
  have htrace : WordTrace (prefixWord ++ tailWord_344728) baseStart_344728 baseEnd_344728 := by
    simpa [prefixWord, tailWord_344728, baseEnd_344728] using wordTrace_append hprefix tailTrace_344728
  have hstable : (prefixWord ++ tailWord_344728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344728).length < 2 ^ (prefixWord ++ tailWord_344728).sum := by decide
  have hdescent : baseEnd_344728 < baseStart_344728 := by decide
  rcases family_descends (prefixWord ++ tailWord_344728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344796 : List Nat := [2, 2, 5, 1, 1, 2, 3, 2, 4]
def baseStart_344796 : Nat := 118140960795 + 344796 * 2 ^ 59
def prefixEnd_344796 : Nat := 4983230072969 + 3 ^ 40 * 344796 * 2
def baseEnd_344796 : Nat := 39343572388386270614293

theorem tailTrace_344796 : CollatzResearch.WordTrace tailWord_344796 prefixEnd_344796 39343572388386270614293 := by
  unfold tailWord_344796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287871629435226656859121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8383828839246968875812161 6287871629435226656859121)
  ·
    refine ⟨4715903722076419992644341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6287871629435226656859121 4715903722076419992644341)
    ·
      refine ⟨442115973944664374310407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4715903722076419992644341 442115973944664374310407)
      ·
        refine ⟨663173960916996561465611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442115973944664374310407 663173960916996561465611)
        ·
          refine ⟨994760941375494842198417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663173960916996561465611 994760941375494842198417)
          ·
            refine ⟨746070706031621131648813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994760941375494842198417 746070706031621131648813)
            ·
              refine ⟨279776514761857924368305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746070706031621131648813 279776514761857924368305)
              ·
                refine ⟨209832386071393443276229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279776514761857924368305 209832386071393443276229)
                ·
                  refine ⟨39343572388386270614293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209832386071393443276229 39343572388386270614293)
                  ·
                    rfl

theorem cell22_344796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_344796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344796 prefixEnd_344796 := by exact prefixLift 344796
  have htrace : WordTrace (prefixWord ++ tailWord_344796) baseStart_344796 baseEnd_344796 := by
    simpa [prefixWord, tailWord_344796, baseEnd_344796] using wordTrace_append hprefix tailTrace_344796
  have hstable : (prefixWord ++ tailWord_344796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344796).length < 2 ^ (prefixWord ++ tailWord_344796).sum := by decide
  have hdescent : baseEnd_344796 < baseStart_344796 := by decide
  rcases family_descends (prefixWord ++ tailWord_344796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344822 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_344822 : Nat := 118140960795 + 344822 * 2 ^ 59
def prefixEnd_344822 : Nat := 4983230072969 + 3 ^ 40 * 344822 * 2
def baseEnd_344822 : Nat := 118039617496503410692799

theorem tailTrace_344822 : CollatzResearch.WordTrace tailWord_344822 prefixEnd_344822 118039617496503410692799 := by
  unfold tailWord_344822
  simp only [CollatzResearch.WordTrace]
  refine ⟨786043222298516234635295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8384461037850839836109813 786043222298516234635295)
  ·
    refine ⟨1179064833447774351952943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786043222298516234635295 1179064833447774351952943)
    ·
      refine ⟨1768597250171661527929415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179064833447774351952943 1768597250171661527929415)
      ·
        refine ⟨2652895875257492291894123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768597250171661527929415 2652895875257492291894123)
        ·
          refine ⟨3979343812886238437841185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652895875257492291894123 3979343812886238437841185)
          ·
            refine ⟨2984507859664678828380889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3979343812886238437841185 2984507859664678828380889)
            ·
              refine ⟨2238380894748509121285667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2984507859664678828380889 2238380894748509121285667)
              ·
                refine ⟨3357571342122763681928501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238380894748509121285667 3357571342122763681928501)
                ·
                  refine ⟨314772313324009095180797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3357571342122763681928501 314772313324009095180797)
                  ·
                    refine ⟨118039617496503410692799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 314772313324009095180797 118039617496503410692799)
                    ·
                      rfl

theorem cell22_344822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_344822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344822 prefixEnd_344822 := by exact prefixLift 344822
  have htrace : WordTrace (prefixWord ++ tailWord_344822) baseStart_344822 baseEnd_344822 := by
    simpa [prefixWord, tailWord_344822, baseEnd_344822] using wordTrace_append hprefix tailTrace_344822
  have hstable : (prefixWord ++ tailWord_344822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344822).length < 2 ^ (prefixWord ++ tailWord_344822).sum := by decide
  have hdescent : baseEnd_344822 < baseStart_344822 := by decide
  rcases family_descends (prefixWord ++ tailWord_344822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344865 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_344865 : Nat := 118140960795 + 344865 * 2 ^ 59
def prefixEnd_344865 : Nat := 4983230072969 + 3 ^ 40 * 344865 * 2
def baseEnd_344865 : Nat := 118054337275265631867667

theorem tailTrace_344865 : CollatzResearch.WordTrace tailWord_344865 prefixEnd_344865 118054337275265631867667 := by
  unfold tailWord_344865
  simp only [CollatzResearch.WordTrace]
  refine ⟨12578259895620478097980049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8385506597080318731986699 12578259895620478097980049)
  ·
    refine ⟨9433694921715358573485037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12578259895620478097980049 9433694921715358573485037)
    ·
      refine ⟨3537635595643259465056889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9433694921715358573485037 3537635595643259465056889)
      ·
        refine ⟨2653226696732444598792667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3537635595643259465056889 2653226696732444598792667)
        ·
          refine ⟨3979840045098666898189001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653226696732444598792667 3979840045098666898189001)
          ·
            refine ⟨2984880033824000173641751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3979840045098666898189001 2984880033824000173641751)
            ·
              refine ⟨4477320050736000260462627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984880033824000173641751 4477320050736000260462627)
              ·
                refine ⟨6715980076104000390693941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477320050736000260462627 6715980076104000390693941)
                ·
                  refine ⟨629623132134750036627557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6715980076104000390693941 629623132134750036627557)
                  ·
                    refine ⟨118054337275265631867667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 629623132134750036627557 118054337275265631867667)
                    ·
                      rfl

theorem cell22_344865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_344865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344865 prefixEnd_344865 := by exact prefixLift 344865
  have htrace : WordTrace (prefixWord ++ tailWord_344865) baseStart_344865 baseEnd_344865 := by
    simpa [prefixWord, tailWord_344865, baseEnd_344865] using wordTrace_append hprefix tailTrace_344865
  have hstable : (prefixWord ++ tailWord_344865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344865).length < 2 ^ (prefixWord ++ tailWord_344865).sum := by decide
  have hdescent : baseEnd_344865 < baseStart_344865 := by decide
  rcases family_descends (prefixWord ++ tailWord_344865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344882 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_344882 : Nat := 118140960795 + 344882 * 2 ^ 59
def prefixEnd_344882 : Nat := 4983230072969 + 3 ^ 40 * 344882 * 2
def baseEnd_344882 : Nat := 118060156722683254192615

theorem tailTrace_344882 : CollatzResearch.WordTrace tailWord_344882 prefixEnd_344882 118060156722683254192615 := by
  unfold tailWord_344882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144719984139722500337225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8385919957705926667565933 3144719984139722500337225)
  ·
    refine ⟨2358539988104791875252919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3144719984139722500337225 2358539988104791875252919)
    ·
      refine ⟨3537809982157187812879379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358539988104791875252919 3537809982157187812879379)
      ·
        refine ⟨5306714973235781719319069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537809982157187812879379 5306714973235781719319069)
        ·
          refine ⟨1990018114963418144744651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5306714973235781719319069 1990018114963418144744651)
          ·
            refine ⟨2985027172445127217116977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990018114963418144744651 2985027172445127217116977)
            ·
              refine ⟨2238770379333845412837733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2985027172445127217116977 2238770379333845412837733)
              ·
                refine ⟨419769446125096014907075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2238770379333845412837733 419769446125096014907075)
                ·
                  refine ⟨629654169187644022360613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419769446125096014907075 629654169187644022360613)
                  ·
                    refine ⟨118060156722683254192615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 629654169187644022360613 118060156722683254192615)
                    ·
                      rfl

theorem cell22_344882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_344882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344882 prefixEnd_344882 := by exact prefixLift 344882
  have htrace : WordTrace (prefixWord ++ tailWord_344882) baseStart_344882 baseEnd_344882 := by
    simpa [prefixWord, tailWord_344882, baseEnd_344882] using wordTrace_append hprefix tailTrace_344882
  have hstable : (prefixWord ++ tailWord_344882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344882).length < 2 ^ (prefixWord ++ tailWord_344882).sum := by decide
  have hdescent : baseEnd_344882 < baseStart_344882 := by decide
  rcases family_descends (prefixWord ++ tailWord_344882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344940 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_344940 : Nat := 118140960795 + 344940 * 2 ^ 59
def prefixEnd_344940 : Nat := 4983230072969 + 3 ^ 40 * 344940 * 2
def baseEnd_344940 : Nat := 118080011307990436242437

theorem tailTrace_344940 : CollatzResearch.WordTrace tailWord_344940 prefixEnd_344940 118080011307990436242437 := by
  unfold tailWord_344940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6290497685174382953480137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8387330246899177271306849 6290497685174382953480137)
  ·
    refine ⟨4717873263880787215110103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6290497685174382953480137 4717873263880787215110103)
    ·
      refine ⟨7076809895821180822665155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4717873263880787215110103 7076809895821180822665155)
      ·
        refine ⟨10615214843731771233997733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7076809895821180822665155 10615214843731771233997733)
        ·
          refine ⟨1990352783199707106374575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10615214843731771233997733 1990352783199707106374575)
          ·
            refine ⟨2985529174799560659561863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990352783199707106374575 2985529174799560659561863)
            ·
              refine ⟨4478293762199340989342795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985529174799560659561863 4478293762199340989342795)
              ·
                refine ⟨6717440643299011484014193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4478293762199340989342795 6717440643299011484014193)
                ·
                  refine ⟨5038080482474258613010645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6717440643299011484014193 5038080482474258613010645)
                  ·
                    refine ⟨118080011307990436242437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5038080482474258613010645 118080011307990436242437)
                    ·
                      rfl

theorem cell22_344940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_344940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344940 prefixEnd_344940 := by exact prefixLift 344940
  have htrace : WordTrace (prefixWord ++ tailWord_344940) baseStart_344940 baseEnd_344940 := by
    simpa [prefixWord, tailWord_344940, baseEnd_344940] using wordTrace_append hprefix tailTrace_344940
  have hstable : (prefixWord ++ tailWord_344940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344940).length < 2 ^ (prefixWord ++ tailWord_344940).sum := by decide
  have hdescent : baseEnd_344940 < baseStart_344940 := by decide
  rcases family_descends (prefixWord ++ tailWord_344940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344957 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_344957 : Nat := 118140960795 + 344957 * 2 ^ 59
def prefixEnd_344957 : Nat := 4983230072969 + 3 ^ 40 * 344957 * 2
def baseEnd_344957 : Nat := 118085830755408058567385

theorem tailTrace_344957 : CollatzResearch.WordTrace tailWord_344957 prefixEnd_344957 118085830755408058567385 := by
  unfold tailWord_344957
  simp only [CollatzResearch.WordTrace]
  refine ⟨12581615411287177810329125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8387743607524785206886083 12581615411287177810329125)
  ·
    refine ⟨2359052889616345839436711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12581615411287177810329125 2359052889616345839436711)
    ·
      refine ⟨3538579334424518759155067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2359052889616345839436711 3538579334424518759155067)
      ·
        refine ⟨5307869001636778138732601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3538579334424518759155067 5307869001636778138732601)
        ·
          refine ⟨3980901751227583604049451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5307869001636778138732601 3980901751227583604049451)
          ·
            refine ⟨5971352626841375406074177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980901751227583604049451 5971352626841375406074177)
            ·
              refine ⟨4478514470131031554555633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5971352626841375406074177 4478514470131031554555633)
              ·
                refine ⟨3358885852598273665916725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4478514470131031554555633 3358885852598273665916725)
                ·
                  refine ⟨314895548681088156179693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3358885852598273665916725 314895548681088156179693)
                  ·
                    refine ⟨118085830755408058567385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 314895548681088156179693 118085830755408058567385)
                    ·
                      rfl

theorem cell22_344957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_344957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344957 prefixEnd_344957 := by exact prefixLift 344957
  have htrace : WordTrace (prefixWord ++ tailWord_344957) baseStart_344957 baseEnd_344957 := by
    simpa [prefixWord, tailWord_344957, baseEnd_344957] using wordTrace_append hprefix tailTrace_344957
  have hstable : (prefixWord ++ tailWord_344957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344957).length < 2 ^ (prefixWord ++ tailWord_344957).sum := by decide
  have hdescent : baseEnd_344957 < baseStart_344957 := by decide
  rcases family_descends (prefixWord ++ tailWord_344957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344985 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_344985 : Nat := 118140960795 + 344985 * 2 ^ 59
def prefixEnd_344985 : Nat := 4983230072969 + 3 ^ 40 * 344985 * 2
def baseEnd_344985 : Nat := 118095415727625318867299

theorem tailTrace_344985 : CollatzResearch.WordTrace tailWord_344985 prefixEnd_344985 118095415727625318867299 := by
  unfold tailWord_344985
  simp only [CollatzResearch.WordTrace]
  refine ⟨12582636655185738592348409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8388424436790492394898939 12582636655185738592348409)
  ·
    refine ⟨9436977491389303944261307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12582636655185738592348409 9436977491389303944261307)
    ·
      refine ⟨14155466237083955916391961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9436977491389303944261307 14155466237083955916391961)
      ·
        refine ⟨10616599677812966937293971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14155466237083955916391961 10616599677812966937293971)
        ·
          refine ⟨15924899516719450405940957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10616599677812966937293971 15924899516719450405940957)
          ·
            refine ⟨5971837318769793902227859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15924899516719450405940957 5971837318769793902227859)
            ·
              refine ⟨8957755978154690853341789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5971837318769793902227859 8957755978154690853341789)
              ·
                refine ⟨3359158491808009070003171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8957755978154690853341789 3359158491808009070003171)
                ·
                  refine ⟨5038737737712013605004757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3359158491808009070003171 5038737737712013605004757)
                  ·
                    refine ⟨118095415727625318867299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5038737737712013605004757 118095415727625318867299)
                    ·
                      rfl

theorem cell22_344985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_344985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_344985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_344985 prefixEnd_344985 := by exact prefixLift 344985
  have htrace : WordTrace (prefixWord ++ tailWord_344985) baseStart_344985 baseEnd_344985 := by
    simpa [prefixWord, tailWord_344985, baseEnd_344985] using wordTrace_append hprefix tailTrace_344985
  have hstable : (prefixWord ++ tailWord_344985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344985).length < 2 ^ (prefixWord ++ tailWord_344985).sum := by decide
  have hdescent : baseEnd_344985 < baseStart_344985 := by decide
  rcases family_descends (prefixWord ++ tailWord_344985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345066 : List Nat := [3, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_345066 : Nat := 118140960795 + 345066 * 2 ^ 59
def prefixEnd_345066 : Nat := 4983230072969 + 3 ^ 40 * 345066 * 2
def baseEnd_345066 : Nat := 39374381227656035864017

theorem tailTrace_345066 : CollatzResearch.WordTrace tailWord_345066 prefixEnd_345066 39374381227656035864017 := by
  unfold tailWord_345066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146397741973072356511763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8390393978594859617364701 3146397741973072356511763)
  ·
    refine ⟨4719596612959608534767645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3146397741973072356511763 4719596612959608534767645)
    ·
      refine ⟨1769848729859853200537867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4719596612959608534767645 1769848729859853200537867)
      ·
        refine ⟨2654773094789779800806801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769848729859853200537867 2654773094789779800806801)
        ·
          refine ⟨1991079821092334850605101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2654773094789779800806801 1991079821092334850605101)
          ·
            refine ⟨746654932909625568976913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1991079821092334850605101 746654932909625568976913)
            ·
              refine ⟨559991199682219176732685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746654932909625568976913 559991199682219176732685)
              ·
                refine ⟨209996699880832191274757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559991199682219176732685 209996699880832191274757)
                ·
                  refine ⟨39374381227656035864017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209996699880832191274757 39374381227656035864017)
                  ·
                    rfl

theorem cell22_345066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_345066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345066 prefixEnd_345066 := by exact prefixLift 345066
  have htrace : WordTrace (prefixWord ++ tailWord_345066) baseStart_345066 baseEnd_345066 := by
    simpa [prefixWord, tailWord_345066, baseEnd_345066] using wordTrace_append hprefix tailTrace_345066
  have hstable : (prefixWord ++ tailWord_345066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345066).length < 2 ^ (prefixWord ++ tailWord_345066).sum := by decide
  have hdescent : baseEnd_345066 < baseStart_345066 := by decide
  rcases family_descends (prefixWord ++ tailWord_345066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345098 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_345098 : Nat := 118140960795 + 345098 * 2 ^ 59
def prefixEnd_345098 : Nat := 4983230072969 + 3 ^ 40 * 345098 * 2
def baseEnd_345098 : Nat := 118134097936930690791953

theorem tailTrace_345098 : CollatzResearch.WordTrace tailWord_345098 prefixEnd_345098 118134097936930690791953 := by
  unfold tailWord_345098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146689525944089722802987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8391172069184239260807965 3146689525944089722802987)
  ·
    refine ⟨4720034288916134584204481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3146689525944089722802987 4720034288916134584204481)
    ·
      refine ⟨3540025716687100938153361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4720034288916134584204481 3540025716687100938153361)
      ·
        refine ⟨2655019287515325703615021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540025716687100938153361 2655019287515325703615021)
        ·
          refine ⟨995632232818247138855633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2655019287515325703615021 995632232818247138855633)
          ·
            refine ⟨746724174613685354141725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995632232818247138855633 746724174613685354141725)
            ·
              refine ⟨280021565480132007803147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746724174613685354141725 280021565480132007803147)
              ·
                refine ⟨420032348220198011704721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280021565480132007803147 420032348220198011704721)
                ·
                  refine ⟨315024261165148508778541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420032348220198011704721 315024261165148508778541)
                  ·
                    refine ⟨118134097936930690791953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315024261165148508778541 118134097936930690791953)
                    ·
                      rfl

theorem cell22_345098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_345098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345098 prefixEnd_345098 := by exact prefixLift 345098
  have htrace : WordTrace (prefixWord ++ tailWord_345098) baseStart_345098 baseEnd_345098 := by
    simpa [prefixWord, tailWord_345098, baseEnd_345098] using wordTrace_append hprefix tailTrace_345098
  have hstable : (prefixWord ++ tailWord_345098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345098).length < 2 ^ (prefixWord ++ tailWord_345098).sum := by decide
  have hdescent : baseEnd_345098 < baseStart_345098 := by decide
  rcases family_descends (prefixWord ++ tailWord_345098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345111 : List Nat := [1, 1, 3, 5, 1, 3, 2, 6]
def baseStart_345111 : Nat := 118140960795 + 345111 * 2 ^ 59
def prefixEnd_345111 : Nat := 4983230072969 + 3 ^ 40 * 345111 * 2
def baseEnd_345111 : Nat := 13126505344733665579657

theorem tailTrace_345111 : CollatzResearch.WordTrace tailWord_345111 prefixEnd_345111 13126505344733665579657 := by
  unfold tailWord_345111
  simp only [CollatzResearch.WordTrace]
  refine ⟨12587232252729262111435187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8391488168486174740956791 12587232252729262111435187)
  ·
    refine ⟨18880848379093893167152781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12587232252729262111435187 18880848379093893167152781)
    ·
      refine ⟨7080318142160209937682293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18880848379093893167152781 7080318142160209937682293)
      ·
        refine ⟨663779825827519681657715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7080318142160209937682293 663779825827519681657715)
        ·
          refine ⟨995669738741279522486573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663779825827519681657715 995669738741279522486573)
          ·
            refine ⟨373376152027979820932465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 995669738741279522486573 373376152027979820932465)
            ·
              refine ⟨280032114020984865699349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373376152027979820932465 280032114020984865699349)
              ·
                refine ⟨13126505344733665579657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 280032114020984865699349 13126505344733665579657)
                ·
                  rfl

theorem cell22_345111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 6].length) (baseStart_345111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345111 prefixEnd_345111 := by exact prefixLift 345111
  have htrace : WordTrace (prefixWord ++ tailWord_345111) baseStart_345111 baseEnd_345111 := by
    simpa [prefixWord, tailWord_345111, baseEnd_345111] using wordTrace_append hprefix tailTrace_345111
  have hstable : (prefixWord ++ tailWord_345111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345111).length < 2 ^ (prefixWord ++ tailWord_345111).sum := by decide
  have hdescent : baseEnd_345111 < baseStart_345111 := by decide
  rcases family_descends (prefixWord ++ tailWord_345111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345216 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 2, 3]
def baseStart_345216 : Nat := 118140960795 + 345216 * 2 ^ 59
def prefixEnd_345216 : Nat := 4983230072969 + 3 ^ 40 * 345216 * 2
def baseEnd_345216 : Nat := 118174491748417716341591

theorem tailTrace_345216 : CollatzResearch.WordTrace tailWord_345216 prefixEnd_345216 118174491748417716341591 := by
  unfold tailWord_345216
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295530958674432522003751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8394041278232576696005001 6295530958674432522003751)
  ·
    refine ⟨9443296438011648783005627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6295530958674432522003751 9443296438011648783005627)
    ·
      refine ⟨14164944657017473174508441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9443296438011648783005627 14164944657017473174508441)
      ·
        refine ⟨10623708492763104880881331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14164944657017473174508441 10623708492763104880881331)
        ·
          refine ⟨15935562739144657321321997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10623708492763104880881331 15935562739144657321321997)
          ·
            refine ⟨5975836027179246495495749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15935562739144657321321997 5975836027179246495495749)
            ·
              refine ⟨1120469255096108717905453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5975836027179246495495749 1120469255096108717905453)
              ·
                refine ⟨420175970661040769214545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1120469255096108717905453 420175970661040769214545)
                ·
                  refine ⟨315131977995780576910909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420175970661040769214545 315131977995780576910909)
                  ·
                    refine ⟨118174491748417716341591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315131977995780576910909 118174491748417716341591)
                    ·
                      rfl

theorem cell22_345216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_345216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345216 prefixEnd_345216 := by exact prefixLift 345216
  have htrace : WordTrace (prefixWord ++ tailWord_345216) baseStart_345216 baseEnd_345216 := by
    simpa [prefixWord, tailWord_345216, baseEnd_345216] using wordTrace_append hprefix tailTrace_345216
  have hstable : (prefixWord ++ tailWord_345216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345216).length < 2 ^ (prefixWord ++ tailWord_345216).sum := by decide
  have hdescent : baseEnd_345216 < baseStart_345216 := by decide
  rcases family_descends (prefixWord ++ tailWord_345216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345246 : List Nat := [4, 3, 1, 1, 2, 2, 9]
def baseStart_345246 : Nat := 118140960795 + 345246 * 2 ^ 59
def prefixEnd_345246 : Nat := 4983230072969 + 3 ^ 40 * 345246 * 2
def baseEnd_345246 : Nat := 4377213383759542151537

theorem tailTrace_345246 : CollatzResearch.WordTrace tailWord_345246 prefixEnd_345246 4377213383759542151537 := by
  unfold tailWord_345246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574019513405022520949949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8394770738160120111733061 1574019513405022520949949)
  ·
    refine ⟨590257317526883445356231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1574019513405022520949949 590257317526883445356231)
    ·
      refine ⟨885385976290325168034347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590257317526883445356231 885385976290325168034347)
      ·
        refine ⟨1328078964435487752051521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885385976290325168034347 1328078964435487752051521)
        ·
          refine ⟨996059223326615814038641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1328078964435487752051521 996059223326615814038641)
          ·
            refine ⟨747044417494961860528981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 996059223326615814038641 747044417494961860528981)
            ·
              refine ⟨4377213383759542151537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 747044417494961860528981 4377213383759542151537)
              ·
                rfl

theorem cell22_345246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 9].length) (baseStart_345246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345246 prefixEnd_345246 := by exact prefixLift 345246
  have htrace : WordTrace (prefixWord ++ tailWord_345246) baseStart_345246 baseEnd_345246 := by
    simpa [prefixWord, tailWord_345246, baseEnd_345246] using wordTrace_append hprefix tailTrace_345246
  have hstable : (prefixWord ++ tailWord_345246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345246).length < 2 ^ (prefixWord ++ tailWord_345246).sum := by decide
  have hdescent : baseEnd_345246 < baseStart_345246 := by decide
  rcases family_descends (prefixWord ++ tailWord_345246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345278 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_345278 : Nat := 118140960795 + 345278 * 2 ^ 59
def prefixEnd_345278 : Nat := 4983230072969 + 3 ^ 40 * 345278 * 2
def baseEnd_345278 : Nat := 118195715615470221291401

theorem tailTrace_345278 : CollatzResearch.WordTrace tailWord_345278 prefixEnd_345278 118195715615470221291401 := by
  unfold tailWord_345278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574165405390531204095561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8395548828749499755176325 1574165405390531204095561)
  ·
    refine ⟨1180624054042898403071671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1574165405390531204095561 1180624054042898403071671)
    ·
      refine ⟨1770936081064347604607507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180624054042898403071671 1770936081064347604607507)
      ·
        refine ⟨2656404121596521406911261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770936081064347604607507 2656404121596521406911261)
        ·
          refine ⟨996151545598695527591723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2656404121596521406911261 996151545598695527591723)
          ·
            refine ⟨1494227318398043291387585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996151545598695527591723 1494227318398043291387585)
            ·
              refine ⟨1120670488798532468540689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494227318398043291387585 1120670488798532468540689)
              ·
                refine ⟨840502866598899351405517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120670488798532468540689 840502866598899351405517)
                ·
                  refine ⟨315188574974587256777069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 840502866598899351405517 315188574974587256777069)
                  ·
                    refine ⟨118195715615470221291401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315188574974587256777069 118195715615470221291401)
                    ·
                      rfl

theorem cell22_345278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_345278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345278 prefixEnd_345278 := by exact prefixLift 345278
  have htrace : WordTrace (prefixWord ++ tailWord_345278) baseStart_345278 baseEnd_345278 := by
    simpa [prefixWord, tailWord_345278, baseEnd_345278] using wordTrace_append hprefix tailTrace_345278
  have hstable : (prefixWord ++ tailWord_345278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345278).length < 2 ^ (prefixWord ++ tailWord_345278).sum := by decide
  have hdescent : baseEnd_345278 < baseStart_345278 := by decide
  rcases family_descends (prefixWord ++ tailWord_345278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345286 : List Nat := [6, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_345286 : Nat := 118140960795 + 345286 * 2 ^ 59
def prefixEnd_345286 : Nat := 4983230072969 + 3 ^ 40 * 345286 * 2
def baseEnd_345286 : Nat := 39399484726320289030459

theorem tailTrace_345286 : CollatzResearch.WordTrace tailWord_345286 prefixEnd_345286 39399484726320289030459 := by
  unfold tailWord_345286
  simp only [CollatzResearch.WordTrace]
  refine ⟨393550469596727093720491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8395743351396844666037141 393550469596727093720491)
  ·
    refine ⟨590325704395090640580737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393550469596727093720491 590325704395090640580737)
    ·
      refine ⟨442744278296317980435553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 590325704395090640580737 442744278296317980435553)
      ·
        refine ⟨332058208722238485326665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442744278296317980435553 332058208722238485326665)
        ·
          refine ⟨249043656541678863994999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332058208722238485326665 249043656541678863994999)
          ·
            refine ⟨373565484812518295992499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249043656541678863994999 373565484812518295992499)
            ·
              refine ⟨560348227218777443988749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373565484812518295992499 560348227218777443988749)
              ·
                refine ⟨210130585207041541495781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 560348227218777443988749 210130585207041541495781)
                ·
                  refine ⟨39399484726320289030459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210130585207041541495781 39399484726320289030459)
                  ·
                    rfl

theorem cell22_345286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_345286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345286 prefixEnd_345286 := by exact prefixLift 345286
  have htrace : WordTrace (prefixWord ++ tailWord_345286) baseStart_345286 baseEnd_345286 := by
    simpa [prefixWord, tailWord_345286, baseEnd_345286] using wordTrace_append hprefix tailTrace_345286
  have hstable : (prefixWord ++ tailWord_345286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345286).length < 2 ^ (prefixWord ++ tailWord_345286).sum := by decide
  have hdescent : baseEnd_345286 < baseStart_345286 := by decide
  rcases family_descends (prefixWord ++ tailWord_345286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345325 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 5]
def baseStart_345325 : Nat := 118140960795 + 345325 * 2 ^ 59
def prefixEnd_345325 : Nat := 4983230072969 + 3 ^ 40 * 345325 * 2
def baseEnd_345325 : Nat := 39403934891992588455419

theorem tailTrace_345325 : CollatzResearch.WordTrace tailWord_345325 prefixEnd_345325 39403934891992588455419 := by
  unfold tailWord_345325
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595037473953976659725429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8396691649302651106483619 12595037473953976659725429)
  ·
    refine ⟨1180784763183185311849259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12595037473953976659725429 1180784763183185311849259)
    ·
      refine ⟨1771177144774777967773889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180784763183185311849259 1771177144774777967773889)
      ·
        refine ⟨1328382858581083475830417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1771177144774777967773889 1328382858581083475830417)
        ·
          refine ⟨996287143935812606872813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1328382858581083475830417 996287143935812606872813)
          ·
            refine ⟨373607678975929727577305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 996287143935812606872813 373607678975929727577305)
            ·
              refine ⟨280205759231947295682979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373607678975929727577305 280205759231947295682979)
              ·
                refine ⟨420308638847920943524469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280205759231947295682979 420308638847920943524469)
                ·
                  refine ⟨39403934891992588455419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 420308638847920943524469 39403934891992588455419)
                  ·
                    rfl

theorem cell22_345325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_345325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345325 prefixEnd_345325 := by exact prefixLift 345325
  have htrace : WordTrace (prefixWord ++ tailWord_345325) baseStart_345325 baseEnd_345325 := by
    simpa [prefixWord, tailWord_345325, baseEnd_345325] using wordTrace_append hprefix tailTrace_345325
  have hstable : (prefixWord ++ tailWord_345325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345325).length < 2 ^ (prefixWord ++ tailWord_345325).sum := by decide
  have hdescent : baseEnd_345325 < baseStart_345325 := by decide
  rcases family_descends (prefixWord ++ tailWord_345325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345364 : List Nat := [2, 4, 16]
def baseStart_345364 : Nat := 118140960795 + 345364 * 2 ^ 59
def prefixEnd_345364 : Nat := 4983230072969 + 3 ^ 40 * 345364 * 2
def baseEnd_345364 : Nat := 54058141368538940851

theorem tailTrace_345364 : CollatzResearch.WordTrace tailWord_345364 prefixEnd_345364 54058141368538940851 := by
  unfold tailWord_345364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6298229960406343160197573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8397639947208457546930097 6298229960406343160197573)
  ·
    refine ⟨1180918117576189342537045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6298229960406343160197573 1180918117576189342537045)
    ·
      refine ⟨54058141368538940851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 1180918117576189342537045 54058141368538940851)
      ·
        rfl

theorem cell22_345364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 16].length) (baseStart_345364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345364 prefixEnd_345364 := by exact prefixLift 345364
  have htrace : WordTrace (prefixWord ++ tailWord_345364) baseStart_345364 baseEnd_345364 := by
    simpa [prefixWord, tailWord_345364, baseEnd_345364] using wordTrace_append hprefix tailTrace_345364
  have hstable : (prefixWord ++ tailWord_345364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345364).length < 2 ^ (prefixWord ++ tailWord_345364).sum := by decide
  have hdescent : baseEnd_345364 < baseStart_345364 := by decide
  rcases family_descends (prefixWord ++ tailWord_345364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345368 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 2, 3]
def baseStart_345368 : Nat := 118140960795 + 345368 * 2 ^ 59
def prefixEnd_345368 : Nat := 4983230072969 + 3 ^ 40 * 345368 * 2
def baseEnd_345368 : Nat := 118226524454739986541125

theorem tailTrace_345368 : CollatzResearch.WordTrace tailWord_345368 prefixEnd_345368 118226524454739986541125 := by
  unfold tailWord_345368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6298302906399097501770379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8397737208532130002360505 6298302906399097501770379)
  ·
    refine ⟨9447454359598646252655569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6298302906399097501770379 9447454359598646252655569)
    ·
      refine ⟨7085590769698984689491677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9447454359598646252655569 7085590769698984689491677)
      ·
        refine ⟨2657096538637119258559379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7085590769698984689491677 2657096538637119258559379)
        ·
          refine ⟨3985644807955678887839069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657096538637119258559379 3985644807955678887839069)
          ·
            refine ⟨1494616802983379582939651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3985644807955678887839069 1494616802983379582939651)
            ·
              refine ⟨2241925204475069374409477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494616802983379582939651 2241925204475069374409477)
              ·
                refine ⟨420360975839075507701777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2241925204475069374409477 420360975839075507701777)
                ·
                  refine ⟨315270731879306630776333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420360975839075507701777 315270731879306630776333)
                  ·
                    refine ⟨118226524454739986541125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315270731879306630776333 118226524454739986541125)
                    ·
                      rfl

theorem cell22_345368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_345368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345368 prefixEnd_345368 := by exact prefixLift 345368
  have htrace : WordTrace (prefixWord ++ tailWord_345368) baseStart_345368 baseEnd_345368 := by
    simpa [prefixWord, tailWord_345368, baseEnd_345368] using wordTrace_append hprefix tailTrace_345368
  have hstable : (prefixWord ++ tailWord_345368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345368).length < 2 ^ (prefixWord ++ tailWord_345368).sum := by decide
  have hdescent : baseEnd_345368 < baseStart_345368 := by decide
  rcases family_descends (prefixWord ++ tailWord_345368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345370 : List Nat := [3, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_345370 : Nat := 118140960795 + 345370 * 2 ^ 59
def prefixEnd_345370 : Nat := 4983230072969 + 3 ^ 40 * 345370 * 2
def baseEnd_345370 : Nat := 39409069698537549330373

theorem tailTrace_345370 : CollatzResearch.WordTrace tailWord_345370 prefixEnd_345370 39409069698537549330373 := by
  unfold tailWord_345370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149169689697737336278391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8397785839193966230075709 3149169689697737336278391)
  ·
    refine ⟨4723754534546606004417587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3149169689697737336278391 4723754534546606004417587)
    ·
      refine ⟨7085631801819909006626381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723754534546606004417587 7085631801819909006626381)
      ·
        refine ⟨2657111925682465877484893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7085631801819909006626381 2657111925682465877484893)
        ·
          refine ⟨996416972130924704056835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2657111925682465877484893 996416972130924704056835)
          ·
            refine ⟨1494625458196387056085253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996416972130924704056835 1494625458196387056085253)
            ·
              refine ⟨280242273411822573015985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1494625458196387056085253 280242273411822573015985)
              ·
                refine ⟨210181705058866929761989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280242273411822573015985 210181705058866929761989)
                ·
                  refine ⟨39409069698537549330373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210181705058866929761989 39409069698537549330373)
                  ·
                    rfl

theorem cell22_345370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_345370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345370 prefixEnd_345370 := by exact prefixLift 345370
  have htrace : WordTrace (prefixWord ++ tailWord_345370) baseStart_345370 baseEnd_345370 := by
    simpa [prefixWord, tailWord_345370, baseEnd_345370] using wordTrace_append hprefix tailTrace_345370
  have hstable : (prefixWord ++ tailWord_345370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345370).length < 2 ^ (prefixWord ++ tailWord_345370).sum := by decide
  have hdescent : baseEnd_345370 < baseStart_345370 := by decide
  rcases family_descends (prefixWord ++ tailWord_345370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345381 : List Nat := [1, 3, 1, 2, 4, 1, 3, 7]
def baseStart_345381 : Nat := 118140960795 + 345381 * 2 ^ 59
def prefixEnd_345381 : Nat := 4983230072969 + 3 ^ 40 * 345381 * 2
def baseEnd_345381 : Nat := 13136774957823587329565

theorem tailTrace_345381 : CollatzResearch.WordTrace tailWord_345381 prefixEnd_345381 13136774957823587329565 := by
  unfold tailWord_345381
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597079961751098223763997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8398053307834065482509331 12597079961751098223763997)
  ·
    refine ⟨4723904985656661833911499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12597079961751098223763997 4723904985656661833911499)
    ·
      refine ⟨7085857478484992750867249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4723904985656661833911499 7085857478484992750867249)
      ·
        refine ⟨5314393108863744563150437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7085857478484992750867249 5314393108863744563150437)
        ·
          refine ⟨996448707911952105590707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5314393108863744563150437 996448707911952105590707)
          ·
            refine ⟨1494673061867928158386061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996448707911952105590707 1494673061867928158386061)
            ·
              refine ⟨560502398200473059394773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1494673061867928158386061 560502398200473059394773)
              ·
                refine ⟨13136774957823587329565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 560502398200473059394773 13136774957823587329565)
                ·
                  rfl

theorem cell22_345381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 7].length) (baseStart_345381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345381 prefixEnd_345381 := by exact prefixLift 345381
  have htrace : WordTrace (prefixWord ++ tailWord_345381) baseStart_345381 baseEnd_345381 := by
    simpa [prefixWord, tailWord_345381, baseEnd_345381] using wordTrace_append hprefix tailTrace_345381
  have hstable : (prefixWord ++ tailWord_345381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345381).length < 2 ^ (prefixWord ++ tailWord_345381).sum := by decide
  have hdescent : baseEnd_345381 < baseStart_345381 := by decide
  rcases family_descends (prefixWord ++ tailWord_345381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345516 : List Nat := [2, 2, 1, 1, 1, 1, 6, 8]
def baseStart_345516 : Nat := 118140960795 + 345516 * 2 ^ 59
def prefixEnd_345516 : Nat := 4983230072969 + 3 ^ 40 * 345516 * 2
def baseEnd_345516 : Nat := 13141909764368548204519

theorem tailTrace_345516 : CollatzResearch.WordTrace tailWord_345516 prefixEnd_345516 13141909764368548204519 := by
  unfold tailWord_345516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301001908131008139964201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8401335877508010853285601 6301001908131008139964201)
  ·
    refine ⟨4725751431098256104973151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6301001908131008139964201 4725751431098256104973151)
    ·
      refine ⟨7088627146647384157459727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4725751431098256104973151 7088627146647384157459727)
      ·
        refine ⟨10632940719971076236189591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7088627146647384157459727 10632940719971076236189591)
        ·
          refine ⟨15949411079956614354284387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10632940719971076236189591 15949411079956614354284387)
          ·
            refine ⟨23924116619934921531426581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15949411079956614354284387 23924116619934921531426581)
            ·
              refine ⟨1121442966559449446785621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23924116619934921531426581 1121442966559449446785621)
              ·
                refine ⟨13141909764368548204519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1121442966559449446785621 13141909764368548204519)
                ·
                  rfl

theorem cell22_345516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 8].length) (baseStart_345516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345516 prefixEnd_345516 := by exact prefixLift 345516
  have htrace : WordTrace (prefixWord ++ tailWord_345516) baseStart_345516 baseEnd_345516 := by
    simpa [prefixWord, tailWord_345516, baseEnd_345516] using wordTrace_append hprefix tailTrace_345516
  have hstable : (prefixWord ++ tailWord_345516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345516).length < 2 ^ (prefixWord ++ tailWord_345516).sum := by decide
  have hdescent : baseEnd_345516 < baseStart_345516 := by decide
  rcases family_descends (prefixWord ++ tailWord_345516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345565 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_345565 : Nat := 118140960795 + 345565 * 2 ^ 59
def prefixEnd_345565 : Nat := 4983230072969 + 3 ^ 40 * 345565 * 2
def baseEnd_345565 : Nat := 118293961580697139365521

theorem tailTrace_345565 : CollatzResearch.WordTrace tailWord_345565 prefixEnd_345565 118293961580697139365521 := by
  unfold tailWord_345565
  simp only [CollatzResearch.WordTrace]
  refine ⟨12603790993084497648462149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8402527328722998432308099 12603790993084497648462149)
  ·
    refine ⟨2363210811203343309086653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12603790993084497648462149 2363210811203343309086653)
    ·
      refine ⟨886204054201253740907495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2363210811203343309086653 886204054201253740907495)
      ·
        refine ⟨1329306081301880611361243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886204054201253740907495 1329306081301880611361243)
        ·
          refine ⟨1993959121952820917041865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329306081301880611361243 1993959121952820917041865)
          ·
            refine ⟨1495469341464615687781399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993959121952820917041865 1495469341464615687781399)
            ·
              refine ⟨2243204012196923531672099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495469341464615687781399 2243204012196923531672099)
              ·
                refine ⟨3364806018295385297508149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243204012196923531672099 3364806018295385297508149)
                ·
                  refine ⟨315450564215192371641389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3364806018295385297508149 315450564215192371641389)
                  ·
                    refine ⟨118293961580697139365521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315450564215192371641389 118293961580697139365521)
                    ·
                      rfl

theorem cell22_345565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_345565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345565 prefixEnd_345565 := by exact prefixLift 345565
  have htrace : WordTrace (prefixWord ++ tailWord_345565) baseStart_345565 baseEnd_345565 := by
    simpa [prefixWord, tailWord_345565, baseEnd_345565] using wordTrace_append hprefix tailTrace_345565
  have hstable : (prefixWord ++ tailWord_345565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345565).length < 2 ^ (prefixWord ++ tailWord_345565).sum := by decide
  have hdescent : baseEnd_345565 < baseStart_345565 := by decide
  rcases family_descends (prefixWord ++ tailWord_345565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345608 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_345608 : Nat := 118140960795 + 345608 * 2 ^ 59
def prefixEnd_345608 : Nat := 4983230072969 + 3 ^ 40 * 345608 * 2
def baseEnd_345608 : Nat := 118308681359459360540389

theorem tailTrace_345608 : CollatzResearch.WordTrace tailWord_345608 prefixEnd_345608 118308681359459360540389 := by
  unfold tailWord_345608
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302679665964357996138739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8403572887952477328184985 6302679665964357996138739)
  ·
    refine ⟨9454019498946536994208109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6302679665964357996138739 9454019498946536994208109)
    ·
      refine ⟨3545257312104951372828041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9454019498946536994208109 3545257312104951372828041)
      ·
        refine ⟨2658942984078713529621031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3545257312104951372828041 2658942984078713529621031)
        ·
          refine ⟨3988414476118070294431547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2658942984078713529621031 3988414476118070294431547)
          ·
            refine ⟨5982621714177105441647321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988414476118070294431547 5982621714177105441647321)
            ·
              refine ⟨4486966285632829081235491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5982621714177105441647321 4486966285632829081235491)
              ·
                refine ⟨6730449428449243621853237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4486966285632829081235491 6730449428449243621853237)
                ·
                  refine ⟨630979633917116589548741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6730449428449243621853237 630979633917116589548741)
                  ·
                    refine ⟨118308681359459360540389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 630979633917116589548741 118308681359459360540389)
                    ·
                      rfl

theorem cell22_345608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_345608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345608 prefixEnd_345608 := by exact prefixLift 345608
  have htrace : WordTrace (prefixWord ++ tailWord_345608) baseStart_345608 baseEnd_345608 := by
    simpa [prefixWord, tailWord_345608, baseEnd_345608] using wordTrace_append hprefix tailTrace_345608
  have hstable : (prefixWord ++ tailWord_345608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345608).length < 2 ^ (prefixWord ++ tailWord_345608).sum := by decide
  have hdescent : baseEnd_345608 < baseStart_345608 := by decide
  rcases family_descends (prefixWord ++ tailWord_345608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345612 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 5]
def baseStart_345612 : Nat := 118140960795 + 345612 * 2 ^ 59
def prefixEnd_345612 : Nat := 4983230072969 + 3 ^ 40 * 345612 * 2
def baseEnd_345612 : Nat := 39436683547068227813459

theorem tailTrace_345612 : CollatzResearch.WordTrace tailWord_345612 prefixEnd_345612 39436683547068227813459 := by
  unfold tailWord_345612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302752611957112337711545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8403670149276149783615393 6302752611957112337711545)
  ·
    refine ⟨4727064458967834253283659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6302752611957112337711545 4727064458967834253283659)
    ·
      refine ⟨7090596688451751379925489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4727064458967834253283659 7090596688451751379925489)
      ·
        refine ⟨5317947516338813534944117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7090596688451751379925489 5317947516338813534944117)
        ·
          refine ⟨498557579656763768901011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5317947516338813534944117 498557579656763768901011)
          ·
            refine ⟨747836369485145653351517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498557579656763768901011 747836369485145653351517)
            ·
              refine ⟨280438638556929620006819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 747836369485145653351517 280438638556929620006819)
              ·
                refine ⟨420657957835394430010229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280438638556929620006819 420657957835394430010229)
                ·
                  refine ⟨39436683547068227813459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 420657957835394430010229 39436683547068227813459)
                  ·
                    rfl

theorem cell22_345612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_345612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345612 prefixEnd_345612 := by exact prefixLift 345612
  have htrace : WordTrace (prefixWord ++ tailWord_345612) baseStart_345612 baseEnd_345612 := by
    simpa [prefixWord, tailWord_345612, baseEnd_345612] using wordTrace_append hprefix tailTrace_345612
  have hstable : (prefixWord ++ tailWord_345612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345612).length < 2 ^ (prefixWord ++ tailWord_345612).sum := by decide
  have hdescent : baseEnd_345612 < baseStart_345612 := by decide
  rcases family_descends (prefixWord ++ tailWord_345612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345655 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 4, 3]
def baseStart_345655 : Nat := 118140960795 + 345655 * 2 ^ 59
def prefixEnd_345655 : Nat := 4983230072969 + 3 ^ 40 * 345655 * 2
def baseEnd_345655 : Nat := 118324770419966904615245

theorem tailTrace_345655 : CollatzResearch.WordTrace tailWord_345655 prefixEnd_345655 118324770419966904615245 := by
  unfold tailWord_345655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12607073562758443019238419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8404715708505628679492279 12607073562758443019238419)
  ·
    refine ⟨18910610344137664528857629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12607073562758443019238419 18910610344137664528857629)
    ·
      refine ⟨7091478879051624198321611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18910610344137664528857629 7091478879051624198321611)
      ·
        refine ⟨10637218318577436297482417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7091478879051624198321611 10637218318577436297482417)
        ·
          refine ⟨7977913738933077223111813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10637218318577436297482417 7977913738933077223111813)
          ·
            refine ⟨1495858826049951979333465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7977913738933077223111813 1495858826049951979333465)
            ·
              refine ⟨1121894119537463984500099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495858826049951979333465 1121894119537463984500099)
              ·
                refine ⟨1682841179306195976750149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121894119537463984500099 1682841179306195976750149)
                ·
                  refine ⟨315532721119911745640653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1682841179306195976750149 315532721119911745640653)
                  ·
                    refine ⟨118324770419966904615245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315532721119911745640653 118324770419966904615245)
                    ·
                      rfl

theorem cell22_345655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_345655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345655 prefixEnd_345655 := by exact prefixLift 345655
  have htrace : WordTrace (prefixWord ++ tailWord_345655) baseStart_345655 baseEnd_345655 := by
    simpa [prefixWord, tailWord_345655, baseEnd_345655] using wordTrace_append hprefix tailTrace_345655
  have hstable : (prefixWord ++ tailWord_345655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345655).length < 2 ^ (prefixWord ++ tailWord_345655).sum := by decide
  have hdescent : baseEnd_345655 < baseStart_345655 := by decide
  rcases family_descends (prefixWord ++ tailWord_345655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345713 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 7]
def baseStart_345713 : Nat := 118140960795 + 345713 * 2 ^ 59
def prefixEnd_345713 : Nat := 4983230072969 + 3 ^ 40 * 345713 * 2
def baseEnd_345713 : Nat := 39448208335091362221689

theorem tailTrace_345713 : CollatzResearch.WordTrace tailWord_345713 prefixEnd_345713 39448208335091362221689 := by
  unfold tailWord_345713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12609188996548318924849793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8406125997698879283233195 12609188996548318924849793)
  ·
    refine ⟨9456891747411239193637345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12609188996548318924849793 9456891747411239193637345)
    ·
      refine ⟨7092668810558429395228009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9456891747411239193637345 7092668810558429395228009)
      ·
        refine ⟨5319501607918822046421007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7092668810558429395228009 5319501607918822046421007)
        ·
          refine ⟨7979252411878233069631511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319501607918822046421007 7979252411878233069631511)
          ·
            refine ⟨11968878617817349604447267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7979252411878233069631511 11968878617817349604447267)
            ·
              refine ⟨17953317926726024406670901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11968878617817349604447267 17953317926726024406670901)
              ·
                refine ⟨1683123555630564788125397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17953317926726024406670901 1683123555630564788125397)
                ·
                  refine ⟨39448208335091362221689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1683123555630564788125397 39448208335091362221689)
                  ·
                    rfl

theorem cell22_345713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_345713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345713 prefixEnd_345713 := by exact prefixLift 345713
  have htrace : WordTrace (prefixWord ++ tailWord_345713) baseStart_345713 baseEnd_345713 := by
    simpa [prefixWord, tailWord_345713, baseEnd_345713] using wordTrace_append hprefix tailTrace_345713
  have hstable : (prefixWord ++ tailWord_345713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345713).length < 2 ^ (prefixWord ++ tailWord_345713).sum := by decide
  have hdescent : baseEnd_345713 < baseStart_345713 := by decide
  rcases family_descends (prefixWord ++ tailWord_345713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345768 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 3, 3]
def baseStart_345768 : Nat := 118140960795 + 345768 * 2 ^ 59
def prefixEnd_345768 : Nat := 4983230072969 + 3 ^ 40 * 345768 * 2
def baseEnd_345768 : Nat := 118363452629272276539899

theorem tailTrace_345768 : CollatzResearch.WordTrace tailWord_345768 prefixEnd_345768 118363452629272276539899 := by
  unfold tailWord_345768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6305597505674531659050979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8407463340899375545401305 6305597505674531659050979)
  ·
    refine ⟨9458396258511797488576469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6305597505674531659050979 9458396258511797488576469)
    ·
      refine ⟨221681162308870253638511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9458396258511797488576469 221681162308870253638511)
      ·
        refine ⟨332521743463305380457767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221681162308870253638511 332521743463305380457767)
        ·
          refine ⟨498782615194958070686651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332521743463305380457767 498782615194958070686651)
          ·
            refine ⟨748173922792437106029977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498782615194958070686651 748173922792437106029977)
            ·
              refine ⟨561130442094327829522483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748173922792437106029977 561130442094327829522483)
              ·
                refine ⟨841695663141491744283725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561130442094327829522483 841695663141491744283725)
                ·
                  refine ⟨315635873678059404106397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841695663141491744283725 315635873678059404106397)
                  ·
                    refine ⟨118363452629272276539899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315635873678059404106397 118363452629272276539899)
                    ·
                      rfl

theorem cell22_345768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_345768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345768 prefixEnd_345768 := by exact prefixLift 345768
  have htrace : WordTrace (prefixWord ++ tailWord_345768) baseStart_345768 baseEnd_345768 := by
    simpa [prefixWord, tailWord_345768, baseEnd_345768] using wordTrace_append hprefix tailTrace_345768
  have hstable : (prefixWord ++ tailWord_345768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345768).length < 2 ^ (prefixWord ++ tailWord_345768).sum := by decide
  have hdescent : baseEnd_345768 < baseStart_345768 := by decide
  rcases family_descends (prefixWord ++ tailWord_345768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345775 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 6]
def baseStart_345775 : Nat := 118140960795 + 345775 * 2 ^ 59
def prefixEnd_345775 : Nat := 4983230072969 + 3 ^ 40 * 345775 * 2
def baseEnd_345775 : Nat := 39455282957442197204959

theorem tailTrace_345775 : CollatzResearch.WordTrace tailWord_345775 prefixEnd_345775 39455282957442197204959 := by
  unfold tailWord_345775
  simp only [CollatzResearch.WordTrace]
  refine ⟨12611450322323703513606779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8407633548215802342404519 12611450322323703513606779)
  ·
    refine ⟨18917175483485555270410169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12611450322323703513606779 18917175483485555270410169)
    ·
      refine ⟨14187881612614166452807627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18917175483485555270410169 14187881612614166452807627)
      ·
        refine ⟨21281822418921249679211441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14187881612614166452807627 21281822418921249679211441)
        ·
          refine ⟨15961366814190937259408581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21281822418921249679211441 15961366814190937259408581)
          ·
            refine ⟨2992756277660800736139109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15961366814190937259408581 2992756277660800736139109)
            ·
              refine ⟨561141802061400138026083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2992756277660800736139109 561141802061400138026083)
              ·
                refine ⟨841712703092100207039125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561141802061400138026083 841712703092100207039125)
                ·
                  refine ⟨39455282957442197204959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 841712703092100207039125 39455282957442197204959)
                  ·
                    rfl

theorem cell22_345775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 6].length) (baseStart_345775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345775 prefixEnd_345775 := by exact prefixLift 345775
  have htrace : WordTrace (prefixWord ++ tailWord_345775) baseStart_345775 baseEnd_345775 := by
    simpa [prefixWord, tailWord_345775, baseEnd_345775] using wordTrace_append hprefix tailTrace_345775
  have hstable : (prefixWord ++ tailWord_345775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345775).length < 2 ^ (prefixWord ++ tailWord_345775).sum := by decide
  have hdescent : baseEnd_345775 < baseStart_345775 := by decide
  rcases family_descends (prefixWord ++ tailWord_345775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345809 : List Nat := [1, 2, 2, 1, 2, 6, 1, 3, 4]
def baseStart_345809 : Nat := 118140960795 + 345809 * 2 ^ 59
def prefixEnd_345809 : Nat := 4983230072969 + 3 ^ 40 * 345809 * 2
def baseEnd_345809 : Nat := 39459162589053945421591

theorem tailTrace_345809 : CollatzResearch.WordTrace tailWord_345809 prefixEnd_345809 39459162589053945421591 := by
  unfold tailWord_345809
  simp only [CollatzResearch.WordTrace]
  refine ⟨12612690404200527320344481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8408460269467018213562987 12612690404200527320344481)
  ·
    refine ⟨9459517803150395490258361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12612690404200527320344481 9459517803150395490258361)
    ·
      refine ⟨7094638352362796617693771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9459517803150395490258361 7094638352362796617693771)
      ·
        refine ⟨10641957528544194926540657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7094638352362796617693771 10641957528544194926540657)
        ·
          refine ⟨7981468146408146194905493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641957528544194926540657 7981468146408146194905493)
          ·
            refine ⟨374131319362881852886195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7981468146408146194905493 374131319362881852886195)
            ·
              refine ⟨561196979044322779329293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374131319362881852886195 561196979044322779329293)
              ·
                refine ⟨210448867141621042248485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561196979044322779329293 210448867141621042248485)
                ·
                  refine ⟨39459162589053945421591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210448867141621042248485 39459162589053945421591)
                  ·
                    rfl

theorem cell22_345809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_345809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345809 prefixEnd_345809 := by exact prefixLift 345809
  have htrace : WordTrace (prefixWord ++ tailWord_345809) baseStart_345809 baseEnd_345809 := by
    simpa [prefixWord, tailWord_345809, baseEnd_345809] using wordTrace_append hprefix tailTrace_345809
  have hstable : (prefixWord ++ tailWord_345809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345809).length < 2 ^ (prefixWord ++ tailWord_345809).sum := by decide
  have hdescent : baseEnd_345809 < baseStart_345809 := by decide
  rcases family_descends (prefixWord ++ tailWord_345809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345837 : List Nat := [1, 5, 1, 2, 1, 3, 2, 7]
def baseStart_345837 : Nat := 118140960795 + 345837 * 2 ^ 59
def prefixEnd_345837 : Nat := 4983230072969 + 3 ^ 40 * 345837 * 2
def baseEnd_345837 : Nat := 13154119193264344062743

theorem tailTrace_345837 : CollatzResearch.WordTrace tailWord_345837 prefixEnd_345837 13154119193264344062743 := by
  unfold tailWord_345837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12613711648099088102363765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8409141098732725401575843 12613711648099088102363765)
  ·
    refine ⟨1182535467009289509596603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12613711648099088102363765 1182535467009289509596603)
    ·
      refine ⟨1773803200513934264394905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182535467009289509596603 1773803200513934264394905)
      ·
        refine ⟨1330352400385450698296179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773803200513934264394905 1330352400385450698296179)
        ·
          refine ⟨1995528600578176047444269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330352400385450698296179 1995528600578176047444269)
          ·
            refine ⟨748323225216816017791601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1995528600578176047444269 748323225216816017791601)
            ·
              refine ⟨561242418912612013343701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748323225216816017791601 561242418912612013343701)
              ·
                refine ⟨13154119193264344062743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 561242418912612013343701 13154119193264344062743)
                ·
                  rfl

theorem cell22_345837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 7].length) (baseStart_345837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345837 prefixEnd_345837 := by exact prefixLift 345837
  have htrace : WordTrace (prefixWord ++ tailWord_345837) baseStart_345837 baseEnd_345837 := by
    simpa [prefixWord, tailWord_345837, baseEnd_345837] using wordTrace_append hprefix tailTrace_345837
  have hstable : (prefixWord ++ tailWord_345837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345837).length < 2 ^ (prefixWord ++ tailWord_345837).sum := by decide
  have hdescent : baseEnd_345837 < baseStart_345837 := by decide
  rcases family_descends (prefixWord ++ tailWord_345837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345841 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 2, 3]
def baseStart_345841 : Nat := 118140960795 + 345841 * 2 ^ 59
def prefixEnd_345841 : Nat := 4983230072969 + 3 ^ 40 * 345841 * 2
def baseEnd_345841 : Nat := 118388442021124419464675

theorem tailTrace_345841 : CollatzResearch.WordTrace tailWord_345841 prefixEnd_345841 118388442021124419464675 := by
  unfold tailWord_345841
  simp only [CollatzResearch.WordTrace]
  refine ⟨12613857540084596785509377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8409238360056397857006251 12613857540084596785509377)
  ·
    refine ⟨9460393155063447589132033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12613857540084596785509377 9460393155063447589132033)
    ·
      refine ⟨7095294866297585691849025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9460393155063447589132033 7095294866297585691849025)
      ·
        refine ⟨5321471149723189268886769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7095294866297585691849025 5321471149723189268886769)
        ·
          refine ⟨3991103362292391951665077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5321471149723189268886769 3991103362292391951665077)
          ·
            refine ⟨374165940214911745468601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3991103362292391951665077 374165940214911745468601)
            ·
              refine ⟨280624455161183809101451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374165940214911745468601 280624455161183809101451)
              ·
                refine ⟨420936682741775713652177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280624455161183809101451 420936682741775713652177)
                ·
                  refine ⟨315702512056331785239133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420936682741775713652177 315702512056331785239133)
                  ·
                    refine ⟨118388442021124419464675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315702512056331785239133 118388442021124419464675)
                    ·
                      rfl

theorem cell22_345841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_345841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345841 prefixEnd_345841 := by exact prefixLift 345841
  have htrace : WordTrace (prefixWord ++ tailWord_345841) baseStart_345841 baseEnd_345841 := by
    simpa [prefixWord, tailWord_345841, baseEnd_345841] using wordTrace_append hprefix tailTrace_345841
  have hstable : (prefixWord ++ tailWord_345841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345841).length < 2 ^ (prefixWord ++ tailWord_345841).sum := by decide
  have hdescent : baseEnd_345841 < baseStart_345841 := by decide
  rcases family_descends (prefixWord ++ tailWord_345841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345852 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 5, 3]
def baseStart_345852 : Nat := 118140960795 + 345852 * 2 ^ 59
def prefixEnd_345852 : Nat := 4983230072969 + 3 ^ 40 * 345852 * 2
def baseEnd_345852 : Nat := 118392207545924057439641

theorem tailTrace_345852 : CollatzResearch.WordTrace tailWord_345852 prefixEnd_345852 118392207545924057439641 := by
  unfold tailWord_345852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307129371522372832079905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8409505828696497109439873 6307129371522372832079905)
  ·
    refine ⟨4730347028641779624059929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6307129371522372832079905 4730347028641779624059929)
    ·
      refine ⟨3547760271481334718044947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4730347028641779624059929 3547760271481334718044947)
      ·
        refine ⟨5321640407222002077067421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3547760271481334718044947 5321640407222002077067421)
        ·
          refine ⟨1995615152708250778900283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5321640407222002077067421 1995615152708250778900283)
          ·
            refine ⟨2993422729062376168350425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995615152708250778900283 2993422729062376168350425)
            ·
              refine ⟨2245067046796782126262819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993422729062376168350425 2245067046796782126262819)
              ·
                refine ⟨3367600570195173189394229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245067046796782126262819 3367600570195173189394229)
                ·
                  refine ⟨315712553455797486505709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3367600570195173189394229 315712553455797486505709)
                  ·
                    refine ⟨118392207545924057439641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315712553455797486505709 118392207545924057439641)
                    ·
                      rfl

theorem cell22_345852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_345852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345852 prefixEnd_345852 := by exact prefixLift 345852
  have htrace : WordTrace (prefixWord ++ tailWord_345852) baseStart_345852 baseEnd_345852 := by
    simpa [prefixWord, tailWord_345852, baseEnd_345852] using wordTrace_append hprefix tailTrace_345852
  have hstable : (prefixWord ++ tailWord_345852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345852).length < 2 ^ (prefixWord ++ tailWord_345852).sum := by decide
  have hdescent : baseEnd_345852 < baseStart_345852 := by decide
  rcases family_descends (prefixWord ++ tailWord_345852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345882 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_345882 : Nat := 118140960795 + 345882 * 2 ^ 59
def prefixEnd_345882 : Nat := 4983230072969 + 3 ^ 40 * 345882 * 2
def baseEnd_345882 : Nat := 39467492386337993063183

theorem tailTrace_345882 : CollatzResearch.WordTrace tailWord_345882 prefixEnd_345882 39467492386337993063183 := by
  unfold tailWord_345882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153838233234015196937975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8410235288624040525167933 3153838233234015196937975)
  ·
    refine ⟨4730757349851022795406963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3153838233234015196937975 4730757349851022795406963)
    ·
      refine ⟨7096136024776534193110445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4730757349851022795406963 7096136024776534193110445)
      ·
        refine ⟨2661051009291200322416417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7096136024776534193110445 2661051009291200322416417)
        ·
          refine ⟨1995788256968400241812313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2661051009291200322416417 1995788256968400241812313)
          ·
            refine ⟨1496841192726300181359235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1995788256968400241812313 1496841192726300181359235)
            ·
              refine ⟨2245261789089450272038853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496841192726300181359235 2245261789089450272038853)
              ·
                refine ⟨420986585454271926007285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2245261789089450272038853 420986585454271926007285)
                ·
                  refine ⟨39467492386337993063183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 420986585454271926007285 39467492386337993063183)
                  ·
                    rfl

theorem cell22_345882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_345882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345882 prefixEnd_345882 := by exact prefixLift 345882
  have htrace : WordTrace (prefixWord ++ tailWord_345882) baseStart_345882 baseEnd_345882 := by
    simpa [prefixWord, tailWord_345882, baseEnd_345882] using wordTrace_append hprefix tailTrace_345882
  have hstable : (prefixWord ++ tailWord_345882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345882).length < 2 ^ (prefixWord ++ tailWord_345882).sum := by decide
  have hdescent : baseEnd_345882 < baseStart_345882 := by decide
  rcases family_descends (prefixWord ++ tailWord_345882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345912 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 3, 4]
def baseStart_345912 : Nat := 118140960795 + 345912 * 2 ^ 59
def prefixEnd_345912 : Nat := 4983230072969 + 3 ^ 40 * 345912 * 2
def baseEnd_345912 : Nat := 118412746772103900939457

theorem tailTrace_345912 : CollatzResearch.WordTrace tailWord_345912 prefixEnd_345912 118412746772103900939457 := by
  unfold tailWord_345912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308223561413687955671995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8410964748551583940895993 6308223561413687955671995)
  ·
    refine ⟨9462335342120531933507993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6308223561413687955671995 9462335342120531933507993)
    ·
      refine ⟨7096751506590398950130995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9462335342120531933507993 7096751506590398950130995)
      ·
        refine ⟨10645127259885598425196493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7096751506590398950130995 10645127259885598425196493)
        ·
          refine ⟨3991922722457099409448685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10645127259885598425196493 3991922722457099409448685)
          ·
            refine ⟨1496971020921412278543257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3991922722457099409448685 1496971020921412278543257)
            ·
              refine ⟨1122728265691059208907443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496971020921412278543257 1122728265691059208907443)
              ·
                refine ⟨1684092398536588813361165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122728265691059208907443 1684092398536588813361165)
                ·
                  refine ⟨631534649451220805010437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1684092398536588813361165 631534649451220805010437)
                  ·
                    refine ⟨118412746772103900939457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 631534649451220805010437 118412746772103900939457)
                    ·
                      rfl

theorem cell22_345912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_345912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_345912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_345912 prefixEnd_345912 := by exact prefixLift 345912
  have htrace : WordTrace (prefixWord ++ tailWord_345912) baseStart_345912 baseEnd_345912 := by
    simpa [prefixWord, tailWord_345912, baseEnd_345912] using wordTrace_append hprefix tailTrace_345912
  have hstable : (prefixWord ++ tailWord_345912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345912).length < 2 ^ (prefixWord ++ tailWord_345912).sum := by decide
  have hdescent : baseEnd_345912 < baseStart_345912 := by decide
  rcases family_descends (prefixWord ++ tailWord_345912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346066 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_346066 : Nat := 118140960795 + 346066 * 2 ^ 59
def prefixEnd_346066 : Nat := 4983230072969 + 3 ^ 40 * 346066 * 2
def baseEnd_346066 : Nat := 118465464119298832588985

theorem tailTrace_346066 : CollatzResearch.WordTrace tailWord_346066 prefixEnd_346066 118465464119298832588985 := by
  unfold tailWord_346066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3155515991067365053112513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8414709309512973474966701 3155515991067365053112513)
  ·
    refine ⟨2366636993300523789834385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3155515991067365053112513 2366636993300523789834385)
    ·
      refine ⟨1774977744975392842375789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2366636993300523789834385 1774977744975392842375789)
      ·
        refine ⟨665616654365772315890921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1774977744975392842375789 665616654365772315890921)
        ·
          refine ⟨499212490774329236918191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665616654365772315890921 499212490774329236918191)
          ·
            refine ⟨748818736161493855377287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499212490774329236918191 748818736161493855377287)
            ·
              refine ⟨1123228104242240783065931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748818736161493855377287 1123228104242240783065931)
              ·
                refine ⟨1684842156363361174598897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123228104242240783065931 1684842156363361174598897)
                ·
                  refine ⟨1263631617272520880949173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1684842156363361174598897 1263631617272520880949173)
                  ·
                    refine ⟨118465464119298832588985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1263631617272520880949173 118465464119298832588985)
                    ·
                      rfl

theorem cell22_346066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_346066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346066 prefixEnd_346066 := by exact prefixLift 346066
  have htrace : WordTrace (prefixWord ++ tailWord_346066) baseStart_346066 baseEnd_346066 := by
    simpa [prefixWord, tailWord_346066, baseEnd_346066] using wordTrace_append hprefix tailTrace_346066
  have hstable : (prefixWord ++ tailWord_346066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346066).length < 2 ^ (prefixWord ++ tailWord_346066).sum := by decide
  have hdescent : baseEnd_346066 < baseStart_346066 := by decide
  rcases family_descends (prefixWord ++ tailWord_346066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346079 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 6]
def baseStart_346079 : Nat := 118140960795 + 346079 * 2 ^ 59
def prefixEnd_346079 : Nat := 4983230072969 + 3 ^ 40 * 346079 * 2
def baseEnd_346079 : Nat := 39489971428323710671315

theorem tailTrace_346079 : CollatzResearch.WordTrace tailWord_346079 prefixEnd_346079 39489971428323710671315 := by
  unfold tailWord_346079
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622538113222363432673291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8415025408814908955115527 12622538113222363432673291)
  ·
    refine ⟨18933807169833545149009937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12622538113222363432673291 18933807169833545149009937)
    ·
      refine ⟨14200355377375158861757453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18933807169833545149009937 14200355377375158861757453)
      ·
        refine ⟨5325133266515684573159045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14200355377375158861757453 5325133266515684573159045)
        ·
          refine ⟨998462487471690857467321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5325133266515684573159045 998462487471690857467321)
          ·
            refine ⟨748846865603768143100491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 998462487471690857467321 748846865603768143100491)
            ·
              refine ⟨1123270298405652214650737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748846865603768143100491 1123270298405652214650737)
              ·
                refine ⟨842452723804239160988053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123270298405652214650737 842452723804239160988053)
                ·
                  refine ⟨39489971428323710671315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 842452723804239160988053 39489971428323710671315)
                  ·
                    rfl

theorem cell22_346079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 6].length) (baseStart_346079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346079 prefixEnd_346079 := by exact prefixLift 346079
  have htrace : WordTrace (prefixWord ++ tailWord_346079) baseStart_346079 baseEnd_346079 := by
    simpa [prefixWord, tailWord_346079, baseEnd_346079] using wordTrace_append hprefix tailTrace_346079
  have hstable : (prefixWord ++ tailWord_346079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346079).length < 2 ^ (prefixWord ++ tailWord_346079).sum := by decide
  have hdescent : baseEnd_346079 < baseStart_346079 := by decide
  rcases family_descends (prefixWord ++ tailWord_346079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346109 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_346109 : Nat := 118140960795 + 346109 * 2 ^ 59
def prefixEnd_346109 : Nat := 4983230072969 + 3 ^ 40 * 346109 * 2
def baseEnd_346109 : Nat := 118480183898061053763853

theorem tailTrace_346109 : CollatzResearch.WordTrace tailWord_346109 prefixEnd_346109 118480183898061053763853 := by
  unfold tailWord_346109
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623632303113678556265381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8415754868742452370843587 12623632303113678556265381)
  ·
    refine ⟨2366931056833814729299759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12623632303113678556265381 2366931056833814729299759)
    ·
      refine ⟨3550396585250722093949639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366931056833814729299759 3550396585250722093949639)
      ·
        refine ⟨5325594877876083140924459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550396585250722093949639 5325594877876083140924459)
        ·
          refine ⟨7988392316814124711386689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5325594877876083140924459 7988392316814124711386689)
          ·
            refine ⟨5991294237610593533540017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7988392316814124711386689 5991294237610593533540017)
            ·
              refine ⟨4493470678207945150155013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991294237610593533540017 4493470678207945150155013)
              ·
                refine ⟨842525752163989715654065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4493470678207945150155013 842525752163989715654065)
                ·
                  refine ⟨631894314122992286740549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 842525752163989715654065 631894314122992286740549)
                  ·
                    refine ⟨118480183898061053763853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 631894314122992286740549 118480183898061053763853)
                    ·
                      rfl

theorem cell22_346109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_346109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346109 prefixEnd_346109 := by exact prefixLift 346109
  have htrace : WordTrace (prefixWord ++ tailWord_346109) baseStart_346109 baseEnd_346109 := by
    simpa [prefixWord, tailWord_346109, baseEnd_346109] using wordTrace_append hprefix tailTrace_346109
  have hstable : (prefixWord ++ tailWord_346109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346109).length < 2 ^ (prefixWord ++ tailWord_346109).sum := by decide
  have hdescent : baseEnd_346109 < baseStart_346109 := by decide
  rcases family_descends (prefixWord ++ tailWord_346109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346139 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 5, 3]
def baseStart_346139 : Nat := 118140960795 + 346139 * 2 ^ 59
def prefixEnd_346139 : Nat := 4983230072969 + 3 ^ 40 * 346139 * 2
def baseEnd_346139 : Nat := 118490453511150975513761

theorem tailTrace_346139 : CollatzResearch.WordTrace tailWord_346139 prefixEnd_346139 118490453511150975513761 := by
  unfold tailWord_346139
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624726493004993679857471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8416484328669995786571647 12624726493004993679857471)
  ·
    refine ⟨18937089739507490519786207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12624726493004993679857471 18937089739507490519786207)
    ·
      refine ⟨28405634609261235779679311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18937089739507490519786207 28405634609261235779679311)
      ·
        refine ⟨42608451913891853669518967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28405634609261235779679311 42608451913891853669518967)
        ·
          refine ⟨63912677870837780504278451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42608451913891853669518967 63912677870837780504278451)
          ·
            refine ⟨95869016806256670756417677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63912677870837780504278451 95869016806256670756417677)
            ·
              refine ⟨35950881302346251533656629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95869016806256670756417677 35950881302346251533656629)
              ·
                refine ⟨3370395122094961081280309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35950881302346251533656629 3370395122094961081280309)
                ·
                  refine ⟨315974542696402601370029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370395122094961081280309 315974542696402601370029)
                  ·
                    refine ⟨118490453511150975513761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315974542696402601370029 118490453511150975513761)
                    ·
                      rfl

theorem cell22_346139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 3].length) (baseStart_346139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346139 prefixEnd_346139 := by exact prefixLift 346139
  have htrace : WordTrace (prefixWord ++ tailWord_346139) baseStart_346139 baseEnd_346139 := by
    simpa [prefixWord, tailWord_346139, baseEnd_346139] using wordTrace_append hprefix tailTrace_346139
  have hstable : (prefixWord ++ tailWord_346139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346139).length < 2 ^ (prefixWord ++ tailWord_346139).sum := by decide
  have hdescent : baseEnd_346139 < baseStart_346139 := by decide
  rcases family_descends (prefixWord ++ tailWord_346139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346141 : List Nat := [1, 4, 2, 2, 2, 1, 4, 6]
def baseStart_346141 : Nat := 118140960795 + 346141 * 2 ^ 59
def prefixEnd_346141 : Nat := 4983230072969 + 3 ^ 40 * 346141 * 2
def baseEnd_346141 : Nat := 13165682016891515218195

theorem tailTrace_346141 : CollatzResearch.WordTrace tailWord_346141 prefixEnd_346141 13165682016891515218195 := by
  unfold tailWord_346141
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624799438997748021430277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8416532959331832014286851 12624799438997748021430277)
  ·
    refine ⟨2367149894812077754018177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12624799438997748021430277 2367149894812077754018177)
    ·
      refine ⟨1775362421109058315513633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2367149894812077754018177 1775362421109058315513633)
      ·
        refine ⟨1331521815831793736635225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1775362421109058315513633 1331521815831793736635225)
        ·
          refine ⟨998641361873845302476419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1331521815831793736635225 998641361873845302476419)
          ·
            refine ⟨1497962042810767953714629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998641361873845302476419 1497962042810767953714629)
            ·
              refine ⟨280867883027018991321493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1497962042810767953714629 280867883027018991321493)
              ·
                refine ⟨13165682016891515218195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 280867883027018991321493 13165682016891515218195)
                ·
                  rfl

theorem cell22_346141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 6].length) (baseStart_346141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346141 prefixEnd_346141 := by exact prefixLift 346141
  have htrace : WordTrace (prefixWord ++ tailWord_346141) baseStart_346141 baseEnd_346141 := by
    simpa [prefixWord, tailWord_346141, baseEnd_346141] using wordTrace_append hprefix tailTrace_346141
  have hstable : (prefixWord ++ tailWord_346141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346141).length < 2 ^ (prefixWord ++ tailWord_346141).sum := by decide
  have hdescent : baseEnd_346141 < baseStart_346141 := by decide
  rcases family_descends (prefixWord ++ tailWord_346141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346276 : List Nat := [2, 3, 1, 2, 4, 1, 9]
def baseStart_346276 : Nat := 118140960795 + 346276 * 2 ^ 59
def prefixEnd_346276 : Nat := 4983230072969 + 3 ^ 40 * 346276 * 2
def baseEnd_346276 : Nat := 4390272274478825364383

theorem tailTrace_346276 : CollatzResearch.WordTrace tailWord_346276 prefixEnd_346276 4390272274478825364383 := by
  unfold tailWord_346276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6314861646754333038797341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8419815529005777385063121 6314861646754333038797341)
  ·
    refine ⟨2368073117532874889549003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6314861646754333038797341 2368073117532874889549003)
    ·
      refine ⟨3552109676299312334323505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368073117532874889549003 3552109676299312334323505)
      ·
        refine ⟨2664082257224484250742629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3552109676299312334323505 2664082257224484250742629)
        ·
          refine ⟨499515423229590797014243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2664082257224484250742629 499515423229590797014243)
          ·
            refine ⟨749273134844386195521365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499515423229590797014243 749273134844386195521365)
            ·
              refine ⟨4390272274478825364383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 749273134844386195521365 4390272274478825364383)
              ·
                rfl

theorem cell22_346276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 9].length) (baseStart_346276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346276 prefixEnd_346276 := by exact prefixLift 346276
  have htrace : WordTrace (prefixWord ++ tailWord_346276) baseStart_346276 baseEnd_346276 := by
    simpa [prefixWord, tailWord_346276, baseEnd_346276] using wordTrace_append hprefix tailTrace_346276
  have hstable : (prefixWord ++ tailWord_346276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346276).length < 2 ^ (prefixWord ++ tailWord_346276).sum := by decide
  have hdescent : baseEnd_346276 < baseStart_346276 := by decide
  rcases family_descends (prefixWord ++ tailWord_346276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346368 : List Nat := [2, 1, 1, 2, 1, 1, 7, 2, 1, 4]
def baseStart_346368 : Nat := 118140960795 + 346368 * 2 ^ 59
def prefixEnd_346368 : Nat := 4983230072969 + 3 ^ 40 * 346368 * 2
def baseEnd_346368 : Nat := 118568844891070711538059

theorem tailTrace_346368 : CollatzResearch.WordTrace tailWord_346368 prefixEnd_346368 118568844891070711538059 := by
  unfold tailWord_346368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316539404587682894971879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8422052539450243859962505 6316539404587682894971879)
  ·
    refine ⟨9474809106881524342457819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6316539404587682894971879 9474809106881524342457819)
    ·
      refine ⟨14212213660322286513686729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9474809106881524342457819 14212213660322286513686729)
      ·
        refine ⟨10659160245241714885265047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14212213660322286513686729 10659160245241714885265047)
        ·
          refine ⟨15988740367862572327897571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659160245241714885265047 15988740367862572327897571)
          ·
            refine ⟨23983110551793858491846357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15988740367862572327897571 23983110551793858491846357)
            ·
              refine ⟨562104153557668558402649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23983110551793858491846357 562104153557668558402649)
              ·
                refine ⟨421578115168251418801987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562104153557668558402649 421578115168251418801987)
                ·
                  refine ⟨632367172752377128202981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421578115168251418801987 632367172752377128202981)
                  ·
                    refine ⟨118568844891070711538059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632367172752377128202981 118568844891070711538059)
                    ·
                      rfl

theorem cell22_346368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_346368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346368 prefixEnd_346368 := by exact prefixLift 346368
  have htrace : WordTrace (prefixWord ++ tailWord_346368) baseStart_346368 baseEnd_346368 := by
    simpa [prefixWord, tailWord_346368, baseEnd_346368] using wordTrace_append hprefix tailTrace_346368
  have hstable : (prefixWord ++ tailWord_346368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346368).length < 2 ^ (prefixWord ++ tailWord_346368).sum := by decide
  have hdescent : baseEnd_346368 < baseStart_346368 := by decide
  rcases family_descends (prefixWord ++ tailWord_346368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346385 : List Nat := [1, 2, 2, 1, 1, 6, 3, 1, 1, 4]
def baseStart_346385 : Nat := 118140960795 + 346385 * 2 ^ 59
def prefixEnd_346385 : Nat := 4983230072969 + 3 ^ 40 * 346385 * 2
def baseEnd_346385 : Nat := 118574664338488333863007

theorem tailTrace_346385 : CollatzResearch.WordTrace tailWord_346385 prefixEnd_346385 118574664338488333863007 := by
  unfold tailWord_346385
  simp only [CollatzResearch.WordTrace]
  refine ⟨12633698850113777693312609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8422465900075851795541739 12633698850113777693312609)
  ·
    refine ⟨9475274137585333269984457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12633698850113777693312609 9475274137585333269984457)
    ·
      refine ⟨7106455603188999952488343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9475274137585333269984457 7106455603188999952488343)
      ·
        refine ⟨10659683404783499928732515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7106455603188999952488343 10659683404783499928732515)
        ·
          refine ⟨15989525107175249893098773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659683404783499928732515 15989525107175249893098773)
          ·
            refine ⟨749508989398839838739005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15989525107175249893098773 749508989398839838739005)
            ·
              refine ⟨281065871024564939527127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749508989398839838739005 281065871024564939527127)
              ·
                refine ⟨421598806536847409290691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281065871024564939527127 421598806536847409290691)
                ·
                  refine ⟨632398209805271113936037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421598806536847409290691 632398209805271113936037)
                  ·
                    refine ⟨118574664338488333863007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632398209805271113936037 118574664338488333863007)
                    ·
                      rfl

theorem cell22_346385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_346385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346385 prefixEnd_346385 := by exact prefixLift 346385
  have htrace : WordTrace (prefixWord ++ tailWord_346385) baseStart_346385 baseEnd_346385 := by
    simpa [prefixWord, tailWord_346385, baseEnd_346385] using wordTrace_append hprefix tailTrace_346385
  have hstable : (prefixWord ++ tailWord_346385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346385).length < 2 ^ (prefixWord ++ tailWord_346385).sum := by decide
  have hdescent : baseEnd_346385 < baseStart_346385 := by decide
  rcases family_descends (prefixWord ++ tailWord_346385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346396 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_346396 : Nat := 118140960795 + 346396 * 2 ^ 59
def prefixEnd_346396 : Nat := 4983230072969 + 3 ^ 40 * 346396 * 2
def baseEnd_346396 : Nat := 118578429863287971837973

theorem tailTrace_346396 : CollatzResearch.WordTrace tailWord_346396 prefixEnd_346396 118578429863287971837973 := by
  unfold tailWord_346396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317050026536963285981521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8422733368715951047975361 6317050026536963285981521)
  ·
    refine ⟨4737787519902722464486141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6317050026536963285981521 4737787519902722464486141)
    ·
      refine ⟨1776670319963520924182303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4737787519902722464486141 1776670319963520924182303)
      ·
        refine ⟨2665005479945281386273455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776670319963520924182303 2665005479945281386273455)
        ·
          refine ⟨3997508219917922079410183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665005479945281386273455 3997508219917922079410183)
          ·
            refine ⟨5996262329876883119115275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997508219917922079410183 5996262329876883119115275)
            ·
              refine ⟨8994393494815324678672913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5996262329876883119115275 8994393494815324678672913)
              ·
                refine ⟨6745795121111493509004685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8994393494815324678672913 6745795121111493509004685)
                ·
                  refine ⟨2529673170416810065876757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6745795121111493509004685 2529673170416810065876757)
                  ·
                    refine ⟨118578429863287971837973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2529673170416810065876757 118578429863287971837973)
                    ·
                      rfl

theorem cell22_346396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_346396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346396 prefixEnd_346396 := by exact prefixLift 346396
  have htrace : WordTrace (prefixWord ++ tailWord_346396) baseStart_346396 baseEnd_346396 := by
    simpa [prefixWord, tailWord_346396, baseEnd_346396] using wordTrace_append hprefix tailTrace_346396
  have hstable : (prefixWord ++ tailWord_346396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346396).length < 2 ^ (prefixWord ++ tailWord_346396).sum := by decide
  have hdescent : baseEnd_346396 < baseStart_346396 := by decide
  rcases family_descends (prefixWord ++ tailWord_346396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346400 : List Nat := [2, 1, 1, 5, 2, 2, 1, 4, 4]
def baseStart_346400 : Nat := 118140960795 + 346400 * 2 ^ 59
def prefixEnd_346400 : Nat := 4983230072969 + 3 ^ 40 * 346400 * 2
def baseEnd_346400 : Nat := 39526599715011098245987

theorem tailTrace_346400 : CollatzResearch.WordTrace tailWord_346400 prefixEnd_346400 39526599715011098245987 := by
  unfold tailWord_346400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317122972529717627554327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8422830630039623503405769 6317122972529717627554327)
  ·
    refine ⟨9475684458794576441331491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6317122972529717627554327 9475684458794576441331491)
    ·
      refine ⟨14213526688191864661997237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9475684458794576441331491 14213526688191864661997237)
      ·
        refine ⟨1332518127017987312062241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14213526688191864661997237 1332518127017987312062241)
        ·
          refine ⟨999388595263490484046681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1332518127017987312062241 999388595263490484046681)
          ·
            refine ⟨749541446447617863035011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999388595263490484046681 749541446447617863035011)
            ·
              refine ⟨1124312169671426794552517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749541446447617863035011 1124312169671426794552517)
              ·
                refine ⟨210808531813392523978597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1124312169671426794552517 210808531813392523978597)
                ·
                  refine ⟨39526599715011098245987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 210808531813392523978597 39526599715011098245987)
                  ·
                    rfl

theorem cell22_346400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_346400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346400 prefixEnd_346400 := by exact prefixLift 346400
  have htrace : WordTrace (prefixWord ++ tailWord_346400) baseStart_346400 baseEnd_346400 := by
    simpa [prefixWord, tailWord_346400, baseEnd_346400] using wordTrace_append hprefix tailTrace_346400
  have hstable : (prefixWord ++ tailWord_346400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346400).length < 2 ^ (prefixWord ++ tailWord_346400).sum := by decide
  have hdescent : baseEnd_346400 < baseStart_346400 := by decide
  rcases family_descends (prefixWord ++ tailWord_346400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346428 : List Nat := [2, 2, 2, 2, 1, 2, 5, 6]
def baseStart_346428 : Nat := 118140960795 + 346428 * 2 ^ 59
def prefixEnd_346428 : Nat := 4983230072969 + 3 ^ 40 * 346428 * 2
def baseEnd_346428 : Nat := 13176598235250061670875

theorem tailTrace_346428 : CollatzResearch.WordTrace tailWord_346428 prefixEnd_346428 13176598235250061670875 := by
  unfold tailWord_346428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317633594478998018563969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8423511459305330691418625 6317633594478998018563969)
  ·
    refine ⟨4738225195859248513922977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6317633594478998018563969 4738225195859248513922977)
    ·
      refine ⟨3553668896894436385442233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4738225195859248513922977 3553668896894436385442233)
      ·
        refine ⟨2665251672670827289081675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3553668896894436385442233 2665251672670827289081675)
        ·
          refine ⟨3997877509006240933622513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665251672670827289081675 3997877509006240933622513)
          ·
            refine ⟨2998408131754680700216885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3997877509006240933622513 2998408131754680700216885)
            ·
              refine ⟨281100762352001315645333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2998408131754680700216885 281100762352001315645333)
              ·
                refine ⟨13176598235250061670875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281100762352001315645333 13176598235250061670875)
                ·
                  rfl

theorem cell22_346428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 6].length) (baseStart_346428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346428 prefixEnd_346428 := by exact prefixLift 346428
  have htrace : WordTrace (prefixWord ++ tailWord_346428) baseStart_346428 baseEnd_346428 := by
    simpa [prefixWord, tailWord_346428, baseEnd_346428] using wordTrace_append hprefix tailTrace_346428
  have hstable : (prefixWord ++ tailWord_346428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346428).length < 2 ^ (prefixWord ++ tailWord_346428).sum := by decide
  have hdescent : baseEnd_346428 < baseStart_346428 := by decide
  rcases family_descends (prefixWord ++ tailWord_346428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346430 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_346430 : Nat := 118140960795 + 346430 * 2 ^ 59
def prefixEnd_346430 : Nat := 4983230072969 + 3 ^ 40 * 346430 * 2
def baseEnd_346430 : Nat := 118590068758123216487869

theorem tailTrace_346430 : CollatzResearch.WordTrace tailWord_346430 prefixEnd_346430 118590068758123216487869 := by
  unfold tailWord_346430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579417516868843797337593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8423560089967166919133829 1579417516868843797337593)
  ·
    refine ⟨1184563137651632848003195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1579417516868843797337593 1184563137651632848003195)
    ·
      refine ⟨1776844706477449272004793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1184563137651632848003195 1776844706477449272004793)
      ·
        refine ⟨1332633529858086954003595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1776844706477449272004793 1332633529858086954003595)
        ·
          refine ⟨1998950294787130431005393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332633529858086954003595 1998950294787130431005393)
          ·
            refine ⟨1499212721090347823254045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998950294787130431005393 1499212721090347823254045)
            ·
              refine ⟨562204770408880433720267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1499212721090347823254045 562204770408880433720267)
              ·
                refine ⟨843307155613320650580401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562204770408880433720267 843307155613320650580401)
                ·
                  refine ⟨632480366709990487935301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 843307155613320650580401 632480366709990487935301)
                  ·
                    refine ⟨118590068758123216487869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632480366709990487935301 118590068758123216487869)
                    ·
                      rfl

theorem cell22_346430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_346430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346430 prefixEnd_346430 := by exact prefixLift 346430
  have htrace : WordTrace (prefixWord ++ tailWord_346430) baseStart_346430 baseEnd_346430 := by
    simpa [prefixWord, tailWord_346430, baseEnd_346430] using wordTrace_append hprefix tailTrace_346430
  have hstable : (prefixWord ++ tailWord_346430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346430).length < 2 ^ (prefixWord ++ tailWord_346430).sum := by decide
  have hdescent : baseEnd_346430 < baseStart_346430 := by decide
  rcases family_descends (prefixWord ++ tailWord_346430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346436 : List Nat := [2, 3, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_346436 : Nat := 118140960795 + 346436 * 2 ^ 59
def prefixEnd_346436 : Nat := 4983230072969 + 3 ^ 40 * 346436 * 2
def baseEnd_346436 : Nat := 118592122680741200837851

theorem tailTrace_346436 : CollatzResearch.WordTrace tailWord_346436 prefixEnd_346436 118592122680741200837851 := by
  unfold tailWord_346436
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317779486464506701709581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8423705981952675602279441 6317779486464506701709581)
  ·
    refine ⟨2369167307424190013141093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6317779486464506701709581 2369167307424190013141093)
    ·
      refine ⟨444218870142035627463955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2369167307424190013141093 444218870142035627463955)
      ·
        refine ⟨666328305213053441195933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444218870142035627463955 666328305213053441195933)
        ·
          refine ⟨249873114454895040448475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 666328305213053441195933 249873114454895040448475)
          ·
            refine ⟨374809671682342560672713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249873114454895040448475 374809671682342560672713)
            ·
              refine ⟨281107253761756920504535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374809671682342560672713 281107253761756920504535)
              ·
                refine ⟨421660880642635380756803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281107253761756920504535 421660880642635380756803)
                ·
                  refine ⟨632491320963953071135205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421660880642635380756803 632491320963953071135205)
                  ·
                    refine ⟨118592122680741200837851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632491320963953071135205 118592122680741200837851)
                    ·
                      rfl

theorem cell22_346436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_346436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346436 prefixEnd_346436 := by exact prefixLift 346436
  have htrace : WordTrace (prefixWord ++ tailWord_346436) baseStart_346436 baseEnd_346436 := by
    simpa [prefixWord, tailWord_346436, baseEnd_346436] using wordTrace_append hprefix tailTrace_346436
  have hstable : (prefixWord ++ tailWord_346436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346436).length < 2 ^ (prefixWord ++ tailWord_346436).sum := by decide
  have hdescent : baseEnd_346436 < baseStart_346436 := by decide
  rcases family_descends (prefixWord ++ tailWord_346436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346533 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_346533 : Nat := 118140960795 + 346533 * 2 ^ 59
def prefixEnd_346533 : Nat := 4983230072969 + 3 ^ 40 * 346533 * 2
def baseEnd_346533 : Nat := 118625327763065281162553

theorem tailTrace_346533 : CollatzResearch.WordTrace tailWord_346533 prefixEnd_346533 118625327763065281162553 := by
  unfold tailWord_346533
  simp only [CollatzResearch.WordTrace]
  refine ⟨12639096853577598969700253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8426064569051732646466835 12639096853577598969700253)
  ·
    refine ⟨4739661320091599613637595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12639096853577598969700253 4739661320091599613637595)
    ·
      refine ⟨7109491980137399420456393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4739661320091599613637595 7109491980137399420456393)
      ·
        refine ⟨5332118985103049565342295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7109491980137399420456393 5332118985103049565342295)
        ·
          refine ⟨7998178477654574348013443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332118985103049565342295 7998178477654574348013443)
          ·
            refine ⟨11997267716481861522020165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998178477654574348013443 11997267716481861522020165)
            ·
              refine ⟨2249487696840349035378781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11997267716481861522020165 2249487696840349035378781)
              ·
                refine ⟨843557886315130888267043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2249487696840349035378781 843557886315130888267043)
                ·
                  refine ⟨1265336829472696332400565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 843557886315130888267043 1265336829472696332400565)
                  ·
                    refine ⟨118625327763065281162553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1265336829472696332400565 118625327763065281162553)
                    ·
                      rfl

theorem cell22_346533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_346533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346533 prefixEnd_346533 := by exact prefixLift 346533
  have htrace : WordTrace (prefixWord ++ tailWord_346533) baseStart_346533 baseEnd_346533 := by
    simpa [prefixWord, tailWord_346533, baseEnd_346533] using wordTrace_append hprefix tailTrace_346533
  have hstable : (prefixWord ++ tailWord_346533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346533).length < 2 ^ (prefixWord ++ tailWord_346533).sum := by decide
  have hdescent : baseEnd_346533 < baseStart_346533 := by decide
  rcases family_descends (prefixWord ++ tailWord_346533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346567 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 2, 3]
def baseStart_346567 : Nat := 118140960795 + 346567 * 2 ^ 59
def prefixEnd_346567 : Nat := 4983230072969 + 3 ^ 40 * 346567 * 2
def baseEnd_346567 : Nat := 118636966657900525812449

theorem tailTrace_346567 : CollatzResearch.WordTrace tailWord_346567 prefixEnd_346567 118636966657900525812449 := by
  unfold tailWord_346567
  simp only [CollatzResearch.WordTrace]
  refine ⟨12640336935454422776437955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8426891290302948517625303 12640336935454422776437955)
  ·
    refine ⟨18960505403181634164656933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12640336935454422776437955 18960505403181634164656933)
    ·
      refine ⟨3555094763096556405873175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18960505403181634164656933 3555094763096556405873175)
      ·
        refine ⟨5332642144644834608809763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555094763096556405873175 5332642144644834608809763)
        ·
          refine ⟨7998963216967251913214645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332642144644834608809763 7998963216967251913214645)
          ·
            refine ⟨749902801590679866863873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7998963216967251913214645 749902801590679866863873)
            ·
              refine ⟨562427101193009900147905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749902801590679866863873 562427101193009900147905)
              ·
                refine ⟨421820325894757425110929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562427101193009900147905 421820325894757425110929)
                ·
                  refine ⟨316365244421068068833197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421820325894757425110929 316365244421068068833197)
                  ·
                    refine ⟨118636966657900525812449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 316365244421068068833197 118636966657900525812449)
                    ·
                      rfl

theorem cell22_346567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_346567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346567 prefixEnd_346567 := by exact prefixLift 346567
  have htrace : WordTrace (prefixWord ++ tailWord_346567) baseStart_346567 baseEnd_346567 := by
    simpa [prefixWord, tailWord_346567, baseEnd_346567] using wordTrace_append hprefix tailTrace_346567
  have hstable : (prefixWord ++ tailWord_346567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346567).length < 2 ^ (prefixWord ++ tailWord_346567).sum := by decide
  have hdescent : baseEnd_346567 < baseStart_346567 := by decide
  rcases family_descends (prefixWord ++ tailWord_346567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346580 : List Nat := [2, 4, 1, 2, 2, 1, 3, 7]
def baseStart_346580 : Nat := 118140960795 + 346580 * 2 ^ 59
def prefixEnd_346580 : Nat := 4983230072969 + 3 ^ 40 * 346580 * 2
def baseEnd_346580 : Nat := 13182379647063647248601

theorem tailTrace_346580 : CollatzResearch.WordTrace tailWord_346580 prefixEnd_346580 13182379647063647248601 := by
  unfold tailWord_346580
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320405542203662998330597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8427207389604883997774129 6320405542203662998330597)
  ·
    refine ⟨1185076039163186812186987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6320405542203662998330597 1185076039163186812186987)
    ·
      refine ⟨1777614058744780218280481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1185076039163186812186987 1777614058744780218280481)
      ·
        refine ⟨1333210544058585163710361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1777614058744780218280481 1333210544058585163710361)
        ·
          refine ⟨999907908043938872782771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333210544058585163710361 999907908043938872782771)
          ·
            refine ⟨1499861862065908309174157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999907908043938872782771 1499861862065908309174157)
            ·
              refine ⟨562448198274715615940309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1499861862065908309174157 562448198274715615940309)
              ·
                refine ⟨13182379647063647248601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 562448198274715615940309 13182379647063647248601)
                ·
                  rfl

theorem cell22_346580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 7].length) (baseStart_346580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346580 prefixEnd_346580 := by exact prefixLift 346580
  have htrace : WordTrace (prefixWord ++ tailWord_346580) baseStart_346580 baseEnd_346580 := by
    simpa [prefixWord, tailWord_346580, baseEnd_346580] using wordTrace_append hprefix tailTrace_346580
  have hstable : (prefixWord ++ tailWord_346580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346580).length < 2 ^ (prefixWord ++ tailWord_346580).sum := by decide
  have hdescent : baseEnd_346580 < baseStart_346580 := by decide
  rcases family_descends (prefixWord ++ tailWord_346580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346593 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_346593 : Nat := 118140960795 + 346593 * 2 ^ 59
def prefixEnd_346593 : Nat := 4983230072969 + 3 ^ 40 * 346593 * 2
def baseEnd_346593 : Nat := 118645866989245124662369

theorem tailTrace_346593 : CollatzResearch.WordTrace tailWord_346593 prefixEnd_346593 118645866989245124662369 := by
  unfold tailWord_346593
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641285233360229216884433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8427523488906819477922955 12641285233360229216884433)
  ·
    refine ⟨9480963925020171912663325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12641285233360229216884433 9480963925020171912663325)
    ·
      refine ⟨3555361471882564467248747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9480963925020171912663325 3555361471882564467248747)
      ·
        refine ⟨5333042207823846700873121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555361471882564467248747 5333042207823846700873121)
        ·
          refine ⟨3999781655867885025654841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5333042207823846700873121 3999781655867885025654841)
          ·
            refine ⟨2999836241900913769241131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3999781655867885025654841 2999836241900913769241131)
            ·
              refine ⟨4499754362851370653861697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999836241900913769241131 4499754362851370653861697)
              ·
                refine ⟨3374815772138527990396273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499754362851370653861697 3374815772138527990396273)
                ·
                  refine ⟨2531111829103895992797205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374815772138527990396273 2531111829103895992797205)
                  ·
                    refine ⟨118645866989245124662369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2531111829103895992797205 118645866989245124662369)
                    ·
                      rfl

theorem cell22_346593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_346593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346593 prefixEnd_346593 := by exact prefixLift 346593
  have htrace : WordTrace (prefixWord ++ tailWord_346593) baseStart_346593 baseEnd_346593 := by
    simpa [prefixWord, tailWord_346593, baseEnd_346593] using wordTrace_append hprefix tailTrace_346593
  have hstable : (prefixWord ++ tailWord_346593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346593).length < 2 ^ (prefixWord ++ tailWord_346593).sum := by decide
  have hdescent : baseEnd_346593 < baseStart_346593 := by decide
  rcases family_descends (prefixWord ++ tailWord_346593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346597 : List Nat := [1, 3, 1, 5, 2, 1, 3, 6]
def baseStart_346597 : Nat := 118140960795 + 346597 * 2 ^ 59
def prefixEnd_346597 : Nat := 4983230072969 + 3 ^ 40 * 346597 * 2
def baseEnd_346597 : Nat := 13183026252332271951373

theorem tailTrace_346597 : CollatzResearch.WordTrace tailWord_346597 prefixEnd_346597 13183026252332271951373 := by
  unfold tailWord_346597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641431125345737900030045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8427620750230491933353363 12641431125345737900030045)
  ·
    refine ⟨4740536672004651712511267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12641431125345737900030045 4740536672004651712511267)
    ·
      refine ⟨7110805008006977568766901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4740536672004651712511267 7110805008006977568766901)
      ·
        refine ⟨666637969500654147071897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7110805008006977568766901 666637969500654147071897)
        ·
          refine ⟨499978477125490610303923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666637969500654147071897 499978477125490610303923)
          ·
            refine ⟨749967715688235915455885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499978477125490610303923 749967715688235915455885)
            ·
              refine ⟨281237893383088468295957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749967715688235915455885 281237893383088468295957)
              ·
                refine ⟨13183026252332271951373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281237893383088468295957 13183026252332271951373)
                ·
                  rfl

theorem cell22_346597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 6].length) (baseStart_346597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346597 prefixEnd_346597 := by exact prefixLift 346597
  have htrace : WordTrace (prefixWord ++ tailWord_346597) baseStart_346597 baseEnd_346597 := by
    simpa [prefixWord, tailWord_346597, baseEnd_346597] using wordTrace_append hprefix tailTrace_346597
  have hstable : (prefixWord ++ tailWord_346597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346597).length < 2 ^ (prefixWord ++ tailWord_346597).sum := by decide
  have hdescent : baseEnd_346597 < baseStart_346597 := by decide
  rcases family_descends (prefixWord ++ tailWord_346597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346608 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 7]
def baseStart_346608 : Nat := 118140960795 + 346608 * 2 ^ 59
def prefixEnd_346608 : Nat := 4983230072969 + 3 ^ 40 * 346608 * 2
def baseEnd_346608 : Nat := 39550333931930028512441

theorem tailTrace_346608 : CollatzResearch.WordTrace tailWord_346608 prefixEnd_346608 39550333931930028512441 := by
  unfold tailWord_346608
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320916164152943389340239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8427888218870591185786985 6320916164152943389340239)
  ·
    refine ⟨9481374246229415084010359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6320916164152943389340239 9481374246229415084010359)
    ·
      refine ⟨14222061369344122626015539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9481374246229415084010359 14222061369344122626015539)
      ·
        refine ⟨21333092054016183939023309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14222061369344122626015539 21333092054016183939023309)
        ·
          refine ⟨7999909520256068977133741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21333092054016183939023309 7999909520256068977133741)
          ·
            refine ⟨2999966070096025866425153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7999909520256068977133741 2999966070096025866425153)
            ·
              refine ⟨2249974552572019399818865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2999966070096025866425153 2249974552572019399818865)
              ·
                refine ⟨1687480914429014549864149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249974552572019399818865 1687480914429014549864149)
                ·
                  refine ⟨39550333931930028512441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1687480914429014549864149 39550333931930028512441)
                  ·
                    rfl

theorem cell22_346608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_346608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346608 prefixEnd_346608 := by exact prefixLift 346608
  have htrace : WordTrace (prefixWord ++ tailWord_346608) baseStart_346608 baseEnd_346608 := by
    simpa [prefixWord, tailWord_346608, baseEnd_346608] using wordTrace_append hprefix tailTrace_346608
  have hstable : (prefixWord ++ tailWord_346608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346608).length < 2 ^ (prefixWord ++ tailWord_346608).sum := by decide
  have hdescent : baseEnd_346608 < baseStart_346608 := by decide
  rcases family_descends (prefixWord ++ tailWord_346608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346623 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 4, 5]
def baseStart_346623 : Nat := 118140960795 + 346623 * 2 ^ 59
def prefixEnd_346623 : Nat := 4983230072969 + 3 ^ 40 * 346623 * 2
def baseEnd_346623 : Nat := 118656136602335046412277

theorem tailTrace_346623 : CollatzResearch.WordTrace tailWord_346623 prefixEnd_346623 118656136602335046412277 := by
  unfold tailWord_346623
  simp only [CollatzResearch.WordTrace]
  refine ⟨12642379423251544340476523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8428252948834362893651015 12642379423251544340476523)
  ·
    refine ⟨18963569134877316510714785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12642379423251544340476523 18963569134877316510714785)
    ·
      refine ⟨14222676851157987383036089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18963569134877316510714785 14222676851157987383036089)
      ·
        refine ⟨10667007638368490537277067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14222676851157987383036089 10667007638368490537277067)
        ·
          refine ⟨16000511457552735805915601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10667007638368490537277067 16000511457552735805915601)
          ·
            refine ⟨12000383593164551854436701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16000511457552735805915601 12000383593164551854436701)
            ·
              refine ⟨4500143847436706945413763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12000383593164551854436701 4500143847436706945413763)
              ·
                refine ⟨6750215771155060418120645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500143847436706945413763 6750215771155060418120645)
                ·
                  refine ⟨1265665457091573828397621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6750215771155060418120645 1265665457091573828397621)
                  ·
                    refine ⟨118656136602335046412277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1265665457091573828397621 118656136602335046412277)
                    ·
                      rfl

theorem cell22_346623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_346623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346623 prefixEnd_346623 := by exact prefixLift 346623
  have htrace : WordTrace (prefixWord ++ tailWord_346623) baseStart_346623 baseEnd_346623 := by
    simpa [prefixWord, tailWord_346623, baseEnd_346623] using wordTrace_append hprefix tailTrace_346623
  have hstable : (prefixWord ++ tailWord_346623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346623).length < 2 ^ (prefixWord ++ tailWord_346623).sum := by decide
  have hdescent : baseEnd_346623 < baseStart_346623 := by decide
  rcases family_descends (prefixWord ++ tailWord_346623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346625 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 7]
def baseStart_346625 : Nat := 118140960795 + 346625 * 2 ^ 59
def prefixEnd_346625 : Nat := 4983230072969 + 3 ^ 40 * 346625 * 2
def baseEnd_346625 : Nat := 39552273747735902620757

theorem tailTrace_346625 : CollatzResearch.WordTrace tailWord_346625 prefixEnd_346625 39552273747735902620757 := by
  unfold tailWord_346625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12642452369244298682049329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8428301579496199121366219 12642452369244298682049329)
  ·
    refine ⟨9481839276933224011536997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12642452369244298682049329 9481839276933224011536997)
    ·
      refine ⟨1777844864424979502163187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9481839276933224011536997 1777844864424979502163187)
      ·
        refine ⟨2666767296637469253244781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777844864424979502163187 2666767296637469253244781)
        ·
          refine ⟨1000037736239050969966793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2666767296637469253244781 1000037736239050969966793)
          ·
            refine ⟨750028302179288227475095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000037736239050969966793 750028302179288227475095)
            ·
              refine ⟨1125042453268932341212643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750028302179288227475095 1125042453268932341212643)
              ·
                refine ⟨1687563679903398511818965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125042453268932341212643 1687563679903398511818965)
                ·
                  refine ⟨39552273747735902620757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1687563679903398511818965 39552273747735902620757)
                  ·
                    rfl

theorem cell22_346625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_346625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346625 prefixEnd_346625 := by exact prefixLift 346625
  have htrace : WordTrace (prefixWord ++ tailWord_346625) baseStart_346625 baseEnd_346625 := by
    simpa [prefixWord, tailWord_346625, baseEnd_346625] using wordTrace_append hprefix tailTrace_346625
  have hstable : (prefixWord ++ tailWord_346625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346625).length < 2 ^ (prefixWord ++ tailWord_346625).sum := by decide
  have hdescent : baseEnd_346625 < baseStart_346625 := by decide
  rcases family_descends (prefixWord ++ tailWord_346625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346700 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_346700 : Nat := 118140960795 + 346700 * 2 ^ 59
def prefixEnd_346700 : Nat := 4983230072969 + 3 ^ 40 * 346700 * 2
def baseEnd_346700 : Nat := 118682495275932512237041

theorem tailTrace_346700 : CollatzResearch.WordTrace tailWord_346700 prefixEnd_346700 118682495275932512237041 := by
  unfold tailWord_346700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6322593921986293245514777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8430125229315057660686369 6322593921986293245514777)
  ·
    refine ⟨4741945441489719934136083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6322593921986293245514777 4741945441489719934136083)
    ·
      refine ⟨7112918162234579901204125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4741945441489719934136083 7112918162234579901204125)
      ·
        refine ⟨2667344310837967462951547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7112918162234579901204125 2667344310837967462951547)
        ·
          refine ⟨4001016466256951194427321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667344310837967462951547 4001016466256951194427321)
          ·
            refine ⟨3000762349692713395820491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001016466256951194427321 3000762349692713395820491)
            ·
              refine ⟨4501143524539070093730737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000762349692713395820491 4501143524539070093730737)
              ·
                refine ⟨3375857643404302570298053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501143524539070093730737 3375857643404302570298053)
                ·
                  refine ⟨632973308138306731930885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3375857643404302570298053 632973308138306731930885)
                  ·
                    refine ⟨118682495275932512237041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632973308138306731930885 118682495275932512237041)
                    ·
                      rfl

theorem cell22_346700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_346700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346700 prefixEnd_346700 := by exact prefixLift 346700
  have htrace : WordTrace (prefixWord ++ tailWord_346700) baseStart_346700 baseEnd_346700 := by
    simpa [prefixWord, tailWord_346700, baseEnd_346700] using wordTrace_append hprefix tailTrace_346700
  have hstable : (prefixWord ++ tailWord_346700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346700).length < 2 ^ (prefixWord ++ tailWord_346700).sum := by decide
  have hdescent : baseEnd_346700 < baseStart_346700 := by decide
  rcases family_descends (prefixWord ++ tailWord_346700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346738 : List Nat := [3, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_346738 : Nat := 118140960795 + 346738 * 2 ^ 59
def prefixEnd_346738 : Nat := 4983230072969 + 3 ^ 40 * 346738 * 2
def baseEnd_346738 : Nat := 39565167817504359928975

theorem tailTrace_346738 : CollatzResearch.WordTrace tailWord_346738 prefixEnd_346738 39565167817504359928975 := by
  unfold tailWord_346738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161643454458729745228217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8431049211889945987275245 3161643454458729745228217)
  ·
    refine ⟨2371232590844047308921163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3161643454458729745228217 2371232590844047308921163)
    ·
      refine ⟨3556848886266070963381745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371232590844047308921163 3556848886266070963381745)
      ·
        refine ⟨2667636664699553222536309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3556848886266070963381745 2667636664699553222536309)
        ·
          refine ⟨250090937315583114612779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2667636664699553222536309 250090937315583114612779)
          ·
            refine ⟨375136405973374671919169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250090937315583114612779 375136405973374671919169)
            ·
              refine ⟨281352304480031003939377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375136405973374671919169 281352304480031003939377)
              ·
                refine ⟨211014228360023252954533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281352304480031003939377 211014228360023252954533)
                ·
                  refine ⟨39565167817504359928975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211014228360023252954533 39565167817504359928975)
                  ·
                    rfl

theorem cell22_346738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_346738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346738 prefixEnd_346738 := by exact prefixLift 346738
  have htrace : WordTrace (prefixWord ++ tailWord_346738) baseStart_346738 baseEnd_346738 := by
    simpa [prefixWord, tailWord_346738, baseEnd_346738] using wordTrace_append hprefix tailTrace_346738
  have hstable : (prefixWord ++ tailWord_346738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346738).length < 2 ^ (prefixWord ++ tailWord_346738).sum := by decide
  have hdescent : baseEnd_346738 < baseStart_346738 := by decide
  rcases family_descends (prefixWord ++ tailWord_346738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346745 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_346745 : Nat := 118140960795 + 346745 * 2 ^ 59
def prefixEnd_346745 : Nat := 4983230072969 + 3 ^ 40 * 346745 * 2
def baseEnd_346745 : Nat := 118697899695567394861903

theorem tailTrace_346745 : CollatzResearch.WordTrace tailWord_346745 prefixEnd_346745 118697899695567394861903 := by
  unfold tailWord_346745
  simp only [CollatzResearch.WordTrace]
  refine ⟨12646829128809559176417689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8431219419206372784278459 12646829128809559176417689)
  ·
    refine ⟨9485121846607169382313267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12646829128809559176417689 9485121846607169382313267)
    ·
      refine ⟨14227682769910754073469901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9485121846607169382313267 14227682769910754073469901)
      ·
        refine ⟨5335381038716532777551213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14227682769910754073469901 5335381038716532777551213)
        ·
          refine ⟨2000767889518699791581705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5335381038716532777551213 2000767889518699791581705)
          ·
            refine ⟨1500575917139024843686279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2000767889518699791581705 1500575917139024843686279)
            ·
              refine ⟨2250863875708537265529419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500575917139024843686279 2250863875708537265529419)
              ·
                refine ⟨3376295813562805898294129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250863875708537265529419 3376295813562805898294129)
                ·
                  refine ⟨2532221860172104423720597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376295813562805898294129 2532221860172104423720597)
                  ·
                    refine ⟨118697899695567394861903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2532221860172104423720597 118697899695567394861903)
                    ·
                      rfl

theorem cell22_346745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_346745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346745 prefixEnd_346745 := by exact prefixLift 346745
  have htrace : WordTrace (prefixWord ++ tailWord_346745) baseStart_346745 baseEnd_346745 := by
    simpa [prefixWord, tailWord_346745, baseEnd_346745] using wordTrace_append hprefix tailTrace_346745
  have hstable : (prefixWord ++ tailWord_346745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346745).length < 2 ^ (prefixWord ++ tailWord_346745).sum := by decide
  have hdescent : baseEnd_346745 < baseStart_346745 := by decide
  rcases family_descends (prefixWord ++ tailWord_346745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346749 : List Nat := [1, 4, 1, 1, 6, 1, 1, 7]
def baseStart_346749 : Nat := 118140960795 + 346749 * 2 ^ 59
def prefixEnd_346749 : Nat := 4983230072969 + 3 ^ 40 * 346749 * 2
def baseEnd_346749 : Nat := 13188807664145857529099

theorem tailTrace_346749 : CollatzResearch.WordTrace tailWord_346749 prefixEnd_346749 13188807664145857529099 := by
  unfold tailWord_346749
  simp only [CollatzResearch.WordTrace]
  refine ⟨12646975020795067859563301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8431316680530045239708867 12646975020795067859563301)
  ·
    refine ⟨2371307816399075223668119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12646975020795067859563301 2371307816399075223668119)
    ·
      refine ⟨3556961724598612835502179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371307816399075223668119 3556961724598612835502179)
      ·
        refine ⟨5335442586897919253253269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556961724598612835502179 5335442586897919253253269)
        ·
          refine ⟨250098871260839964996247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5335442586897919253253269 250098871260839964996247)
          ·
            refine ⟨375148306891259947494371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250098871260839964996247 375148306891259947494371)
            ·
              refine ⟨562722460336889921241557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375148306891259947494371 562722460336889921241557)
              ·
                refine ⟨13188807664145857529099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 562722460336889921241557 13188807664145857529099)
                ·
                  rfl

theorem cell22_346749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 7].length) (baseStart_346749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346749 prefixEnd_346749 := by exact prefixLift 346749
  have htrace : WordTrace (prefixWord ++ tailWord_346749) baseStart_346749 baseEnd_346749 := by
    simpa [prefixWord, tailWord_346749, baseEnd_346749] using wordTrace_append hprefix tailTrace_346749
  have hstable : (prefixWord ++ tailWord_346749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346749).length < 2 ^ (prefixWord ++ tailWord_346749).sum := by decide
  have hdescent : baseEnd_346749 < baseStart_346749 := by decide
  rcases family_descends (prefixWord ++ tailWord_346749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346775 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 1, 7]
def baseStart_346775 : Nat := 118140960795 + 346775 * 2 ^ 59
def prefixEnd_346775 : Nat := 4983230072969 + 3 ^ 40 * 346775 * 2
def baseEnd_346775 : Nat := 118708169308657316611811

theorem tailTrace_346775 : CollatzResearch.WordTrace tailWord_346775 prefixEnd_346775 118708169308657316611811 := by
  unfold tailWord_346775
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647923318700874300009779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8431948879133916200006519 12647923318700874300009779)
  ·
    refine ⟨18971884978051311450014669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12647923318700874300009779 18971884978051311450014669)
    ·
      refine ⟨7114456866769241793755501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18971884978051311450014669 7114456866769241793755501)
      ·
        refine ⟨2667921325038465672658313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7114456866769241793755501 2667921325038465672658313)
        ·
          refine ⟨2000940993778849254493735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2667921325038465672658313 2000940993778849254493735)
          ·
            refine ⟨3001411490668273881740603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000940993778849254493735 3001411490668273881740603)
            ·
              refine ⟨4502117236002410822610905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001411490668273881740603 4502117236002410822610905)
              ·
                refine ⟨3376587927001808116958179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4502117236002410822610905 3376587927001808116958179)
                ·
                  refine ⟨5064881890502712175437269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376587927001808116958179 5064881890502712175437269)
                  ·
                    refine ⟨118708169308657316611811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5064881890502712175437269 118708169308657316611811)
                    ·
                      rfl

theorem cell22_346775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_346775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346775 prefixEnd_346775 := by exact prefixLift 346775
  have htrace : WordTrace (prefixWord ++ tailWord_346775) baseStart_346775 baseEnd_346775 := by
    simpa [prefixWord, tailWord_346775, baseEnd_346775] using wordTrace_append hprefix tailTrace_346775
  have hstable : (prefixWord ++ tailWord_346775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346775).length < 2 ^ (prefixWord ++ tailWord_346775).sum := by decide
  have hdescent : baseEnd_346775 < baseStart_346775 := by decide
  rcases family_descends (prefixWord ++ tailWord_346775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346798 : List Nat := [4, 1, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_346798 : Nat := 118140960795 + 346798 * 2 ^ 59
def prefixEnd_346798 : Nat := 4983230072969 + 3 ^ 40 * 346798 * 2
def baseEnd_346798 : Nat := 118716042678692923286741

theorem tailTrace_346798 : CollatzResearch.WordTrace tailWord_346798 prefixEnd_346798 118716042678692923286741 := by
  unfold tailWord_346798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581095274702193653512131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8432508131745032818731365 1581095274702193653512131)
  ·
    refine ⟨2371642912053290480268197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1581095274702193653512131 2371642912053290480268197)
    ·
      refine ⟨444683046009991965050287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2371642912053290480268197 444683046009991965050287)
      ·
        refine ⟨667024569014987947575431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444683046009991965050287 667024569014987947575431)
        ·
          refine ⟨1000536853522481921363147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667024569014987947575431 1000536853522481921363147)
          ·
            refine ⟨1500805280283722882044721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000536853522481921363147 1500805280283722882044721)
            ·
              refine ⟨1125603960212792161533541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500805280283722882044721 1125603960212792161533541)
              ·
                refine ⟨211050742539898530287539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1125603960212792161533541 211050742539898530287539)
                ·
                  refine ⟨316576113809847795431309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211050742539898530287539 316576113809847795431309)
                  ·
                    refine ⟨118716042678692923286741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 316576113809847795431309 118716042678692923286741)
                    ·
                      rfl

theorem cell22_346798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_346798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346798 prefixEnd_346798 := by exact prefixLift 346798
  have htrace : WordTrace (prefixWord ++ tailWord_346798) baseStart_346798 baseEnd_346798 := by
    simpa [prefixWord, tailWord_346798, baseEnd_346798] using wordTrace_append hprefix tailTrace_346798
  have hstable : (prefixWord ++ tailWord_346798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346798).length < 2 ^ (prefixWord ++ tailWord_346798).sum := by decide
  have hdescent : baseEnd_346798 < baseStart_346798 := by decide
  rcases family_descends (prefixWord ++ tailWord_346798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346824 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 1, 4]
def baseStart_346824 : Nat := 118140960795 + 346824 * 2 ^ 59
def prefixEnd_346824 : Nat := 4983230072969 + 3 ^ 40 * 346824 * 2
def baseEnd_346824 : Nat := 118724943010037522136661

theorem tailTrace_346824 : CollatzResearch.WordTrace tailWord_346824 prefixEnd_346824 118724943010037522136661 := by
  unfold tailWord_346824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6324855247761677834271763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8433140330348903779029017 6324855247761677834271763)
  ·
    refine ⟨9487282871642516751407645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6324855247761677834271763 9487282871642516751407645)
    ·
      refine ⟨3557731076865943781777867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9487282871642516751407645 3557731076865943781777867)
      ·
        refine ⟨5336596615298915672666801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557731076865943781777867 5336596615298915672666801)
        ·
          refine ⟨4002447461474186754500101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5336596615298915672666801 4002447461474186754500101)
          ·
            refine ⟨750458899026410016468769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4002447461474186754500101 750458899026410016468769)
            ·
              refine ⟨562844174269807512351577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750458899026410016468769 562844174269807512351577)
              ·
                refine ⟨422133130702355634263683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562844174269807512351577 422133130702355634263683)
                ·
                  refine ⟨633199696053533451395525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422133130702355634263683 633199696053533451395525)
                  ·
                    refine ⟨118724943010037522136661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 633199696053533451395525 118724943010037522136661)
                    ·
                      rfl

theorem cell22_346824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_346824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346824 prefixEnd_346824 := by exact prefixLift 346824
  have htrace : WordTrace (prefixWord ++ tailWord_346824) baseStart_346824 baseEnd_346824 := by
    simpa [prefixWord, tailWord_346824, baseEnd_346824] using wordTrace_append hprefix tailTrace_346824
  have hstable : (prefixWord ++ tailWord_346824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346824).length < 2 ^ (prefixWord ++ tailWord_346824).sum := by decide
  have hdescent : baseEnd_346824 < baseStart_346824 := by decide
  rcases family_descends (prefixWord ++ tailWord_346824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346839 : List Nat := [1, 1, 3, 2, 1, 4, 3, 3, 4]
def baseStart_346839 : Nat := 118140960795 + 346839 * 2 ^ 59
def prefixEnd_346839 : Nat := 4983230072969 + 3 ^ 40 * 346839 * 2
def baseEnd_346839 : Nat := 39576692605527494337205

theorem tailTrace_346839 : CollatzResearch.WordTrace tailWord_346839 prefixEnd_346839 39576692605527494337205 := by
  unfold tailWord_346839
  simp only [CollatzResearch.WordTrace]
  refine ⟨12650257590469013230339571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8433505060312675486893047 12650257590469013230339571)
  ·
    refine ⟨18975386385703519845509357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12650257590469013230339571 18975386385703519845509357)
    ·
      refine ⟨7115769894638819942066009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18975386385703519845509357 7115769894638819942066009)
      ·
        refine ⟨5336827420979114956549507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7115769894638819942066009 5336827420979114956549507)
        ·
          refine ⟨8005241131468672434824261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336827420979114956549507 8005241131468672434824261)
          ·
            refine ⟨1500982712150376081529549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8005241131468672434824261 1500982712150376081529549)
            ·
              refine ⟨562868517056391030573581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1500982712150376081529549 562868517056391030573581)
              ·
                refine ⟨211075693896146636465093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562868517056391030573581 211075693896146636465093)
                ·
                  refine ⟨39576692605527494337205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211075693896146636465093 39576692605527494337205)
                  ·
                    rfl

theorem cell22_346839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 4].length) (baseStart_346839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346839 prefixEnd_346839 := by exact prefixLift 346839
  have htrace : WordTrace (prefixWord ++ tailWord_346839) baseStart_346839 baseEnd_346839 := by
    simpa [prefixWord, tailWord_346839, baseEnd_346839] using wordTrace_append hprefix tailTrace_346839
  have hstable : (prefixWord ++ tailWord_346839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346839).length < 2 ^ (prefixWord ++ tailWord_346839).sum := by decide
  have hdescent : baseEnd_346839 < baseStart_346839 := by decide
  rcases family_descends (prefixWord ++ tailWord_346839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346852 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_346852 : Nat := 118140960795 + 346852 * 2 ^ 59
def prefixEnd_346852 : Nat := 4983230072969 + 3 ^ 40 * 346852 * 2
def baseEnd_346852 : Nat := 118734527982254782436575

theorem tailTrace_346852 : CollatzResearch.WordTrace tailWord_346852 prefixEnd_346852 118734527982254782436575 := by
  unfold tailWord_346852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325365869710958225281405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8433821159614610967041873 6325365869710958225281405)
  ·
    refine ⟨2372012201141609334480527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6325365869710958225281405 2372012201141609334480527)
    ·
      refine ⟨3558018301712414001720791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2372012201141609334480527 3558018301712414001720791)
      ·
        refine ⟨5337027452568621002581187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558018301712414001720791 5337027452568621002581187)
        ·
          refine ⟨8005541178852931503871781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337027452568621002581187 8005541178852931503871781)
          ·
            refine ⟨1501038971034924656975959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8005541178852931503871781 1501038971034924656975959)
            ·
              refine ⟨2251558456552386985463939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501038971034924656975959 2251558456552386985463939)
              ·
                refine ⟨3377337684828580478195909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251558456552386985463939 3377337684828580478195909)
                ·
                  refine ⟨633250815905358839661733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3377337684828580478195909 633250815905358839661733)
                  ·
                    refine ⟨118734527982254782436575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 633250815905358839661733 118734527982254782436575)
                    ·
                      rfl

theorem cell22_346852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_346852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346852 prefixEnd_346852 := by exact prefixLift 346852
  have htrace : WordTrace (prefixWord ++ tailWord_346852) baseStart_346852 baseEnd_346852 := by
    simpa [prefixWord, tailWord_346852, baseEnd_346852] using wordTrace_append hprefix tailTrace_346852
  have hstable : (prefixWord ++ tailWord_346852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346852).length < 2 ^ (prefixWord ++ tailWord_346852).sum := by decide
  have hdescent : baseEnd_346852 < baseStart_346852 := by decide
  rcases family_descends (prefixWord ++ tailWord_346852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346856 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 6]
def baseStart_346856 : Nat := 118140960795 + 346856 * 2 ^ 59
def prefixEnd_346856 : Nat := 4983230072969 + 3 ^ 40 * 346856 * 2
def baseEnd_346856 : Nat := 39578632421333368445521

theorem tailTrace_346856 : CollatzResearch.WordTrace tailWord_346856 prefixEnd_346856 39578632421333368445521 := by
  unfold tailWord_346856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325438815703712566854211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8433918420938283422472281 6325438815703712566854211)
  ·
    refine ⟨9488158223555568850281317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6325438815703712566854211 9488158223555568850281317)
    ·
      refine ⟨1779029666916669159427747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9488158223555568850281317 1779029666916669159427747)
      ·
        refine ⟨2668544500375003739141621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779029666916669159427747 2668544500375003739141621)
        ·
          refine ⟨250176046910156600544527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2668544500375003739141621 250176046910156600544527)
          ·
            refine ⟨375264070365234900816791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250176046910156600544527 375264070365234900816791)
            ·
              refine ⟨562896105547852351225187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375264070365234900816791 562896105547852351225187)
              ·
                refine ⟨844344158321778526837781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562896105547852351225187 844344158321778526837781)
                ·
                  refine ⟨39578632421333368445521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 844344158321778526837781 39578632421333368445521)
                  ·
                    rfl

theorem cell22_346856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_346856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346856 prefixEnd_346856 := by exact prefixLift 346856
  have htrace : WordTrace (prefixWord ++ tailWord_346856) baseStart_346856 baseEnd_346856 := by
    simpa [prefixWord, tailWord_346856, baseEnd_346856] using wordTrace_append hprefix tailTrace_346856
  have hstable : (prefixWord ++ tailWord_346856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346856).length < 2 ^ (prefixWord ++ tailWord_346856).sum := by decide
  have hdescent : baseEnd_346856 < baseStart_346856 := by decide
  rcases family_descends (prefixWord ++ tailWord_346856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346987 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 1, 6]
def baseStart_346987 : Nat := 118140960795 + 346987 * 2 ^ 59
def prefixEnd_346987 : Nat := 4983230072969 + 3 ^ 40 * 346987 * 2
def baseEnd_346987 : Nat := 118780741241159430311161

theorem tailTrace_346987 : CollatzResearch.WordTrace tailWord_346987 prefixEnd_346987 118780741241159430311161 := by
  unfold tailWord_346987
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655655593932834506727215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8437103729288556337818143 12655655593932834506727215)
  ·
    refine ⟨18983483390899251760090823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12655655593932834506727215 18983483390899251760090823)
    ·
      refine ⟨28475225086348877640136235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18983483390899251760090823 28475225086348877640136235)
      ·
        refine ⟨42712837629523316460204353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28475225086348877640136235 42712837629523316460204353)
        ·
          refine ⟨32034628222142487345153265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42712837629523316460204353 32034628222142487345153265)
          ·
            refine ⟨24025971166606865508864949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32034628222142487345153265 24025971166606865508864949)
            ·
              refine ⟨2252434796869393641456089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24025971166606865508864949 2252434796869393641456089)
              ·
                refine ⟨1689326097652045231092067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252434796869393641456089 1689326097652045231092067)
                ·
                  refine ⟨2533989146478067846638101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689326097652045231092067 2533989146478067846638101)
                  ·
                    refine ⟨118780741241159430311161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2533989146478067846638101 118780741241159430311161)
                    ·
                      rfl

theorem cell22_346987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_346987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_346987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_346987 prefixEnd_346987 := by exact prefixLift 346987
  have htrace : WordTrace (prefixWord ++ tailWord_346987) baseStart_346987 baseEnd_346987 := by
    simpa [prefixWord, tailWord_346987, baseEnd_346987] using wordTrace_append hprefix tailTrace_346987
  have hstable : (prefixWord ++ tailWord_346987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346987).length < 2 ^ (prefixWord ++ tailWord_346987).sum := by decide
  have hdescent : baseEnd_346987 < baseStart_346987 := by decide
  rcases family_descends (prefixWord ++ tailWord_346987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347036 : List Nat := [2, 2, 3, 3, 2, 1, 2, 7]
def baseStart_347036 : Nat := 118140960795 + 347036 * 2 ^ 59
def prefixEnd_347036 : Nat := 4983230072969 + 3 ^ 40 * 347036 * 2
def baseEnd_347036 : Nat := 13199723882504403981779

theorem tailTrace_347036 : CollatzResearch.WordTrace tailWord_347036 prefixEnd_347036 13199723882504403981779 := by
  unfold tailWord_347036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328721385377657937630481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8438295180503543916840641 6328721385377657937630481)
  ·
    refine ⟨4746541039033243453222861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6328721385377657937630481 4746541039033243453222861)
    ·
      refine ⟨1779952889637466294958573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4746541039033243453222861 1779952889637466294958573)
      ·
        refine ⟨667482333614049860609465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1779952889637466294958573 667482333614049860609465)
        ·
          refine ⟨500611750210537395457099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667482333614049860609465 500611750210537395457099)
          ·
            refine ⟨750917625315806093185649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500611750210537395457099 750917625315806093185649)
            ·
              refine ⟨563188218986854569889237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750917625315806093185649 563188218986854569889237)
              ·
                refine ⟨13199723882504403981779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 563188218986854569889237 13199723882504403981779)
                ·
                  rfl

theorem cell22_347036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 7].length) (baseStart_347036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347036 prefixEnd_347036 := by exact prefixLift 347036
  have htrace : WordTrace (prefixWord ++ tailWord_347036) baseStart_347036 baseEnd_347036 := by
    simpa [prefixWord, tailWord_347036, baseEnd_347036] using wordTrace_append hprefix tailTrace_347036
  have hstable : (prefixWord ++ tailWord_347036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347036).length < 2 ^ (prefixWord ++ tailWord_347036).sum := by decide
  have hdescent : baseEnd_347036 < baseStart_347036 := by decide
  rcases family_descends (prefixWord ++ tailWord_347036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347111 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 3, 4]
def baseStart_347111 : Nat := 118140960795 + 347111 * 2 ^ 59
def prefixEnd_347111 : Nat := 4983230072969 + 3 ^ 40 * 347111 * 2
def baseEnd_347111 : Nat := 118823188975264440210781

theorem tailTrace_347111 : CollatzResearch.WordTrace tailWord_347111 prefixEnd_347111 118823188975264440210781 := by
  unfold tailWord_347111
  simp only [CollatzResearch.WordTrace]
  refine ⟨12660178245483603684241187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8440118830322402456160791 12660178245483603684241187)
  ·
    refine ⟨18990267368225405526361781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12660178245483603684241187 18990267368225405526361781)
    ·
      refine ⟨1780337565771131768096417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18990267368225405526361781 1780337565771131768096417)
      ·
        refine ⟨1335253174328348826072313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1780337565771131768096417 1335253174328348826072313)
        ·
          refine ⟨1001439880746261619554235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335253174328348826072313 1001439880746261619554235)
          ·
            refine ⟨1502159821119392429331353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001439880746261619554235 1502159821119392429331353)
            ·
              refine ⟨1126619865839544321998515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502159821119392429331353 1126619865839544321998515)
              ·
                refine ⟨1689929798759316482997773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126619865839544321998515 1689929798759316482997773)
                ·
                  refine ⟨633723674534743681124165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1689929798759316482997773 633723674534743681124165)
                  ·
                    refine ⟨118823188975264440210781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 633723674534743681124165 118823188975264440210781)
                    ·
                      rfl

theorem cell22_347111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_347111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347111 prefixEnd_347111 := by exact prefixLift 347111
  have htrace : WordTrace (prefixWord ++ tailWord_347111) baseStart_347111 baseEnd_347111 := by
    simpa [prefixWord, tailWord_347111, baseEnd_347111] using wordTrace_append hprefix tailTrace_347111
  have hstable : (prefixWord ++ tailWord_347111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347111).length < 2 ^ (prefixWord ++ tailWord_347111).sum := by decide
  have hdescent : baseEnd_347111 < baseStart_347111 := by decide
  rcases family_descends (prefixWord ++ tailWord_347111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347141 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_347141 : Nat := 118140960795 + 347141 * 2 ^ 59
def prefixEnd_347141 : Nat := 4983230072969 + 3 ^ 40 * 347141 * 2
def baseEnd_347141 : Nat := 118833458588354361960689

theorem tailTrace_347141 : CollatzResearch.WordTrace tailWord_347141 prefixEnd_347141 118833458588354361960689 := by
  unfold tailWord_347141
  simp only [CollatzResearch.WordTrace]
  refine ⟨12661272435374918807833277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8440848290249945871888851 12661272435374918807833277)
  ·
    refine ⟨4747977163265594552937479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12661272435374918807833277 4747977163265594552937479)
    ·
      refine ⟨7121965744898391829406219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4747977163265594552937479 7121965744898391829406219)
      ·
        refine ⟨10682948617347587744109329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7121965744898391829406219 10682948617347587744109329)
        ·
          refine ⟨8012211463010690808081997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10682948617347587744109329 8012211463010690808081997)
          ·
            refine ⟨3004579298629009053030749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8012211463010690808081997 3004579298629009053030749)
            ·
              refine ⟨1126717236985878394886531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3004579298629009053030749 1126717236985878394886531)
              ·
                refine ⟨1690075855478817592329797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126717236985878394886531 1690075855478817592329797)
                ·
                  refine ⟨316889222902278298561837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690075855478817592329797 316889222902278298561837)
                  ·
                    refine ⟨118833458588354361960689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 316889222902278298561837 118833458588354361960689)
                    ·
                      rfl

theorem cell22_347141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_347141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347141 prefixEnd_347141 := by exact prefixLift 347141
  have htrace : WordTrace (prefixWord ++ tailWord_347141) baseStart_347141 baseEnd_347141 := by
    simpa [prefixWord, tailWord_347141, baseEnd_347141] using wordTrace_append hprefix tailTrace_347141
  have hstable : (prefixWord ++ tailWord_347141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347141).length < 2 ^ (prefixWord ++ tailWord_347141).sum := by decide
  have hdescent : baseEnd_347141 < baseStart_347141 := by decide
  rcases family_descends (prefixWord ++ tailWord_347141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347171 : List Nat := [1, 1, 1, 4, 3, 2, 4, 6]
def baseStart_347171 : Nat := 118140960795 + 347171 * 2 ^ 59
def prefixEnd_347171 : Nat := 4983230072969 + 3 ^ 40 * 347171 * 2
def baseEnd_347171 : Nat := 13204858689049364856733

theorem tailTrace_347171 : CollatzResearch.WordTrace tailWord_347171 prefixEnd_347171 13204858689049364856733 := by
  unfold tailWord_347171
  simp only [CollatzResearch.WordTrace]
  refine ⟨12662366625266233931425367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8441577750177489287616911 12662366625266233931425367)
  ·
    refine ⟨18993549937899350897138051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12662366625266233931425367 18993549937899350897138051)
    ·
      refine ⟨28490324906849026345707077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18993549937899350897138051 28490324906849026345707077)
      ·
        refine ⟨5341935920034192439820077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28490324906849026345707077 5341935920034192439820077)
        ·
          refine ⟨2003225970012822164932529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5341935920034192439820077 2003225970012822164932529)
          ·
            refine ⟨1502419477509616623699397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003225970012822164932529 1502419477509616623699397)
            ·
              refine ⟨281703652033053116943637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1502419477509616623699397 281703652033053116943637)
              ·
                refine ⟨13204858689049364856733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281703652033053116943637 13204858689049364856733)
                ·
                  rfl

theorem cell22_347171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 6].length) (baseStart_347171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347171 prefixEnd_347171 := by exact prefixLift 347171
  have htrace : WordTrace (prefixWord ++ tailWord_347171) baseStart_347171 baseEnd_347171 := by
    simpa [prefixWord, tailWord_347171, baseEnd_347171] using wordTrace_append hprefix tailTrace_347171
  have hstable : (prefixWord ++ tailWord_347171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347171).length < 2 ^ (prefixWord ++ tailWord_347171).sum := by decide
  have hdescent : baseEnd_347171 < baseStart_347171 := by decide
  rcases family_descends (prefixWord ++ tailWord_347171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347188 : List Nat := [2, 5, 1, 2, 1, 3, 8]
def baseStart_347188 : Nat := 118140960795 + 347188 * 2 ^ 59
def prefixEnd_347188 : Nat := 4983230072969 + 3 ^ 40 * 347188 * 2
def baseEnd_347188 : Nat := 4401835098105996519835

theorem tailTrace_347188 : CollatzResearch.WordTrace tailWord_347188 prefixEnd_347188 4401835098105996519835 := by
  unfold tailWord_347188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331493333102322917397109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8441991110803097223196145 6331493333102322917397109)
  ·
    refine ⟨593577499978342773505979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6331493333102322917397109 593577499978342773505979)
    ·
      refine ⟨890366249967514160258969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593577499978342773505979 890366249967514160258969)
      ·
        refine ⟨667774687475635620194227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 890366249967514160258969 667774687475635620194227)
        ·
          refine ⟨1001662031213453430291341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667774687475635620194227 1001662031213453430291341)
          ·
            refine ⟨375623261705045036359253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1001662031213453430291341 375623261705045036359253)
            ·
              refine ⟨4401835098105996519835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 375623261705045036359253 4401835098105996519835)
              ·
                rfl

theorem cell22_347188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 8].length) (baseStart_347188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347188 prefixEnd_347188 := by exact prefixLift 347188
  have htrace : WordTrace (prefixWord ++ tailWord_347188) baseStart_347188 baseEnd_347188 := by
    simpa [prefixWord, tailWord_347188, baseEnd_347188] using wordTrace_append hprefix tailTrace_347188
  have hstable : (prefixWord ++ tailWord_347188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347188).length < 2 ^ (prefixWord ++ tailWord_347188).sum := by decide
  have hdescent : baseEnd_347188 < baseStart_347188 := by decide
  rcases family_descends (prefixWord ++ tailWord_347188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347261 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 6]
def baseStart_347261 : Nat := 118140960795 + 347261 * 2 ^ 59
def prefixEnd_347261 : Nat := 4983230072969 + 3 ^ 40 * 347261 * 2
def baseEnd_347261 : Nat := 39624845680238016320107

theorem tailTrace_347261 : CollatzResearch.WordTrace tailWord_347261 prefixEnd_347261 39624845680238016320107 := by
  unfold tailWord_347261
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665649194940179302201637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8443766129960119534801091 12665649194940179302201637)
  ·
    refine ⟨2374809224051283619162807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12665649194940179302201637 2374809224051283619162807)
    ·
      refine ⟨3562213836076925428744211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374809224051283619162807 3562213836076925428744211)
      ·
        refine ⟨5343320754115388143116317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562213836076925428744211 5343320754115388143116317)
        ·
          refine ⟨2003745282793270553668619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5343320754115388143116317 2003745282793270553668619)
          ·
            refine ⟨3005617924189905830502929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003745282793270553668619 3005617924189905830502929)
            ·
              refine ⟨2254213443142429372877197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005617924189905830502929 2254213443142429372877197)
              ·
                refine ⟨845330041178411014828949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2254213443142429372877197 845330041178411014828949)
                ·
                  refine ⟨39624845680238016320107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 845330041178411014828949 39624845680238016320107)
                  ·
                    rfl

theorem cell22_347261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_347261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347261 prefixEnd_347261 := by exact prefixLift 347261
  have htrace : WordTrace (prefixWord ++ tailWord_347261) baseStart_347261 baseEnd_347261 := by
    simpa [prefixWord, tailWord_347261, baseEnd_347261] using wordTrace_append hprefix tailTrace_347261
  have hstable : (prefixWord ++ tailWord_347261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347261).length < 2 ^ (prefixWord ++ tailWord_347261).sum := by decide
  have hdescent : baseEnd_347261 < baseStart_347261 := by decide
  rcases family_descends (prefixWord ++ tailWord_347261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347278 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_347278 : Nat := 118140960795 + 347278 * 2 ^ 59
def prefixEnd_347278 : Nat := 4983230072969 + 3 ^ 40 * 347278 * 2
def baseEnd_347278 : Nat := 39626785496043890428423

theorem tailTrace_347278 : CollatzResearch.WordTrace tailWord_347278 prefixEnd_347278 39626785496043890428423 := by
  unfold tailWord_347278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583283654484823900696311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8444179490585727470380325 1583283654484823900696311)
  ·
    refine ⟨2374925481727235851044467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1583283654484823900696311 2374925481727235851044467)
    ·
      refine ⟨3562388222590853776566701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374925481727235851044467 3562388222590853776566701)
      ·
        refine ⟨1335895583471570166212513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3562388222590853776566701 1335895583471570166212513)
        ·
          refine ⟨1001921687603677624659385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335895583471570166212513 1001921687603677624659385)
          ·
            refine ⟨751441265702758218494539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001921687603677624659385 751441265702758218494539)
            ·
              refine ⟨1127161898554137327741809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751441265702758218494539 1127161898554137327741809)
              ·
                refine ⟨845371423915602995806357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127161898554137327741809 845371423915602995806357)
                ·
                  refine ⟨39626785496043890428423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 845371423915602995806357 39626785496043890428423)
                  ·
                    rfl

theorem cell22_347278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_347278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347278 prefixEnd_347278 := by exact prefixLift 347278
  have htrace : WordTrace (prefixWord ++ tailWord_347278) baseStart_347278 baseEnd_347278 := by
    simpa [prefixWord, tailWord_347278, baseEnd_347278] using wordTrace_append hprefix tailTrace_347278
  have hstable : (prefixWord ++ tailWord_347278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347278).length < 2 ^ (prefixWord ++ tailWord_347278).sum := by decide
  have hdescent : baseEnd_347278 < baseStart_347278 := by decide
  rcases family_descends (prefixWord ++ tailWord_347278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347293 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_347293 : Nat := 118140960795 + 347293 * 2 ^ 59
def prefixEnd_347293 : Nat := 4983230072969 + 3 ^ 40 * 347293 * 2
def baseEnd_347293 : Nat := 118885491294676632160223

theorem tailTrace_347293 : CollatzResearch.WordTrace tailWord_347293 prefixEnd_347293 118885491294676632160223 := by
  unfold tailWord_347293
  simp only [CollatzResearch.WordTrace]
  refine ⟨12666816330824248767366533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8444544220549499178244355 12666816330824248767366533)
  ·
    refine ⟨2375028062029546643881225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12666816330824248767366533 2375028062029546643881225)
    ·
      refine ⟨1781271046522159982910919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375028062029546643881225 1781271046522159982910919)
      ·
        refine ⟨2671906569783239974366379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781271046522159982910919 2671906569783239974366379)
        ·
          refine ⟨4007859854674859961549569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671906569783239974366379 4007859854674859961549569)
          ·
            refine ⟨3005894891006144971162177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007859854674859961549569 3005894891006144971162177)
            ·
              refine ⟨2254421168254608728371633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005894891006144971162177 2254421168254608728371633)
              ·
                refine ⟨1690815876190956546278725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254421168254608728371633 1690815876190956546278725)
                ·
                  refine ⟨317027976785804352427261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690815876190956546278725 317027976785804352427261)
                  ·
                    refine ⟨118885491294676632160223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317027976785804352427261 118885491294676632160223)
                    ·
                      rfl

theorem cell22_347293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_347293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347293 prefixEnd_347293 := by exact prefixLift 347293
  have htrace : WordTrace (prefixWord ++ tailWord_347293) baseStart_347293 baseEnd_347293 := by
    simpa [prefixWord, tailWord_347293, baseEnd_347293] using wordTrace_append hprefix tailTrace_347293
  have hstable : (prefixWord ++ tailWord_347293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347293).length < 2 ^ (prefixWord ++ tailWord_347293).sum := by decide
  have hdescent : baseEnd_347293 < baseStart_347293 := by decide
  rcases family_descends (prefixWord ++ tailWord_347293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347336 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_347336 : Nat := 118140960795 + 347336 * 2 ^ 59
def prefixEnd_347336 : Nat := 4983230072969 + 3 ^ 40 * 347336 * 2
def baseEnd_347336 : Nat := 118900211073438853335091

theorem tailTrace_347336 : CollatzResearch.WordTrace tailWord_347336 prefixEnd_347336 118900211073438853335091 := by
  unfold tailWord_347336
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334192334834233555590931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8445589779778978074121241 6334192334834233555590931)
  ·
    refine ⟨9501288502251350333386397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6334192334834233555590931 9501288502251350333386397)
    ·
      refine ⟨3562983188344256375019899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9501288502251350333386397 3562983188344256375019899)
      ·
        refine ⟨5344474782516384562529849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3562983188344256375019899 5344474782516384562529849)
        ·
          refine ⟨4008356086887288421897387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5344474782516384562529849 4008356086887288421897387)
          ·
            refine ⟨6012534130330932632846081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008356086887288421897387 6012534130330932632846081)
            ·
              refine ⟨4509400597748199474634561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6012534130330932632846081 4509400597748199474634561)
              ·
                refine ⟨3382050448311149605975921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4509400597748199474634561 3382050448311149605975921)
                ·
                  refine ⟨2536537836233362204481941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382050448311149605975921 2536537836233362204481941)
                  ·
                    refine ⟨118900211073438853335091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2536537836233362204481941 118900211073438853335091)
                    ·
                      rfl

theorem cell22_347336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_347336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347336 prefixEnd_347336 := by exact prefixLift 347336
  have htrace : WordTrace (prefixWord ++ tailWord_347336) baseStart_347336 baseEnd_347336 := by
    simpa [prefixWord, tailWord_347336, baseEnd_347336] using wordTrace_append hprefix tailTrace_347336
  have hstable : (prefixWord ++ tailWord_347336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347336).length < 2 ^ (prefixWord ++ tailWord_347336).sum := by decide
  have hdescent : baseEnd_347336 < baseStart_347336 := by decide
  rcases family_descends (prefixWord ++ tailWord_347336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347351 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 7]
def baseStart_347351 : Nat := 118140960795 + 347351 * 2 ^ 59
def prefixEnd_347351 : Nat := 4983230072969 + 3 ^ 40 * 347351 * 2
def baseEnd_347351 : Nat := 39635115293327938070015

theorem tailTrace_347351 : CollatzResearch.WordTrace tailWord_347351 prefixEnd_347351 39635115293327938070015 := by
  unfold tailWord_347351
  simp only [CollatzResearch.WordTrace]
  refine ⟨12668931764614124672977907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8445954509742749781985271 12668931764614124672977907)
  ·
    refine ⟨19003397646921187009466861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12668931764614124672977907 19003397646921187009466861)
    ·
      refine ⟨7126274117595445128550073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19003397646921187009466861 7126274117595445128550073)
      ·
        refine ⟨5344705588196583846412555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7126274117595445128550073 5344705588196583846412555)
        ·
          refine ⟨8017058382294875769618833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344705588196583846412555 8017058382294875769618833)
          ·
            refine ⟨6012793786721156827214125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8017058382294875769618833 6012793786721156827214125)
            ·
              refine ⟨2254797670020433810205297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6012793786721156827214125 2254797670020433810205297)
              ·
                refine ⟨1691098252515325357653973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254797670020433810205297 1691098252515325357653973)
                ·
                  refine ⟨39635115293327938070015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1691098252515325357653973 39635115293327938070015)
                  ·
                    rfl

theorem cell22_347351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 7].length) (baseStart_347351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347351 prefixEnd_347351 := by exact prefixLift 347351
  have htrace : WordTrace (prefixWord ++ tailWord_347351) baseStart_347351 baseEnd_347351 := by
    simpa [prefixWord, tailWord_347351, baseEnd_347351] using wordTrace_append hprefix tailTrace_347351
  have hstable : (prefixWord ++ tailWord_347351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347351).length < 2 ^ (prefixWord ++ tailWord_347351).sum := by decide
  have hdescent : baseEnd_347351 < baseStart_347351 := by decide
  rcases family_descends (prefixWord ++ tailWord_347351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347368 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 5]
def baseStart_347368 : Nat := 118140960795 + 347368 * 2 ^ 59
def prefixEnd_347368 : Nat := 4983230072969 + 3 ^ 40 * 347368 * 2
def baseEnd_347368 : Nat := 39637055109133812178331

theorem tailTrace_347368 : CollatzResearch.WordTrace tailWord_347368 prefixEnd_347368 39637055109133812178331 := by
  unfold tailWord_347368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334775902776268288173379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8446367870368357717564505 6334775902776268288173379)
  ·
    refine ⟨9502163854164402432260069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6334775902776268288173379 9502163854164402432260069)
    ·
      refine ⟨1781655722655825456048763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9502163854164402432260069 1781655722655825456048763)
      ·
        refine ⟨2672483583983738184073145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781655722655825456048763 2672483583983738184073145)
        ·
          refine ⟨2004362687987803638054859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2672483583983738184073145 2004362687987803638054859)
          ·
            refine ⟨3006544031981705457082289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004362687987803638054859 3006544031981705457082289)
            ·
              refine ⟨2254908023986279092811717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3006544031981705457082289 2254908023986279092811717)
              ·
                refine ⟨422795254497427329902197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2254908023986279092811717 422795254497427329902197)
                ·
                  refine ⟨39637055109133812178331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 422795254497427329902197 39637055109133812178331)
                  ·
                    rfl

theorem cell22_347368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_347368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347368 prefixEnd_347368 := by exact prefixLift 347368
  have htrace : WordTrace (prefixWord ++ tailWord_347368) baseStart_347368 baseEnd_347368 := by
    simpa [prefixWord, tailWord_347368, baseEnd_347368] using wordTrace_append hprefix tailTrace_347368
  have hstable : (prefixWord ++ tailWord_347368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347368).length < 2 ^ (prefixWord ++ tailWord_347368).sum := by decide
  have hdescent : baseEnd_347368 < baseStart_347368 := by decide
  rcases family_descends (prefixWord ++ tailWord_347368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347428 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_347428 : Nat := 118140960795 + 347428 * 2 ^ 59
def prefixEnd_347428 : Nat := 4983230072969 + 3 ^ 40 * 347428 * 2
def baseEnd_347428 : Nat := 118931704553581280034809

theorem tailTrace_347428 : CollatzResearch.WordTrace tailWord_347428 prefixEnd_347428 118931704553581280034809 := by
  unfold tailWord_347428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6335870092667583411765469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8447826790223444549020625 6335870092667583411765469)
  ·
    refine ⟨2375951284750343779412051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6335870092667583411765469 2375951284750343779412051)
    ·
      refine ⟨3563926927125515669118077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2375951284750343779412051 3563926927125515669118077)
      ·
        refine ⟨1336472597672068375919279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3563926927125515669118077 1336472597672068375919279)
        ·
          refine ⟨2004708896508102563878919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336472597672068375919279 2004708896508102563878919)
          ·
            refine ⟨3007063344762153845818379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004708896508102563878919 3007063344762153845818379)
            ·
              refine ⟨4510595017143230768727569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007063344762153845818379 4510595017143230768727569)
              ·
                refine ⟨3382946262857423076545677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510595017143230768727569 3382946262857423076545677)
                ·
                  refine ⟨1268604848571533653704629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3382946262857423076545677 1268604848571533653704629)
                  ·
                    refine ⟨118931704553581280034809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1268604848571533653704629 118931704553581280034809)
                    ·
                      rfl

theorem cell22_347428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_347428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347428 prefixEnd_347428 := by exact prefixLift 347428
  have htrace : WordTrace (prefixWord ++ tailWord_347428) baseStart_347428 baseEnd_347428 := by
    simpa [prefixWord, tailWord_347428, baseEnd_347428] using wordTrace_append hprefix tailTrace_347428
  have hstable : (prefixWord ++ tailWord_347428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347428).length < 2 ^ (prefixWord ++ tailWord_347428).sum := by decide
  have hdescent : baseEnd_347428 < baseStart_347428 := by decide
  rcases family_descends (prefixWord ++ tailWord_347428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347445 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_347445 : Nat := 118140960795 + 347445 * 2 ^ 59
def prefixEnd_347445 : Nat := 4983230072969 + 3 ^ 40 * 347445 * 2
def baseEnd_347445 : Nat := 118937524000998902359757

theorem tailTrace_347445 : CollatzResearch.WordTrace tailWord_347445 prefixEnd_347445 118937524000998902359757 := by
  unfold tailWord_347445
  simp only [CollatzResearch.WordTrace]
  refine ⟨12672360226273578726899789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8448240150849052484599859 12672360226273578726899789)
  ·
    refine ⟨4752135084852592022587421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12672360226273578726899789 4752135084852592022587421)
    ·
      refine ⟨1782050656819722008470283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4752135084852592022587421 1782050656819722008470283)
      ·
        refine ⟨2673075985229583012705425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782050656819722008470283 2673075985229583012705425)
        ·
          refine ⟨2004806988922187259529069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673075985229583012705425 2004806988922187259529069)
          ·
            refine ⟨751802620845820222323401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2004806988922187259529069 751802620845820222323401)
            ·
              refine ⟨563851965634365166742551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751802620845820222323401 563851965634365166742551)
              ·
                refine ⟨845777948451547750113827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563851965634365166742551 845777948451547750113827)
                ·
                  refine ⟨1268666922677321625170741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845777948451547750113827 1268666922677321625170741)
                  ·
                    refine ⟨118937524000998902359757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1268666922677321625170741 118937524000998902359757)
                    ·
                      rfl

theorem cell22_347445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_347445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347445 prefixEnd_347445 := by exact prefixLift 347445
  have htrace : WordTrace (prefixWord ++ tailWord_347445) baseStart_347445 baseEnd_347445 := by
    simpa [prefixWord, tailWord_347445, baseEnd_347445] using wordTrace_append hprefix tailTrace_347445
  have hstable : (prefixWord ++ tailWord_347445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347445).length < 2 ^ (prefixWord ++ tailWord_347445).sum := by decide
  have hdescent : baseEnd_347445 < baseStart_347445 := by decide
  rcases family_descends (prefixWord ++ tailWord_347445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347509 : List Nat := [1, 3, 4, 1, 4, 1, 2, 6]
def baseStart_347509 : Nat := 118140960795 + 347509 * 2 ^ 59
def prefixEnd_347509 : Nat := 4983230072969 + 3 ^ 40 * 347509 * 2
def baseEnd_347509 : Nat := 13217714723213785417729

theorem tailTrace_347509 : CollatzResearch.WordTrace tailWord_347509 prefixEnd_347509 13217714723213785417729 := by
  unfold tailWord_347509
  simp only [CollatzResearch.WordTrace]
  refine ⟨12674694498041717657229581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8449796332027811771486387 12674694498041717657229581)
  ·
    refine ⟨4753010436765644121461093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12674694498041717657229581 4753010436765644121461093)
    ·
      refine ⟨891189456893558272773955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4753010436765644121461093 891189456893558272773955)
      ·
        refine ⟨1336784185340337409160933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891189456893558272773955 1336784185340337409160933)
        ·
          refine ⟨250647034751313264217675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1336784185340337409160933 250647034751313264217675)
          ·
            refine ⟨375970552126969896326513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250647034751313264217675 375970552126969896326513)
            ·
              refine ⟨281977914095227422244885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375970552126969896326513 281977914095227422244885)
              ·
                refine ⟨13217714723213785417729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 281977914095227422244885 13217714723213785417729)
                ·
                  rfl

theorem cell22_347509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 6].length) (baseStart_347509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347509 prefixEnd_347509 := by exact prefixLift 347509
  have htrace : WordTrace (prefixWord ++ tailWord_347509) baseStart_347509 baseEnd_347509 := by
    simpa [prefixWord, tailWord_347509, baseEnd_347509] using wordTrace_append hprefix tailTrace_347509
  have hstable : (prefixWord ++ tailWord_347509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347509).length < 2 ^ (prefixWord ++ tailWord_347509).sum := by decide
  have hdescent : baseEnd_347509 < baseStart_347509 := by decide
  rcases family_descends (prefixWord ++ tailWord_347509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347524 : List Nat := [2, 3, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_347524 : Nat := 118140960795 + 347524 * 2 ^ 59
def prefixEnd_347524 : Nat := 4983230072969 + 3 ^ 40 * 347524 * 2
def baseEnd_347524 : Nat := 118964567315469029634515

theorem tailTrace_347524 : CollatzResearch.WordTrace tailWord_347524 prefixEnd_347524 118964567315469029634515 := by
  unfold tailWord_347524
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337620796493687609512813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8450161061991583479350417 6337620796493687609512813)
  ·
    refine ⟨2376607798685132853567305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6337620796493687609512813 2376607798685132853567305)
    ·
      refine ⟨1782455849013849640175479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2376607798685132853567305 1782455849013849640175479)
      ·
        refine ⟨2673683773520774460263219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782455849013849640175479 2673683773520774460263219)
        ·
          refine ⟨4010525660281161690394829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673683773520774460263219 4010525660281161690394829)
          ·
            refine ⟨1503947122605435633898061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4010525660281161690394829 1503947122605435633898061)
            ·
              refine ⟨563980170977038362711773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1503947122605435633898061 563980170977038362711773)
              ·
                refine ⟨211492564116389386016915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563980170977038362711773 211492564116389386016915)
                ·
                  refine ⟨317238846174584079025373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211492564116389386016915 317238846174584079025373)
                  ·
                    refine ⟨118964567315469029634515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317238846174584079025373 118964567315469029634515)
                    ·
                      rfl

theorem cell22_347524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_347524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347524 prefixEnd_347524 := by exact prefixLift 347524
  have htrace : WordTrace (prefixWord ++ tailWord_347524) baseStart_347524 baseEnd_347524 := by
    simpa [prefixWord, tailWord_347524, baseEnd_347524] using wordTrace_append hprefix tailTrace_347524
  have hstable : (prefixWord ++ tailWord_347524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347524).length < 2 ^ (prefixWord ++ tailWord_347524).sum := by decide
  have hdescent : baseEnd_347524 < baseStart_347524 := by decide
  rcases family_descends (prefixWord ++ tailWord_347524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347554 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_347554 : Nat := 118140960795 + 347554 * 2 ^ 59
def prefixEnd_347554 : Nat := 4983230072969 + 3 ^ 40 * 347554 * 2
def baseEnd_347554 : Nat := 39658278976186317128141

theorem tailTrace_347554 : CollatzResearch.WordTrace tailWord_347554 prefixEnd_347554 39658278976186317128141 := by
  unfold tailWord_347554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169083945719672585654429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8450890521919126895078477 3169083945719672585654429)
  ·
    refine ⟨1188406479644877219620411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3169083945719672585654429 1188406479644877219620411)
    ·
      refine ⟨1782609719467315829430617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188406479644877219620411 1782609719467315829430617)
      ·
        refine ⟨1336957289600486872072963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1782609719467315829430617 1336957289600486872072963)
        ·
          refine ⟨2005435934400730308109445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336957289600486872072963 2005435934400730308109445)
          ·
            refine ⟨376019237700136932770521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2005435934400730308109445 376019237700136932770521)
            ·
              refine ⟨282014428275102699577891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376019237700136932770521 282014428275102699577891)
              ·
                refine ⟨423021642412654049366837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282014428275102699577891 423021642412654049366837)
                ·
                  refine ⟨39658278976186317128141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 423021642412654049366837 39658278976186317128141)
                  ·
                    rfl

theorem cell22_347554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_347554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347554 prefixEnd_347554 := by exact prefixLift 347554
  have htrace : WordTrace (prefixWord ++ tailWord_347554) baseStart_347554 baseEnd_347554 := by
    simpa [prefixWord, tailWord_347554, baseEnd_347554] using wordTrace_append hprefix tailTrace_347554
  have hstable : (prefixWord ++ tailWord_347554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347554).length < 2 ^ (prefixWord ++ tailWord_347554).sum := by decide
  have hdescent : baseEnd_347554 < baseStart_347554 := by decide
  rcases family_descends (prefixWord ++ tailWord_347554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347582 : List Nat := [4, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_347582 : Nat := 118140960795 + 347582 * 2 ^ 59
def prefixEnd_347582 : Nat := 4983230072969 + 3 ^ 40 * 347582 * 2
def baseEnd_347582 : Nat := 39661473966925403894779

theorem tailTrace_347582 : CollatzResearch.WordTrace tailWord_347582 prefixEnd_347582 39661473966925403894779 := by
  unfold tailWord_347582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584669628347156390579625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8451571351184834083091333 1584669628347156390579625)
  ·
    refine ⟨1188502221260367292934719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1584669628347156390579625 1188502221260367292934719)
    ·
      refine ⟨1782753331890550939402079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188502221260367292934719 1782753331890550939402079)
      ·
        refine ⟨2674129997835826409103119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782753331890550939402079 2674129997835826409103119)
        ·
          refine ⟨4011194996753739613654679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2674129997835826409103119 4011194996753739613654679)
          ·
            refine ⟨6016792495130609420482019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011194996753739613654679 6016792495130609420482019)
            ·
              refine ⟨9025188742695914130723029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016792495130609420482019 9025188742695914130723029)
              ·
                refine ⟨211527861156935487438821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9025188742695914130723029 211527861156935487438821)
                ·
                  refine ⟨39661473966925403894779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211527861156935487438821 39661473966925403894779)
                  ·
                    rfl

theorem cell22_347582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_347582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347582 prefixEnd_347582 := by exact prefixLift 347582
  have htrace : WordTrace (prefixWord ++ tailWord_347582) baseStart_347582 baseEnd_347582 := by
    simpa [prefixWord, tailWord_347582, baseEnd_347582] using wordTrace_append hprefix tailTrace_347582
  have hstable : (prefixWord ++ tailWord_347582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347582).length < 2 ^ (prefixWord ++ tailWord_347582).sum := by decide
  have hdescent : baseEnd_347582 < baseStart_347582 := by decide
  rcases family_descends (prefixWord ++ tailWord_347582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347595 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 2, 4]
def baseStart_347595 : Nat := 118140960795 + 347595 * 2 ^ 59
def prefixEnd_347595 : Nat := 4983230072969 + 3 ^ 40 * 347595 * 2
def baseEnd_347595 : Nat := 118988872066448511109297

theorem tailTrace_347595 : CollatzResearch.WordTrace tailWord_347595 prefixEnd_347595 118988872066448511109297 := by
  unfold tailWord_347595
  simp only [CollatzResearch.WordTrace]
  refine ⟨12677831175730154344860239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8451887450486769563240159 12677831175730154344860239)
  ·
    refine ⟨19016746763595231517290359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12677831175730154344860239 19016746763595231517290359)
    ·
      refine ⟨28525120145392847275935539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19016746763595231517290359 28525120145392847275935539)
      ·
        refine ⟨42787680218089270913903309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28525120145392847275935539 42787680218089270913903309)
        ·
          refine ⟨16045380081783476592713741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42787680218089270913903309 16045380081783476592713741)
          ·
            refine ⟨6017017530668803722267653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16045380081783476592713741 6017017530668803722267653)
            ·
              refine ⟨1128190787000400697925185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6017017530668803722267653 1128190787000400697925185)
              ·
                refine ⟨846143090250300523443889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128190787000400697925185 846143090250300523443889)
                ·
                  refine ⟨634607317687725392582917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846143090250300523443889 634607317687725392582917)
                  ·
                    refine ⟨118988872066448511109297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 634607317687725392582917 118988872066448511109297)
                    ·
                      rfl

theorem cell22_347595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_347595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347595 prefixEnd_347595 := by exact prefixLift 347595
  have htrace : WordTrace (prefixWord ++ tailWord_347595) baseStart_347595 baseEnd_347595 := by
    simpa [prefixWord, tailWord_347595, baseEnd_347595] using wordTrace_append hprefix tailTrace_347595
  have hstable : (prefixWord ++ tailWord_347595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347595).length < 2 ^ (prefixWord ++ tailWord_347595).sum := by decide
  have hdescent : baseEnd_347595 < baseStart_347595 := by decide
  rcases family_descends (prefixWord ++ tailWord_347595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347610 : List Nat := [3, 1, 1, 2, 3, 2, 3, 7]
def baseStart_347610 : Nat := 118140960795 + 347610 * 2 ^ 59
def prefixEnd_347610 : Nat := 4983230072969 + 3 ^ 40 * 347610 * 2
def baseEnd_347610 : Nat := 13221556319221496887139

theorem tailTrace_347610 : CollatzResearch.WordTrace tailWord_347610 prefixEnd_347610 13221556319221496887139 := by
  unfold tailWord_347610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3169594567668952976664071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8452252180450541271104189 3169594567668952976664071)
  ·
    refine ⟨4754391851503429464996107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3169594567668952976664071 4754391851503429464996107)
    ·
      refine ⟨7131587777255144197494161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4754391851503429464996107 7131587777255144197494161)
      ·
        refine ⟨5348690832941358148120621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7131587777255144197494161 5348690832941358148120621)
        ·
          refine ⟨2005759062353009305545233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5348690832941358148120621 2005759062353009305545233)
          ·
            refine ⟨1504319296764756979158925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005759062353009305545233 1504319296764756979158925)
            ·
              refine ⟨564119736286783867184597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1504319296764756979158925 564119736286783867184597)
              ·
                refine ⟨13221556319221496887139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 564119736286783867184597 13221556319221496887139)
                ·
                  rfl

theorem cell22_347610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_347610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347610 prefixEnd_347610 := by exact prefixLift 347610
  have htrace : WordTrace (prefixWord ++ tailWord_347610) baseStart_347610 baseEnd_347610 := by
    simpa [prefixWord, tailWord_347610, baseEnd_347610] using wordTrace_append hprefix tailTrace_347610
  have hstable : (prefixWord ++ tailWord_347610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347610).length < 2 ^ (prefixWord ++ tailWord_347610).sum := by decide
  have hdescent : baseEnd_347610 < baseStart_347610 := by decide
  rcases family_descends (prefixWord ++ tailWord_347610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347659 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 3, 3]
def baseStart_347659 : Nat := 118140960795 + 347659 * 2 ^ 59
def prefixEnd_347659 : Nat := 4983230072969 + 3 ^ 40 * 347659 * 2
def baseEnd_347659 : Nat := 119010780574373677509101

theorem tailTrace_347659 : CollatzResearch.WordTrace tailWord_347659 prefixEnd_347659 119010780574373677509101 := by
  unfold tailWord_347659
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680165447498293275190031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8453443631665528850126687 12680165447498293275190031)
  ·
    refine ⟨19020248171247439912785047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12680165447498293275190031 19020248171247439912785047)
    ·
      refine ⟨28530372256871159869177571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19020248171247439912785047 28530372256871159869177571)
      ·
        refine ⟨42795558385306739803766357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28530372256871159869177571 42795558385306739803766357)
        ·
          refine ⟨501510449827813357075387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 42795558385306739803766357 501510449827813357075387)
          ·
            refine ⟨752265674741720035613081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501510449827813357075387 752265674741720035613081)
            ·
              refine ⟨564199256056290026709811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752265674741720035613081 564199256056290026709811)
              ·
                refine ⟨846298884084435040064717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564199256056290026709811 846298884084435040064717)
                ·
                  refine ⟨317362081531663140024269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846298884084435040064717 317362081531663140024269)
                  ·
                    refine ⟨119010780574373677509101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317362081531663140024269 119010780574373677509101)
                    ·
                      rfl

theorem cell22_347659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 3].length) (baseStart_347659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347659 prefixEnd_347659 := by exact prefixLift 347659
  have htrace : WordTrace (prefixWord ++ tailWord_347659) baseStart_347659 baseEnd_347659 := by
    simpa [prefixWord, tailWord_347659, baseEnd_347659] using wordTrace_append hprefix tailTrace_347659
  have hstable : (prefixWord ++ tailWord_347659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347659).length < 2 ^ (prefixWord ++ tailWord_347659).sum := by decide
  have hdescent : baseEnd_347659 < baseStart_347659 := by decide
  rcases family_descends (prefixWord ++ tailWord_347659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347732 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_347732 : Nat := 118140960795 + 347732 * 2 ^ 59
def prefixEnd_347732 : Nat := 4983230072969 + 3 ^ 40 * 347732 * 2
def baseEnd_347732 : Nat := 119035769966225820433877

theorem tailTrace_347732 : CollatzResearch.WordTrace tailWord_347732 prefixEnd_347732 119035769966225820433877 := by
  unfold tailWord_347732
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341413988116913371298725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8455218650822551161731633 6341413988116913371298725)
  ·
    refine ⟨1189015122771921257118511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6341413988116913371298725 1189015122771921257118511)
    ·
      refine ⟨1783522684157881885677767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189015122771921257118511 1783522684157881885677767)
      ·
        refine ⟨2675284026236822828516651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783522684157881885677767 2675284026236822828516651)
        ·
          refine ⟨4012926039355234242774977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675284026236822828516651 4012926039355234242774977)
          ·
            refine ⟨3009694529516425682081233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4012926039355234242774977 3009694529516425682081233)
            ·
              refine ⟨2257270897137319261560925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3009694529516425682081233 2257270897137319261560925)
              ·
                refine ⟨846476586426494723085347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257270897137319261560925 846476586426494723085347)
                ·
                  refine ⟨1269714879639742084628021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846476586426494723085347 1269714879639742084628021)
                  ·
                    refine ⟨119035769966225820433877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1269714879639742084628021 119035769966225820433877)
                    ·
                      rfl

theorem cell22_347732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_347732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347732 prefixEnd_347732 := by exact prefixLift 347732
  have htrace : WordTrace (prefixWord ++ tailWord_347732) baseStart_347732 baseEnd_347732 := by
    simpa [prefixWord, tailWord_347732, baseEnd_347732] using wordTrace_append hprefix tailTrace_347732
  have hstable : (prefixWord ++ tailWord_347732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347732).length < 2 ^ (prefixWord ++ tailWord_347732).sum := by decide
  have hdescent : baseEnd_347732 < baseStart_347732 := by decide
  rcases family_descends (prefixWord ++ tailWord_347732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347745 : List Nat := [1, 2, 3, 1, 1, 3, 1, 10]
def baseStart_347745 : Nat := 118140960795 + 347745 * 2 ^ 59
def prefixEnd_347745 : Nat := 4983230072969 + 3 ^ 40 * 347745 * 2
def baseEnd_347745 : Nat := 13226691125766457762093

theorem tailTrace_347745 : CollatzResearch.WordTrace tailWord_347745 prefixEnd_347745 13226691125766457762093 := by
  unfold tailWord_347745
  simp only [CollatzResearch.WordTrace]
  refine ⟨12683302125186729962820689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8455534750124486641880459 12683302125186729962820689)
  ·
    refine ⟨9512476593890047472115517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12683302125186729962820689 9512476593890047472115517)
    ·
      refine ⟨3567178722708767802043319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9512476593890047472115517 3567178722708767802043319)
      ·
        refine ⟨5350768084063151703064979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567178722708767802043319 5350768084063151703064979)
        ·
          refine ⟨8026152126094727554597469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350768084063151703064979 8026152126094727554597469)
          ·
            refine ⟨3009807047285522832974051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8026152126094727554597469 3009807047285522832974051)
            ·
              refine ⟨4514710570928284249461077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009807047285522832974051 4514710570928284249461077)
              ·
                refine ⟨13226691125766457762093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4514710570928284249461077 13226691125766457762093)
                ·
                  rfl

theorem cell22_347745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 10].length) (baseStart_347745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347745 prefixEnd_347745 := by exact prefixLift 347745
  have htrace : WordTrace (prefixWord ++ tailWord_347745) baseStart_347745 baseEnd_347745 := by
    simpa [prefixWord, tailWord_347745, baseEnd_347745] using wordTrace_append hprefix tailTrace_347745
  have hstable : (prefixWord ++ tailWord_347745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347745).length < 2 ^ (prefixWord ++ tailWord_347745).sum := by decide
  have hdescent : baseEnd_347745 < baseStart_347745 := by decide
  rcases family_descends (prefixWord ++ tailWord_347745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347747 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 2, 4]
def baseStart_347747 : Nat := 118140960795 + 347747 * 2 ^ 59
def prefixEnd_347747 : Nat := 4983230072969 + 3 ^ 40 * 347747 * 2
def baseEnd_347747 : Nat := 119040904772770781308831

theorem tailTrace_347747 : CollatzResearch.WordTrace tailWord_347747 prefixEnd_347747 119040904772770781308831 := by
  unfold tailWord_347747
  simp only [CollatzResearch.WordTrace]
  refine ⟨12683375071179484304393495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8455583380786322869595663 12683375071179484304393495)
  ·
    refine ⟨19025062606769226456590243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12683375071179484304393495 19025062606769226456590243)
    ·
      refine ⟨28537593910153839684885365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19025062606769226456590243 28537593910153839684885365)
      ·
        refine ⟨2675399429076922470458003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28537593910153839684885365 2675399429076922470458003)
        ·
          refine ⟨4013099143615383705687005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675399429076922470458003 4013099143615383705687005)
          ·
            refine ⟨1504912178855768889632627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4013099143615383705687005 1504912178855768889632627)
            ·
              refine ⟨2257368268283653334448941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504912178855768889632627 2257368268283653334448941)
              ·
                refine ⟨846513100606370000418353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257368268283653334448941 846513100606370000418353)
                ·
                  refine ⟨634884825454777500313765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846513100606370000418353 634884825454777500313765)
                  ·
                    refine ⟨119040904772770781308831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 634884825454777500313765 119040904772770781308831)
                    ·
                      rfl

theorem cell22_347747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_347747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347747 prefixEnd_347747 := by exact prefixLift 347747
  have htrace : WordTrace (prefixWord ++ tailWord_347747) baseStart_347747 baseEnd_347747 := by
    simpa [prefixWord, tailWord_347747, baseEnd_347747] using wordTrace_append hprefix tailTrace_347747
  have hstable : (prefixWord ++ tailWord_347747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347747).length < 2 ^ (prefixWord ++ tailWord_347747).sum := by decide
  have hdescent : baseEnd_347747 < baseStart_347747 := by decide
  rcases family_descends (prefixWord ++ tailWord_347747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347766 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_347766 : Nat := 118140960795 + 347766 * 2 ^ 59
def prefixEnd_347766 : Nat := 4983230072969 + 3 ^ 40 * 347766 * 2
def baseEnd_347766 : Nat := 119047408861061065083773

theorem tailTrace_347766 : CollatzResearch.WordTrace tailWord_347766 prefixEnd_347766 119047408861061065083773 := by
  unfold tailWord_347766
  simp only [CollatzResearch.WordTrace]
  refine ⟨792754253631915659333447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8456045372073767032890101 792754253631915659333447)
  ·
    refine ⟨1189131380447873489000171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 792754253631915659333447 1189131380447873489000171)
    ·
      refine ⟨1783697070671810233500257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189131380447873489000171 1783697070671810233500257)
      ·
        refine ⟨1337772803003857675125193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1783697070671810233500257 1337772803003857675125193)
        ·
          refine ⟨1003329602252893256343895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337772803003857675125193 1003329602252893256343895)
          ·
            refine ⟨1504994403379339884515843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003329602252893256343895 1504994403379339884515843)
            ·
              refine ⟨2257491605069009826773765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504994403379339884515843 2257491605069009826773765)
              ·
                refine ⟨423279675950439342520081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2257491605069009826773765 423279675950439342520081)
                ·
                  refine ⟨317459756962829506890061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423279675950439342520081 317459756962829506890061)
                  ·
                    refine ⟨119047408861061065083773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317459756962829506890061 119047408861061065083773)
                    ·
                      rfl

theorem cell22_347766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_347766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347766 prefixEnd_347766 := by exact prefixLift 347766
  have htrace : WordTrace (prefixWord ++ tailWord_347766) baseStart_347766 baseEnd_347766 := by
    simpa [prefixWord, tailWord_347766, baseEnd_347766] using wordTrace_append hprefix tailTrace_347766
  have hstable : (prefixWord ++ tailWord_347766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347766).length < 2 ^ (prefixWord ++ tailWord_347766).sum := by decide
  have hdescent : baseEnd_347766 < baseStart_347766 := by decide
  rcases family_descends (prefixWord ++ tailWord_347766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347796 : List Nat := [2, 4, 2, 2, 2, 1, 3, 6]
def baseStart_347796 : Nat := 118140960795 + 347796 * 2 ^ 59
def prefixEnd_347796 : Nat := 4983230072969 + 3 ^ 40 * 347796 * 2
def baseEnd_347796 : Nat := 13228630941572331870409

theorem tailTrace_347796 : CollatzResearch.WordTrace tailWord_347796 prefixEnd_347796 13228630941572331870409 := by
  unfold tailWord_347796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342581124000982836463621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8456774832001310448618161 6342581124000982836463621)
  ·
    refine ⟨1189233960750184281836929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6342581124000982836463621 1189233960750184281836929)
    ·
      refine ⟨891925470562638211377697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1189233960750184281836929 891925470562638211377697)
      ·
        refine ⟨668944102921978658533273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 891925470562638211377697 668944102921978658533273)
        ·
          refine ⟨501708077191483993899955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668944102921978658533273 501708077191483993899955)
          ·
            refine ⟨752562115787225990849933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501708077191483993899955 752562115787225990849933)
            ·
              refine ⟨282210793420209746568725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752562115787225990849933 282210793420209746568725)
              ·
                refine ⟨13228630941572331870409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282210793420209746568725 13228630941572331870409)
                ·
                  rfl

theorem cell22_347796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 6].length) (baseStart_347796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347796 prefixEnd_347796 := by exact prefixLift 347796
  have htrace : WordTrace (prefixWord ++ tailWord_347796) baseStart_347796 baseEnd_347796 := by
    simpa [prefixWord, tailWord_347796, baseEnd_347796] using wordTrace_append hprefix tailTrace_347796
  have hstable : (prefixWord ++ tailWord_347796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347796).length < 2 ^ (prefixWord ++ tailWord_347796).sum := by decide
  have hdescent : baseEnd_347796 < baseStart_347796 := by decide
  rcases family_descends (prefixWord ++ tailWord_347796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347811 : List Nat := [1, 1, 1, 4, 1, 1, 6, 3, 1, 3]
def baseStart_347811 : Nat := 118140960795 + 347811 * 2 ^ 59
def prefixEnd_347811 : Nat := 4983230072969 + 3 ^ 40 * 347811 * 2
def baseEnd_347811 : Nat := 119062813280695947708635

theorem tailTrace_347811 : CollatzResearch.WordTrace tailWord_347811 prefixEnd_347811 119062813280695947708635 := by
  unfold tailWord_347811
  simp only [CollatzResearch.WordTrace]
  refine ⟨12685709342947623234723287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8457139561965082156482191 12685709342947623234723287)
  ·
    refine ⟨19028564014421434852084931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12685709342947623234723287 19028564014421434852084931)
    ·
      refine ⟨28542846021632152278127397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19028564014421434852084931 28542846021632152278127397)
      ·
        refine ⟨5351783629056028552148887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28542846021632152278127397 5351783629056028552148887)
        ·
          refine ⟨8027675443584042828223331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351783629056028552148887 8027675443584042828223331)
          ·
            refine ⟨12041513165376064242334997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027675443584042828223331 12041513165376064242334997)
            ·
              refine ⟨564445929627003011359453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12041513165376064242334997 564445929627003011359453)
              ·
                refine ⟨211667223610126129259795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 564445929627003011359453 211667223610126129259795)
                ·
                  refine ⟨317500835415189193889693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211667223610126129259795 317500835415189193889693)
                  ·
                    refine ⟨119062813280695947708635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317500835415189193889693 119062813280695947708635)
                    ·
                      rfl

theorem cell22_347811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 1, 3].length) (baseStart_347811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347811 prefixEnd_347811 := by exact prefixLift 347811
  have htrace : WordTrace (prefixWord ++ tailWord_347811) baseStart_347811 baseEnd_347811 := by
    simpa [prefixWord, tailWord_347811, baseEnd_347811] using wordTrace_append hprefix tailTrace_347811
  have hstable : (prefixWord ++ tailWord_347811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347811).length < 2 ^ (prefixWord ++ tailWord_347811).sum := by decide
  have hdescent : baseEnd_347811 < baseStart_347811 := by decide
  rcases family_descends (prefixWord ++ tailWord_347811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347884 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_347884 : Nat := 118140960795 + 347884 * 2 ^ 59
def prefixEnd_347884 : Nat := 4983230072969 + 3 ^ 40 * 347884 * 2
def baseEnd_347884 : Nat := 119087802672548090633411

theorem tailTrace_347884 : CollatzResearch.WordTrace tailWord_347884 prefixEnd_347884 119087802672548090633411 := by
  unfold tailWord_347884
  simp only [CollatzResearch.WordTrace]
  refine ⟨6344185935841578351065353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8458914581122104468087137 6344185935841578351065353)
  ·
    refine ⟨4758139451881183763299015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6344185935841578351065353 4758139451881183763299015)
    ·
      refine ⟨7137209177821775644948523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4758139451881183763299015 7137209177821775644948523)
      ·
        refine ⟨10705813766732663467422785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7137209177821775644948523 10705813766732663467422785)
        ·
          refine ⟨8029360325049497600567089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10705813766732663467422785 8029360325049497600567089)
          ·
            refine ⟨6022020243787123200425317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8029360325049497600567089 6022020243787123200425317)
            ·
              refine ⟨1129128795710085600079747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6022020243787123200425317 1129128795710085600079747)
              ·
                refine ⟨1693693193565128400119621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129128795710085600079747 1693693193565128400119621)
                ·
                  refine ⟨317567473793461575022429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1693693193565128400119621 317567473793461575022429)
                  ·
                    refine ⟨119087802672548090633411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317567473793461575022429 119087802672548090633411)
                    ·
                      rfl

theorem cell22_347884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_347884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347884 prefixEnd_347884 := by exact prefixLift 347884
  have htrace : WordTrace (prefixWord ++ tailWord_347884) baseStart_347884 baseEnd_347884 := by
    simpa [prefixWord, tailWord_347884, baseEnd_347884] using wordTrace_append hprefix tailTrace_347884
  have hstable : (prefixWord ++ tailWord_347884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347884).length < 2 ^ (prefixWord ++ tailWord_347884).sum := by decide
  have hdescent : baseEnd_347884 < baseStart_347884 := by decide
  rcases family_descends (prefixWord ++ tailWord_347884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347944 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_347944 : Nat := 118140960795 + 347944 * 2 ^ 59
def prefixEnd_347944 : Nat := 4983230072969 + 3 ^ 40 * 347944 * 2
def baseEnd_347944 : Nat := 119108341898727934133227

theorem tailTrace_347944 : CollatzResearch.WordTrace tailWord_347944 prefixEnd_347944 119108341898727934133227 := by
  unfold tailWord_347944
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345280125732893474657443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8460373500977191299543257 6345280125732893474657443)
  ·
    refine ⟨9517920188599340211986165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6345280125732893474657443 9517920188599340211986165)
    ·
      refine ⟨892305017681188144873703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9517920188599340211986165 892305017681188144873703)
      ·
        refine ⟨1338457526521782217310555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892305017681188144873703 1338457526521782217310555)
        ·
          refine ⟨2007686289782673325965833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1338457526521782217310555 2007686289782673325965833)
          ·
            refine ⟨1505764717337004994474375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2007686289782673325965833 1505764717337004994474375)
            ·
              refine ⟨2258647076005507491711563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505764717337004994474375 2258647076005507491711563)
              ·
                refine ⟨3387970614008261237567345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258647076005507491711563 3387970614008261237567345)
                ·
                  refine ⟨2540977960506195928175509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3387970614008261237567345 2540977960506195928175509)
                  ·
                    refine ⟨119108341898727934133227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2540977960506195928175509 119108341898727934133227)
                    ·
                      rfl

theorem cell22_347944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_347944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347944 prefixEnd_347944 := by exact prefixLift 347944
  have htrace : WordTrace (prefixWord ++ tailWord_347944) baseStart_347944 baseEnd_347944 := by
    simpa [prefixWord, tailWord_347944, baseEnd_347944] using wordTrace_append hprefix tailTrace_347944
  have hstable : (prefixWord ++ tailWord_347944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347944).length < 2 ^ (prefixWord ++ tailWord_347944).sum := by decide
  have hdescent : baseEnd_347944 < baseStart_347944 := by decide
  rcases family_descends (prefixWord ++ tailWord_347944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347980 : List Nat := [2, 2, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_347980 : Nat := 118140960795 + 347980 * 2 ^ 59
def prefixEnd_347980 : Nat := 4983230072969 + 3 ^ 40 * 347980 * 2
def baseEnd_347980 : Nat := 119120665434435840233117

theorem tailTrace_347980 : CollatzResearch.WordTrace tailWord_347980 prefixEnd_347980 119120665434435840233117 := by
  unfold tailWord_347980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345936639667682548812697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8461248852890243398416929 6345936639667682548812697)
  ·
    refine ⟨4759452479750761911609523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6345936639667682548812697 4759452479750761911609523)
    ·
      refine ⟨7139178719626142867414285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4759452479750761911609523 7139178719626142867414285)
      ·
        refine ⟨2677192019859803575280357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7139178719626142867414285 2677192019859803575280357)
        ·
          refine ⟨501973503723713170365067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2677192019859803575280357 501973503723713170365067)
          ·
            refine ⟨752960255585569755547601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501973503723713170365067 752960255585569755547601)
            ·
              refine ⟨564720191689177316660701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752960255585569755547601 564720191689177316660701)
              ·
                refine ⟨211770071883441493747763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 564720191689177316660701 211770071883441493747763)
                ·
                  refine ⟨317655107825162240621645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211770071883441493747763 317655107825162240621645)
                  ·
                    refine ⟨119120665434435840233117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317655107825162240621645 119120665434435840233117)
                    ·
                      rfl

theorem cell22_347980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_347980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_347980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_347980 prefixEnd_347980 := by exact prefixLift 347980
  have htrace : WordTrace (prefixWord ++ tailWord_347980) baseStart_347980 baseEnd_347980 := by
    simpa [prefixWord, tailWord_347980, baseEnd_347980] using wordTrace_append hprefix tailTrace_347980
  have hstable : (prefixWord ++ tailWord_347980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347980).length < 2 ^ (prefixWord ++ tailWord_347980).sum := by decide
  have hdescent : baseEnd_347980 < baseStart_347980 := by decide
  rcases family_descends (prefixWord ++ tailWord_347980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348010 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_348010 : Nat := 118140960795 + 348010 * 2 ^ 59
def prefixEnd_348010 : Nat := 4983230072969 + 3 ^ 40 * 348010 * 2
def baseEnd_348010 : Nat := 39710311682508587327675

theorem tailTrace_348010 : CollatzResearch.WordTrace tailWord_348010 prefixEnd_348010 39710311682508587327675 := by
  unfold tailWord_348010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173241867306670055304371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8461978312817786814144989 3173241867306670055304371)
  ·
    refine ⟨4759862800960005082956557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3173241867306670055304371 4759862800960005082956557)
    ·
      refine ⟨1784948550360001906108709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4759862800960005082956557 1784948550360001906108709)
      ·
        refine ⟨334677853192500357395383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1784948550360001906108709 334677853192500357395383)
        ·
          refine ⟨502016779788750536093075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334677853192500357395383 502016779788750536093075)
          ·
            refine ⟨753025169683125804139613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502016779788750536093075 753025169683125804139613)
            ·
              refine ⟨282384438631172176552355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753025169683125804139613 282384438631172176552355)
              ·
                refine ⟨423576657946758264828533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282384438631172176552355 423576657946758264828533)
                ·
                  refine ⟨39710311682508587327675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 423576657946758264828533 39710311682508587327675)
                  ·
                    rfl

theorem cell22_348010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_348010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348010 prefixEnd_348010 := by exact prefixLift 348010
  have htrace : WordTrace (prefixWord ++ tailWord_348010) baseStart_348010 baseEnd_348010 := by
    simpa [prefixWord, tailWord_348010, baseEnd_348010] using wordTrace_append hprefix tailTrace_348010
  have hstable : (prefixWord ++ tailWord_348010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348010).length < 2 ^ (prefixWord ++ tailWord_348010).sum := by decide
  have hdescent : baseEnd_348010 < baseStart_348010 := by decide
  rcases family_descends (prefixWord ++ tailWord_348010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348036 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 4, 3]
def baseStart_348036 : Nat := 118140960795 + 348036 * 2 ^ 59
def prefixEnd_348036 : Nat := 4983230072969 + 3 ^ 40 * 348036 * 2
def baseEnd_348036 : Nat := 119139835378870360832945

theorem tailTrace_348036 : CollatzResearch.WordTrace tailWord_348036 prefixEnd_348036 119139835378870360832945 := by
  unfold tailWord_348036
  simp only [CollatzResearch.WordTrace]
  refine ⟨6346957883566243330831981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8462610511421657774442641 6346957883566243330831981)
  ·
    refine ⟨2380109206337341249061993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6346957883566243330831981 2380109206337341249061993)
    ·
      refine ⟨1785081904753005936796495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2380109206337341249061993 1785081904753005936796495)
      ·
        refine ⟨2677622857129508905194743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785081904753005936796495 2677622857129508905194743)
        ·
          refine ⟨4016434285694263357792115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677622857129508905194743 4016434285694263357792115)
          ·
            refine ⟨6024651428541395036688173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016434285694263357792115 6024651428541395036688173)
            ·
              refine ⟨2259244285703023138758065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6024651428541395036688173 2259244285703023138758065)
              ·
                refine ⟨1694433214277267354068549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2259244285703023138758065 1694433214277267354068549)
                ·
                  refine ⟨317706227676987628887853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694433214277267354068549 317706227676987628887853)
                  ·
                    refine ⟨119139835378870360832945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317706227676987628887853 119139835378870360832945)
                    ·
                      rfl

theorem cell22_348036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_348036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348036 prefixEnd_348036 := by exact prefixLift 348036
  have htrace : WordTrace (prefixWord ++ tailWord_348036) baseStart_348036 baseEnd_348036 := by
    simpa [prefixWord, tailWord_348036, baseEnd_348036] using wordTrace_append hprefix tailTrace_348036
  have hstable : (prefixWord ++ tailWord_348036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348036).length < 2 ^ (prefixWord ++ tailWord_348036).sum := by decide
  have hdescent : baseEnd_348036 < baseStart_348036 := by decide
  rcases family_descends (prefixWord ++ tailWord_348036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348111 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 5]
def baseStart_348111 : Nat := 118140960795 + 348111 * 2 ^ 59
def prefixEnd_348111 : Nat := 4983230072969 + 3 ^ 40 * 348111 * 2
def baseEnd_348111 : Nat := 39721836470531721735905

theorem tailTrace_348111 : CollatzResearch.WordTrace tailWord_348111 prefixEnd_348111 39721836470531721735905 := by
  unfold tailWord_348111
  simp only [CollatzResearch.WordTrace]
  refine ⟨12696651241860774470644187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8464434161240516313762791 12696651241860774470644187)
  ·
    refine ⟨19044976862791161705966281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12696651241860774470644187 19044976862791161705966281)
    ·
      refine ⟨14283732647093371279474711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19044976862791161705966281 14283732647093371279474711)
      ·
        refine ⟨21425598970640056919212067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14283732647093371279474711 21425598970640056919212067)
        ·
          refine ⟨32138398455960085378818101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21425598970640056919212067 32138398455960085378818101)
          ·
            refine ⟨3012974855246258004264197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32138398455960085378818101 3012974855246258004264197)
            ·
              refine ⟨564932785358673375799537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3012974855246258004264197 564932785358673375799537)
              ·
                refine ⟨423699589019005031849653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564932785358673375799537 423699589019005031849653)
                ·
                  refine ⟨39721836470531721735905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 423699589019005031849653 39721836470531721735905)
                  ·
                    rfl

theorem cell22_348111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 5].length) (baseStart_348111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348111 prefixEnd_348111 := by exact prefixLift 348111
  have htrace : WordTrace (prefixWord ++ tailWord_348111) baseStart_348111 baseEnd_348111 := by
    simpa [prefixWord, tailWord_348111, baseEnd_348111] using wordTrace_append hprefix tailTrace_348111
  have hstable : (prefixWord ++ tailWord_348111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348111).length < 2 ^ (prefixWord ++ tailWord_348111).sum := by decide
  have hdescent : baseEnd_348111 < baseStart_348111 := by decide
  rcases family_descends (prefixWord ++ tailWord_348111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348166 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_348166 : Nat := 118140960795 + 348166 * 2 ^ 59
def prefixEnd_348166 : Nat := 4983230072969 + 3 ^ 40 * 348166 * 2
def baseEnd_348166 : Nat := 119184337035593355082547

theorem tailTrace_348166 : CollatzResearch.WordTrace tailWord_348166 prefixEnd_348166 119184337035593355082547 := by
  unfold tailWord_348166
  simp only [CollatzResearch.WordTrace]
  refine ⟨396833039270672464496761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8465771504441012575930901 396833039270672464496761)
  ·
    refine ⟨297624779453004348372571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 396833039270672464496761 297624779453004348372571)
    ·
      refine ⟨446437169179506522558857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297624779453004348372571 446437169179506522558857)
      ·
        refine ⟨334827876884629891919143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446437169179506522558857 334827876884629891919143)
        ·
          refine ⟨502241815326944837878715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334827876884629891919143 502241815326944837878715)
          ·
            refine ⟨753362722990417256818073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502241815326944837878715 753362722990417256818073)
            ·
              refine ⟨565022042242812942613555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753362722990417256818073 565022042242812942613555)
              ·
                refine ⟨847533063364219413920333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565022042242812942613555 847533063364219413920333)
                ·
                  refine ⟨317824898761582280220125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847533063364219413920333 317824898761582280220125)
                  ·
                    refine ⟨119184337035593355082547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317824898761582280220125 119184337035593355082547)
                    ·
                      rfl

theorem cell22_348166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_348166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348166 prefixEnd_348166 := by exact prefixLift 348166
  have htrace : WordTrace (prefixWord ++ tailWord_348166) baseStart_348166 baseEnd_348166 := by
    simpa [prefixWord, tailWord_348166, baseEnd_348166] using wordTrace_append hprefix tailTrace_348166
  have hstable : (prefixWord ++ tailWord_348166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348166).length < 2 ^ (prefixWord ++ tailWord_348166).sum := by decide
  have hdescent : baseEnd_348166 < baseStart_348166 := by decide
  rcases family_descends (prefixWord ++ tailWord_348166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348186 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_348186 : Nat := 118140960795 + 348186 * 2 ^ 59
def prefixEnd_348186 : Nat := 4983230072969 + 3 ^ 40 * 348186 * 2
def baseEnd_348186 : Nat := 119191183444319969582485

theorem tailTrace_348186 : CollatzResearch.WordTrace tailWord_348186 prefixEnd_348186 119191183444319969582485 := by
  unfold tailWord_348186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3174846679147265569906103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8466257811059374853082941 3174846679147265569906103)
  ·
    refine ⟨4762270018720898354859155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3174846679147265569906103 4762270018720898354859155)
    ·
      refine ⟨7143405028081347532288733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4762270018720898354859155 7143405028081347532288733)
      ·
        refine ⟨2678776885530505324608275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7143405028081347532288733 2678776885530505324608275)
        ·
          refine ⟨4018165328295757986912413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678776885530505324608275 4018165328295757986912413)
          ·
            refine ⟨1506811998110909245092155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4018165328295757986912413 1506811998110909245092155)
            ·
              refine ⟨2260217997166363867638233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506811998110909245092155 2260217997166363867638233)
              ·
                refine ⟨1695163497874772900728675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260217997166363867638233 1695163497874772900728675)
                ·
                  refine ⟨2542745246812159351093013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695163497874772900728675 2542745246812159351093013)
                  ·
                    refine ⟨119191183444319969582485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2542745246812159351093013 119191183444319969582485)
                    ·
                      rfl

theorem cell22_348186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_348186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348186 prefixEnd_348186 := by exact prefixLift 348186
  have htrace : WordTrace (prefixWord ++ tailWord_348186) baseStart_348186 baseEnd_348186 := by
    simpa [prefixWord, tailWord_348186, baseEnd_348186] using wordTrace_append hprefix tailTrace_348186
  have hstable : (prefixWord ++ tailWord_348186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348186).length < 2 ^ (prefixWord ++ tailWord_348186).sum := by decide
  have hdescent : baseEnd_348186 < baseStart_348186 := by decide
  rcases family_descends (prefixWord ++ tailWord_348186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348188 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_348188 : Nat := 118140960795 + 348188 * 2 ^ 59
def prefixEnd_348188 : Nat := 4983230072969 + 3 ^ 40 * 348188 * 2
def baseEnd_348188 : Nat := 119191868085192631032479

theorem tailTrace_348188 : CollatzResearch.WordTrace tailWord_348188 prefixEnd_348188 119191868085192631032479 := by
  unfold tailWord_348188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349729831290908310598609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8466306441721211080798145 6349729831290908310598609)
  ·
    refine ⟨4762297373468181232948957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6349729831290908310598609 4762297373468181232948957)
    ·
      refine ⟨1785861515050567962355859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4762297373468181232948957 1785861515050567962355859)
      ·
        refine ⟨2678792272575851943533789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785861515050567962355859 2678792272575851943533789)
        ·
          refine ⟨1004547102215944478825171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2678792272575851943533789 1004547102215944478825171)
          ·
            refine ⟨1506820653323916718237757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004547102215944478825171 1506820653323916718237757)
            ·
              refine ⟨565057744996468769339159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1506820653323916718237757 565057744996468769339159)
              ·
                refine ⟨847586617494703154008739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565057744996468769339159 847586617494703154008739)
                ·
                  refine ⟨1271379926242054731013109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847586617494703154008739 1271379926242054731013109)
                  ·
                    refine ⟨119191868085192631032479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1271379926242054731013109 119191868085192631032479)
                    ·
                      rfl

theorem cell22_348188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_348188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348188 prefixEnd_348188 := by exact prefixLift 348188
  have htrace : WordTrace (prefixWord ++ tailWord_348188) baseStart_348188 baseEnd_348188 := by
    simpa [prefixWord, tailWord_348188, baseEnd_348188] using wordTrace_append hprefix tailTrace_348188
  have hstable : (prefixWord ++ tailWord_348188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348188).length < 2 ^ (prefixWord ++ tailWord_348188).sum := by decide
  have hdescent : baseEnd_348188 < baseStart_348188 := by decide
  rcases family_descends (prefixWord ++ tailWord_348188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348231 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 2, 6]
def baseStart_348231 : Nat := 118140960795 + 348231 * 2 ^ 59
def prefixEnd_348231 : Nat := 4983230072969 + 3 ^ 40 * 348231 * 2
def baseEnd_348231 : Nat := 119206587863954852207347

theorem tailTrace_348231 : CollatzResearch.WordTrace tailWord_348231 prefixEnd_348231 119206587863954852207347 := by
  unfold tailWord_348231
  simp only [CollatzResearch.WordTrace]
  refine ⟨12701028001426034965012547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8467352000950689976675031 12701028001426034965012547)
  ·
    refine ⟨19051542002139052447518821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12701028001426034965012547 19051542002139052447518821)
    ·
      refine ⟨3572164125401072333909779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19051542002139052447518821 3572164125401072333909779)
      ·
        refine ⟨5358246188101608500864669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572164125401072333909779 5358246188101608500864669)
        ·
          refine ⟨2009342320538103187824251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5358246188101608500864669 2009342320538103187824251)
          ·
            refine ⟨3014013480807154781736377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009342320538103187824251 3014013480807154781736377)
            ·
              refine ⟨2260510110605366086302283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3014013480807154781736377 2260510110605366086302283)
              ·
                refine ⟨3390765165908049129453425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260510110605366086302283 3390765165908049129453425)
                ·
                  refine ⟨2543073874431036847090069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3390765165908049129453425 2543073874431036847090069)
                  ·
                    refine ⟨119206587863954852207347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2543073874431036847090069 119206587863954852207347)
                    ·
                      rfl

theorem cell22_348231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_348231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348231 prefixEnd_348231 := by exact prefixLift 348231
  have htrace : WordTrace (prefixWord ++ tailWord_348231) baseStart_348231 baseEnd_348231 := by
    simpa [prefixWord, tailWord_348231, baseEnd_348231] using wordTrace_append hprefix tailTrace_348231
  have hstable : (prefixWord ++ tailWord_348231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348231).length < 2 ^ (prefixWord ++ tailWord_348231).sum := by decide
  have hdescent : baseEnd_348231 < baseStart_348231 := by decide
  rcases family_descends (prefixWord ++ tailWord_348231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348254 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_348254 : Nat := 118140960795 + 348254 * 2 ^ 59
def prefixEnd_348254 : Nat := 4983230072969 + 3 ^ 40 * 348254 * 2
def baseEnd_348254 : Nat := 119214461233990458882277

theorem tailTrace_348254 : CollatzResearch.WordTrace tailWord_348254 prefixEnd_348254 119214461233990458882277 := by
  unfold tailWord_348254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587733360042838736637477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8467911253561806595399877 1587733360042838736637477)
  ·
    refine ⟨297700005008032263119527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1587733360042838736637477 297700005008032263119527)
    ·
      refine ⟨446550007512048394679291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297700005008032263119527 446550007512048394679291)
      ·
        refine ⟨669825011268072592018937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446550007512048394679291 669825011268072592018937)
        ·
          refine ⟨502368758451054444014203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669825011268072592018937 502368758451054444014203)
          ·
            refine ⟨753553137676581666021305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502368758451054444014203 753553137676581666021305)
            ·
              refine ⟨565164853257436249515979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753553137676581666021305 565164853257436249515979)
              ·
                refine ⟨847747279886154374273969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565164853257436249515979 847747279886154374273969)
                ·
                  refine ⟨635810459914615780705477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 847747279886154374273969 635810459914615780705477)
                  ·
                    refine ⟨119214461233990458882277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 635810459914615780705477 119214461233990458882277)
                    ·
                      rfl

theorem cell22_348254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_348254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348254 prefixEnd_348254 := by exact prefixLift 348254
  have htrace : WordTrace (prefixWord ++ tailWord_348254) baseStart_348254 baseEnd_348254 := by
    simpa [prefixWord, tailWord_348254, baseEnd_348254] using wordTrace_append hprefix tailTrace_348254
  have hstable : (prefixWord ++ tailWord_348254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348254).length < 2 ^ (prefixWord ++ tailWord_348254).sum := by decide
  have hdescent : baseEnd_348254 < baseStart_348254 := by decide
  rcases family_descends (prefixWord ++ tailWord_348254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348284 : List Nat := [2, 2, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_348284 : Nat := 118140960795 + 348284 * 2 ^ 59
def prefixEnd_348284 : Nat := 4983230072969 + 3 ^ 40 * 348284 * 2
def baseEnd_348284 : Nat := 119224730847080380632185

theorem tailTrace_348284 : CollatzResearch.WordTrace tailWord_348284 prefixEnd_348284 119224730847080380632185 := by
  unfold tailWord_348284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351480535117012508345953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8468640713489350011127937 6351480535117012508345953)
  ·
    refine ⟨4763610401337759381259465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6351480535117012508345953 4763610401337759381259465)
    ·
      refine ⟨3572707801003319535944599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4763610401337759381259465 3572707801003319535944599)
      ·
        refine ⟨5359061701504979303916899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572707801003319535944599 5359061701504979303916899)
        ·
          refine ⟨8038592552257468955875349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359061701504979303916899 8038592552257468955875349)
          ·
            refine ⟨376809025887068857306657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8038592552257468955875349 376809025887068857306657)
            ·
              refine ⟨282606769415301642979993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376809025887068857306657 282606769415301642979993)
              ·
                refine ⟨211955077061476232234995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282606769415301642979993 211955077061476232234995)
                ·
                  refine ⟨317932615592214348352493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211955077061476232234995 317932615592214348352493)
                  ·
                    refine ⟨119224730847080380632185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317932615592214348352493 119224730847080380632185)
                    ·
                      rfl

theorem cell22_348284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_348284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348284 prefixEnd_348284 := by exact prefixLift 348284
  have htrace : WordTrace (prefixWord ++ tailWord_348284) baseStart_348284 baseEnd_348284 := by
    simpa [prefixWord, tailWord_348284, baseEnd_348284] using wordTrace_append hprefix tailTrace_348284
  have hstable : (prefixWord ++ tailWord_348284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348284).length < 2 ^ (prefixWord ++ tailWord_348284).sum := by decide
  have hdescent : baseEnd_348284 < baseStart_348284 := by decide
  rcases family_descends (prefixWord ++ tailWord_348284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348293 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_348293 : Nat := 118140960795 + 348293 * 2 ^ 59
def prefixEnd_348293 : Nat := 4983230072969 + 3 ^ 40 * 348293 * 2
def baseEnd_348293 : Nat := 119227811731007357157157

theorem tailTrace_348293 : CollatzResearch.WordTrace tailWord_348293 prefixEnd_348293 119227811731007357157157 := by
  unfold tailWord_348293
  simp only [CollatzResearch.WordTrace]
  refine ⟨12703289327201419553769533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8468859551467613035846355 12703289327201419553769533)
  ·
    refine ⟨4763733497700532332663575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12703289327201419553769533 4763733497700532332663575)
    ·
      refine ⟨7145600246550798498995363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4763733497700532332663575 7145600246550798498995363)
      ·
        refine ⟨10718400369826197748493045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7145600246550798498995363 10718400369826197748493045)
        ·
          refine ⟨1004850034671206038921223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10718400369826197748493045 1004850034671206038921223)
          ·
            refine ⟨1507275052006809058381835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004850034671206038921223 1507275052006809058381835)
            ·
              refine ⟨2260912578010213587572753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507275052006809058381835 2260912578010213587572753)
              ·
                refine ⟨1695684433507660190679565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260912578010213587572753 1695684433507660190679565)
                ·
                  refine ⟨635881662565372571504837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1695684433507660190679565 635881662565372571504837)
                  ·
                    refine ⟨119227811731007357157157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 635881662565372571504837 119227811731007357157157)
                    ·
                      rfl

theorem cell22_348293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_348293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348293 prefixEnd_348293 := by exact prefixLift 348293
  have htrace : WordTrace (prefixWord ++ tailWord_348293) baseStart_348293 baseEnd_348293 := by
    simpa [prefixWord, tailWord_348293, baseEnd_348293] using wordTrace_append hprefix tailTrace_348293
  have hstable : (prefixWord ++ tailWord_348293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348293).length < 2 ^ (prefixWord ++ tailWord_348293).sum := by decide
  have hdescent : baseEnd_348293 < baseStart_348293 := by decide
  rcases family_descends (prefixWord ++ tailWord_348293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348325 : List Nat := [1, 3, 1, 2, 1, 3, 4, 3, 4]
def baseStart_348325 : Nat := 118140960795 + 348325 * 2 ^ 59
def prefixEnd_348325 : Nat := 4983230072969 + 3 ^ 40 * 348325 * 2
def baseEnd_348325 : Nat := 39746255328323313452353

theorem tailTrace_348325 : CollatzResearch.WordTrace tailWord_348325 prefixEnd_348325 39746255328323313452353 := by
  unfold tailWord_348325
  simp only [CollatzResearch.WordTrace]
  refine ⟨12704456463085489018934429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8469637642056992679289619 12704456463085489018934429)
  ·
    refine ⟨4764171173657058382100411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12704456463085489018934429 4764171173657058382100411)
    ·
      refine ⟨7146256760485587573150617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4764171173657058382100411 7146256760485587573150617)
      ·
        refine ⟨5359692570364190679862963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7146256760485587573150617 5359692570364190679862963)
        ·
          refine ⟨8039538855546286019794445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359692570364190679862963 8039538855546286019794445)
          ·
            refine ⟨3014827070829857257422917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8039538855546286019794445 3014827070829857257422917)
            ·
              refine ⟨565280075780598235766797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3014827070829857257422917 565280075780598235766797)
              ·
                refine ⟨211980028417724338412549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565280075780598235766797 211980028417724338412549)
                ·
                  refine ⟨39746255328323313452353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 211980028417724338412549 39746255328323313452353)
                  ·
                    rfl

theorem cell22_348325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_348325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348325 prefixEnd_348325 := by exact prefixLift 348325
  have htrace : WordTrace (prefixWord ++ tailWord_348325) baseStart_348325 baseEnd_348325 := by
    simpa [prefixWord, tailWord_348325, baseEnd_348325] using wordTrace_append hprefix tailTrace_348325
  have hstable : (prefixWord ++ tailWord_348325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348325).length < 2 ^ (prefixWord ++ tailWord_348325).sum := by decide
  have hdescent : baseEnd_348325 < baseStart_348325 := by decide
  rcases family_descends (prefixWord ++ tailWord_348325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348327 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 1, 4]
def baseStart_348327 : Nat := 118140960795 + 348327 * 2 ^ 59
def prefixEnd_348327 : Nat := 4983230072969 + 3 ^ 40 * 348327 * 2
def baseEnd_348327 : Nat := 119239450625842601807053

theorem tailTrace_348327 : CollatzResearch.WordTrace tailWord_348327 prefixEnd_348327 119239450625842601807053 := by
  unfold tailWord_348327
  simp only [CollatzResearch.WordTrace]
  refine ⟨12704529409078243360507235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8469686272718828907004823 12704529409078243360507235)
  ·
    refine ⟨19056794113617365040760853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12704529409078243360507235 19056794113617365040760853)
    ·
      refine ⟨893287224075813986285665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19056794113617365040760853 893287224075813986285665)
      ·
        refine ⟨669965418056860489714249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893287224075813986285665 669965418056860489714249)
        ·
          refine ⟨502474063542645367285687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669965418056860489714249 502474063542645367285687)
          ·
            refine ⟨753711095313968050928531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502474063542645367285687 753711095313968050928531)
            ·
              refine ⟨1130566642970952076392797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753711095313968050928531 1130566642970952076392797)
              ·
                refine ⟨423962491114107028647299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130566642970952076392797 423962491114107028647299)
                ·
                  refine ⟨635943736671160542970949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423962491114107028647299 635943736671160542970949)
                  ·
                    refine ⟨119239450625842601807053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 635943736671160542970949 119239450625842601807053)
                    ·
                      rfl

theorem cell22_348327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_348327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348327 prefixEnd_348327 := by exact prefixLift 348327
  have htrace : WordTrace (prefixWord ++ tailWord_348327) baseStart_348327 baseEnd_348327 := by
    simpa [prefixWord, tailWord_348327, baseEnd_348327] using wordTrace_append hprefix tailTrace_348327
  have hstable : (prefixWord ++ tailWord_348327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348327).length < 2 ^ (prefixWord ++ tailWord_348327).sum := by decide
  have hdescent : baseEnd_348327 < baseStart_348327 := by decide
  rcases family_descends (prefixWord ++ tailWord_348327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348338 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_348338 : Nat := 118140960795 + 348338 * 2 ^ 59
def prefixEnd_348338 : Nat := 4983230072969 + 3 ^ 40 * 348338 * 2
def baseEnd_348338 : Nat := 119243216150642239782019

theorem tailTrace_348338 : CollatzResearch.WordTrace tailWord_348338 prefixEnd_348338 119243216150642239782019 := by
  unfold tailWord_348338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176232653009598059789417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8469953741358928159438445 3176232653009598059789417)
  ·
    refine ⟨2382174489757198544842063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3176232653009598059789417 2382174489757198544842063)
    ·
      refine ⟨3573261734635797817263095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2382174489757198544842063 3573261734635797817263095)
      ·
        refine ⟨5359892601953696725894643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3573261734635797817263095 5359892601953696725894643)
        ·
          refine ⟨8039838902930545088841965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359892601953696725894643 8039838902930545088841965)
          ·
            refine ⟨3014939588598954408315737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8039838902930545088841965 3014939588598954408315737)
            ·
              refine ⟨2261204691449215806236803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3014939588598954408315737 2261204691449215806236803)
              ·
                refine ⟨3391807037173823709355205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2261204691449215806236803 3391807037173823709355205)
                ·
                  refine ⟨635963819470091945504101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3391807037173823709355205 635963819470091945504101)
                  ·
                    refine ⟨119243216150642239782019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 635963819470091945504101 119243216150642239782019)
                    ·
                      rfl

theorem cell22_348338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_348338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348338 prefixEnd_348338 := by exact prefixLift 348338
  have htrace : WordTrace (prefixWord ++ tailWord_348338) baseStart_348338 baseEnd_348338 := by
    simpa [prefixWord, tailWord_348338, baseEnd_348338] using wordTrace_append hprefix tailTrace_348338
  have hstable : (prefixWord ++ tailWord_348338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348338).length < 2 ^ (prefixWord ++ tailWord_348338).sum := by decide
  have hdescent : baseEnd_348338 < baseStart_348338 := by decide
  rcases family_descends (prefixWord ++ tailWord_348338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348370 : List Nat := [3, 2, 2, 2, 1, 2, 4, 6]
def baseStart_348370 : Nat := 118140960795 + 348370 * 2 ^ 59
def prefixEnd_348370 : Nat := 4983230072969 + 3 ^ 40 * 348370 * 2
def baseEnd_348370 : Nat := 13250463378289424775769

theorem tailTrace_348370 : CollatzResearch.WordTrace tailWord_348370 prefixEnd_348370 13250463378289424775769 := by
  unfold tailWord_348370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176524436980615426080641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8470731831948307802881709 3176524436980615426080641)
  ·
    refine ⟨2382393327735461569560481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3176524436980615426080641 2382393327735461569560481)
    ·
      refine ⟨1786794995801596177170361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2382393327735461569560481 1786794995801596177170361)
      ·
        refine ⟨1340096246851197132877771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1786794995801596177170361 1340096246851197132877771)
        ·
          refine ⟨2010144370276795699316657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340096246851197132877771 2010144370276795699316657)
          ·
            refine ⟨1507608277707596774487493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2010144370276795699316657 1507608277707596774487493)
            ·
              refine ⟨282676552070174395216405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1507608277707596774487493 282676552070174395216405)
              ·
                refine ⟨13250463378289424775769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282676552070174395216405 13250463378289424775769)
                ·
                  rfl

theorem cell22_348370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_348370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348370 prefixEnd_348370 := by exact prefixLift 348370
  have htrace : WordTrace (prefixWord ++ tailWord_348370) baseStart_348370 baseEnd_348370 := by
    simpa [prefixWord, tailWord_348370, baseEnd_348370] using wordTrace_append hprefix tailTrace_348370
  have hstable : (prefixWord ++ tailWord_348370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348370).length < 2 ^ (prefixWord ++ tailWord_348370).sum := by decide
  have hdescent : baseEnd_348370 < baseStart_348370 := by decide
  rcases family_descends (prefixWord ++ tailWord_348370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348387 : List Nat := [1, 1, 1, 8, 2, 1, 8]
def baseStart_348387 : Nat := 118140960795 + 348387 * 2 ^ 59
def prefixEnd_348387 : Nat := 4983230072969 + 3 ^ 40 * 348387 * 2
def baseEnd_348387 : Nat := 4417036661186016492847

theorem tailTrace_348387 : CollatzResearch.WordTrace tailWord_348387 prefixEnd_348387 4417036661186016492847 := by
  unfold tailWord_348387
  simp only [CollatzResearch.WordTrace]
  refine ⟨12706717788860873607691415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8471145192573915738460943 12706717788860873607691415)
  ·
    refine ⟨19060076683291310411537123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12706717788860873607691415 19060076683291310411537123)
    ·
      refine ⟨28590115024936965617305685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19060076683291310411537123 28590115024936965617305685)
      ·
        refine ⟨335040410448480065827801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 28590115024936965617305685 335040410448480065827801)
        ·
          refine ⟨251280307836360049370851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335040410448480065827801 251280307836360049370851)
          ·
            refine ⟨376920461754540074056277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251280307836360049370851 376920461754540074056277)
            ·
              refine ⟨4417036661186016492847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 376920461754540074056277 4417036661186016492847)
              ·
                rfl

theorem cell22_348387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 8].length) (baseStart_348387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348387 prefixEnd_348387 := by exact prefixLift 348387
  have htrace : WordTrace (prefixWord ++ tailWord_348387) baseStart_348387 baseEnd_348387 := by
    simpa [prefixWord, tailWord_348387, baseEnd_348387] using wordTrace_append hprefix tailTrace_348387
  have hstable : (prefixWord ++ tailWord_348387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348387).length < 2 ^ (prefixWord ++ tailWord_348387).sum := by decide
  have hdescent : baseEnd_348387 < baseStart_348387 := by decide
  rcases family_descends (prefixWord ++ tailWord_348387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348402 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_348402 : Nat := 118140960795 + 348402 * 2 ^ 59
def prefixEnd_348402 : Nat := 4983230072969 + 3 ^ 40 * 348402 * 2
def baseEnd_348402 : Nat := 119265124658567406181823

theorem tailTrace_348402 : CollatzResearch.WordTrace tailWord_348402 prefixEnd_348402 119265124658567406181823 := by
  unfold tailWord_348402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176816220951632792371865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8471509922537687446324973 3176816220951632792371865)
  ·
    refine ⟨2382612165713724594278899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3176816220951632792371865 2382612165713724594278899)
    ·
      refine ⟨3573918248570586891418349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2382612165713724594278899 3573918248570586891418349)
      ·
        refine ⟨1340219343213970084281881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3573918248570586891418349 1340219343213970084281881)
        ·
          refine ⟨1005164507410477563211411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1340219343213970084281881 1005164507410477563211411)
          ·
            refine ⟨1507746761115716344817117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005164507410477563211411 1507746761115716344817117)
            ·
              refine ⟨565405035418393629306419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1507746761115716344817117 565405035418393629306419)
              ·
                refine ⟨848107553127590443959629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565405035418393629306419 848107553127590443959629)
                ·
                  refine ⟨318040332422846416484861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848107553127590443959629 318040332422846416484861)
                  ·
                    refine ⟨119265124658567406181823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318040332422846416484861 119265124658567406181823)
                    ·
                      rfl

theorem cell22_348402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_348402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348402 prefixEnd_348402 := by exact prefixLift 348402
  have htrace : WordTrace (prefixWord ++ tailWord_348402) baseStart_348402 baseEnd_348402 := by
    simpa [prefixWord, tailWord_348402, baseEnd_348402] using wordTrace_append hprefix tailTrace_348402
  have hstable : (prefixWord ++ tailWord_348402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348402).length < 2 ^ (prefixWord ++ tailWord_348402).sum := by decide
  have hdescent : baseEnd_348402 < baseStart_348402 := by decide
  rcases family_descends (prefixWord ++ tailWord_348402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348413 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_348413 : Nat := 118140960795 + 348413 * 2 ^ 59
def prefixEnd_348413 : Nat := 4983230072969 + 3 ^ 40 * 348413 * 2
def baseEnd_348413 : Nat := 119268890183367044156789

theorem tailTrace_348413 : CollatzResearch.WordTrace tailWord_348413 prefixEnd_348413 119268890183367044156789 := by
  unfold tailWord_348413
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707666086766680048137893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8471777391177786698758595 12707666086766680048137893)
  ·
    refine ⟨2382687391268752509025855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12707666086766680048137893 2382687391268752509025855)
    ·
      refine ⟨3574031086903128763538783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2382687391268752509025855 3574031086903128763538783)
      ·
        refine ⟨5361046630354693145308175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574031086903128763538783 5361046630354693145308175)
        ·
          refine ⟨8041569945532039717962263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5361046630354693145308175 8041569945532039717962263)
          ·
            refine ⟨12062354918298059576943395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8041569945532039717962263 12062354918298059576943395)
            ·
              refine ⟨18093532377447089365415093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12062354918298059576943395 18093532377447089365415093)
              ·
                refine ⟨1696268660385664628007665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18093532377447089365415093 1696268660385664628007665)
                ·
                  refine ⟨1272201495289248471005749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1696268660385664628007665 1272201495289248471005749)
                  ·
                    refine ⟨119268890183367044156789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1272201495289248471005749 119268890183367044156789)
                    ·
                      rfl

theorem cell22_348413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_348413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348413 prefixEnd_348413 := by exact prefixLift 348413
  have htrace : WordTrace (prefixWord ++ tailWord_348413) baseStart_348413 baseEnd_348413 := by
    simpa [prefixWord, tailWord_348413, baseEnd_348413] using wordTrace_append hprefix tailTrace_348413
  have hstable : (prefixWord ++ tailWord_348413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348413).length < 2 ^ (prefixWord ++ tailWord_348413).sum := by decide
  have hdescent : baseEnd_348413 < baseStart_348413 := by decide
  rcases family_descends (prefixWord ++ tailWord_348413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348453 : List Nat := [1, 3, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_348453 : Nat := 118140960795 + 348453 * 2 ^ 59
def prefixEnd_348453 : Nat := 4983230072969 + 3 ^ 40 * 348453 * 2
def baseEnd_348453 : Nat := 119282583000820273156667

theorem tailTrace_348453 : CollatzResearch.WordTrace tailWord_348453 prefixEnd_348453 119282583000820273156667 := by
  unfold tailWord_348453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12709125006621766879594013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8472750004414511253062675 12709125006621766879594013)
  ·
    refine ⟨4765921877483162579847755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12709125006621766879594013 4765921877483162579847755)
    ·
      refine ⟨7148882816224743869771633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4765921877483162579847755 7148882816224743869771633)
      ·
        refine ⟨5361662112168557902328725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7148882816224743869771633 5361662112168557902328725)
        ·
          refine ⟨251327911507901151671659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5361662112168557902328725 251327911507901151671659)
          ·
            refine ⟨376991867261851727507489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251327911507901151671659 376991867261851727507489)
            ·
              refine ⟨282743900446388795630617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376991867261851727507489 282743900446388795630617)
              ·
                refine ⟨212057925334791596722963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282743900446388795630617 212057925334791596722963)
                ·
                  refine ⟨318086888002187395084445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212057925334791596722963 318086888002187395084445)
                  ·
                    refine ⟨119282583000820273156667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318086888002187395084445 119282583000820273156667)
                    ·
                      rfl

theorem cell22_348453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_348453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348453 prefixEnd_348453 := by exact prefixLift 348453
  have htrace : WordTrace (prefixWord ++ tailWord_348453) baseStart_348453 baseEnd_348453 := by
    simpa [prefixWord, tailWord_348453, baseEnd_348453] using wordTrace_append hprefix tailTrace_348453
  have hstable : (prefixWord ++ tailWord_348453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348453).length < 2 ^ (prefixWord ++ tailWord_348453).sum := by decide
  have hdescent : baseEnd_348453 < baseStart_348453 := by decide
  rcases family_descends (prefixWord ++ tailWord_348453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348488 : List Nat := [2, 1, 3, 1, 1, 2, 2, 10]
def baseStart_348488 : Nat := 118140960795 + 348488 * 2 ^ 59
def prefixEnd_348488 : Nat := 4983230072969 + 3 ^ 40 * 348488 * 2
def baseEnd_348488 : Nat := 13254951579565760947951

theorem tailTrace_348488 : CollatzResearch.WordTrace tailWord_348488 prefixEnd_348488 13254951579565760947951 := by
  unfold tailWord_348488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355200780747483928559059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8473601040996645238078745 6355200780747483928559059)
  ·
    refine ⟨9532801171121225892838589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6355200780747483928559059 9532801171121225892838589)
    ·
      refine ⟨3574800439170459709814471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9532801171121225892838589 3574800439170459709814471)
      ·
        refine ⟨5362200658755689564721707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574800439170459709814471 5362200658755689564721707)
        ·
          refine ⟨8043300988133534347082561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362200658755689564721707 8043300988133534347082561)
          ·
            refine ⟨6032475741100150760311921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8043300988133534347082561 6032475741100150760311921)
            ·
              refine ⟨4524356805825113070233941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032475741100150760311921 4524356805825113070233941)
              ·
                refine ⟨13254951579565760947951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4524356805825113070233941 13254951579565760947951)
                ·
                  rfl

theorem cell22_348488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_348488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348488 prefixEnd_348488 := by exact prefixLift 348488
  have htrace : WordTrace (prefixWord ++ tailWord_348488) baseStart_348488 baseEnd_348488 := by
    simpa [prefixWord, tailWord_348488, baseEnd_348488] using wordTrace_append hprefix tailTrace_348488
  have hstable : (prefixWord ++ tailWord_348488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348488).length < 2 ^ (prefixWord ++ tailWord_348488).sum := by decide
  have hdescent : baseEnd_348488 < baseStart_348488 := by decide
  rcases family_descends (prefixWord ++ tailWord_348488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348584 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 5]
def baseStart_348584 : Nat := 118140960795 + 348584 * 2 ^ 59
def prefixEnd_348584 : Nat := 4983230072969 + 3 ^ 40 * 348584 * 2
def baseEnd_348584 : Nat := 39775808992659866043755

theorem tailTrace_348584 : CollatzResearch.WordTrace tailWord_348584 prefixEnd_348584 39775808992659866043755 := by
  unfold tailWord_348584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356951484573588126306403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8475935312764784168408537 6356951484573588126306403)
  ·
    refine ⟨9535427226860382189459605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6356951484573588126306403 9535427226860382189459605)
    ·
      refine ⟨446973151259080415130919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9535427226860382189459605 446973151259080415130919)
      ·
        refine ⟨670459726888620622696379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446973151259080415130919 670459726888620622696379)
        ·
          refine ⟨1005689590332930934044569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670459726888620622696379 1005689590332930934044569)
          ·
            refine ⟨754267192749698200533427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005689590332930934044569 754267192749698200533427)
            ·
              refine ⟨1131400789124547300800141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754267192749698200533427 1131400789124547300800141)
              ·
                refine ⟨424275295921705237800053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1131400789124547300800141 424275295921705237800053)
                ·
                  refine ⟨39775808992659866043755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 424275295921705237800053 39775808992659866043755)
                  ·
                    rfl

theorem cell22_348584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_348584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348584 prefixEnd_348584 := by exact prefixLift 348584
  have htrace : WordTrace (prefixWord ++ tailWord_348584) baseStart_348584 baseEnd_348584 := by
    simpa [prefixWord, tailWord_348584, baseEnd_348584] using wordTrace_append hprefix tailTrace_348584
  have hstable : (prefixWord ++ tailWord_348584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348584).length < 2 ^ (prefixWord ++ tailWord_348584).sum := by decide
  have hdescent : baseEnd_348584 < baseStart_348584 := by decide
  rcases family_descends (prefixWord ++ tailWord_348584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348629 : List Nat := [1, 3, 2, 3, 1, 3, 1, 4, 4]
def baseStart_348629 : Nat := 118140960795 + 348629 * 2 ^ 59
def prefixEnd_348629 : Nat := 4983230072969 + 3 ^ 40 * 348629 * 2
def baseEnd_348629 : Nat := 39780943799204826918709

theorem tailTrace_348629 : CollatzResearch.WordTrace tailWord_348629 prefixEnd_348629 39780943799204826918709 := by
  unfold tailWord_348629
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715544253984148938000941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8477029502656099292000627 12715544253984148938000941)
  ·
    refine ⟨4768329095244055851750353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12715544253984148938000941 4768329095244055851750353)
    ·
      refine ⟨3576246821433041888812765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4768329095244055851750353 3576246821433041888812765)
      ·
        refine ⟨1341092558037390708304787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3576246821433041888812765 1341092558037390708304787)
        ·
          refine ⟨2011638837056086062457181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341092558037390708304787 2011638837056086062457181)
          ·
            refine ⟨754364563896032273421443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2011638837056086062457181 754364563896032273421443)
            ·
              refine ⟨1131546845844048410132165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754364563896032273421443 1131546845844048410132165)
              ·
                refine ⟨212165033595759076899781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1131546845844048410132165 212165033595759076899781)
                ·
                  refine ⟨39780943799204826918709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212165033595759076899781 39780943799204826918709)
                  ·
                    rfl

theorem cell22_348629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_348629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348629 prefixEnd_348629 := by exact prefixLift 348629
  have htrace : WordTrace (prefixWord ++ tailWord_348629) baseStart_348629 baseEnd_348629 := by
    simpa [prefixWord, tailWord_348629, baseEnd_348629] using wordTrace_append hprefix tailTrace_348629
  have hstable : (prefixWord ++ tailWord_348629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348629).length < 2 ^ (prefixWord ++ tailWord_348629).sum := by decide
  have hdescent : baseEnd_348629 < baseStart_348629 := by decide
  rcases family_descends (prefixWord ++ tailWord_348629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348657 : List Nat := [1, 2, 2, 2, 3, 1, 5, 6]
def baseStart_348657 : Nat := 118140960795 + 348657 * 2 ^ 59
def prefixEnd_348657 : Nat := 4983230072969 + 3 ^ 40 * 348657 * 2
def baseEnd_348657 : Nat := 13261379596647971228449

theorem tailTrace_348657 : CollatzResearch.WordTrace tailWord_348657 prefixEnd_348657 13261379596647971228449 := by
  unfold tailWord_348657
  simp only [CollatzResearch.WordTrace]
  refine ⟨12716565497882709720020225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8477710331921806480013483 12716565497882709720020225)
  ·
    refine ⟨9537424123412032290015169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12716565497882709720020225 9537424123412032290015169)
    ·
      refine ⟨7153068092559024217511377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9537424123412032290015169 7153068092559024217511377)
      ·
        refine ⟨5364801069419268163133533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7153068092559024217511377 5364801069419268163133533)
        ·
          refine ⟨2011800401032225561175075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5364801069419268163133533 2011800401032225561175075)
          ·
            refine ⟨3017700601548338341762613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011800401032225561175075 3017700601548338341762613)
            ·
              refine ⟨282909431395156719540245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3017700601548338341762613 282909431395156719540245)
              ·
                refine ⟨13261379596647971228449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282909431395156719540245 13261379596647971228449)
                ·
                  rfl

theorem cell22_348657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 6].length) (baseStart_348657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348657 prefixEnd_348657 := by exact prefixLift 348657
  have htrace : WordTrace (prefixWord ++ tailWord_348657) baseStart_348657 baseEnd_348657 := by
    simpa [prefixWord, tailWord_348657, baseEnd_348657] using wordTrace_append hprefix tailTrace_348657
  have hstable : (prefixWord ++ tailWord_348657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348657).length < 2 ^ (prefixWord ++ tailWord_348657).sum := by decide
  have hdescent : baseEnd_348657 < baseStart_348657 := by decide
  rcases family_descends (prefixWord ++ tailWord_348657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348674 : List Nat := [3, 4, 1, 2, 2, 1, 9]
def baseStart_348674 : Nat := 118140960795 + 348674 * 2 ^ 59
def prefixEnd_348674 : Nat := 4983230072969 + 3 ^ 40 * 348674 * 2
def baseEnd_348674 : Nat := 4420675400638865310407

theorem tailTrace_348674 : CollatzResearch.WordTrace tailWord_348674 prefixEnd_348674 4420675400638865310407 := by
  unfold tailWord_348674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179296384705280405847269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8478123692547414415592717 3179296384705280405847269)
  ·
    refine ⟨596118072132240076096363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3179296384705280405847269 596118072132240076096363)
    ·
      refine ⟨894177108198360114144545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596118072132240076096363 894177108198360114144545)
      ·
        refine ⟨670632831148770085608409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 894177108198360114144545 670632831148770085608409)
        ·
          refine ⟨502974623361577564206307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 670632831148770085608409 502974623361577564206307)
          ·
            refine ⟨754461935042366346309461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502974623361577564206307 754461935042366346309461)
            ·
              refine ⟨4420675400638865310407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 754461935042366346309461 4420675400638865310407)
              ·
                rfl

theorem cell22_348674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 9].length) (baseStart_348674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348674 prefixEnd_348674 := by exact prefixLift 348674
  have htrace : WordTrace (prefixWord ++ tailWord_348674) baseStart_348674 baseEnd_348674 := by
    simpa [prefixWord, tailWord_348674, baseEnd_348674] using wordTrace_append hprefix tailTrace_348674
  have hstable : (prefixWord ++ tailWord_348674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348674).length < 2 ^ (prefixWord ++ tailWord_348674).sum := by decide
  have hdescent : baseEnd_348674 < baseStart_348674 := by decide
  rcases family_descends (prefixWord ++ tailWord_348674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348708 : List Nat := [2, 3, 1, 5, 2, 1, 2, 6]
def baseStart_348708 : Nat := 118140960795 + 348708 * 2 ^ 59
def prefixEnd_348708 : Nat := 4983230072969 + 3 ^ 40 * 348708 * 2
def baseEnd_348708 : Nat := 13263319412453845336765

theorem tailTrace_348708 : CollatzResearch.WordTrace tailWord_348708 prefixEnd_348708 13263319412453845336765 := by
  unfold tailWord_348708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359212810348972715063389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8478950413798630286751185 6359212810348972715063389)
  ·
    refine ⟨2384704803880864768148771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6359212810348972715063389 2384704803880864768148771)
    ·
      refine ⟨3577057205821297152223157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2384704803880864768148771 3577057205821297152223157)
      ·
        refine ⟨335349113045746608020921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3577057205821297152223157 335349113045746608020921)
        ·
          refine ⟨251511834784309956015691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335349113045746608020921 251511834784309956015691)
          ·
            refine ⟨377267752176464934023537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251511834784309956015691 377267752176464934023537)
            ·
              refine ⟨282950814132348700517653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377267752176464934023537 282950814132348700517653)
              ·
                refine ⟨13263319412453845336765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 282950814132348700517653 13263319412453845336765)
                ·
                  rfl

theorem cell22_348708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 6].length) (baseStart_348708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348708 prefixEnd_348708 := by exact prefixLift 348708
  have htrace : WordTrace (prefixWord ++ tailWord_348708) baseStart_348708 baseEnd_348708 := by
    simpa [prefixWord, tailWord_348708, baseEnd_348708] using wordTrace_append hprefix tailTrace_348708
  have hstable : (prefixWord ++ tailWord_348708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348708).length < 2 ^ (prefixWord ++ tailWord_348708).sum := by decide
  have hdescent : baseEnd_348708 < baseStart_348708 := by decide
  rcases family_descends (prefixWord ++ tailWord_348708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348715 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 8]
def baseStart_348715 : Nat := 118140960795 + 348715 * 2 ^ 59
def prefixEnd_348715 : Nat := 4983230072969 + 3 ^ 40 * 348715 * 2
def baseEnd_348715 : Nat := 119372270955138923105863

theorem tailTrace_348715 : CollatzResearch.WordTrace tailWord_348715 prefixEnd_348715 119372270955138923105863 := by
  unfold tailWord_348715
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718680931672585625631599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8479120621115057083754399 12718680931672585625631599)
  ·
    refine ⟨19078021397508878438447399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12718680931672585625631599 19078021397508878438447399)
    ·
      refine ⟨28617032096263317657671099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19078021397508878438447399 28617032096263317657671099)
      ·
        refine ⟨42925548144394976486506649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28617032096263317657671099 42925548144394976486506649)
        ·
          refine ⟨32194161108296232364879987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42925548144394976486506649 32194161108296232364879987)
          ·
            refine ⟨48291241662444348547319981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32194161108296232364879987 48291241662444348547319981)
            ·
              refine ⟨18109215623416630705244993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48291241662444348547319981 18109215623416630705244993)
              ·
                refine ⟨13581911717562473028933745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18109215623416630705244993 13581911717562473028933745)
                ·
                  refine ⟨10186433788171854771700309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13581911717562473028933745 10186433788171854771700309)
                  ·
                    refine ⟨119372270955138923105863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10186433788171854771700309 119372270955138923105863)
                    ·
                      rfl

theorem cell22_348715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_348715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348715 prefixEnd_348715 := by exact prefixLift 348715
  have htrace : WordTrace (prefixWord ++ tailWord_348715) baseStart_348715 baseEnd_348715 := by
    simpa [prefixWord, tailWord_348715, baseEnd_348715] using wordTrace_append hprefix tailTrace_348715
  have hstable : (prefixWord ++ tailWord_348715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348715).length < 2 ^ (prefixWord ++ tailWord_348715).sum := by decide
  have hdescent : baseEnd_348715 < baseStart_348715 := by decide
  rcases family_descends (prefixWord ++ tailWord_348715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348747 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 6]
def baseStart_348747 : Nat := 118140960795 + 348747 * 2 ^ 59
def prefixEnd_348747 : Nat := 4983230072969 + 3 ^ 40 * 348747 * 2
def baseEnd_348747 : Nat := 39794408403033835435255

theorem tailTrace_348747 : CollatzResearch.WordTrace tailWord_348747 prefixEnd_348747 39794408403033835435255 := by
  unfold tailWord_348747
  simp only [CollatzResearch.WordTrace]
  refine ⟨12719848067556655090796495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8479898711704436727197663 12719848067556655090796495)
  ·
    refine ⟨19079772101334982636194743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12719848067556655090796495 19079772101334982636194743)
    ·
      refine ⟨28619658152002473954292115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19079772101334982636194743 28619658152002473954292115)
      ·
        refine ⟨42929487228003710931438173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28619658152002473954292115 42929487228003710931438173)
        ·
          refine ⟨16098557710501391599289315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42929487228003710931438173 16098557710501391599289315)
          ·
            refine ⟨24147836565752087398933973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16098557710501391599289315 24147836565752087398933973)
            ·
              refine ⟨565964919509814548412515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24147836565752087398933973 565964919509814548412515)
              ·
                refine ⟨848947379264721822618773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565964919509814548412515 848947379264721822618773)
                ·
                  refine ⟨39794408403033835435255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 848947379264721822618773 39794408403033835435255)
                  ·
                    rfl

theorem cell22_348747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 6].length) (baseStart_348747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348747 prefixEnd_348747 := by exact prefixLift 348747
  have htrace : WordTrace (prefixWord ++ tailWord_348747) baseStart_348747 baseEnd_348747 := by
    simpa [prefixWord, tailWord_348747, baseEnd_348747] using wordTrace_append hprefix tailTrace_348747
  have hstable : (prefixWord ++ tailWord_348747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348747).length < 2 ^ (prefixWord ++ tailWord_348747).sum := by decide
  have hdescent : baseEnd_348747 < baseStart_348747 := by decide
  rcases family_descends (prefixWord ++ tailWord_348747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348837 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 7]
def baseStart_348837 : Nat := 118140960795 + 348837 * 2 ^ 59
def prefixEnd_348837 : Nat := 4983230072969 + 3 ^ 40 * 348837 * 2
def baseEnd_348837 : Nat := 39804678016123757185163

theorem tailTrace_348837 : CollatzResearch.WordTrace tailWord_348837 prefixEnd_348837 39804678016123757185163 := by
  unfold tailWord_348837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12723130637230600461572765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8482087091487066974381843 12723130637230600461572765)
  ·
    refine ⟨4771173988961475173089787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12723130637230600461572765 4771173988961475173089787)
    ·
      refine ⟨7156760983442212759634681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771173988961475173089787 7156760983442212759634681)
      ·
        refine ⟨5367570737581659569726011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7156760983442212759634681 5367570737581659569726011)
        ·
          refine ⟨8051356106372489354589017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367570737581659569726011 8051356106372489354589017)
          ·
            refine ⟨6038517079779367015941763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8051356106372489354589017 6038517079779367015941763)
            ·
              refine ⟨9057775619669050523912645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6038517079779367015941763 9057775619669050523912645)
              ·
                refine ⟨1698332928687946973233621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9057775619669050523912645 1698332928687946973233621)
                ·
                  refine ⟨39804678016123757185163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1698332928687946973233621 39804678016123757185163)
                  ·
                    rfl

theorem cell22_348837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_348837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348837 prefixEnd_348837 := by exact prefixLift 348837
  have htrace : WordTrace (prefixWord ++ tailWord_348837) baseStart_348837 baseEnd_348837 := by
    simpa [prefixWord, tailWord_348837, baseEnd_348837] using wordTrace_append hprefix tailTrace_348837
  have hstable : (prefixWord ++ tailWord_348837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348837).length < 2 ^ (prefixWord ++ tailWord_348837).sum := by decide
  have hdescent : baseEnd_348837 < baseStart_348837 := by decide
  rcases family_descends (prefixWord ++ tailWord_348837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348841 : List Nat := [1, 2, 1, 1, 1, 1, 2, 9, 1, 3]
def baseStart_348841 : Nat := 118140960795 + 348841 * 2 ^ 59
def prefixEnd_348841 : Nat := 4983230072969 + 3 ^ 40 * 348841 * 2
def baseEnd_348841 : Nat := 119415403330116594455477

theorem tailTrace_348841 : CollatzResearch.WordTrace tailWord_348841 prefixEnd_348841 119415403330116594455477 := by
  unfold tailWord_348841
  simp only [CollatzResearch.WordTrace]
  refine ⟨12723276529216109144718377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8482184352810739429812251 12723276529216109144718377)
  ·
    refine ⟨9542457396912081858538783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12723276529216109144718377 9542457396912081858538783)
    ·
      refine ⟨14313686095368122787808175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9542457396912081858538783 14313686095368122787808175)
      ·
        refine ⟨21470529143052184181712263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14313686095368122787808175 21470529143052184181712263)
        ·
          refine ⟨32205793714578276272568395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21470529143052184181712263 32205793714578276272568395)
          ·
            refine ⟨48308690571867414408852593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32205793714578276272568395 48308690571867414408852593)
            ·
              refine ⟨36231517928900560806639445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48308690571867414408852593 36231517928900560806639445)
              ·
                refine ⟨212294050364651723476403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 36231517928900560806639445 212294050364651723476403)
                ·
                  refine ⟨318441075546977585214605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212294050364651723476403 318441075546977585214605)
                  ·
                    refine ⟨119415403330116594455477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318441075546977585214605 119415403330116594455477)
                    ·
                      rfl

theorem cell22_348841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 3].length) (baseStart_348841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348841 prefixEnd_348841 := by exact prefixLift 348841
  have htrace : WordTrace (prefixWord ++ tailWord_348841) baseStart_348841 baseEnd_348841 := by
    simpa [prefixWord, tailWord_348841, baseEnd_348841] using wordTrace_append hprefix tailTrace_348841
  have hstable : (prefixWord ++ tailWord_348841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348841).length < 2 ^ (prefixWord ++ tailWord_348841).sum := by decide
  have hdescent : baseEnd_348841 < baseStart_348841 := by decide
  rcases family_descends (prefixWord ++ tailWord_348841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348892 : List Nat := [2, 2, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_348892 : Nat := 118140960795 + 348892 * 2 ^ 59
def prefixEnd_348892 : Nat := 4983230072969 + 3 ^ 40 * 348892 * 2
def baseEnd_348892 : Nat := 119432861672369461430321

theorem tailTrace_348892 : CollatzResearch.WordTrace tailWord_348892 prefixEnd_348892 119432861672369461430321 := by
  unfold tailWord_348892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6362568326015672427412465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8483424434687563236549953 6362568326015672427412465)
  ·
    refine ⟨4771926244511754320559349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6362568326015672427412465 4771926244511754320559349)
    ·
      refine ⟨447368085422976967552439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4771926244511754320559349 447368085422976967552439)
      ·
        refine ⟨671052128134465451328659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447368085422976967552439 671052128134465451328659)
        ·
          refine ⟨1006578192201698176992989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671052128134465451328659 1006578192201698176992989)
          ·
            refine ⟨377466822075636816372371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1006578192201698176992989 377466822075636816372371)
            ·
              refine ⟨566200233113455224558557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377466822075636816372371 566200233113455224558557)
              ·
                refine ⟨212325087417545709209459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566200233113455224558557 212325087417545709209459)
                ·
                  refine ⟨318487631126318563814189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212325087417545709209459 318487631126318563814189)
                  ·
                    refine ⟨119432861672369461430321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318487631126318563814189 119432861672369461430321)
                    ·
                      rfl

theorem cell22_348892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_348892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348892 prefixEnd_348892 := by exact prefixLift 348892
  have htrace : WordTrace (prefixWord ++ tailWord_348892) baseStart_348892 baseEnd_348892 := by
    simpa [prefixWord, tailWord_348892, baseEnd_348892] using wordTrace_append hprefix tailTrace_348892
  have hstable : (prefixWord ++ tailWord_348892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348892).length < 2 ^ (prefixWord ++ tailWord_348892).sum := by decide
  have hdescent : baseEnd_348892 < baseStart_348892 := by decide
  rcases family_descends (prefixWord ++ tailWord_348892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348901 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_348901 : Nat := 118140960795 + 348901 * 2 ^ 59
def prefixEnd_348901 : Nat := 4983230072969 + 3 ^ 40 * 348901 * 2
def baseEnd_348901 : Nat := 119435942556296437955293

theorem tailTrace_348901 : CollatzResearch.WordTrace tailWord_348901 prefixEnd_348901 119435942556296437955293 := by
  unfold tailWord_348901
  simp only [CollatzResearch.WordTrace]
  refine ⟨12725464908998739391902557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8483643272665826261268371 12725464908998739391902557)
  ·
    refine ⟨4772049340874527271963459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12725464908998739391902557 4772049340874527271963459)
    ·
      refine ⟨7158074011311790907945189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4772049340874527271963459 7158074011311790907945189)
      ·
        refine ⟨1342138877120960795239723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7158074011311790907945189 1342138877120960795239723)
        ·
          refine ⟨2013208315681441192859585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342138877120960795239723 2013208315681441192859585)
          ·
            refine ⟨1509906236761080894644689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2013208315681441192859585 1509906236761080894644689)
            ·
              refine ⟨1132429677570810670983517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1509906236761080894644689 1132429677570810670983517)
              ·
                refine ⟨424661129089054001618819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1132429677570810670983517 424661129089054001618819)
                ·
                  refine ⟨636991693633581002428229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424661129089054001618819 636991693633581002428229)
                  ·
                    refine ⟨119435942556296437955293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 636991693633581002428229 119435942556296437955293)
                    ·
                      rfl

theorem cell22_348901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_348901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348901 prefixEnd_348901 := by exact prefixLift 348901
  have htrace : WordTrace (prefixWord ++ tailWord_348901) baseStart_348901 baseEnd_348901 := by
    simpa [prefixWord, tailWord_348901, baseEnd_348901] using wordTrace_append hprefix tailTrace_348901
  have hstable : (prefixWord ++ tailWord_348901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348901).length < 2 ^ (prefixWord ++ tailWord_348901).sum := by decide
  have hdescent : baseEnd_348901 < baseStart_348901 := by decide
  rcases family_descends (prefixWord ++ tailWord_348901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348929 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_348929 : Nat := 118140960795 + 348929 * 2 ^ 59
def prefixEnd_348929 : Nat := 4983230072969 + 3 ^ 40 * 348929 * 2
def baseEnd_348929 : Nat := 119445527528513698255207

theorem tailTrace_348929 : CollatzResearch.WordTrace tailWord_348929 prefixEnd_348929 119445527528513698255207 := by
  unfold tailWord_348929
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726486152897300173921841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8484324101931533449281227 12726486152897300173921841)
  ·
    refine ⟨9544864614672975130441381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12726486152897300173921841 9544864614672975130441381)
    ·
      refine ⟨1789662115251182836957759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9544864614672975130441381 1789662115251182836957759)
      ·
        refine ⟨2684493172876774255436639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789662115251182836957759 2684493172876774255436639)
        ·
          refine ⟨4026739759315161383154959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2684493172876774255436639 4026739759315161383154959)
          ·
            refine ⟨6040109638972742074732439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026739759315161383154959 6040109638972742074732439)
            ·
              refine ⟨9060164458459113112098659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040109638972742074732439 9060164458459113112098659)
              ·
                refine ⟨13590246687688669668147989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9060164458459113112098659 13590246687688669668147989)
                ·
                  refine ⟨637042813485406390694437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13590246687688669668147989 637042813485406390694437)
                  ·
                    refine ⟨119445527528513698255207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 637042813485406390694437 119445527528513698255207)
                    ·
                      rfl

theorem cell22_348929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_348929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_348929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_348929 prefixEnd_348929 := by exact prefixLift 348929
  have htrace : WordTrace (prefixWord ++ tailWord_348929) baseStart_348929 baseEnd_348929 := by
    simpa [prefixWord, tailWord_348929, baseEnd_348929] using wordTrace_append hprefix tailTrace_348929
  have hstable : (prefixWord ++ tailWord_348929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348929).length < 2 ^ (prefixWord ++ tailWord_348929).sum := by decide
  have hdescent : baseEnd_348929 < baseStart_348929 := by decide
  rcases family_descends (prefixWord ++ tailWord_348929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349010 : List Nat := [3, 2, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_349010 : Nat := 118140960795 + 349010 * 2 ^ 59
def prefixEnd_349010 : Nat := 4983230072969 + 3 ^ 40 * 349010 * 2
def baseEnd_349010 : Nat := 119473255483856486979959

theorem tailTrace_349010 : CollatzResearch.WordTrace tailWord_349010 prefixEnd_349010 119473255483856486979959 := by
  unfold tailWord_349010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182360116400962751905121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8486293643735900671746989 3182360116400962751905121)
  ·
    refine ⟨2386770087300722063928841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3182360116400962751905121 2386770087300722063928841)
    ·
      refine ⟨1790077565475541547946631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2386770087300722063928841 1790077565475541547946631)
      ·
        refine ⟨2685116348213312321919947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790077565475541547946631 2685116348213312321919947)
        ·
          refine ⟨4027674522319968482879921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685116348213312321919947 4027674522319968482879921)
          ·
            refine ⟨3020755891739976362159941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4027674522319968482879921 3020755891739976362159941)
            ·
              refine ⟨566391729701245567904989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3020755891739976362159941 566391729701245567904989)
              ·
                refine ⟨212396898637967087964371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566391729701245567904989 212396898637967087964371)
                ·
                  refine ⟨318595347956950631946557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212396898637967087964371 318595347956950631946557)
                  ·
                    refine ⟨119473255483856486979959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318595347956950631946557 119473255483856486979959)
                    ·
                      rfl

theorem cell22_349010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_349010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349010 prefixEnd_349010 := by exact prefixLift 349010
  have htrace : WordTrace (prefixWord ++ tailWord_349010) baseStart_349010 baseEnd_349010 := by
    simpa [prefixWord, tailWord_349010, baseEnd_349010] using wordTrace_append hprefix tailTrace_349010
  have hstable : (prefixWord ++ tailWord_349010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349010).length < 2 ^ (prefixWord ++ tailWord_349010).sum := by decide
  have hdescent : baseEnd_349010 < baseStart_349010 := by decide
  rcases family_descends (prefixWord ++ tailWord_349010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349068 : List Nat := [2, 2, 1, 2, 1, 2, 5, 3, 4]
def baseStart_349068 : Nat := 118140960795 + 349068 * 2 ^ 59
def prefixEnd_349068 : Nat := 4983230072969 + 3 ^ 40 * 349068 * 2
def baseEnd_349068 : Nat := 39831036689721223009927

theorem tailTrace_349068 : CollatzResearch.WordTrace tailWord_349068 prefixEnd_349068 39831036689721223009927 := by
  unfold tailWord_349068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6365777949696863456615929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8487703932929151275487905 6365777949696863456615929)
  ·
    refine ⟨4774333462272647592461947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6365777949696863456615929 4774333462272647592461947)
    ·
      refine ⟨7161500193408971388692921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4774333462272647592461947 7161500193408971388692921)
      ·
        refine ⟨5371125145056728541519691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7161500193408971388692921 5371125145056728541519691)
        ·
          refine ⟨8056687717585092812279537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371125145056728541519691 8056687717585092812279537)
          ·
            refine ⟨6042515788188819609209653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056687717585092812279537 6042515788188819609209653)
            ·
              refine ⟨566485855142701838363405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6042515788188819609209653 566485855142701838363405)
              ·
                refine ⟨212432195678513189386277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566485855142701838363405 212432195678513189386277)
                ·
                  refine ⟨39831036689721223009927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212432195678513189386277 39831036689721223009927)
                  ·
                    rfl

theorem cell22_349068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_349068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349068 prefixEnd_349068 := by exact prefixLift 349068
  have htrace : WordTrace (prefixWord ++ tailWord_349068) baseStart_349068 baseEnd_349068 := by
    simpa [prefixWord, tailWord_349068, baseEnd_349068] using wordTrace_append hprefix tailTrace_349068
  have hstable : (prefixWord ++ tailWord_349068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349068).length < 2 ^ (prefixWord ++ tailWord_349068).sum := by decide
  have hdescent : baseEnd_349068 < baseStart_349068 := by decide
  rcases family_descends (prefixWord ++ tailWord_349068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349085 : List Nat := [1, 4, 2, 1, 2, 1, 5, 2, 4]
def baseStart_349085 : Nat := 118140960795 + 349085 * 2 ^ 59
def prefixEnd_349085 : Nat := 4983230072969 + 3 ^ 40 * 349085 * 2
def baseEnd_349085 : Nat := 39832976505527097118243

theorem tailTrace_349085 : CollatzResearch.WordTrace tailWord_349085 prefixEnd_349085 39832976505527097118243 := by
  unfold tailWord_349085
  simp only [CollatzResearch.WordTrace]
  refine ⟨12732175940332138816600709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8488117293554759211067139 12732175940332138816600709)
  ·
    refine ⟨2387282988812276028112633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12732175940332138816600709 2387282988812276028112633)
    ·
      refine ⟨1790462241609207021084475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2387282988812276028112633 1790462241609207021084475)
      ·
        refine ⟨2685693362413810531626713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790462241609207021084475 2685693362413810531626713)
        ·
          refine ⟨2014270021810357898720035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685693362413810531626713 2014270021810357898720035)
          ·
            refine ⟨3021405032715536848080053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014270021810357898720035 3021405032715536848080053)
            ·
              refine ⟨283256721817081579507505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3021405032715536848080053 283256721817081579507505)
              ·
                refine ⟨212442541362811184630629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283256721817081579507505 212442541362811184630629)
                ·
                  refine ⟨39832976505527097118243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212442541362811184630629 39832976505527097118243)
                  ·
                    rfl

theorem cell22_349085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_349085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349085 prefixEnd_349085 := by exact prefixLift 349085
  have htrace : WordTrace (prefixWord ++ tailWord_349085) baseStart_349085 baseEnd_349085 := by
    simpa [prefixWord, tailWord_349085, baseEnd_349085] using wordTrace_append hprefix tailTrace_349085
  have hstable : (prefixWord ++ tailWord_349085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349085).length < 2 ^ (prefixWord ++ tailWord_349085).sum := by decide
  have hdescent : baseEnd_349085 < baseStart_349085 := by decide
  rcases family_descends (prefixWord ++ tailWord_349085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349201 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_349201 : Nat := 118140960795 + 349201 * 2 ^ 59
def prefixEnd_349201 : Nat := 4983230072969 + 3 ^ 40 * 349201 * 2
def baseEnd_349201 : Nat := 119538638687195655454373

theorem tailTrace_349201 : CollatzResearch.WordTrace tailWord_349201 prefixEnd_349201 119538638687195655454373 := by
  unfold tailWord_349201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12736406807911890627823457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8490937871941260418548971 12736406807911890627823457)
  ·
    refine ⟨9552305105933917970867593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12736406807911890627823457 9552305105933917970867593)
    ·
      refine ⟨7164228829450438478150695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9552305105933917970867593 7164228829450438478150695)
      ·
        refine ⟨10746343244175657717226043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7164228829450438478150695 10746343244175657717226043)
        ·
          refine ⟨16119514866263486575839065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746343244175657717226043 16119514866263486575839065)
          ·
            refine ⟨12089636149697614931879299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16119514866263486575839065 12089636149697614931879299)
            ·
              refine ⟨18134454224546422397818949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12089636149697614931879299 18134454224546422397818949)
              ·
                refine ⟨3400210167102454199591053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18134454224546422397818949 3400210167102454199591053)
                ·
                  refine ⟨1275078812663420324846645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3400210167102454199591053 1275078812663420324846645)
                  ·
                    refine ⟨119538638687195655454373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1275078812663420324846645 119538638687195655454373)
                    ·
                      rfl

theorem cell22_349201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_349201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_349201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_349201 prefixEnd_349201 := by exact prefixLift 349201
  have htrace : WordTrace (prefixWord ++ tailWord_349201) baseStart_349201 baseEnd_349201 := by
    simpa [prefixWord, tailWord_349201, baseEnd_349201] using wordTrace_append hprefix tailTrace_349201
  have hstable : (prefixWord ++ tailWord_349201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349201).length < 2 ^ (prefixWord ++ tailWord_349201).sum := by decide
  have hdescent : baseEnd_349201 < baseStart_349201 := by decide
  rcases family_descends (prefixWord ++ tailWord_349201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
