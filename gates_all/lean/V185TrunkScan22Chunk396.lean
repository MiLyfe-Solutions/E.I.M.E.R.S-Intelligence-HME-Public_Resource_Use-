import V185TrunkScan22Chunk395

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3532764 : List Nat := [2, 2, 6, 1, 1, 2, 1, 7]
def baseStart_3532764 : Nat := 118140960795 + 3532764 * 2 ^ 59
def prefixEnd_3532764 : Nat := 4983230072969 + 3 ^ 40 * 3532764 * 2
def baseEnd_3532764 : Nat := 134370812659283057652083

theorem tailTrace_3532764 : CollatzResearch.WordTrace tailWord_3532764 prefixEnd_3532764 134370812659283057652083 := by
  unfold tailWord_3532764
  simp only [CollatzResearch.WordTrace]
  refine ⟨64425244286703425450658673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85900325715604567267544897 64425244286703425450658673)
  ·
    refine ⟨48318933215027569087994005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64425244286703425450658673 48318933215027569087994005)
    ·
      refine ⟨2264949994454417300999719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48318933215027569087994005 2264949994454417300999719)
      ·
        refine ⟨3397424991681625951499579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2264949994454417300999719 3397424991681625951499579)
        ·
          refine ⟨5096137487522438927249369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397424991681625951499579 5096137487522438927249369)
          ·
            refine ⟨3822103115641829195437027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5096137487522438927249369 3822103115641829195437027)
            ·
              refine ⟨5733154673462743793155541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822103115641829195437027 5733154673462743793155541)
              ·
                refine ⟨134370812659283057652083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5733154673462743793155541 134370812659283057652083)
                ·
                  rfl

theorem cell22_3532764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 7].length) (baseStart_3532764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532764 prefixEnd_3532764 := by exact prefixLift 3532764
  have htrace : WordTrace (prefixWord ++ tailWord_3532764) baseStart_3532764 baseEnd_3532764 := by
    simpa [prefixWord, tailWord_3532764, baseEnd_3532764] using wordTrace_append hprefix tailTrace_3532764
  have hstable : (prefixWord ++ tailWord_3532764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532764).length < 2 ^ (prefixWord ++ tailWord_3532764).sum := by decide
  have hdescent : baseEnd_3532764 < baseStart_3532764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532805 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_3532805 : Nat := 118140960795 + 3532805 * 2 ^ 59
def prefixEnd_3532805 : Nat := 4983230072969 + 3 ^ 40 * 3532805 * 2
def baseEnd_3532805 : Nat := 1209351349071437078593621

theorem tailTrace_3532805 : CollatzResearch.WordTrace tailWord_3532805 prefixEnd_3532805 1209351349071437078593621 := by
  unfold tailWord_3532805
  simp only [CollatzResearch.WordTrace]
  refine ⟨128851983966258314903559869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85901322644172209935706579 128851983966258314903559869)
  ·
    refine ⟨48319493987346868088834951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128851983966258314903559869 48319493987346868088834951)
    ·
      refine ⟨72479240981020302133252427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48319493987346868088834951 72479240981020302133252427)
      ·
        refine ⟨108718861471530453199878641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72479240981020302133252427 108718861471530453199878641)
        ·
          refine ⟨81539146103647839899908981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108718861471530453199878641 81539146103647839899908981)
          ·
            refine ⟨7644294947216984990616467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81539146103647839899908981 7644294947216984990616467)
            ·
              refine ⟨11466442420825477485924701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644294947216984990616467 11466442420825477485924701)
              ·
                refine ⟨4299915907809554057221763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11466442420825477485924701 4299915907809554057221763)
                ·
                  refine ⟨6449873861714331085832645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299915907809554057221763 6449873861714331085832645)
                  ·
                    refine ⟨1209351349071437078593621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6449873861714331085832645 1209351349071437078593621)
                    ·
                      rfl

theorem cell22_3532805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_3532805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532805 prefixEnd_3532805 := by exact prefixLift 3532805
  have htrace : WordTrace (prefixWord ++ tailWord_3532805) baseStart_3532805 baseEnd_3532805 := by
    simpa [prefixWord, tailWord_3532805, baseEnd_3532805] using wordTrace_append hprefix tailTrace_3532805
  have hstable : (prefixWord ++ tailWord_3532805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532805).length < 2 ^ (prefixWord ++ tailWord_3532805).sum := by decide
  have hdescent : baseEnd_3532805 < baseStart_3532805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532839 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3532839 : Nat := 118140960795 + 3532839 * 2 ^ 59
def prefixEnd_3532839 : Nat := 4983230072969 + 3 ^ 40 * 3532839 * 2
def baseEnd_3532839 : Nat := 1209362987966272323243517

theorem tailTrace_3532839 : CollatzResearch.WordTrace tailWord_3532839 prefixEnd_3532839 1209362987966272323243517 := by
  unfold tailWord_3532839
  simp only [CollatzResearch.WordTrace]
  refine ⟨128853224048135138710297571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85902149365423425806865047 128853224048135138710297571)
  ·
    refine ⟨193279836072202708065446357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128853224048135138710297571 193279836072202708065446357)
    ·
      refine ⟨4529996157942250970283899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 193279836072202708065446357 4529996157942250970283899)
      ·
        refine ⟨6794994236913376455425849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529996157942250970283899 6794994236913376455425849)
        ·
          refine ⟨5096245677685032341569387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6794994236913376455425849 5096245677685032341569387)
          ·
            refine ⟨7644368516527548512354081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096245677685032341569387 7644368516527548512354081)
            ·
              refine ⟨5733276387395661384265561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644368516527548512354081 5733276387395661384265561)
              ·
                refine ⟨4299957290546746038199171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5733276387395661384265561 4299957290546746038199171)
                ·
                  refine ⟨6449935935820119057298757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299957290546746038199171 6449935935820119057298757)
                  ·
                    refine ⟨1209362987966272323243517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6449935935820119057298757 1209362987966272323243517)
                    ·
                      rfl

theorem cell22_3532839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3532839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532839 prefixEnd_3532839 := by exact prefixLift 3532839
  have htrace : WordTrace (prefixWord ++ tailWord_3532839) baseStart_3532839 baseEnd_3532839 := by
    simpa [prefixWord, tailWord_3532839, baseEnd_3532839] using wordTrace_append hprefix tailTrace_3532839
  have hstable : (prefixWord ++ tailWord_3532839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532839).length < 2 ^ (prefixWord ++ tailWord_3532839).sum := by decide
  have hdescent : baseEnd_3532839 < baseStart_3532839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532848 : List Nat := [2, 1, 1, 1, 2, 6, 1, 8]
def baseStart_3532848 : Nat := 118140960795 + 3532848 * 2 ^ 59
def prefixEnd_3532848 : Nat := 4983230072969 + 3 ^ 40 * 3532848 * 2
def baseEnd_3532848 : Nat := 134374007650022144418721

theorem tailTrace_3532848 : CollatzResearch.WordTrace tailWord_3532848 prefixEnd_3532848 134374007650022144418721 := by
  unfold tailWord_3532848
  simp only [CollatzResearch.WordTrace]
  refine ⟨64426776152551266623687599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85902368203401688831583465 64426776152551266623687599)
  ·
    refine ⟨96640164228826899935531399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64426776152551266623687599 96640164228826899935531399)
    ·
      refine ⟨144960246343240349903297099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96640164228826899935531399 144960246343240349903297099)
      ·
        refine ⟨217440369514860524854945649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144960246343240349903297099 217440369514860524854945649)
        ·
          refine ⟨163080277136145393641209237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217440369514860524854945649 163080277136145393641209237)
          ·
            refine ⟨7644387990756815326931683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163080277136145393641209237 7644387990756815326931683)
            ·
              refine ⟨11466581986135222990397525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644387990756815326931683 11466581986135222990397525)
              ·
                refine ⟨134374007650022144418721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11466581986135222990397525 134374007650022144418721)
                ·
                  rfl

theorem cell22_3532848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_3532848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532848 prefixEnd_3532848 := by exact prefixLift 3532848
  have htrace : WordTrace (prefixWord ++ tailWord_3532848) baseStart_3532848 baseEnd_3532848 := by
    simpa [prefixWord, tailWord_3532848, baseEnd_3532848] using wordTrace_append hprefix tailTrace_3532848
  have hstable : (prefixWord ++ tailWord_3532848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532848).length < 2 ^ (prefixWord ++ tailWord_3532848).sum := by decide
  have hdescent : baseEnd_3532848 < baseStart_3532848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532865 : List Nat := [1, 2, 5, 1, 2, 3, 8]
def baseStart_3532865 : Nat := 118140960795 + 3532865 * 2 ^ 59
def prefixEnd_3532865 : Nat := 4983230072969 + 3 ^ 40 * 3532865 * 2
def baseEnd_3532865 : Nat := 44791551418430256373831

theorem tailTrace_3532865 : CollatzResearch.WordTrace tailWord_3532865 prefixEnd_3532865 44791551418430256373831 := by
  unfold tailWord_3532865
  simp only [CollatzResearch.WordTrace]
  refine ⟨128854172346040945150744049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85902781564027296767162699 128854172346040945150744049)
  ·
    refine ⟨96640629259530708863058037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128854172346040945150744049 96640629259530708863058037)
    ·
      refine ⟨9060058993081003955911691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96640629259530708863058037 9060058993081003955911691)
      ·
        refine ⟨13590088489621505933867537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060058993081003955911691 13590088489621505933867537)
        ·
          refine ⟨10192566367216129450400653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13590088489621505933867537 10192566367216129450400653)
          ·
            refine ⟨3822212387706048543900245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10192566367216129450400653 3822212387706048543900245)
            ·
              refine ⟨44791551418430256373831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3822212387706048543900245 44791551418430256373831)
              ·
                rfl

theorem cell22_3532865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 8].length) (baseStart_3532865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532865 prefixEnd_3532865 := by exact prefixLift 3532865
  have htrace : WordTrace (prefixWord ++ tailWord_3532865) baseStart_3532865 baseEnd_3532865 := by
    simpa [prefixWord, tailWord_3532865, baseEnd_3532865] using wordTrace_append hprefix tailTrace_3532865
  have hstable : (prefixWord ++ tailWord_3532865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532865).length < 2 ^ (prefixWord ++ tailWord_3532865).sum := by decide
  have hdescent : baseEnd_3532865 < baseStart_3532865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532886 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3532886 : Nat := 118140960795 + 3532886 * 2 ^ 59
def prefixEnd_3532886 : Nat := 4983230072969 + 3 ^ 40 * 3532886 * 2
def baseEnd_3532886 : Nat := 1209379077026779867318373

theorem tailTrace_3532886 : CollatzResearch.WordTrace tailWord_3532886 prefixEnd_3532886 1209379077026779867318373 := by
  unfold tailWord_3532886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053433642435304108578657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85903292185976577158172341 8053433642435304108578657)
  ·
    refine ⟨6040075231826478081433993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8053433642435304108578657 6040075231826478081433993)
    ·
      refine ⟨4530056423869858561075495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6040075231826478081433993 4530056423869858561075495)
      ·
        refine ⟨6795084635804787841613243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530056423869858561075495 6795084635804787841613243)
        ·
          refine ⟨10192626953707181762419865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6795084635804787841613243 10192626953707181762419865)
          ·
            refine ⟨7644470215280386321814899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10192626953707181762419865 7644470215280386321814899)
            ·
              refine ⟨11466705322920579482722349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644470215280386321814899 11466705322920579482722349)
              ·
                refine ⟨4300014496095217306020881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11466705322920579482722349 4300014496095217306020881)
                ·
                  refine ⟨3225010872071412979515661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300014496095217306020881 3225010872071412979515661)
                  ·
                    refine ⟨1209379077026779867318373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225010872071412979515661 1209379077026779867318373)
                    ·
                      rfl

theorem cell22_3532886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3532886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532886 prefixEnd_3532886 := by exact prefixLift 3532886
  have htrace : WordTrace (prefixWord ++ tailWord_3532886) baseStart_3532886 baseEnd_3532886 := by
    simpa [prefixWord, tailWord_3532886, baseEnd_3532886] using wordTrace_append hprefix tailTrace_3532886
  have hstable : (prefixWord ++ tailWord_3532886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532886).length < 2 ^ (prefixWord ++ tailWord_3532886).sum := by decide
  have hdescent : baseEnd_3532886 < baseStart_3532886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532931 : List Nat := [1, 1, 1, 3, 3, 5, 2, 2, 1, 3]
def baseStart_3532931 : Nat := 118140960795 + 3532931 * 2 ^ 59
def prefixEnd_3532931 : Nat := 4983230072969 + 3 ^ 40 * 3532931 * 2
def baseEnd_3532931 : Nat := 1209394481446414749943235

theorem tailTrace_3532931 : CollatzResearch.WordTrace tailWord_3532931 prefixEnd_3532931 1209394481446414749943235 := by
  unfold tailWord_3532931
  simp only [CollatzResearch.WordTrace]
  refine ⟨128856579563801838422646647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85904386375867892281764431 128856579563801838422646647)
  ·
    refine ⟨193284869345702757633969971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128856579563801838422646647 193284869345702757633969971)
    ·
      refine ⟨289927304018554136450954957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193284869345702757633969971 289927304018554136450954957)
      ·
        refine ⟨108722739006957801169108109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289927304018554136450954957 108722739006957801169108109)
        ·
          refine ⟨40771027127609175438415541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108722739006957801169108109 40771027127609175438415541)
          ·
            refine ⟨3822283793213360197351457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40771027127609175438415541 3822283793213360197351457)
            ·
              refine ⟨2866712844910020148013593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822283793213360197351457 2866712844910020148013593)
              ·
                refine ⟨2150034633682515111010195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866712844910020148013593 2150034633682515111010195)
                ·
                  refine ⟨3225051950523772666515293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150034633682515111010195 3225051950523772666515293)
                  ·
                    refine ⟨1209394481446414749943235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225051950523772666515293 1209394481446414749943235)
                    ·
                      rfl

theorem cell22_3532931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 1, 3].length) (baseStart_3532931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532931 prefixEnd_3532931 := by exact prefixLift 3532931
  have htrace : WordTrace (prefixWord ++ tailWord_3532931) baseStart_3532931 baseEnd_3532931 := by
    simpa [prefixWord, tailWord_3532931, baseEnd_3532931] using wordTrace_append hprefix tailTrace_3532931
  have hstable : (prefixWord ++ tailWord_3532931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532931).length < 2 ^ (prefixWord ++ tailWord_3532931).sum := by decide
  have hdescent : baseEnd_3532931 < baseStart_3532931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532942 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3532942 : Nat := 118140960795 + 3532942 * 2 ^ 59
def prefixEnd_3532942 : Nat := 4983230072969 + 3 ^ 40 * 3532942 * 2
def baseEnd_3532942 : Nat := 1209398246971214387918201

theorem tailTrace_3532942 : CollatzResearch.WordTrace tailWord_3532942 prefixEnd_3532942 1209398246971214387918201 := by
  unfold tailWord_3532942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16107122595845248412662135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85904653844507991534198053 16107122595845248412662135)
  ·
    refine ⟨24160683893767872618993203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16107122595845248412662135 24160683893767872618993203)
    ·
      refine ⟨36241025840651808928489805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24160683893767872618993203 36241025840651808928489805)
      ·
        refine ⟨13590384690244428348183677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36241025840651808928489805 13590384690244428348183677)
        ·
          refine ⟨5096394258841660630568879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13590384690244428348183677 5096394258841660630568879)
          ·
            refine ⟨7644591388262490945853319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096394258841660630568879 7644591388262490945853319)
            ·
              refine ⟨11466887082393736418779979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644591388262490945853319 11466887082393736418779979)
              ·
                refine ⟨17200330623590604628169969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11466887082393736418779979 17200330623590604628169969)
                ·
                  refine ⟨12900247967692953471127477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17200330623590604628169969 12900247967692953471127477)
                  ·
                    refine ⟨1209398246971214387918201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12900247967692953471127477 1209398246971214387918201)
                    ·
                      rfl

theorem cell22_3532942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3532942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532942 prefixEnd_3532942 := by exact prefixLift 3532942
  have htrace : WordTrace (prefixWord ++ tailWord_3532942) baseStart_3532942 baseEnd_3532942 := by
    simpa [prefixWord, tailWord_3532942, baseEnd_3532942] using wordTrace_append hprefix tailTrace_3532942
  have hstable : (prefixWord ++ tailWord_3532942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532942).length < 2 ^ (prefixWord ++ tailWord_3532942).sum := by decide
  have hdescent : baseEnd_3532942 < baseStart_3532942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532985 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_3532985 : Nat := 118140960795 + 3532985 * 2 ^ 59
def prefixEnd_3532985 : Nat := 4983230072969 + 3 ^ 40 * 3532985 * 2
def baseEnd_3532985 : Nat := 1209412966749976609093069

theorem tailTrace_3532985 : CollatzResearch.WordTrace tailWord_3532985 prefixEnd_3532985 1209412966749976609093069 := by
  unfold tailWord_3532985
  simp only [CollatzResearch.WordTrace]
  refine ⟨128858549105606205645112409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85905699403737470430074939 128858549105606205645112409)
  ·
    refine ⟨96643911829204654233834307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128858549105606205645112409 96643911829204654233834307)
    ·
      refine ⟨144965867743806981350751461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96643911829204654233834307 144965867743806981350751461)
      ·
        refine ⟨27181100201963809003265899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144965867743806981350751461 27181100201963809003265899)
        ·
          refine ⟨40771650302945713504898849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27181100201963809003265899 40771650302945713504898849)
          ·
            refine ⟨30578737727209285128674137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40771650302945713504898849 30578737727209285128674137)
            ·
              refine ⟨22934053295406963846505603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30578737727209285128674137 22934053295406963846505603)
              ·
                refine ⟨34401079943110445769758405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22934053295406963846505603 34401079943110445769758405)
                ·
                  refine ⟨6450202489333208581829701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34401079943110445769758405 6450202489333208581829701)
                  ·
                    refine ⟨1209412966749976609093069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6450202489333208581829701 1209412966749976609093069)
                    ·
                      rfl

theorem cell22_3532985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_3532985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3532985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3532985 prefixEnd_3532985 := by exact prefixLift 3532985
  have htrace : WordTrace (prefixWord ++ tailWord_3532985) baseStart_3532985 baseEnd_3532985 := by
    simpa [prefixWord, tailWord_3532985, baseEnd_3532985] using wordTrace_append hprefix tailTrace_3532985
  have hstable : (prefixWord ++ tailWord_3532985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532985).length < 2 ^ (prefixWord ++ tailWord_3532985).sum := by decide
  have hdescent : baseEnd_3532985 < baseStart_3532985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533137 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_3533137 : Nat := 118140960795 + 3533137 * 2 ^ 59
def prefixEnd_3533137 : Nat := 4983230072969 + 3 ^ 40 * 3533137 * 2
def baseEnd_3533137 : Nat := 1209464999456298879292603

theorem tailTrace_3533137 : CollatzResearch.WordTrace tailWord_3533137 prefixEnd_3533137 1209464999456298879292603 := by
  unfold tailWord_3533137
  simp only [CollatzResearch.WordTrace]
  refine ⟨128864093001055535604645665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85909395334037023736430443 128864093001055535604645665)
  ·
    refine ⟨96648069750791651703484249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128864093001055535604645665 96648069750791651703484249)
    ·
      refine ⟨72486052313093738777613187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96648069750791651703484249 72486052313093738777613187)
      ·
        refine ⟨108729078469640608166419781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72486052313093738777613187 108729078469640608166419781)
        ·
          refine ⟨20386702213057614031203709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108729078469640608166419781 20386702213057614031203709)
          ·
            refine ⟨7645013329896605261701391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20386702213057614031203709 7645013329896605261701391)
            ·
              refine ⟨11467519994844907892552087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645013329896605261701391 11467519994844907892552087)
              ·
                refine ⟨17201279992267361838828131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11467519994844907892552087 17201279992267361838828131)
                ·
                  refine ⟨25801919988401042758242197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17201279992267361838828131 25801919988401042758242197)
                  ·
                    refine ⟨1209464999456298879292603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25801919988401042758242197 1209464999456298879292603)
                    ·
                      rfl

theorem cell22_3533137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_3533137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533137 prefixEnd_3533137 := by exact prefixLift 3533137
  have htrace : WordTrace (prefixWord ++ tailWord_3533137) baseStart_3533137 baseEnd_3533137 := by
    simpa [prefixWord, tailWord_3533137, baseEnd_3533137] using wordTrace_append hprefix tailTrace_3533137
  have hstable : (prefixWord ++ tailWord_3533137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533137).length < 2 ^ (prefixWord ++ tailWord_3533137).sum := by decide
  have hdescent : baseEnd_3533137 < baseStart_3533137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533141 : List Nat := [1, 3, 2, 2, 4, 1, 2, 3, 4]
def baseStart_3533141 : Nat := 118140960795 + 3533141 * 2 ^ 59
def prefixEnd_3533141 : Nat := 4983230072969 + 3 ^ 40 * 3533141 * 2
def baseEnd_3533141 : Nat := 403155456246014734064197

theorem tailTrace_3533141 : CollatzResearch.WordTrace tailWord_3533141 prefixEnd_3533141 403155456246014734064197 := by
  unfold tailWord_3533141
  simp only [CollatzResearch.WordTrace]
  refine ⟨128864238893041044287791277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85909492595360696191860851 128864238893041044287791277)
  ·
    refine ⟨48324089584890391607921729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128864238893041044287791277 48324089584890391607921729)
    ·
      refine ⟨36243067188667793705941297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48324089584890391607921729 36243067188667793705941297)
      ·
        refine ⟨27182300391500845279455973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36243067188667793705941297 27182300391500845279455973)
        ·
          refine ⟨5096681323406408489897995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27182300391500845279455973 5096681323406408489897995)
          ·
            refine ⟨7645021985109612734846993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096681323406408489897995 7645021985109612734846993)
            ·
              refine ⟨5733766488832209551135245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7645021985109612734846993 5733766488832209551135245)
              ·
                refine ⟨2150162433312078581675717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5733766488832209551135245 2150162433312078581675717)
                ·
                  refine ⟨403155456246014734064197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150162433312078581675717 403155456246014734064197)
                  ·
                    rfl

theorem cell22_3533141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_3533141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533141 prefixEnd_3533141 := by exact prefixLift 3533141
  have htrace : WordTrace (prefixWord ++ tailWord_3533141) baseStart_3533141 baseEnd_3533141 := by
    simpa [prefixWord, tailWord_3533141, baseEnd_3533141] using wordTrace_append hprefix tailTrace_3533141
  have hstable : (prefixWord ++ tailWord_3533141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533141).length < 2 ^ (prefixWord ++ tailWord_3533141).sum := by decide
  have hdescent : baseEnd_3533141 < baseStart_3533141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533152 : List Nat := [2, 1, 1, 3, 5, 1, 9]
def baseStart_3533152 : Nat := 118140960795 + 3533152 * 2 ^ 59
def prefixEnd_3533152 : Nat := 4983230072969 + 3 ^ 40 * 3533152 * 2
def baseEnd_3533152 : Nat := 44795190157883105191391

theorem tailTrace_3533152 : CollatzResearch.WordTrace tailWord_3533152 prefixEnd_3533152 44795190157883105191391 := by
  unfold tailWord_3533152
  simp only [CollatzResearch.WordTrace]
  refine ⟨64432320048000596583220855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85909760064000795444294473 64432320048000596583220855)
  ·
    refine ⟨96648480072000894874831283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64432320048000596583220855 96648480072000894874831283)
    ·
      refine ⟨144972720108001342312246925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96648480072000894874831283 144972720108001342312246925)
      ·
        refine ⟨54364770040500503367092597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144972720108001342312246925 54364770040500503367092597)
        ·
          refine ⟨5096697191296922190664931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54364770040500503367092597 5096697191296922190664931)
          ·
            refine ⟨7645045786945383285997397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096697191296922190664931 7645045786945383285997397)
            ·
              refine ⟨44795190157883105191391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7645045786945383285997397 44795190157883105191391)
              ·
                rfl

theorem cell22_3533152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 9].length) (baseStart_3533152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533152 prefixEnd_3533152 := by exact prefixLift 3533152
  have htrace : WordTrace (prefixWord ++ tailWord_3533152) baseStart_3533152 baseEnd_3533152 := by
    simpa [prefixWord, tailWord_3533152, baseEnd_3533152] using wordTrace_append hprefix tailTrace_3533152
  have hstable : (prefixWord ++ tailWord_3533152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533152).length < 2 ^ (prefixWord ++ tailWord_3533152).sum := by decide
  have hdescent : baseEnd_3533152 < baseStart_3533152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533173 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3533173 : Nat := 118140960795 + 3533173 * 2 ^ 59
def prefixEnd_3533173 : Nat := 4983230072969 + 3 ^ 40 * 3533173 * 2
def baseEnd_3533173 : Nat := 1209477322992006785392493

theorem tailTrace_3533173 : CollatzResearch.WordTrace tailWord_3533173 prefixEnd_3533173 1209477322992006785392493 := by
  unfold tailWord_3533173
  simp only [CollatzResearch.WordTrace]
  refine ⟨128865406028925113752956173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85910270685950075835304115 128865406028925113752956173)
  ·
    refine ⟨48324527260846917657358565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128865406028925113752956173 48324527260846917657358565)
    ·
      refine ⟨9060848861408797060754731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48324527260846917657358565 9060848861408797060754731)
      ·
        refine ⟨13591273292113195591132097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060848861408797060754731 13591273292113195591132097)
        ·
          refine ⟨10193454969084896693349073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13591273292113195591132097 10193454969084896693349073)
          ·
            refine ⟨7645091226813672520011805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10193454969084896693349073 7645091226813672520011805)
            ·
              refine ⟨2866909210055127195004427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7645091226813672520011805 2866909210055127195004427)
              ·
                refine ⟨4300363815082690792506641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866909210055127195004427 4300363815082690792506641)
                ·
                  refine ⟨3225272861312018094379981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300363815082690792506641 3225272861312018094379981)
                  ·
                    refine ⟨1209477322992006785392493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225272861312018094379981 1209477322992006785392493)
                    ·
                      rfl

theorem cell22_3533173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3533173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533173 prefixEnd_3533173 := by exact prefixLift 3533173
  have htrace : WordTrace (prefixWord ++ tailWord_3533173) baseStart_3533173 baseEnd_3533173 := by
    simpa [prefixWord, tailWord_3533173, baseEnd_3533173] using wordTrace_append hprefix tailTrace_3533173
  have hstable : (prefixWord ++ tailWord_3533173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533173).length < 2 ^ (prefixWord ++ tailWord_3533173).sum := by decide
  have hdescent : baseEnd_3533173 < baseStart_3533173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533186 : List Nat := [3, 4, 2, 1, 2, 1, 1, 8]
def baseStart_3533186 : Nat := 118140960795 + 3533186 * 2 ^ 59
def prefixEnd_3533186 : Nat := 4983230072969 + 3 ^ 40 * 3533186 * 2
def baseEnd_3533186 : Nat := 134386863684186564979717

theorem tailTrace_3533186 : CollatzResearch.WordTrace tailWord_3533186 prefixEnd_3533186 134386863684186564979717 := by
  unfold tailWord_3533186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216470044469504243294853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85910586785252011315452941 32216470044469504243294853)
  ·
    refine ⟨6040588133338032045617785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32216470044469504243294853 6040588133338032045617785)
    ·
      refine ⟨4530441100003524034213339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6040588133338032045617785 4530441100003524034213339)
      ·
        refine ⟨6795661650005286051320009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530441100003524034213339 6795661650005286051320009)
        ·
          refine ⟨5096746237503964538490007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6795661650005286051320009 5096746237503964538490007)
          ·
            refine ⟨7645119356255946807735011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096746237503964538490007 7645119356255946807735011)
            ·
              refine ⟨11467679034383920211602517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645119356255946807735011 11467679034383920211602517)
              ·
                refine ⟨134386863684186564979717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11467679034383920211602517 134386863684186564979717)
                ·
                  rfl

theorem cell22_3533186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_3533186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533186 prefixEnd_3533186 := by exact prefixLift 3533186
  have htrace : WordTrace (prefixWord ++ tailWord_3533186) baseStart_3533186 baseEnd_3533186 := by
    simpa [prefixWord, tailWord_3533186, baseEnd_3533186] using wordTrace_append hprefix tailTrace_3533186
  have hstable : (prefixWord ++ tailWord_3533186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533186).length < 2 ^ (prefixWord ++ tailWord_3533186).sum := by decide
  have hdescent : baseEnd_3533186 < baseStart_3533186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533242 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_3533242 : Nat := 118140960795 + 3533242 * 2 ^ 59
def prefixEnd_3533242 : Nat := 4983230072969 + 3 ^ 40 * 3533242 * 2
def baseEnd_3533242 : Nat := 403166981034037868472427

theorem tailTrace_3533242 : CollatzResearch.WordTrace tailWord_3533242 prefixEnd_3533242 403166981034037868472427 := by
  unfold tailWord_3533242
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216980666418784634304495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85911948443783425691478653 32216980666418784634304495)
  ·
    refine ⟨48325470999628176951456743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32216980666418784634304495 48325470999628176951456743)
    ·
      refine ⟨72488206499442265427185115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48325470999628176951456743 72488206499442265427185115)
      ·
        refine ⟨108732309749163398140777673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72488206499442265427185115 108732309749163398140777673)
        ·
          refine ⟨81549232311872548605583255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108732309749163398140777673 81549232311872548605583255)
          ·
            refine ⟨122323848467808822908374883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81549232311872548605583255 122323848467808822908374883)
            ·
              refine ⟨183485772701713234362562325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122323848467808822908374883 183485772701713234362562325)
              ·
                refine ⟨8600895595392807860745109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183485772701713234362562325 8600895595392807860745109)
                ·
                  refine ⟨403166981034037868472427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8600895595392807860745109 403166981034037868472427)
                  ·
                    rfl

theorem cell22_3533242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_3533242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533242 prefixEnd_3533242 := by exact prefixLift 3533242
  have htrace : WordTrace (prefixWord ++ tailWord_3533242) baseStart_3533242 baseEnd_3533242 := by
    simpa [prefixWord, tailWord_3533242, baseEnd_3533242] using wordTrace_append hprefix tailTrace_3533242
  have hstable : (prefixWord ++ tailWord_3533242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533242).length < 2 ^ (prefixWord ++ tailWord_3533242).sum := by decide
  have hdescent : baseEnd_3533242 < baseStart_3533242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533257 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_3533257 : Nat := 118140960795 + 3533257 * 2 ^ 59
def prefixEnd_3533257 : Nat := 4983230072969 + 3 ^ 40 * 3533257 * 2
def baseEnd_3533257 : Nat := 1209506077908658566292235

theorem tailTrace_3533257 : CollatzResearch.WordTrace tailWord_3533257 prefixEnd_3533257 1209506077908658566292235 := by
  unfold tailWord_3533257
  simp only [CollatzResearch.WordTrace]
  refine ⟨128868469760620796099014025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85912313173747197399342683 128868469760620796099014025)
  ·
    refine ⟨96651352320465597074260519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128868469760620796099014025 96651352320465597074260519)
    ·
      refine ⟨144977028480698395611390779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96651352320465597074260519 144977028480698395611390779)
      ·
        refine ⟨217465542721047593417086169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144977028480698395611390779 217465542721047593417086169)
        ·
          refine ⟨163099157040785695062814627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217465542721047593417086169 163099157040785695062814627)
          ·
            refine ⟨244648735561178542594221941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163099157040785695062814627 244648735561178542594221941)
            ·
              refine ⟨22935818958860488368208307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244648735561178542594221941 22935818958860488368208307)
              ·
                refine ⟨34403728438290732552312461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22935818958860488368208307 34403728438290732552312461)
                ·
                  refine ⟨12901398164359024707117173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34403728438290732552312461 12901398164359024707117173)
                  ·
                    refine ⟨1209506077908658566292235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12901398164359024707117173 1209506077908658566292235)
                    ·
                      rfl

theorem cell22_3533257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_3533257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533257 prefixEnd_3533257 := by exact prefixLift 3533257
  have htrace : WordTrace (prefixWord ++ tailWord_3533257) baseStart_3533257 baseEnd_3533257 := by
    simpa [prefixWord, tailWord_3533257, baseEnd_3533257] using wordTrace_append hprefix tailTrace_3533257
  have hstable : (prefixWord ++ tailWord_3533257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533257).length < 2 ^ (prefixWord ++ tailWord_3533257).sum := by decide
  have hdescent : baseEnd_3533257 < baseStart_3533257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533259 : List Nat := [1, 1, 1, 1, 3, 3, 1, 7, 4]
def baseStart_3533259 : Nat := 118140960795 + 3533259 * 2 ^ 59
def prefixEnd_3533259 : Nat := 4983230072969 + 3 ^ 40 * 3533259 * 2
def baseEnd_3533259 : Nat := 403168920849843742580743

theorem tailTrace_3533259 : CollatzResearch.WordTrace tailWord_3533259 prefixEnd_3533259 403168920849843742580743 := by
  unfold tailWord_3533259
  simp only [CollatzResearch.WordTrace]
  refine ⟨128868542706613550440586831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85912361804409033627057887 128868542706613550440586831)
  ·
    refine ⟨193302814059920325660880247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128868542706613550440586831 193302814059920325660880247)
    ·
      refine ⟨289954221089880488491320371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193302814059920325660880247 289954221089880488491320371)
      ·
        refine ⟨434931331634820732736980557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289954221089880488491320371 434931331634820732736980557)
        ·
          refine ⟨163099249363057774776367709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434931331634820732736980557 163099249363057774776367709)
          ·
            refine ⟨61162218511146665541137891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163099249363057774776367709 61162218511146665541137891)
            ·
              refine ⟨91743327766719998311706837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61162218511146665541137891 91743327766719998311706837)
              ·
                refine ⟨2150234244532499960430629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91743327766719998311706837 2150234244532499960430629)
                ·
                  refine ⟨403168920849843742580743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150234244532499960430629 403168920849843742580743)
                  ·
                    rfl

theorem cell22_3533259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 4].length) (baseStart_3533259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533259 prefixEnd_3533259 := by exact prefixLift 3533259
  have htrace : WordTrace (prefixWord ++ tailWord_3533259) baseStart_3533259 baseEnd_3533259 := by
    simpa [prefixWord, tailWord_3533259, baseEnd_3533259] using wordTrace_append hprefix tailTrace_3533259
  have hstable : (prefixWord ++ tailWord_3533259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533259).length < 2 ^ (prefixWord ++ tailWord_3533259).sum := by decide
  have hdescent : baseEnd_3533259 < baseStart_3533259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533272 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_3533272 : Nat := 118140960795 + 3533272 * 2 ^ 59
def prefixEnd_3533272 : Nat := 4983230072969 + 3 ^ 40 * 3533272 * 2
def baseEnd_3533272 : Nat := 1209511212715203527167189

theorem tailTrace_3533272 : CollatzResearch.WordTrace tailWord_3533272 prefixEnd_3533272 1209511212715203527167189 := by
  unfold tailWord_3533272
  simp only [CollatzResearch.WordTrace]
  refine ⟨64434508427783226830405035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85912677903710969107206713 64434508427783226830405035)
  ·
    refine ⟨96651762641674840245607553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64434508427783226830405035 96651762641674840245607553)
    ·
      refine ⟨72488821981256130184205665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96651762641674840245607553 72488821981256130184205665)
      ·
        refine ⟨54366616485942097638154249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72488821981256130184205665 54366616485942097638154249)
        ·
          refine ⟨40774962364456573228615687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54366616485942097638154249 40774962364456573228615687)
          ·
            refine ⟨61162443546684859842923531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40774962364456573228615687 61162443546684859842923531)
            ·
              refine ⟨91743665320027289764385297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61162443546684859842923531 91743665320027289764385297)
              ·
                refine ⟨68807748990020467323288973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91743665320027289764385297 68807748990020467323288973)
                ·
                  refine ⟨25802905871257675246233365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68807748990020467323288973 25802905871257675246233365)
                  ·
                    refine ⟨1209511212715203527167189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25802905871257675246233365 1209511212715203527167189)
                    ·
                      rfl

theorem cell22_3533272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_3533272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533272 prefixEnd_3533272 := by exact prefixLift 3533272
  have htrace : WordTrace (prefixWord ++ tailWord_3533272) baseStart_3533272 baseEnd_3533272 := by
    simpa [prefixWord, tailWord_3533272, baseEnd_3533272] using wordTrace_append hprefix tailTrace_3533272
  have hstable : (prefixWord ++ tailWord_3533272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533272).length < 2 ^ (prefixWord ++ tailWord_3533272).sum := by decide
  have hdescent : baseEnd_3533272 < baseStart_3533272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533304 : List Nat := [2, 1, 2, 1, 1, 4, 5, 6]
def baseStart_3533304 : Nat := 118140960795 + 3533304 * 2 ^ 59
def prefixEnd_3533304 : Nat := 4983230072969 + 3 ^ 40 * 3533304 * 2
def baseEnd_3533304 : Nat := 134391351885462901151899

theorem tailTrace_3533304 : CollatzResearch.WordTrace tailWord_3533304 prefixEnd_3533304 134391351885462901151899 := by
  unfold tailWord_3533304
  simp only [CollatzResearch.WordTrace]
  refine ⟨64435091995725261562987483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85913455994300348750649977 64435091995725261562987483)
  ·
    refine ⟨96652637993587892344481225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64435091995725261562987483 96652637993587892344481225)
    ·
      refine ⟨72489478495190919258360919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96652637993587892344481225 72489478495190919258360919)
      ·
        refine ⟨108734217742786378887541379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72489478495190919258360919 108734217742786378887541379)
        ·
          refine ⟨163101326614179568331312069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108734217742786378887541379 163101326614179568331312069)
          ·
            refine ⟨30581498740158669062121013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163101326614179568331312069 30581498740158669062121013)
            ·
              refine ⟨2867015506889875224573845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30581498740158669062121013 2867015506889875224573845)
              ·
                refine ⟨134391351885462901151899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2867015506889875224573845 134391351885462901151899)
                ·
                  rfl

theorem cell22_3533304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 6].length) (baseStart_3533304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533304 prefixEnd_3533304 := by exact prefixLift 3533304
  have htrace : WordTrace (prefixWord ++ tailWord_3533304) baseStart_3533304 baseEnd_3533304 := by
    simpa [prefixWord, tailWord_3533304, baseEnd_3533304] using wordTrace_append hprefix tailTrace_3533304
  have hstable : (prefixWord ++ tailWord_3533304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533304).length < 2 ^ (prefixWord ++ tailWord_3533304).sum := by decide
  have hdescent : baseEnd_3533304 < baseStart_3533304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533325 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3533325 : Nat := 118140960795 + 3533325 * 2 ^ 59
def prefixEnd_3533325 : Nat := 4983230072969 + 3 ^ 40 * 3533325 * 2
def baseEnd_3533325 : Nat := 1209529355698329055592027

theorem tailTrace_3533325 : CollatzResearch.WordTrace tailWord_3533325 prefixEnd_3533325 1209529355698329055592027 := by
  unfold tailWord_3533325
  simp only [CollatzResearch.WordTrace]
  refine ⟨128870949924374443712489429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85913966616249629141659619 128870949924374443712489429)
  ·
    refine ⟨3020412888852526024511471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 128870949924374443712489429 3020412888852526024511471)
    ·
      refine ⟨4530619333278789036767207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020412888852526024511471 4530619333278789036767207)
      ·
        refine ⟨6795928999918183555150811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530619333278789036767207 6795928999918183555150811)
        ·
          refine ⟨10193893499877275332726217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6795928999918183555150811 10193893499877275332726217)
          ·
            refine ⟨7645420124907956499544663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10193893499877275332726217 7645420124907956499544663)
            ·
              refine ⟨11468130187361934749316995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645420124907956499544663 11468130187361934749316995)
              ·
                refine ⟨17202195281042902123975493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11468130187361934749316995 17202195281042902123975493)
                ·
                  refine ⟨3225411615195544148245405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17202195281042902123975493 3225411615195544148245405)
                  ·
                    refine ⟨1209529355698329055592027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225411615195544148245405 1209529355698329055592027)
                    ·
                      rfl

theorem cell22_3533325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3533325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533325 prefixEnd_3533325 := by exact prefixLift 3533325
  have htrace : WordTrace (prefixWord ++ tailWord_3533325) baseStart_3533325 baseEnd_3533325 := by
    simpa [prefixWord, tailWord_3533325, baseEnd_3533325] using wordTrace_append hprefix tailTrace_3533325
  have hstable : (prefixWord ++ tailWord_3533325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533325).length < 2 ^ (prefixWord ++ tailWord_3533325).sum := by decide
  have hdescent : baseEnd_3533325 < baseStart_3533325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533336 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 3, 3]
def baseStart_3533336 : Nat := 118140960795 + 3533336 * 2 ^ 59
def prefixEnd_3533336 : Nat := 4983230072969 + 3 ^ 40 * 3533336 * 2
def baseEnd_3533336 : Nat := 1209533121223128693566993

theorem tailTrace_3533336 : CollatzResearch.WordTrace tailWord_3533336 prefixEnd_3533336 1209533121223128693566993 := by
  unfold tailWord_3533336
  simp only [CollatzResearch.WordTrace]
  refine ⟨64435675563667296295569931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85914234084889728394093241 64435675563667296295569931)
  ·
    refine ⟨96653513345500944443354897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64435675563667296295569931 96653513345500944443354897)
    ·
      refine ⟨72490135009125708332516173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96653513345500944443354897 72490135009125708332516173)
      ·
        refine ⟨27183800628422140624693565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72490135009125708332516173 27183800628422140624693565)
        ·
          refine ⟨10193925235658302734260087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27183800628422140624693565 10193925235658302734260087)
          ·
            refine ⟨15290887853487454101390131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10193925235658302734260087 15290887853487454101390131)
            ·
              refine ⟨22936331780231181152085197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15290887853487454101390131 22936331780231181152085197)
              ·
                refine ⟨8601124417586692932031949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22936331780231181152085197 8601124417586692932031949)
                ·
                  refine ⟨3225421656595009849511981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8601124417586692932031949 3225421656595009849511981)
                  ·
                    refine ⟨1209533121223128693566993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225421656595009849511981 1209533121223128693566993)
                    ·
                      rfl

theorem cell22_3533336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_3533336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533336 prefixEnd_3533336 := by exact prefixLift 3533336
  have htrace : WordTrace (prefixWord ++ tailWord_3533336) baseStart_3533336 baseEnd_3533336 := by
    simpa [prefixWord, tailWord_3533336, baseEnd_3533336] using wordTrace_append hprefix tailTrace_3533336
  have hstable : (prefixWord ++ tailWord_3533336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533336).length < 2 ^ (prefixWord ++ tailWord_3533336).sum := by decide
  have hdescent : baseEnd_3533336 < baseStart_3533336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533349 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 5]
def baseStart_3533349 : Nat := 118140960795 + 3533349 * 2 ^ 59
def prefixEnd_3533349 : Nat := 4983230072969 + 3 ^ 40 * 3533349 * 2
def baseEnd_3533349 : Nat := 403179190462933664330651

theorem tailTrace_3533349 : CollatzResearch.WordTrace tailWord_3533349 prefixEnd_3533349 403179190462933664330651 := by
  unfold tailWord_3533349
  simp only [CollatzResearch.WordTrace]
  refine ⟨128871825276287495811363101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85914550184191663874242067 128871825276287495811363101)
  ·
    refine ⟨48326934478607810929261163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128871825276287495811363101 48326934478607810929261163)
    ·
      refine ⟨72490401717911716393891745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48326934478607810929261163 72490401717911716393891745)
      ·
        refine ⟨54367801288433787295418809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72490401717911716393891745 54367801288433787295418809)
        ·
          refine ⟨40775850966325340471564107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54367801288433787295418809 40775850966325340471564107)
          ·
            refine ⟨61163776449488010707346161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40775850966325340471564107 61163776449488010707346161)
            ·
              refine ⟨45872832337116008030509621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61163776449488010707346161 45872832337116008030509621)
              ·
                refine ⟨4300578031604625752860277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45872832337116008030509621 4300578031604625752860277)
                ·
                  refine ⟨403179190462933664330651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4300578031604625752860277 403179190462933664330651)
                  ·
                    rfl

theorem cell22_3533349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_3533349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533349 prefixEnd_3533349 := by exact prefixLift 3533349
  have htrace : WordTrace (prefixWord ++ tailWord_3533349) baseStart_3533349 baseEnd_3533349 := by
    simpa [prefixWord, tailWord_3533349, baseEnd_3533349] using wordTrace_append hprefix tailTrace_3533349
  have hstable : (prefixWord ++ tailWord_3533349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533349).length < 2 ^ (prefixWord ++ tailWord_3533349).sum := by decide
  have hdescent : baseEnd_3533349 < baseStart_3533349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533366 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_3533366 : Nat := 118140960795 + 3533366 * 2 ^ 59
def prefixEnd_3533366 : Nat := 4983230072969 + 3 ^ 40 * 3533366 * 2
def baseEnd_3533366 : Nat := 403181130278739538438967

theorem tailTrace_3533366 : CollatzResearch.WordTrace tailWord_3533366 prefixEnd_3533366 403181130278739538438967 := by
  unfold tailWord_3533366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8054527832326619232170747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85914963544817271809821301 8054527832326619232170747)
  ·
    refine ⟨12081791748489928848256121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8054527832326619232170747 12081791748489928848256121)
    ·
      refine ⟨9061343811367446636192091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12081791748489928848256121 9061343811367446636192091)
      ·
        refine ⟨13592015717051169954288137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9061343811367446636192091 13592015717051169954288137)
        ·
          refine ⟨10194011787788377465716103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13592015717051169954288137 10194011787788377465716103)
          ·
            refine ⟨15291017681682566198574155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194011787788377465716103 15291017681682566198574155)
            ·
              refine ⟨22936526522523849297861233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15291017681682566198574155 22936526522523849297861233)
              ·
                refine ⟨17202394891892886973395925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22936526522523849297861233 17202394891892886973395925)
                ·
                  refine ⟨403181130278739538438967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17202394891892886973395925 403181130278739538438967)
                  ·
                    rfl

theorem cell22_3533366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_3533366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533366 prefixEnd_3533366 := by exact prefixLift 3533366
  have htrace : WordTrace (prefixWord ++ tailWord_3533366) baseStart_3533366 baseEnd_3533366 := by
    simpa [prefixWord, tailWord_3533366, baseEnd_3533366] using wordTrace_append hprefix tailTrace_3533366
  have hstable : (prefixWord ++ tailWord_3533366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533366).length < 2 ^ (prefixWord ++ tailWord_3533366).sum := by decide
  have hdescent : baseEnd_3533366 < baseStart_3533366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533370 : List Nat := [3, 1, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_3533370 : Nat := 118140960795 + 3533370 * 2 ^ 59
def prefixEnd_3533370 : Nat := 4983230072969 + 3 ^ 40 * 3533370 * 2
def baseEnd_3533370 : Nat := 1209544760117963938216889

theorem tailTrace_3533370 : CollatzResearch.WordTrace tailWord_3533370 prefixEnd_3533370 1209544760117963938216889 := by
  unfold tailWord_3533370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32218147802302854099469391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85915060806140944265251709 32218147802302854099469391)
  ·
    refine ⟨48327221703454281149204087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32218147802302854099469391 48327221703454281149204087)
    ·
      refine ⟨72490832555181421723806131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48327221703454281149204087 72490832555181421723806131)
      ·
        refine ⟨108736248832772132585709197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72490832555181421723806131 108736248832772132585709197)
        ·
          refine ⟨40776093312289549719640949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108736248832772132585709197 40776093312289549719640949)
          ·
            refine ⟨3822758748027145286216339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40776093312289549719640949 3822758748027145286216339)
            ·
              refine ⟨5734138122040717929324509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822758748027145286216339 5734138122040717929324509)
              ·
                refine ⟨2150301795765269223496691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5734138122040717929324509 2150301795765269223496691)
                ·
                  refine ⟨3225452693647903835245037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150301795765269223496691 3225452693647903835245037)
                  ·
                    refine ⟨1209544760117963938216889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225452693647903835245037 1209544760117963938216889)
                    ·
                      rfl

theorem cell22_3533370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_3533370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533370 prefixEnd_3533370 := by exact prefixLift 3533370
  have htrace : WordTrace (prefixWord ++ tailWord_3533370) baseStart_3533370 baseEnd_3533370 := by
    simpa [prefixWord, tailWord_3533370, baseEnd_3533370] using wordTrace_append hprefix tailTrace_3533370
  have hstable : (prefixWord ++ tailWord_3533370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533370).length < 2 ^ (prefixWord ++ tailWord_3533370).sum := by decide
  have hdescent : baseEnd_3533370 < baseStart_3533370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533441 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3533441 : Nat := 118140960795 + 3533441 * 2 ^ 59
def prefixEnd_3533441 : Nat := 4983230072969 + 3 ^ 40 * 3533441 * 2
def baseEnd_3533441 : Nat := 1209569064868943419691671

theorem tailTrace_3533441 : CollatzResearch.WordTrace tailWord_3533441 prefixEnd_3533441 1209569064868943419691671 := by
  unfold tailWord_3533441
  simp only [CollatzResearch.WordTrace]
  refine ⟨128875180791954195523712177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85916787194636130349141451 128875180791954195523712177)
  ·
    refine ⟨96656385593965646642784133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128875180791954195523712177 96656385593965646642784133)
    ·
      refine ⟨18123072298868558745522025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96656385593965646642784133 18123072298868558745522025)
      ·
        refine ⟨13592304224151419059141519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18123072298868558745522025 13592304224151419059141519)
        ·
          refine ⟨20388456336227128588712279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13592304224151419059141519 20388456336227128588712279)
          ·
            refine ⟨30582684504340692883068419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20388456336227128588712279 30582684504340692883068419)
            ·
              refine ⟨45874026756511039324602629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30582684504340692883068419 45874026756511039324602629)
              ·
                refine ⟨8601380016845819873362993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45874026756511039324602629 8601380016845819873362993)
                ·
                  refine ⟨6451035012634364905022245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601380016845819873362993 6451035012634364905022245)
                  ·
                    refine ⟨1209569064868943419691671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6451035012634364905022245 1209569064868943419691671)
                    ·
                      rfl

theorem cell22_3533441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3533441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533441 prefixEnd_3533441 := by exact prefixLift 3533441
  have htrace : WordTrace (prefixWord ++ tailWord_3533441) baseStart_3533441 baseEnd_3533441 := by
    simpa [prefixWord, tailWord_3533441, baseEnd_3533441] using wordTrace_append hprefix tailTrace_3533441
  have hstable : (prefixWord ++ tailWord_3533441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533441).length < 2 ^ (prefixWord ++ tailWord_3533441).sum := by decide
  have hdescent : baseEnd_3533441 < baseStart_3533441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533445 : List Nat := [1, 3, 1, 1, 4, 4, 2, 2, 4]
def baseStart_3533445 : Nat := 118140960795 + 3533445 * 2 ^ 59
def prefixEnd_3533445 : Nat := 4983230072969 + 3 ^ 40 * 3533445 * 2
def baseEnd_3533445 : Nat := 403190144716896247530553

theorem tailTrace_3533445 : CollatzResearch.WordTrace tailWord_3533445 prefixEnd_3533445 403190144716896247530553 := by
  unfold tailWord_3533445
  simp only [CollatzResearch.WordTrace]
  refine ⟨128875326683939704206857789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85916884455959802804571859 128875326683939704206857789)
  ·
    refine ⟨48328247506477389077571671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128875326683939704206857789 48328247506477389077571671)
    ·
      refine ⟨72492371259716083616357507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48328247506477389077571671 72492371259716083616357507)
      ·
        refine ⟨108738556889574125424536261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72492371259716083616357507 108738556889574125424536261)
        ·
          refine ⟨20388479416795148517100549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108738556889574125424536261 20388479416795148517100549)
          ·
            refine ⟨3822839890649090346956353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20388479416795148517100549 3822839890649090346956353)
            ·
              refine ⟨2867129917986817760217265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822839890649090346956353 2867129917986817760217265)
              ·
                refine ⟨2150347438490113320162949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867129917986817760217265 2150347438490113320162949)
                ·
                  refine ⟨403190144716896247530553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150347438490113320162949 403190144716896247530553)
                  ·
                    rfl

theorem cell22_3533445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_3533445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533445 prefixEnd_3533445 := by exact prefixLift 3533445
  have htrace : WordTrace (prefixWord ++ tailWord_3533445) baseStart_3533445 baseEnd_3533445 := by
    simpa [prefixWord, tailWord_3533445, baseEnd_3533445] using wordTrace_append hprefix tailTrace_3533445
  have hstable : (prefixWord ++ tailWord_3533445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533445).length < 2 ^ (prefixWord ++ tailWord_3533445).sum := by decide
  have hdescent : baseEnd_3533445 < baseStart_3533445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533460 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3533460 : Nat := 118140960795 + 3533460 * 2 ^ 59
def prefixEnd_3533460 : Nat := 4983230072969 + 3 ^ 40 * 3533460 * 2
def baseEnd_3533460 : Nat := 1209575568957233703466613

theorem tailTrace_3533460 : CollatzResearch.WordTrace tailWord_3533460 prefixEnd_3533460 1209575568957233703466613 := by
  unfold tailWord_3533460
  simp only [CollatzResearch.WordTrace]
  refine ⟨64437936889442680884326917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85917249185923574512435889 64437936889442680884326917)
  ·
    refine ⟨12082113166770502665811297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64437936889442680884326917 12082113166770502665811297)
    ·
      refine ⟨9061584875077876999358473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12082113166770502665811297 9061584875077876999358473)
      ·
        refine ⟨6796188656308407749518855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9061584875077876999358473 6796188656308407749518855)
        ·
          refine ⟨10194282984462611624278283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796188656308407749518855 10194282984462611624278283)
          ·
            refine ⟨15291424476693917436417425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194282984462611624278283 15291424476693917436417425)
            ·
              refine ⟨11468568357520438077313069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15291424476693917436417425 11468568357520438077313069)
              ·
                refine ⟨4300713134070164278992401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11468568357520438077313069 4300713134070164278992401)
                ·
                  refine ⟨3225534850552623209244301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300713134070164278992401 3225534850552623209244301)
                  ·
                    refine ⟨1209575568957233703466613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225534850552623209244301 1209575568957233703466613)
                    ·
                      rfl

theorem cell22_3533460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3533460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533460 prefixEnd_3533460 := by exact prefixLift 3533460
  have htrace : WordTrace (prefixWord ++ tailWord_3533460) baseStart_3533460 baseEnd_3533460 := by
    simpa [prefixWord, tailWord_3533460, baseEnd_3533460] using wordTrace_append hprefix tailTrace_3533460
  have hstable : (prefixWord ++ tailWord_3533460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533460).length < 2 ^ (prefixWord ++ tailWord_3533460).sum := by decide
  have hdescent : baseEnd_3533460 < baseStart_3533460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533473 : List Nat := [1, 2, 3, 3, 3, 1, 3, 6]
def baseStart_3533473 : Nat := 118140960795 + 3533473 * 2 ^ 59
def prefixEnd_3533473 : Nat := 4983230072969 + 3 ^ 40 * 3533473 * 2
def baseEnd_3533473 : Nat := 134397779902545111432397

theorem tailTrace_3533473 : CollatzResearch.WordTrace tailWord_3533473 prefixEnd_3533473 134397779902545111432397 := by
  unfold tailWord_3533473
  simp only [CollatzResearch.WordTrace]
  refine ⟨128876347927838264988877073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85917565285225509992584715 128876347927838264988877073)
  ·
    refine ⟨96657260945878698741657805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128876347927838264988877073 96657260945878698741657805)
    ·
      refine ⟨36246472854704512028121677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96657260945878698741657805 36246472854704512028121677)
      ·
        refine ⟨13592427320514192010545629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36246472854704512028121677 13592427320514192010545629)
        ·
          refine ⟨5097160245192822003954611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13592427320514192010545629 5097160245192822003954611)
          ·
            refine ⟨7645740367789233005931917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097160245192822003954611 7645740367789233005931917)
            ·
              refine ⟨2867152637920962377224469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7645740367789233005931917 2867152637920962377224469)
              ·
                refine ⟨134397779902545111432397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2867152637920962377224469 134397779902545111432397)
                ·
                  rfl

theorem cell22_3533473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 6].length) (baseStart_3533473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533473 prefixEnd_3533473 := by exact prefixLift 3533473
  have htrace : WordTrace (prefixWord ++ tailWord_3533473) baseStart_3533473 baseEnd_3533473 := by
    simpa [prefixWord, tailWord_3533473, baseEnd_3533473] using wordTrace_append hprefix tailTrace_3533473
  have hstable : (prefixWord ++ tailWord_3533473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533473).length < 2 ^ (prefixWord ++ tailWord_3533473).sum := by decide
  have hdescent : baseEnd_3533473 < baseStart_3533473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533494 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3533494 : Nat := 118140960795 + 3533494 * 2 ^ 59
def prefixEnd_3533494 : Nat := 4983230072969 + 3 ^ 40 * 3533494 * 2
def baseEnd_3533494 : Nat := 1209587207852068948116509

theorem tailTrace_3533494 : CollatzResearch.WordTrace tailWord_3533494 prefixEnd_3533494 1209587207852068948116509 := by
  unfold tailWord_3533494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8054819616297636598461971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85918075907174790383594357 8054819616297636598461971)
  ·
    refine ⟨12082229424446454897692957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8054819616297636598461971 12082229424446454897692957)
    ·
      refine ⟨4530836034167420586634859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12082229424446454897692957 4530836034167420586634859)
      ·
        refine ⟨6796254051251130879952289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530836034167420586634859 6796254051251130879952289)
        ·
          refine ⟨5097190538438348159964217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6796254051251130879952289 5097190538438348159964217)
          ·
            refine ⟨3822892903828761119973163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5097190538438348159964217 3822892903828761119973163)
            ·
              refine ⟨5734339355743141679959745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822892903828761119973163 5734339355743141679959745)
              ·
                refine ⟨4300754516807356259969809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5734339355743141679959745 4300754516807356259969809)
                ·
                  refine ⟨3225565887605517194977357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300754516807356259969809 3225565887605517194977357)
                  ·
                    refine ⟨1209587207852068948116509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225565887605517194977357 1209587207852068948116509)
                    ·
                      rfl

theorem cell22_3533494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3533494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533494 prefixEnd_3533494 := by exact prefixLift 3533494
  have htrace : WordTrace (prefixWord ++ tailWord_3533494) baseStart_3533494 baseEnd_3533494 := by
    simpa [prefixWord, tailWord_3533494, baseEnd_3533494] using wordTrace_append hprefix tailTrace_3533494
  have hstable : (prefixWord ++ tailWord_3533494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533494).length < 2 ^ (prefixWord ++ tailWord_3533494).sum := by decide
  have hdescent : baseEnd_3533494 < baseStart_3533494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533501 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 7]
def baseStart_3533501 : Nat := 118140960795 + 3533501 * 2 ^ 59
def prefixEnd_3533501 : Nat := 4983230072969 + 3 ^ 40 * 3533501 * 2
def baseEnd_3533501 : Nat := 403196534698374421063829

theorem tailTrace_3533501 : CollatzResearch.WordTrace tailWord_3533501 prefixEnd_3533501 403196534698374421063829 := by
  unfold tailWord_3533501
  simp only [CollatzResearch.WordTrace]
  refine ⟨128877369171736825770896357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85918246114491217180597571 128877369171736825770896357)
  ·
    refine ⟨24164506719700654832043067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128877369171736825770896357 24164506719700654832043067)
    ·
      refine ⟨36246760079550982248064601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24164506719700654832043067 36246760079550982248064601)
      ·
        refine ⟨27185070059663236686048451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36246760079550982248064601 27185070059663236686048451)
        ·
          refine ⟨40777605089494855029072677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27185070059663236686048451 40777605089494855029072677)
          ·
            refine ⟨7645800954280285317951127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40777605089494855029072677 7645800954280285317951127)
            ·
              refine ⟨11468701431420427976926691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645800954280285317951127 11468701431420427976926691)
              ·
                refine ⟨17203052147130641965390037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11468701431420427976926691 17203052147130641965390037)
                ·
                  refine ⟨403196534698374421063829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17203052147130641965390037 403196534698374421063829)
                  ·
                    rfl

theorem cell22_3533501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_3533501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533501 prefixEnd_3533501 := by exact prefixLift 3533501
  have htrace : WordTrace (prefixWord ++ tailWord_3533501) baseStart_3533501 baseEnd_3533501 := by
    simpa [prefixWord, tailWord_3533501, baseEnd_3533501] using wordTrace_append hprefix tailTrace_3533501
  have hstable : (prefixWord ++ tailWord_3533501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533501).length < 2 ^ (prefixWord ++ tailWord_3533501).sum := by decide
  have hdescent : baseEnd_3533501 < baseStart_3533501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533556 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3533556 : Nat := 118140960795 + 3533556 * 2 ^ 59
def prefixEnd_3533556 : Nat := 4983230072969 + 3 ^ 40 * 3533556 * 2
def baseEnd_3533556 : Nat := 1209608431719121453066319

theorem tailTrace_3533556 : CollatzResearch.WordTrace tailWord_3533556 prefixEnd_3533556 1209608431719121453066319 := by
  unfold tailWord_3533556
  simp only [CollatzResearch.WordTrace]
  refine ⟨64439687593268785082074261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85919583457691713442765681 64439687593268785082074261)
  ·
    refine ⟨3020610355934474300722231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64439687593268785082074261 3020610355934474300722231)
    ·
      refine ⟨4530915533901711451083347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020610355934474300722231 4530915533901711451083347)
      ·
        refine ⟨6796373300852567176625021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530915533901711451083347 6796373300852567176625021)
        ·
          refine ⟨2548639987819712691234383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6796373300852567176625021 2548639987819712691234383)
          ·
            refine ⟨3822959981729569036851575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548639987819712691234383 3822959981729569036851575)
            ·
              refine ⟨5734439972594353555277363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822959981729569036851575 5734439972594353555277363)
              ·
                refine ⟨8601659958891530332916045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734439972594353555277363 8601659958891530332916045)
                ·
                  refine ⟨3225622484584323874843517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8601659958891530332916045 3225622484584323874843517)
                  ·
                    refine ⟨1209608431719121453066319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225622484584323874843517 1209608431719121453066319)
                    ·
                      rfl

theorem cell22_3533556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3533556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533556 prefixEnd_3533556 := by exact prefixLift 3533556
  have htrace : WordTrace (prefixWord ++ tailWord_3533556) baseStart_3533556 baseEnd_3533556 := by
    simpa [prefixWord, tailWord_3533556, baseEnd_3533556] using wordTrace_append hprefix tailTrace_3533556
  have hstable : (prefixWord ++ tailWord_3533556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533556).length < 2 ^ (prefixWord ++ tailWord_3533556).sum := by decide
  have hdescent : baseEnd_3533556 < baseStart_3533556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533614 : List Nat := [4, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_3533614 : Nat := 118140960795 + 3533614 * 2 ^ 59
def prefixEnd_3533614 : Nat := 4983230072969 + 3 ^ 40 * 3533614 * 2
def baseEnd_3533614 : Nat := 403209428768142878372047

theorem tailTrace_3533614 : CollatzResearch.WordTrace tailWord_3533614 prefixEnd_3533614 403209428768142878372047 := by
  unfold tailWord_3533614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110186327540930758719987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85920993746884964046506597 16110186327540930758719987)
  ·
    refine ⟨24165279491311396138079981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16110186327540930758719987 24165279491311396138079981)
    ·
      refine ⟨9061979809241773551779993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24165279491311396138079981 9061979809241773551779993)
      ·
        refine ⟨6796484856931330163834995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9061979809241773551779993 6796484856931330163834995)
        ·
          refine ⟨10194727285396995245752493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796484856931330163834995 10194727285396995245752493)
          ·
            refine ⟨3823022732023873217157185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10194727285396995245752493 3823022732023873217157185)
            ·
              refine ⟨2867267049017904912867889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3823022732023873217157185 2867267049017904912867889)
              ·
                refine ⟨2150450286763428684650917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867267049017904912867889 2150450286763428684650917)
                ·
                  refine ⟨403209428768142878372047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150450286763428684650917 403209428768142878372047)
                  ·
                    rfl

theorem cell22_3533614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_3533614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533614 prefixEnd_3533614 := by exact prefixLift 3533614
  have htrace : WordTrace (prefixWord ++ tailWord_3533614) baseStart_3533614 baseEnd_3533614 := by
    simpa [prefixWord, tailWord_3533614, baseEnd_3533614] using wordTrace_append hprefix tailTrace_3533614
  have hstable : (prefixWord ++ tailWord_3533614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533614).length < 2 ^ (prefixWord ++ tailWord_3533614).sum := by decide
  have hdescent : baseEnd_3533614 < baseStart_3533614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533623 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 3, 3]
def baseStart_3533623 : Nat := 118140960795 + 3533623 * 2 ^ 59
def prefixEnd_3533623 : Nat := 4983230072969 + 3 ^ 40 * 3533623 * 2
def baseEnd_3533623 : Nat := 1209631367188355611641113

theorem tailTrace_3533623 : CollatzResearch.WordTrace tailWord_3533623 prefixEnd_3533623 1209631367188355611641113 := by
  unfold tailWord_3533623
  simp only [CollatzResearch.WordTrace]
  refine ⟨128881818877294840606837523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85921212584863227071225015 128881818877294840606837523)
  ·
    refine ⟨193322728315942260910256285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128881818877294840606837523 193322728315942260910256285)
    ·
      refine ⟨72496023118478347841346107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193322728315942260910256285 72496023118478347841346107)
      ·
        refine ⟨108744034677717521762019161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72496023118478347841346107 108744034677717521762019161)
        ·
          refine ⟨81558026008288141321514371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108744034677717521762019161 81558026008288141321514371)
          ·
            refine ⟨122337039012432211982271557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81558026008288141321514371 122337039012432211982271557)
            ·
              refine ⟨22938194814831039746675917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122337039012432211982271557 22938194814831039746675917)
              ·
                refine ⟨8601823055561639905003469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22938194814831039746675917 8601823055561639905003469)
                ·
                  refine ⟨3225683645835614964376301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8601823055561639905003469 3225683645835614964376301)
                  ·
                    refine ⟨1209631367188355611641113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225683645835614964376301 1209631367188355611641113)
                    ·
                      rfl

theorem cell22_3533623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_3533623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533623 prefixEnd_3533623 := by exact prefixLift 3533623
  have htrace : WordTrace (prefixWord ++ tailWord_3533623) baseStart_3533623 baseEnd_3533623 := by
    simpa [prefixWord, tailWord_3533623, baseEnd_3533623] using wordTrace_append hprefix tailTrace_3533623
  have hstable : (prefixWord ++ tailWord_3533623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533623).length < 2 ^ (prefixWord ++ tailWord_3533623).sum := by decide
  have hdescent : baseEnd_3533623 < baseStart_3533623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533657 : List Nat := [1, 2, 1, 2, 2, 5, 2, 3, 1, 3]
def baseStart_3533657 : Nat := 118140960795 + 3533657 * 2 ^ 59
def prefixEnd_3533657 : Nat := 4983230072969 + 3 ^ 40 * 3533657 * 2
def baseEnd_3533657 : Nat := 1209643006083190856291009

theorem tailTrace_3533657 : CollatzResearch.WordTrace tailWord_3533657 prefixEnd_3533657 1209643006083190856291009 := by
  unfold tailWord_3533657
  simp only [CollatzResearch.WordTrace]
  refine ⟨128883058959171664413575225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85922039306114442942383483 128883058959171664413575225)
  ·
    refine ⟨96662294219378748310181419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128883058959171664413575225 96662294219378748310181419)
    ·
      refine ⟨144993441329068122465272129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96662294219378748310181419 144993441329068122465272129)
      ·
        refine ⟨108745080996801091848954097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144993441329068122465272129 108745080996801091848954097)
        ·
          refine ⟨81558810747600818886715573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108745080996801091848954097 81558810747600818886715573)
          ·
            refine ⟨7646138507587576770629585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81558810747600818886715573 7646138507587576770629585)
            ·
              refine ⟨5734603880690682577972189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646138507587576770629585 5734603880690682577972189)
              ·
                refine ⟨2150476455259005966739571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5734603880690682577972189 2150476455259005966739571)
                ·
                  refine ⟨3225714682888508950109357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150476455259005966739571 3225714682888508950109357)
                  ·
                    refine ⟨1209643006083190856291009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225714682888508950109357 1209643006083190856291009)
                    ·
                      rfl

theorem cell22_3533657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 3].length) (baseStart_3533657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533657 prefixEnd_3533657 := by exact prefixLift 3533657
  have htrace : WordTrace (prefixWord ++ tailWord_3533657) baseStart_3533657 baseEnd_3533657 := by
    simpa [prefixWord, tailWord_3533657, baseEnd_3533657] using wordTrace_append hprefix tailTrace_3533657
  have hstable : (prefixWord ++ tailWord_3533657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533657).length < 2 ^ (prefixWord ++ tailWord_3533657).sum := by decide
  have hdescent : baseEnd_3533657 < baseStart_3533657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533668 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3533668 : Nat := 118140960795 + 3533668 * 2 ^ 59
def prefixEnd_3533668 : Nat := 4983230072969 + 3 ^ 40 * 3533668 * 2
def baseEnd_3533668 : Nat := 1209646771607990494265975

theorem tailTrace_3533668 : CollatzResearch.WordTrace tailWord_3533668 prefixEnd_3533668 1209646771607990494265975 := by
  unfold tailWord_3533668
  simp only [CollatzResearch.WordTrace]
  refine ⟨64441730081065906646112829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85922306774754542194817105 64441730081065906646112829)
  ·
    refine ⟨24165648780399714992292311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64441730081065906646112829 24165648780399714992292311)
    ·
      refine ⟨36248473170599572488438467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24165648780399714992292311 36248473170599572488438467)
      ·
        refine ⟨54372709755899358732657701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36248473170599572488438467 54372709755899358732657701)
        ·
          refine ⟨10194883079231129762373319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54372709755899358732657701 10194883079231129762373319)
          ·
            refine ⟨15292324618846694643559979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194883079231129762373319 15292324618846694643559979)
            ·
              refine ⟨22938486928270041965339969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15292324618846694643559979 22938486928270041965339969)
              ·
                refine ⟨17203865196202531474004977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22938486928270041965339969 17203865196202531474004977)
                ·
                  refine ⟨12902898897151898605503733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17203865196202531474004977 12902898897151898605503733)
                  ·
                    refine ⟨1209646771607990494265975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12902898897151898605503733 1209646771607990494265975)
                    ·
                      rfl

theorem cell22_3533668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3533668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533668 prefixEnd_3533668 := by exact prefixLift 3533668
  have htrace : WordTrace (prefixWord ++ tailWord_3533668) baseStart_3533668 baseEnd_3533668 := by
    simpa [prefixWord, tailWord_3533668, baseEnd_3533668] using wordTrace_append hprefix tailTrace_3533668
  have hstable : (prefixWord ++ tailWord_3533668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533668).length < 2 ^ (prefixWord ++ tailWord_3533668).sum := by decide
  have hdescent : baseEnd_3533668 < baseStart_3533668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533728 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_3533728 : Nat := 118140960795 + 3533728 * 2 ^ 59
def prefixEnd_3533728 : Nat := 4983230072969 + 3 ^ 40 * 3533728 * 2
def baseEnd_3533728 : Nat := 1209667310834170337765791

theorem tailTrace_3533728 : CollatzResearch.WordTrace tailWord_3533728 prefixEnd_3533728 1209667310834170337765791 := by
  unfold tailWord_3533728
  simp only [CollatzResearch.WordTrace]
  refine ⟨64442824270957221769704919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85923765694609629026273225 64442824270957221769704919)
  ·
    refine ⟨96664236406435832654557379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64442824270957221769704919 96664236406435832654557379)
    ·
      refine ⟨144996354609653748981836069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96664236406435832654557379 144996354609653748981836069)
      ·
        refine ⟨27186816489310077934094263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144996354609653748981836069 27186816489310077934094263)
        ·
          refine ⟨40780224733965116901141395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27186816489310077934094263 40780224733965116901141395)
          ·
            refine ⟨61170337100947675351712093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40780224733965116901141395 61170337100947675351712093)
            ·
              refine ⟨22938876412855378256892035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61170337100947675351712093 22938876412855378256892035)
              ·
                refine ⟨34408314619283067385338053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22938876412855378256892035 34408314619283067385338053)
                ·
                  refine ⟨6451558991115575134750885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34408314619283067385338053 6451558991115575134750885)
                  ·
                    refine ⟨1209667310834170337765791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6451558991115575134750885 1209667310834170337765791)
                    ·
                      rfl

theorem cell22_3533728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_3533728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533728 prefixEnd_3533728 := by exact prefixLift 3533728
  have htrace : WordTrace (prefixWord ++ tailWord_3533728) baseStart_3533728 baseEnd_3533728 := by
    simpa [prefixWord, tailWord_3533728, baseEnd_3533728] using wordTrace_append hprefix tailTrace_3533728
  have hstable : (prefixWord ++ tailWord_3533728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533728).length < 2 ^ (prefixWord ++ tailWord_3533728).sum := by decide
  have hdescent : baseEnd_3533728 < baseStart_3533728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533732 : List Nat := [2, 3, 1, 2, 1, 2, 5, 2, 4]
def baseStart_3533732 : Nat := 118140960795 + 3533732 * 2 ^ 59
def prefixEnd_3533732 : Nat := 4983230072969 + 3 ^ 40 * 3533732 * 2
def baseEnd_3533732 : Nat := 403222893371971886888593

theorem tailTrace_3533732 : CollatzResearch.WordTrace tailWord_3533732 prefixEnd_3533732 403222893371971886888593 := by
  unfold tailWord_3533732
  simp only [CollatzResearch.WordTrace]
  refine ⟨64442897216949976111277725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85923862955933301481703633 64442897216949976111277725)
  ·
    refine ⟨24166086456356241041729147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64442897216949976111277725 24166086456356241041729147)
    ·
      refine ⟨36249129684534361562593721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24166086456356241041729147 36249129684534361562593721)
      ·
        refine ⟨27186847263400771171945291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36249129684534361562593721 27186847263400771171945291)
        ·
          refine ⟨40780270895101156757917937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27186847263400771171945291 40780270895101156757917937)
          ·
            refine ⟨30585203171325867568438453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40780270895101156757917937 30585203171325867568438453)
            ·
              refine ⟨2867362797311800084541105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30585203171325867568438453 2867362797311800084541105)
              ·
                refine ⟨2150522097983850063405829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867362797311800084541105 2150522097983850063405829)
                ·
                  refine ⟨403222893371971886888593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150522097983850063405829 403222893371971886888593)
                  ·
                    rfl

theorem cell22_3533732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_3533732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533732 prefixEnd_3533732 := by exact prefixLift 3533732
  have htrace : WordTrace (prefixWord ++ tailWord_3533732) baseStart_3533732 baseEnd_3533732 := by
    simpa [prefixWord, tailWord_3533732, baseEnd_3533732] using wordTrace_append hprefix tailTrace_3533732
  have hstable : (prefixWord ++ tailWord_3533732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533732).length < 2 ^ (prefixWord ++ tailWord_3533732).sum := by decide
  have hdescent : baseEnd_3533732 < baseStart_3533732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533850 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_3533850 : Nat := 118140960795 + 3533850 * 2 ^ 59
def prefixEnd_3533850 : Nat := 4983230072969 + 3 ^ 40 * 3533850 * 2
def baseEnd_3533850 : Nat := 403236357975800895405139

theorem tailTrace_3533850 : CollatzResearch.WordTrace tailWord_3533850 prefixEnd_3533850 403236357975800895405139 := by
  unfold tailWord_3533850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32222524561868114593837751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85926732164981638916900669 32222524561868114593837751)
  ·
    refine ⟨48333786842802171890756627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32222524561868114593837751 48333786842802171890756627)
    ·
      refine ⟨72500680264203257836134941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48333786842802171890756627 72500680264203257836134941)
      ·
        refine ⟨27187755099076221688550603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72500680264203257836134941 27187755099076221688550603)
        ·
          refine ⟨40781632648614332532825905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27187755099076221688550603 40781632648614332532825905)
          ·
            refine ⟨30586224486460749399619429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40781632648614332532825905 30586224486460749399619429)
            ·
              refine ⟨5734917091211390512428643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30586224486460749399619429 5734917091211390512428643)
              ·
                refine ⟨8602375636817085768642965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734917091211390512428643 8602375636817085768642965)
                ·
                  refine ⟨403236357975800895405139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8602375636817085768642965 403236357975800895405139)
                  ·
                    rfl

theorem cell22_3533850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_3533850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533850 prefixEnd_3533850 := by exact prefixLift 3533850
  have htrace : WordTrace (prefixWord ++ tailWord_3533850) baseStart_3533850 baseEnd_3533850 := by
    simpa [prefixWord, tailWord_3533850, baseEnd_3533850] using wordTrace_append hprefix tailTrace_3533850
  have hstable : (prefixWord ++ tailWord_3533850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533850).length < 2 ^ (prefixWord ++ tailWord_3533850).sum := by decide
  have hdescent : baseEnd_3533850 < baseStart_3533850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533880 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_3533880 : Nat := 118140960795 + 3533880 * 2 ^ 59
def prefixEnd_3533880 : Nat := 4983230072969 + 3 ^ 40 * 3533880 * 2
def baseEnd_3533880 : Nat := 1209719343540492607965325

theorem tailTrace_3533880 : CollatzResearch.WordTrace tailWord_3533880 prefixEnd_3533880 1209719343540492607965325 := by
  unfold tailWord_3533880
  simp only [CollatzResearch.WordTrace]
  refine ⟨64445596218681886749471547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85927461624909182332628729 64445596218681886749471547)
  ·
    refine ⟨96668394328022830124207321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64445596218681886749471547 96668394328022830124207321)
    ·
      refine ⟨72501295746017122593155491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96668394328022830124207321 72501295746017122593155491)
      ·
        refine ⟨108751943619025683889733237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72501295746017122593155491 108751943619025683889733237)
        ·
          refine ⟨10195494714283657864662491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108751943619025683889733237 10195494714283657864662491)
          ·
            refine ⟨15293242071425486796993737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10195494714283657864662491 15293242071425486796993737)
            ·
              refine ⟨11469931553569115097745303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15293242071425486796993737 11469931553569115097745303)
              ·
                refine ⟨17204897330353672646617955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11469931553569115097745303 17204897330353672646617955)
                ·
                  refine ⟨25807345995530508969926933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17204897330353672646617955 25807345995530508969926933)
                  ·
                    refine ⟨1209719343540492607965325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25807345995530508969926933 1209719343540492607965325)
                    ·
                      rfl

theorem cell22_3533880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_3533880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533880 prefixEnd_3533880 := by exact prefixLift 3533880
  have htrace : WordTrace (prefixWord ++ tailWord_3533880) baseStart_3533880 baseEnd_3533880 := by
    simpa [prefixWord, tailWord_3533880, baseEnd_3533880] using wordTrace_append hprefix tailTrace_3533880
  have hstable : (prefixWord ++ tailWord_3533880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533880).length < 2 ^ (prefixWord ++ tailWord_3533880).sum := by decide
  have hdescent : baseEnd_3533880 < baseStart_3533880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533884 : List Nat := [2, 2, 2, 2, 2, 4, 1, 3, 4]
def baseStart_3533884 : Nat := 118140960795 + 3533884 * 2 ^ 59
def prefixEnd_3533884 : Nat := 4983230072969 + 3 ^ 40 * 3533884 * 2
def baseEnd_3533884 : Nat := 403240237607412643621771

theorem tailTrace_3533884 : CollatzResearch.WordTrace tailWord_3533884 prefixEnd_3533884 403240237607412643621771 := by
  unfold tailWord_3533884
  simp only [CollatzResearch.WordTrace]
  refine ⟨64445669164674641091044353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85927558886232854788059137 64445669164674641091044353)
  ·
    refine ⟨48334251873505980818283265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64445669164674641091044353 48334251873505980818283265)
    ·
      refine ⟨36250688905129485613712449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48334251873505980818283265 36250688905129485613712449)
      ·
        refine ⟨27188016678847114210284337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36250688905129485613712449 27188016678847114210284337)
        ·
          refine ⟨20391012509135335657713253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27188016678847114210284337 20391012509135335657713253)
          ·
            refine ⟨3823314845462875435821235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20391012509135335657713253 3823314845462875435821235)
            ·
              refine ⟨5734972268194313153731853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823314845462875435821235 5734972268194313153731853)
              ·
                refine ⟨2150614600572867432649445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5734972268194313153731853 2150614600572867432649445)
                ·
                  refine ⟨403240237607412643621771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150614600572867432649445 403240237607412643621771)
                  ·
                    rfl

theorem cell22_3533884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_3533884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533884 prefixEnd_3533884 := by exact prefixLift 3533884
  have htrace : WordTrace (prefixWord ++ tailWord_3533884) baseStart_3533884 baseEnd_3533884 := by
    simpa [prefixWord, tailWord_3533884, baseEnd_3533884] using wordTrace_append hprefix tailTrace_3533884
  have hstable : (prefixWord ++ tailWord_3533884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533884).length < 2 ^ (prefixWord ++ tailWord_3533884).sum := by decide
  have hdescent : baseEnd_3533884 < baseStart_3533884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533895 : List Nat := [1, 1, 4, 1, 3, 4, 8]
def baseStart_3533895 : Nat := 118140960795 + 3533895 * 2 ^ 59
def prefixEnd_3533895 : Nat := 4983230072969 + 3 ^ 40 * 3533895 * 2
def baseEnd_3533895 : Nat := 44804610309149539586677

theorem tailTrace_3533895 : CollatzResearch.WordTrace tailWord_3533895 prefixEnd_3533895 44804610309149539586677 := by
  unfold tailWord_3533895
  simp only [CollatzResearch.WordTrace]
  refine ⟨128891739532309431060739139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85927826354872954040492759 128891739532309431060739139)
  ·
    refine ⟨193337609298464146591108709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128891739532309431060739139 193337609298464146591108709)
    ·
      refine ⟨36250801743462027485832883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193337609298464146591108709 36250801743462027485832883)
      ·
        refine ⟨54376202615193041228749325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36250801743462027485832883 54376202615193041228749325)
        ·
          refine ⟨20391075980697390460780997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54376202615193041228749325 20391075980697390460780997)
          ·
            refine ⟨3823326746380760711396437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20391075980697390460780997 3823326746380760711396437)
            ·
              refine ⟨44804610309149539586677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3823326746380760711396437 44804610309149539586677)
              ·
                rfl

theorem cell22_3533895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 8].length) (baseStart_3533895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533895 prefixEnd_3533895 := by exact prefixLift 3533895
  have htrace : WordTrace (prefixWord ++ tailWord_3533895) baseStart_3533895 baseEnd_3533895 := by
    simpa [prefixWord, tailWord_3533895, baseEnd_3533895] using wordTrace_append hprefix tailTrace_3533895
  have hstable : (prefixWord ++ tailWord_3533895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533895).length < 2 ^ (prefixWord ++ tailWord_3533895).sum := by decide
  have hdescent : baseEnd_3533895 < baseStart_3533895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533901 : List Nat := [1, 6, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3533901 : Nat := 118140960795 + 3533901 * 2 ^ 59
def prefixEnd_3533901 : Nat := 4983230072969 + 3 ^ 40 * 3533901 * 2
def baseEnd_3533901 : Nat := 403242177423218517730087

theorem tailTrace_3533901 : CollatzResearch.WordTrace tailWord_3533901 prefixEnd_3533901 403242177423218517730087 := by
  unfold tailWord_3533901
  simp only [CollatzResearch.WordTrace]
  refine ⟨128891958370287694085457557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85927972246858462723638371 128891958370287694085457557)
  ·
    refine ⟨6041810548607235660255823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128891958370287694085457557 6041810548607235660255823)
    ·
      refine ⟨9062715822910853490383735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041810548607235660255823 9062715822910853490383735)
      ·
        refine ⟨13594073734366280235575603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062715822910853490383735 13594073734366280235575603)
        ·
          refine ⟨20391110601549420353363405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594073734366280235575603 20391110601549420353363405)
          ·
            refine ⟨7646666475581032632511277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20391110601549420353363405 7646666475581032632511277)
            ·
              refine ⟨2867499928342887237191729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7646666475581032632511277 2867499928342887237191729)
              ·
                refine ⟨2150624946257165427893797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867499928342887237191729 2150624946257165427893797)
                ·
                  refine ⟨403242177423218517730087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150624946257165427893797 403242177423218517730087)
                  ·
                    rfl

theorem cell22_3533901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3533901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533901 prefixEnd_3533901 := by exact prefixLift 3533901
  have htrace : WordTrace (prefixWord ++ tailWord_3533901) baseStart_3533901 baseEnd_3533901 := by
    simpa [prefixWord, tailWord_3533901, baseEnd_3533901] using wordTrace_append hprefix tailTrace_3533901
  have hstable : (prefixWord ++ tailWord_3533901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533901).length < 2 ^ (prefixWord ++ tailWord_3533901).sum := by decide
  have hdescent : baseEnd_3533901 < baseStart_3533901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533950 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3533950 : Nat := 118140960795 + 3533950 * 2 ^ 59
def prefixEnd_3533950 : Nat := 4983230072969 + 3 ^ 40 * 3533950 * 2
def baseEnd_3533950 : Nat := 1209743305971035758715111

theorem tailTrace_3533950 : CollatzResearch.WordTrace tailWord_3533950 prefixEnd_3533950 1209743305971035758715111 := by
  unfold tailWord_3533950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111718193388771931748913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85929163698073450302660869 16111718193388771931748913)
  ·
    refine ⟨12083788645041578948811685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16111718193388771931748913 12083788645041578948811685)
    ·
      refine ⟨2265710370945296052902191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12083788645041578948811685 2265710370945296052902191)
      ·
        refine ⟨3398565556417944079353287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265710370945296052902191 3398565556417944079353287)
        ·
          refine ⟨5097848334626916119029931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398565556417944079353287 5097848334626916119029931)
          ·
            refine ⟨7646772501940374178544897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097848334626916119029931 7646772501940374178544897)
            ·
              refine ⟨5735079376455280633908673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646772501940374178544897 5735079376455280633908673)
              ·
                refine ⟨4301309532341460475431505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735079376455280633908673 4301309532341460475431505)
                ·
                  refine ⟨3225982149256095356573629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4301309532341460475431505 3225982149256095356573629)
                  ·
                    refine ⟨1209743305971035758715111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225982149256095356573629 1209743305971035758715111)
                    ·
                      rfl

theorem cell22_3533950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3533950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533950 prefixEnd_3533950 := by exact prefixLift 3533950
  have htrace : WordTrace (prefixWord ++ tailWord_3533950) baseStart_3533950 baseEnd_3533950 := by
    simpa [prefixWord, tailWord_3533950, baseEnd_3533950] using wordTrace_append hprefix tailTrace_3533950
  have hstable : (prefixWord ++ tailWord_3533950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533950).length < 2 ^ (prefixWord ++ tailWord_3533950).sum := by decide
  have hdescent : baseEnd_3533950 < baseStart_3533950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533955 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 2, 5]
def baseStart_3533955 : Nat := 118140960795 + 3533955 * 2 ^ 59
def prefixEnd_3533955 : Nat := 4983230072969 + 3 ^ 40 * 3533955 * 2
def baseEnd_3533955 : Nat := 1209745017573217412340095

theorem tailTrace_3533955 : CollatzResearch.WordTrace tailWord_3533955 prefixEnd_3533955 1209745017573217412340095 := by
  unfold tailWord_3533955
  simp only [CollatzResearch.WordTrace]
  refine ⟨128893927912092061307923319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85929285274728040871948879 128893927912092061307923319)
  ·
    refine ⟨193340891868138091961884979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128893927912092061307923319 193340891868138091961884979)
    ·
      refine ⟨290011337802207137942827469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193340891868138091961884979 290011337802207137942827469)
      ·
        refine ⟨108754251675827676728560301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290011337802207137942827469 108754251675827676728560301)
        ·
          refine ⟨40782844378435378773210113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108754251675827676728560301 40782844378435378773210113)
          ·
            refine ⟨30587133283826534079907585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40782844378435378773210113 30587133283826534079907585)
            ·
              refine ⟨22940349962869900559930689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30587133283826534079907585 22940349962869900559930689)
              ·
                refine ⟨17205262472152425419948017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22940349962869900559930689 17205262472152425419948017)
                ·
                  refine ⟨12903946854114319064961013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17205262472152425419948017 12903946854114319064961013)
                  ·
                    refine ⟨1209745017573217412340095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12903946854114319064961013 1209745017573217412340095)
                    ·
                      rfl

theorem cell22_3533955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_3533955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533955 prefixEnd_3533955 := by exact prefixLift 3533955
  have htrace : WordTrace (prefixWord ++ tailWord_3533955) baseStart_3533955 baseEnd_3533955 := by
    simpa [prefixWord, tailWord_3533955, baseEnd_3533955] using wordTrace_append hprefix tailTrace_3533955
  have hstable : (prefixWord ++ tailWord_3533955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533955).length < 2 ^ (prefixWord ++ tailWord_3533955).sum := by decide
  have hdescent : baseEnd_3533955 < baseStart_3533955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533961 : List Nat := [1, 2, 1, 1, 4, 3, 4, 2, 1, 3]
def baseStart_3533961 : Nat := 118140960795 + 3533961 * 2 ^ 59
def prefixEnd_3533961 : Nat := 4983230072969 + 3 ^ 40 * 3533961 * 2
def baseEnd_3533961 : Nat := 1209747071495835396690077

theorem tailTrace_3533961 : CollatzResearch.WordTrace tailWord_3533961 prefixEnd_3533961 1209747071495835396690077 := by
  unfold tailWord_3533961
  simp only [CollatzResearch.WordTrace]
  refine ⟨128894146750070324332641737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85929431166713549555094491 128894146750070324332641737)
  ·
    refine ⟨96670610062552743249481303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128894146750070324332641737 96670610062552743249481303)
    ·
      refine ⟨145005915093829114874221955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96670610062552743249481303 145005915093829114874221955)
      ·
        refine ⟨217508872640743672311332933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145005915093829114874221955 217508872640743672311332933)
        ·
          refine ⟨40782913620139438558374925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217508872640743672311332933 40782913620139438558374925)
          ·
            refine ⟨15293592607552289459390597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40782913620139438558374925 15293592607552289459390597)
            ·
              refine ⟨2867548613916054273635737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15293592607552289459390597 2867548613916054273635737)
              ·
                refine ⟨2150661460437040705226803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867548613916054273635737 2150661460437040705226803)
                ·
                  refine ⟨3225992190655561057840205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150661460437040705226803 3225992190655561057840205)
                  ·
                    refine ⟨1209747071495835396690077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3225992190655561057840205 1209747071495835396690077)
                    ·
                      rfl

theorem cell22_3533961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 3].length) (baseStart_3533961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3533961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3533961 prefixEnd_3533961 := by exact prefixLift 3533961
  have htrace : WordTrace (prefixWord ++ tailWord_3533961) baseStart_3533961 baseEnd_3533961 := by
    simpa [prefixWord, tailWord_3533961, baseEnd_3533961] using wordTrace_append hprefix tailTrace_3533961
  have hstable : (prefixWord ++ tailWord_3533961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533961).length < 2 ^ (prefixWord ++ tailWord_3533961).sum := by decide
  have hdescent : baseEnd_3533961 < baseStart_3533961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534038 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3534038 : Nat := 118140960795 + 3534038 * 2 ^ 59
def prefixEnd_3534038 : Nat := 4983230072969 + 3 ^ 40 * 3534038 * 2
def baseEnd_3534038 : Nat := 1209773430169432862514841

theorem tailTrace_3534038 : CollatzResearch.WordTrace tailWord_3534038 prefixEnd_3534038 1209773430169432862514841 := by
  unfold tailWord_3534038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056059698174460405199673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85931303447194244322129845 8056059698174460405199673)
  ·
    refine ⟨6042044773630845303899755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8056059698174460405199673 6042044773630845303899755)
    ·
      refine ⟨9063067160446267955849633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042044773630845303899755 9063067160446267955849633)
      ·
        refine ⟨6797300370334700966887225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9063067160446267955849633 6797300370334700966887225)
        ·
          refine ⟨5097975277751025725165419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797300370334700966887225 5097975277751025725165419)
          ·
            refine ⟨7646962916626538587748129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097975277751025725165419 7646962916626538587748129)
            ·
              refine ⟨5735222187469903940811097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646962916626538587748129 5735222187469903940811097)
              ·
                refine ⟨4301416640602427955608323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735222187469903940811097 4301416640602427955608323)
                ·
                  refine ⟨6452124960903641933412485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301416640602427955608323 6452124960903641933412485)
                  ·
                    refine ⟨1209773430169432862514841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6452124960903641933412485 1209773430169432862514841)
                    ·
                      rfl

theorem cell22_3534038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3534038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534038 prefixEnd_3534038 := by exact prefixLift 3534038
  have htrace : WordTrace (prefixWord ++ tailWord_3534038) baseStart_3534038 baseEnd_3534038 := by
    simpa [prefixWord, tailWord_3534038, baseEnd_3534038] using wordTrace_append hprefix tailTrace_3534038
  have hstable : (prefixWord ++ tailWord_3534038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534038).length < 2 ^ (prefixWord ++ tailWord_3534038).sum := by decide
  have hdescent : baseEnd_3534038 < baseStart_3534038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534047 : List Nat := [1, 1, 2, 3, 2, 1, 6, 6]
def baseStart_3534047 : Nat := 118140960795 + 3534047 * 2 ^ 59
def prefixEnd_3534047 : Nat := 4983230072969 + 3 ^ 40 * 3534047 * 2
def baseEnd_3534047 : Nat := 134419612339262204337757

theorem tailTrace_3534047 : CollatzResearch.WordTrace tailWord_3534047 prefixEnd_3534047 134419612339262204337757 := by
  unfold tailWord_3534047
  simp only [CollatzResearch.WordTrace]
  refine ⟨128897283427758761020272395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85931522285172507346848263 128897283427758761020272395)
  ·
    refine ⟨193345925141638141530408593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128897283427758761020272395 193345925141638141530408593)
    ·
      refine ⟨145009443856228606147806445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193345925141638141530408593 145009443856228606147806445)
      ·
        refine ⟨54378541446085727305427417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145009443856228606147806445 54378541446085727305427417)
        ·
          refine ⟨40783906084564295479070563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54378541446085727305427417 40783906084564295479070563)
          ·
            refine ⟨61175859126846443218605845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40783906084564295479070563 61175859126846443218605845)
            ·
              refine ⟨2867618396570927025872149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61175859126846443218605845 2867618396570927025872149)
              ·
                refine ⟨134419612339262204337757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2867618396570927025872149 134419612339262204337757)
                ·
                  rfl

theorem cell22_3534047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 6].length) (baseStart_3534047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534047 prefixEnd_3534047 := by exact prefixLift 3534047
  have htrace : WordTrace (prefixWord ++ tailWord_3534047) baseStart_3534047 baseEnd_3534047 := by
    simpa [prefixWord, tailWord_3534047, baseEnd_3534047] using wordTrace_append hprefix tailTrace_3534047
  have hstable : (prefixWord ++ tailWord_3534047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534047).length < 2 ^ (prefixWord ++ tailWord_3534047).sum := by decide
  have hdescent : baseEnd_3534047 < baseStart_3534047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534053 : List Nat := [1, 3, 1, 4, 4, 1, 1, 3, 4]
def baseStart_3534053 : Nat := 118140960795 + 3534053 * 2 ^ 59
def prefixEnd_3534053 : Nat := 4983230072969 + 3 ^ 40 * 3534053 * 2
def baseEnd_3534053 : Nat := 403259521658659274463265

theorem tailTrace_3534053 : CollatzResearch.WordTrace tailWord_3534053 prefixEnd_3534053 403259521658659274463265 := by
  unfold tailWord_3534053
  simp only [CollatzResearch.WordTrace]
  refine ⟨128897502265737024044990813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85931668177158016029993875 128897502265737024044990813)
  ·
    refine ⟨48336563349651384016871555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128897502265737024044990813 48336563349651384016871555)
    ·
      refine ⟨72504845024477076025307333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48336563349651384016871555 72504845024477076025307333)
      ·
        refine ⟨13594658442089451754745125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72504845024477076025307333 13594658442089451754745125)
        ·
          refine ⟨2548998457891772204014711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13594658442089451754745125 2548998457891772204014711)
          ·
            refine ⟨3823497686837658306022067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548998457891772204014711 3823497686837658306022067)
            ·
              refine ⟨5735246530256487459033101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823497686837658306022067 5735246530256487459033101)
              ·
                refine ⟨2150717448846182797137413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5735246530256487459033101 2150717448846182797137413)
                ·
                  refine ⟨403259521658659274463265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150717448846182797137413 403259521658659274463265)
                  ·
                    rfl

theorem cell22_3534053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_3534053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534053 prefixEnd_3534053 := by exact prefixLift 3534053
  have htrace : WordTrace (prefixWord ++ tailWord_3534053) baseStart_3534053 baseEnd_3534053 := by
    simpa [prefixWord, tailWord_3534053, baseEnd_3534053] using wordTrace_append hprefix tailTrace_3534053
  have hstable : (prefixWord ++ tailWord_3534053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534053).length < 2 ^ (prefixWord ++ tailWord_3534053).sum := by decide
  have hdescent : baseEnd_3534053 < baseStart_3534053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534079 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 3, 3]
def baseStart_3534079 : Nat := 118140960795 + 3534079 * 2 ^ 59
def prefixEnd_3534079 : Nat := 4983230072969 + 3 ^ 40 * 3534079 * 2
def baseEnd_3534079 : Nat := 1209787465307322422239715

theorem tailTrace_3534079 : CollatzResearch.WordTrace tailWord_3534079 prefixEnd_3534079 1209787465307322422239715 := by
  unfold tailWord_3534079
  simp only [CollatzResearch.WordTrace]
  refine ⟨128898450563642830485437291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85932300375761886990291527 128898450563642830485437291)
  ·
    refine ⟨193347675845464245728155937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128898450563642830485437291 193347675845464245728155937)
    ·
      refine ⟨145010756884098184296116953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193347675845464245728155937 145010756884098184296116953)
      ·
        refine ⟨108758067663073638222087715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145010756884098184296116953 108758067663073638222087715)
        ·
          refine ⟨163137101494610457333131573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108758067663073638222087715 163137101494610457333131573)
          ·
            refine ⟨15294103265119730374981085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163137101494610457333131573 15294103265119730374981085)
            ·
              refine ⟨5735288724419898890617907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15294103265119730374981085 5735288724419898890617907)
              ·
                refine ⟨8602933086629848335926861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735288724419898890617907 8602933086629848335926861)
                ·
                  refine ⟨3226099907486193125972573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8602933086629848335926861 3226099907486193125972573)
                  ·
                    refine ⟨1209787465307322422239715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226099907486193125972573 1209787465307322422239715)
                    ·
                      rfl

theorem cell22_3534079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_3534079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534079 prefixEnd_3534079 := by exact prefixLift 3534079
  have htrace : WordTrace (prefixWord ++ tailWord_3534079) baseStart_3534079 baseEnd_3534079 := by
    simpa [prefixWord, tailWord_3534079, baseEnd_3534079] using wordTrace_append hprefix tailTrace_3534079
  have hstable : (prefixWord ++ tailWord_3534079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534079).length < 2 ^ (prefixWord ++ tailWord_3534079).sum := by decide
  have hdescent : baseEnd_3534079 < baseStart_3534079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534130 : List Nat := [3, 2, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_3534130 : Nat := 118140960795 + 3534130 * 2 ^ 59
def prefixEnd_3534130 : Nat := 4983230072969 + 3 ^ 40 * 3534130 * 2
def baseEnd_3534130 : Nat := 1209804923649575289214559

theorem tailTrace_3534130 : CollatzResearch.WordTrace tailWord_3534130 prefixEnd_3534130 1209804923649575289214559 := by
  unfold tailWord_3534130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32225077671614516548885961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85933540457638710797029229 32225077671614516548885961)
  ·
    refine ⟨24168808253710887411664471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32225077671614516548885961 24168808253710887411664471)
    ·
      refine ⟨36253212380566331117496707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24168808253710887411664471 36253212380566331117496707)
      ·
        refine ⟨54379818570849496676245061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36253212380566331117496707 54379818570849496676245061)
        ·
          refine ⟨10196215982034280626795949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54379818570849496676245061 10196215982034280626795949)
          ·
            refine ⟨3823580993262855235048481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10196215982034280626795949 3823580993262855235048481)
            ·
              refine ⟨2867685744947141426286361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3823580993262855235048481 2867685744947141426286361)
              ·
                refine ⟨2150764308710356069714771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2867685744947141426286361 2150764308710356069714771)
                ·
                  refine ⟨3226146463065534104572157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150764308710356069714771 3226146463065534104572157)
                  ·
                    refine ⟨1209804923649575289214559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226146463065534104572157 1209804923649575289214559)
                    ·
                      rfl

theorem cell22_3534130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_3534130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534130 prefixEnd_3534130 := by exact prefixLift 3534130
  have htrace : WordTrace (prefixWord ++ tailWord_3534130) baseStart_3534130 baseEnd_3534130 := by
    simpa [prefixWord, tailWord_3534130, baseEnd_3534130] using wordTrace_append hprefix tailTrace_3534130
  have hstable : (prefixWord ++ tailWord_3534130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534130).length < 2 ^ (prefixWord ++ tailWord_3534130).sum := by decide
  have hdescent : baseEnd_3534130 < baseStart_3534130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534141 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_3534141 : Nat := 118140960795 + 3534141 * 2 ^ 59
def prefixEnd_3534141 : Nat := 4983230072969 + 3 ^ 40 * 3534141 * 2
def baseEnd_3534141 : Nat := 1209808689174374927189525

theorem tailTrace_3534141 : CollatzResearch.WordTrace tailWord_3534141 prefixEnd_3534141 1209808689174374927189525 := by
  unfold tailWord_3534141
  simp only [CollatzResearch.WordTrace]
  refine ⟨128900711889418215074194277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85933807926278810049462851 128900711889418215074194277)
  ·
    refine ⟨24168883479265915326411427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128900711889418215074194277 24168883479265915326411427)
    ·
      refine ⟨36253325218898872989617141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24168883479265915326411427 36253325218898872989617141)
      ·
        refine ⟨3398749239271769342776607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36253325218898872989617141 3398749239271769342776607)
        ·
          refine ⟨5098123858907654014164911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398749239271769342776607 5098123858907654014164911)
          ·
            refine ⟨7647185788361481021247367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098123858907654014164911 7647185788361481021247367)
            ·
              refine ⟨11470778682542221531871051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647185788361481021247367 11470778682542221531871051)
              ·
                refine ⟨17206168023813332297806577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11470778682542221531871051 17206168023813332297806577)
                ·
                  refine ⟨12904626017859999223354933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17206168023813332297806577 12904626017859999223354933)
                  ·
                    refine ⟨1209808689174374927189525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12904626017859999223354933 1209808689174374927189525)
                    ·
                      rfl

theorem cell22_3534141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_3534141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534141 prefixEnd_3534141 := by exact prefixLift 3534141
  have htrace : WordTrace (prefixWord ++ tailWord_3534141) baseStart_3534141 baseEnd_3534141 := by
    simpa [prefixWord, tailWord_3534141, baseEnd_3534141] using wordTrace_append hprefix tailTrace_3534141
  have hstable : (prefixWord ++ tailWord_3534141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534141).length < 2 ^ (prefixWord ++ tailWord_3534141).sum := by decide
  have hdescent : baseEnd_3534141 < baseStart_3534141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534216 : List Nat := [2, 1, 3, 3, 1, 4, 2, 6]
def baseStart_3534216 : Nat := 118140960795 + 3534216 * 2 ^ 59
def prefixEnd_3534216 : Nat := 4983230072969 + 3 ^ 40 * 3534216 * 2
def baseEnd_3534216 : Nat := 134426040356344414618255

theorem tailTrace_3534216 : CollatzResearch.WordTrace tailWord_3534216 prefixEnd_3534216 134426040356344414618255 := by
  unfold tailWord_3534216
  simp only [CollatzResearch.WordTrace]
  refine ⟨64451723682073251441587251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85935631576097668588783001 64451723682073251441587251)
  ·
    refine ⟨96677585523109877162380877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64451723682073251441587251 96677585523109877162380877)
    ·
      refine ⟨36254094571166203935892829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96677585523109877162380877 36254094571166203935892829)
      ·
        refine ⟨13595285464187326475959811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36254094571166203935892829 13595285464187326475959811)
        ·
          refine ⟨20392928196280989713939717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13595285464187326475959811 20392928196280989713939717)
          ·
            refine ⟨3823674036802685571363697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20392928196280989713939717 3823674036802685571363697)
            ·
              refine ⟨2867755527602014178522773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3823674036802685571363697 2867755527602014178522773)
              ·
                refine ⟨134426040356344414618255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2867755527602014178522773 134426040356344414618255)
                ·
                  rfl

theorem cell22_3534216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 6].length) (baseStart_3534216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534216 prefixEnd_3534216 := by exact prefixLift 3534216
  have htrace : WordTrace (prefixWord ++ tailWord_3534216) baseStart_3534216 baseEnd_3534216 := by
    simpa [prefixWord, tailWord_3534216, baseEnd_3534216] using wordTrace_append hprefix tailTrace_3534216
  have hstable : (prefixWord ++ tailWord_3534216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534216).length < 2 ^ (prefixWord ++ tailWord_3534216).sum := by decide
  have hdescent : baseEnd_3534216 < baseStart_3534216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534244 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 5]
def baseStart_3534244 : Nat := 118140960795 + 3534244 * 2 ^ 59
def prefixEnd_3534244 : Nat := 4983230072969 + 3 ^ 40 * 3534244 * 2
def baseEnd_3534244 : Nat := 403281316059772330621403

theorem tailTrace_3534244 : CollatzResearch.WordTrace tailWord_3534244 prefixEnd_3534244 403281316059772330621403 := by
  unfold tailWord_3534244
  simp only [CollatzResearch.WordTrace]
  refine ⟨64452234304022531832596893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85936312405363375776795857 64452234304022531832596893)
  ·
    refine ⟨24169587864008449437223835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64452234304022531832596893 24169587864008449437223835)
    ·
      refine ⟨36254381796012674155835753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24169587864008449437223835 36254381796012674155835753)
      ·
        refine ⟨27190786347009505616876815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36254381796012674155835753 27190786347009505616876815)
        ·
          refine ⟨40786179520514258425315223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27190786347009505616876815 40786179520514258425315223)
          ·
            refine ⟨61179269280771387637972835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40786179520514258425315223 61179269280771387637972835)
            ·
              refine ⟨91768903921157081456959253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61179269280771387637972835 91768903921157081456959253)
              ·
                refine ⟨4301667371304238193294965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91768903921157081456959253 4301667371304238193294965)
                ·
                  refine ⟨403281316059772330621403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4301667371304238193294965 403281316059772330621403)
                  ·
                    rfl

theorem cell22_3534244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_3534244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534244 prefixEnd_3534244 := by exact prefixLift 3534244
  have htrace : WordTrace (prefixWord ++ tailWord_3534244) baseStart_3534244 baseEnd_3534244 := by
    simpa [prefixWord, tailWord_3534244, baseEnd_3534244] using wordTrace_append hprefix tailTrace_3534244
  have hstable : (prefixWord ++ tailWord_3534244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534244).length < 2 ^ (prefixWord ++ tailWord_3534244).sum := by decide
  have hdescent : baseEnd_3534244 < baseStart_3534244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534261 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 5]
def baseStart_3534261 : Nat := 118140960795 + 3534261 * 2 ^ 59
def prefixEnd_3534261 : Nat := 4983230072969 + 3 ^ 40 * 3534261 * 2
def baseEnd_3534261 : Nat := 403283255875578204729719

theorem tailTrace_3534261 : CollatzResearch.WordTrace tailWord_3534261 prefixEnd_3534261 403283255875578204729719 := by
  unfold tailWord_3534261
  simp only [CollatzResearch.WordTrace]
  refine ⟨128905088648983475568562637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85936725765988983712375091 128905088648983475568562637)
  ·
    refine ⟨48339408243368803338210989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128905088648983475568562637 48339408243368803338210989)
    ·
      refine ⟨18127278091263301251829121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48339408243368803338210989 18127278091263301251829121)
      ·
        refine ⟨13595458568447475938871841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18127278091263301251829121 13595458568447475938871841)
        ·
          refine ⟨10196593926335606954153881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13595458568447475938871841 10196593926335606954153881)
          ·
            refine ⟨7647445444751705215615411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10196593926335606954153881 7647445444751705215615411)
            ·
              refine ⟨11471168167127557823423117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647445444751705215615411 11471168167127557823423117)
              ·
                refine ⟨4301688062672834183783669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11471168167127557823423117 4301688062672834183783669)
                ·
                  refine ⟨403283255875578204729719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4301688062672834183783669 403283255875578204729719)
                  ·
                    rfl

theorem cell22_3534261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_3534261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534261 prefixEnd_3534261 := by exact prefixLift 3534261
  have htrace : WordTrace (prefixWord ++ tailWord_3534261) baseStart_3534261 baseEnd_3534261 := by
    simpa [prefixWord, tailWord_3534261, baseEnd_3534261] using wordTrace_append hprefix tailTrace_3534261
  have hstable : (prefixWord ++ tailWord_3534261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534261).length < 2 ^ (prefixWord ++ tailWord_3534261).sum := by decide
  have hdescent : baseEnd_3534261 < baseStart_3534261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534319 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 4, 4]
def baseStart_3534319 : Nat := 118140960795 + 3534319 * 2 ^ 59
def prefixEnd_3534319 : Nat := 4983230072969 + 3 ^ 40 * 3534319 * 2
def baseEnd_3534319 : Nat := 1209869622212041796238979

theorem tailTrace_3534319 : CollatzResearch.WordTrace tailWord_3534319 prefixEnd_3534319 1209869622212041796238979 := by
  unfold tailWord_3534319
  simp only [CollatzResearch.WordTrace]
  refine ⟨128907204082773351474174011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85938136055182234316116007 128907204082773351474174011)
  ·
    refine ⟨193360806124160027211261017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128907204082773351474174011 193360806124160027211261017)
    ·
      refine ⟨145020604593120020408445763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193360806124160027211261017 145020604593120020408445763)
      ·
        refine ⟨217530906889680030612668645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145020604593120020408445763 217530906889680030612668645)
        ·
          refine ⟨40787045041815005739875371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217530906889680030612668645 40787045041815005739875371)
          ·
            refine ⟨61180567562722508609813057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40787045041815005739875371 61180567562722508609813057)
            ·
              refine ⟨45885425672041881457359793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61180567562722508609813057 45885425672041881457359793)
              ·
                refine ⟨34414069254031411093019845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45885425672041881457359793 34414069254031411093019845)
                ·
                  refine ⟨6452637985130889579941221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34414069254031411093019845 6452637985130889579941221)
                  ·
                    refine ⟨1209869622212041796238979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6452637985130889579941221 1209869622212041796238979)
                    ·
                      rfl

theorem cell22_3534319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_3534319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534319 prefixEnd_3534319 := by exact prefixLift 3534319
  have htrace : WordTrace (prefixWord ++ tailWord_3534319) baseStart_3534319 baseEnd_3534319 := by
    simpa [prefixWord, tailWord_3534319, baseEnd_3534319] using wordTrace_append hprefix tailTrace_3534319
  have hstable : (prefixWord ++ tailWord_3534319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534319).length < 2 ^ (prefixWord ++ tailWord_3534319).sum := by decide
  have hdescent : baseEnd_3534319 < baseStart_3534319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534321 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_3534321 : Nat := 118140960795 + 3534321 * 2 ^ 59
def prefixEnd_3534321 : Nat := 4983230072969 + 3 ^ 40 * 3534321 * 2
def baseEnd_3534321 : Nat := 1209870306852914457688973

theorem tailTrace_3534321 : CollatzResearch.WordTrace tailWord_3534321 prefixEnd_3534321 1209870306852914457688973 := by
  unfold tailWord_3534321
  simp only [CollatzResearch.WordTrace]
  refine ⟨128907277028766105815746817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85938184685844070543831211 128907277028766105815746817)
  ·
    refine ⟨96680457771574579361810113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128907277028766105815746817 96680457771574579361810113)
    ·
      refine ⟨72510343328680934521357585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96680457771574579361810113 72510343328680934521357585)
      ·
        refine ⟨54382757496510700891018189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72510343328680934521357585 54382757496510700891018189)
        ·
          refine ⟨20393534061191512834131821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54382757496510700891018189 20393534061191512834131821)
          ·
            refine ⟨7647575272946817312799433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20393534061191512834131821 7647575272946817312799433)
            ·
              refine ⟨5735681454710112984599575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647575272946817312799433 5735681454710112984599575)
              ·
                refine ⟨8603522182065169476899363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735681454710112984599575 8603522182065169476899363)
                ·
                  refine ⟨12905283273097754215349045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8603522182065169476899363 12905283273097754215349045)
                  ·
                    refine ⟨1209870306852914457688973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12905283273097754215349045 1209870306852914457688973)
                    ·
                      rfl

theorem cell22_3534321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_3534321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534321 prefixEnd_3534321 := by exact prefixLift 3534321
  have htrace : WordTrace (prefixWord ++ tailWord_3534321) baseStart_3534321 baseEnd_3534321 := by
    simpa [prefixWord, tailWord_3534321, baseEnd_3534321] using wordTrace_append hprefix tailTrace_3534321
  have hstable : (prefixWord ++ tailWord_3534321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534321).length < 2 ^ (prefixWord ++ tailWord_3534321).sum := by decide
  have hdescent : baseEnd_3534321 < baseStart_3534321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534338 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3534338 : Nat := 118140960795 + 3534338 * 2 ^ 59
def prefixEnd_3534338 : Nat := 4983230072969 + 3 ^ 40 * 3534338 * 2
def baseEnd_3534338 : Nat := 1209876126300332080013921

theorem tailTrace_3534338 : CollatzResearch.WordTrace tailWord_3534338 prefixEnd_3534338 1209876126300332080013921 := by
  unfold tailWord_3534338
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226974267426129429778917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85938598046469678479410445 32226974267426129429778917)
  ·
    refine ⟨6042557675142399268083547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32226974267426129429778917 6042557675142399268083547)
    ·
      refine ⟨9063836512713598902125321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042557675142399268083547 9063836512713598902125321)
      ·
        refine ⟨6797877384535199176593991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9063836512713598902125321 6797877384535199176593991)
        ·
          refine ⟨10196816076802798764890987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797877384535199176593991 10196816076802798764890987)
          ·
            refine ⟨15295224115204198147336481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10196816076802798764890987 15295224115204198147336481)
            ·
              refine ⟨11471418086403148610502361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15295224115204198147336481 11471418086403148610502361)
              ·
                refine ⟨8603563564802361457876771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471418086403148610502361 8603563564802361457876771)
                ·
                  refine ⟨12905345347203542186815157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8603563564802361457876771 12905345347203542186815157)
                  ·
                    refine ⟨1209876126300332080013921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12905345347203542186815157 1209876126300332080013921)
                    ·
                      rfl

theorem cell22_3534338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3534338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534338 prefixEnd_3534338 := by exact prefixLift 3534338
  have htrace : WordTrace (prefixWord ++ tailWord_3534338) baseStart_3534338 baseEnd_3534338 := by
    simpa [prefixWord, tailWord_3534338, baseEnd_3534338] using wordTrace_append hprefix tailTrace_3534338
  have hstable : (prefixWord ++ tailWord_3534338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534338).length < 2 ^ (prefixWord ++ tailWord_3534338).sum := by decide
  have hdescent : baseEnd_3534338 < baseStart_3534338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534340 : List Nat := [2, 3, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3534340 : Nat := 118140960795 + 3534340 * 2 ^ 59
def prefixEnd_3534340 : Nat := 4983230072969 + 3 ^ 40 * 3534340 * 2
def baseEnd_3534340 : Nat := 403292270313734913821305

theorem tailTrace_3534340 : CollatzResearch.WordTrace tailWord_3534340 prefixEnd_3534340 403292270313734913821305 := by
  unfold tailWord_3534340
  simp only [CollatzResearch.WordTrace]
  refine ⟨64453985007848636030344237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85938646677131514707125649 64453985007848636030344237)
  ·
    refine ⟨24170244377943238511379089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64453985007848636030344237 24170244377943238511379089)
    ·
      refine ⟨18127683283457428883534317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24170244377943238511379089 18127683283457428883534317)
      ·
        refine ⟨6797881231296535831325369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18127683283457428883534317 6797881231296535831325369)
        ·
          refine ⟨5098410923472401873494027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797881231296535831325369 5098410923472401873494027)
          ·
            refine ⟨7647616385208602810241041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098410923472401873494027 7647616385208602810241041)
            ·
              refine ⟨5735712288906452107680781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647616385208602810241041 5735712288906452107680781)
              ·
                refine ⟨2150892108339919540380293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5735712288906452107680781 2150892108339919540380293)
                ·
                  refine ⟨403292270313734913821305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150892108339919540380293 403292270313734913821305)
                  ·
                    rfl

theorem cell22_3534340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3534340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534340 prefixEnd_3534340 := by exact prefixLift 3534340
  have htrace : WordTrace (prefixWord ++ tailWord_3534340) baseStart_3534340 baseEnd_3534340 := by
    simpa [prefixWord, tailWord_3534340, baseEnd_3534340] using wordTrace_append hprefix tailTrace_3534340
  have hstable : (prefixWord ++ tailWord_3534340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534340).length < 2 ^ (prefixWord ++ tailWord_3534340).sum := by decide
  have hdescent : baseEnd_3534340 < baseStart_3534340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534473 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 2, 3]
def baseStart_3534473 : Nat := 118140960795 + 3534473 * 2 ^ 59
def prefixEnd_3534473 : Nat := 4983230072969 + 3 ^ 40 * 3534473 * 2
def baseEnd_3534473 : Nat := 1209922339559236727888507

theorem tailTrace_3534473 : CollatzResearch.WordTrace tailWord_3534473 prefixEnd_3534473 1209922339559236727888507 := by
  unfold tailWord_3534473
  simp only [CollatzResearch.WordTrace]
  refine ⟨128912820924215435775280073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85941880616143623850186715 128912820924215435775280073)
  ·
    refine ⟨96684615693161576831460055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128912820924215435775280073 96684615693161576831460055)
    ·
      refine ⟨145026923539742365247190083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96684615693161576831460055 145026923539742365247190083)
      ·
        refine ⟨217540385309613547870785125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145026923539742365247190083 217540385309613547870785125)
        ·
          refine ⟨40788822245552540225772211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217540385309613547870785125 40788822245552540225772211)
          ·
            refine ⟨61183233368328810338658317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40788822245552540225772211 61183233368328810338658317)
            ·
              refine ⟨22943712513123303876996869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61183233368328810338658317 22943712513123303876996869)
              ·
                refine ⟨4301946096210619476936913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22943712513123303876996869 4301946096210619476936913)
                ·
                  refine ⟨3226459572157964607702685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4301946096210619476936913 3226459572157964607702685)
                  ·
                    refine ⟨1209922339559236727888507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226459572157964607702685 1209922339559236727888507)
                    ·
                      rfl

theorem cell22_3534473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_3534473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534473 prefixEnd_3534473 := by exact prefixLift 3534473
  have htrace : WordTrace (prefixWord ++ tailWord_3534473) baseStart_3534473 baseEnd_3534473 := by
    simpa [prefixWord, tailWord_3534473, baseEnd_3534473] using wordTrace_append hprefix tailTrace_3534473
  have hstable : (prefixWord ++ tailWord_3534473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534473).length < 2 ^ (prefixWord ++ tailWord_3534473).sum := by decide
  have hdescent : baseEnd_3534473 < baseStart_3534473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534535 : List Nat := [1, 1, 4, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3534535 : Nat := 118140960795 + 3534535 * 2 ^ 59
def prefixEnd_3534535 : Nat := 4983230072969 + 3 ^ 40 * 3534535 * 2
def baseEnd_3534535 : Nat := 1209943563426289232838317

theorem tailTrace_3534535 : CollatzResearch.WordTrace tailWord_3534535 prefixEnd_3534535 1209943563426289232838317 := by
  unfold tailWord_3534535
  simp only [CollatzResearch.WordTrace]
  refine ⟨128915082249990820364037059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85943388166660546909358039 128915082249990820364037059)
  ·
    refine ⟨193372623374986230546055589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128915082249990820364037059 193372623374986230546055589)
    ·
      refine ⟨36257366882809918227385423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193372623374986230546055589 36257366882809918227385423)
      ·
        refine ⟨54386050324214877341078135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36257366882809918227385423 54386050324214877341078135)
        ·
          refine ⟨81579075486322316011617203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54386050324214877341078135 81579075486322316011617203)
          ·
            refine ⟨122368613229483474017425805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81579075486322316011617203 122368613229483474017425805)
            ·
              refine ⟨45888229961056302756534677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122368613229483474017425805 45888229961056302756534677)
              ·
                refine ⟨2151010779424514191712563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45888229961056302756534677 2151010779424514191712563)
                ·
                  refine ⟨3226516169136771287568845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151010779424514191712563 3226516169136771287568845)
                  ·
                    refine ⟨1209943563426289232838317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226516169136771287568845 1209943563426289232838317)
                    ·
                      rfl

theorem cell22_3534535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3534535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534535 prefixEnd_3534535 := by exact prefixLift 3534535
  have htrace : WordTrace (prefixWord ++ tailWord_3534535) baseStart_3534535 baseEnd_3534535 := by
    simpa [prefixWord, tailWord_3534535, baseEnd_3534535] using wordTrace_append hprefix tailTrace_3534535
  have hstable : (prefixWord ++ tailWord_3534535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534535).length < 2 ^ (prefixWord ++ tailWord_3534535).sum := by decide
  have hdescent : baseEnd_3534535 < baseStart_3534535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534593 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 6]
def baseStart_3534593 : Nat := 118140960795 + 3534593 * 2 ^ 59
def prefixEnd_3534593 : Nat := 4983230072969 + 3 ^ 40 * 3534593 * 2
def baseEnd_3534593 : Nat := 403321139337198804962713

theorem tailTrace_3534593 : CollatzResearch.WordTrace tailWord_3534593 prefixEnd_3534593 403321139337198804962713 := by
  unfold tailWord_3534593
  simp only [CollatzResearch.WordTrace]
  refine ⟨128917197683780696269648433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85944798455853797513098955 128917197683780696269648433)
  ·
    refine ⟨96687898262835522202236325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128917197683780696269648433 96687898262835522202236325)
    ·
      refine ⟨18128980924281660412919311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96687898262835522202236325 18128980924281660412919311)
      ·
        refine ⟨27193471386422490619378967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18128980924281660412919311 27193471386422490619378967)
        ·
          refine ⟨40790207079633735929068451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27193471386422490619378967 40790207079633735929068451)
          ·
            refine ⟨61185310619450603893602677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40790207079633735929068451 61185310619450603893602677)
            ·
              refine ⟨5736122870573494115025251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61185310619450603893602677 5736122870573494115025251)
              ·
                refine ⟨8604184305860241172537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736122870573494115025251 8604184305860241172537877)
                ·
                  refine ⟨403321139337198804962713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8604184305860241172537877 403321139337198804962713)
                  ·
                    rfl

theorem cell22_3534593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_3534593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534593 prefixEnd_3534593 := by exact prefixLift 3534593
  have htrace : WordTrace (prefixWord ++ tailWord_3534593) baseStart_3534593 baseEnd_3534593 := by
    simpa [prefixWord, tailWord_3534593, baseEnd_3534593] using wordTrace_append hprefix tailTrace_3534593
  have hstable : (prefixWord ++ tailWord_3534593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534593).length < 2 ^ (prefixWord ++ tailWord_3534593).sum := by decide
  have hdescent : baseEnd_3534593 < baseStart_3534593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534599 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 5]
def baseStart_3534599 : Nat := 118140960795 + 3534599 * 2 ^ 59
def prefixEnd_3534599 : Nat := 4983230072969 + 3 ^ 40 * 3534599 * 2
def baseEnd_3534599 : Nat := 403321823978071466412707

theorem tailTrace_3534599 : CollatzResearch.WordTrace tailWord_3534599 prefixEnd_3534599 403321823978071466412707 := by
  unfold tailWord_3534599
  simp only [CollatzResearch.WordTrace]
  refine ⟨128917416521758959294366851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85944944347839306196244567 128917416521758959294366851)
  ·
    refine ⟨193376124782638438941550277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128917416521758959294366851 193376124782638438941550277)
    ·
      refine ⟨36258023396744707301540677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193376124782638438941550277 36258023396744707301540677)
      ·
        refine ⟨6798379386889632619038877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36258023396744707301540677 6798379386889632619038877)
        ·
          refine ⟨2549392270083612232139579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6798379386889632619038877 2549392270083612232139579)
          ·
            refine ⟨3824088405125418348209369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549392270083612232139579 3824088405125418348209369)
            ·
              refine ⟨2868066303844063761157027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3824088405125418348209369 2868066303844063761157027)
              ·
                refine ⟨4302099455766095641735541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868066303844063761157027 4302099455766095641735541)
                ·
                  refine ⟨403321823978071466412707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302099455766095641735541 403321823978071466412707)
                  ·
                    rfl

theorem cell22_3534599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 5].length) (baseStart_3534599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534599 prefixEnd_3534599 := by exact prefixLift 3534599
  have htrace : WordTrace (prefixWord ++ tailWord_3534599) baseStart_3534599 baseEnd_3534599 := by
    simpa [prefixWord, tailWord_3534599, baseEnd_3534599] using wordTrace_append hprefix tailTrace_3534599
  have hstable : (prefixWord ++ tailWord_3534599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534599).length < 2 ^ (prefixWord ++ tailWord_3534599).sum := by decide
  have hdescent : baseEnd_3534599 < baseStart_3534599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534638 : List Nat := [4, 1, 3, 2, 12]
def baseStart_3534638 : Nat := 118140960795 + 3534638 * 2 ^ 59
def prefixEnd_3534638 : Nat := 4983230072969 + 3 ^ 40 * 3534638 * 2
def baseEnd_3534638 : Nat := 4979336717823997109107

theorem tailTrace_3534638 : CollatzResearch.WordTrace tailWord_3534638 prefixEnd_3534638 4979336717823997109107 := by
  unfold tailWord_3534638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114854871077208619379571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85945892645745112636691045 16114854871077208619379571)
  ·
    refine ⟨24172282306615812929069357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16114854871077208619379571 24172282306615812929069357)
    ·
      refine ⟨9064605864980929848401009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24172282306615812929069357 9064605864980929848401009)
      ·
        refine ⟨6798454398735697386300757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9064605864980929848401009 6798454398735697386300757)
        ·
          refine ⟨4979336717823997109107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6798454398735697386300757 4979336717823997109107)
          ·
            rfl

theorem cell22_3534638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 12].length) (baseStart_3534638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534638 prefixEnd_3534638 := by exact prefixLift 3534638
  have htrace : WordTrace (prefixWord ++ tailWord_3534638) baseStart_3534638 baseEnd_3534638 := by
    simpa [prefixWord, tailWord_3534638, baseEnd_3534638] using wordTrace_append hprefix tailTrace_3534638
  have hstable : (prefixWord ++ tailWord_3534638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534638).length < 2 ^ (prefixWord ++ tailWord_3534638).sum := by decide
  have hdescent : baseEnd_3534638 < baseStart_3534638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534642 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_3534642 : Nat := 118140960795 + 3534642 * 2 ^ 59
def prefixEnd_3534642 : Nat := 4983230072969 + 3 ^ 40 * 3534642 * 2
def baseEnd_3534642 : Nat := 1209980191712976620412989

theorem tailTrace_3534642 : CollatzResearch.WordTrace tailWord_3534642 prefixEnd_3534642 1209980191712976620412989 := by
  unfold tailWord_3534642
  simp only [CollatzResearch.WordTrace]
  refine ⟨32229746215150794409545545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85945989907068785092121453 32229746215150794409545545)
  ·
    refine ⟨24172309661363095807159159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32229746215150794409545545 24172309661363095807159159)
    ·
      refine ⟨36258464492044643710738739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24172309661363095807159159 36258464492044643710738739)
      ·
        refine ⟨54387696738066965566108109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36258464492044643710738739 54387696738066965566108109)
        ·
          refine ⟨20395386276775112087290541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54387696738066965566108109 20395386276775112087290541)
          ·
            refine ⟨7648269853790667032733953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20395386276775112087290541 7648269853790667032733953)
            ·
              refine ⟨5736202390343000274550465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7648269853790667032733953 5736202390343000274550465)
              ·
                refine ⟨4302151792757250205912849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736202390343000274550465 4302151792757250205912849)
                ·
                  refine ⟨3226613844567937654434637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4302151792757250205912849 3226613844567937654434637)
                  ·
                    refine ⟨1209980191712976620412989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226613844567937654434637 1209980191712976620412989)
                    ·
                      rfl

theorem cell22_3534642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_3534642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534642 prefixEnd_3534642 := by exact prefixLift 3534642
  have htrace : WordTrace (prefixWord ++ tailWord_3534642) baseStart_3534642 baseEnd_3534642 := by
    simpa [prefixWord, tailWord_3534642, baseEnd_3534642] using wordTrace_append hprefix tailTrace_3534642
  have hstable : (prefixWord ++ tailWord_3534642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534642).length < 2 ^ (prefixWord ++ tailWord_3534642).sum := by decide
  have hdescent : baseEnd_3534642 < baseStart_3534642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534644 : List Nat := [2, 5, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3534644 : Nat := 118140960795 + 3534644 * 2 ^ 59
def prefixEnd_3534644 : Nat := 4983230072969 + 3 ^ 40 * 3534644 * 2
def baseEnd_3534644 : Nat := 403326958784616427287661

theorem tailTrace_3534644 : CollatzResearch.WordTrace tailWord_3534644 prefixEnd_3534644 403326958784616427287661 := by
  unfold tailWord_3534644
  simp only [CollatzResearch.WordTrace]
  refine ⟨64459528903297965989877493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85946038537730621319836657 64459528903297965989877493)
  ·
    refine ⟨6043080834684184311551015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64459528903297965989877493 6043080834684184311551015)
    ·
      refine ⟨9064621252026276467326523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043080834684184311551015 9064621252026276467326523)
      ·
        refine ⟨13596931878039414700989785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064621252026276467326523 13596931878039414700989785)
        ·
          refine ⟨10197698908529561025742339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13596931878039414700989785 10197698908529561025742339)
          ·
            refine ⟨15296548362794341538613509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10197698908529561025742339 15296548362794341538613509)
            ·
              refine ⟨2868102818023939038490033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15296548362794341538613509 2868102818023939038490033)
              ·
                refine ⟨2151077113517954278867525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868102818023939038490033 2151077113517954278867525)
                ·
                  refine ⟨403326958784616427287661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151077113517954278867525 403326958784616427287661)
                  ·
                    rfl

theorem cell22_3534644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3534644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534644 prefixEnd_3534644 := by exact prefixLift 3534644
  have htrace : WordTrace (prefixWord ++ tailWord_3534644) baseStart_3534644 baseEnd_3534644 := by
    simpa [prefixWord, tailWord_3534644, baseEnd_3534644] using wordTrace_append hprefix tailTrace_3534644
  have hstable : (prefixWord ++ tailWord_3534644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534644).length < 2 ^ (prefixWord ++ tailWord_3534644).sum := by decide
  have hdescent : baseEnd_3534644 < baseStart_3534644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534655 : List Nat := [1, 1, 2, 2, 6, 2, 1, 7]
def baseStart_3534655 : Nat := 118140960795 + 3534655 * 2 ^ 59
def prefixEnd_3534655 : Nat := 4983230072969 + 3 ^ 40 * 3534655 * 2
def baseEnd_3534655 : Nat := 134442737986516546648661

theorem tailTrace_3534655 : CollatzResearch.WordTrace tailWord_3534655 prefixEnd_3534655 134442737986516546648661 := by
  unfold tailWord_3534655
  simp only [CollatzResearch.WordTrace]
  refine ⟨128919459009556080858405419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85946306006370720572270279 128919459009556080858405419)
  ·
    refine ⟨193379188514334121287608129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128919459009556080858405419 193379188514334121287608129)
    ·
      refine ⟨145034391385750590965706097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193379188514334121287608129 145034391385750590965706097)
      ·
        refine ⟨108775793539312943224279573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145034391385750590965706097 108775793539312943224279573)
        ·
          refine ⟨5098865322155294213638105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108775793539312943224279573 5098865322155294213638105)
          ·
            refine ⟨3824148991616470660228579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5098865322155294213638105 3824148991616470660228579)
            ·
              refine ⟨5736223487424705990342869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824148991616470660228579 5736223487424705990342869)
              ·
                refine ⟨134442737986516546648661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5736223487424705990342869 134442737986516546648661)
                ·
                  rfl

theorem cell22_3534655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 7].length) (baseStart_3534655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534655 prefixEnd_3534655 := by exact prefixLift 3534655
  have htrace : WordTrace (prefixWord ++ tailWord_3534655) baseStart_3534655 baseEnd_3534655 := by
    simpa [prefixWord, tailWord_3534655, baseEnd_3534655] using wordTrace_append hprefix tailTrace_3534655
  have hstable : (prefixWord ++ tailWord_3534655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534655).length < 2 ^ (prefixWord ++ tailWord_3534655).sum := by decide
  have hdescent : baseEnd_3534655 < baseStart_3534655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534687 : List Nat := [1, 1, 2, 3, 1, 4, 1, 5, 1, 3]
def baseStart_3534687 : Nat := 118140960795 + 3534687 * 2 ^ 59
def prefixEnd_3534687 : Nat := 4983230072969 + 3 ^ 40 * 3534687 * 2
def baseEnd_3534687 : Nat := 1209995596132611503037851

theorem tailTrace_3534687 : CollatzResearch.WordTrace tailWord_3534687 prefixEnd_3534687 1209995596132611503037851 := by
  unfold tailWord_3534687
  simp only [CollatzResearch.WordTrace]
  refine ⟨128920626145440150323570315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85947084096960100215713543 128920626145440150323570315)
  ·
    refine ⟨193380939218160225485355473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128920626145440150323570315 193380939218160225485355473)
    ·
      refine ⟨145035704413620169114016605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193380939218160225485355473 145035704413620169114016605)
      ·
        refine ⟨54388389155107563417756227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145035704413620169114016605 54388389155107563417756227)
        ·
          refine ⟨81582583732661345126634341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54388389155107563417756227 81582583732661345126634341)
          ·
            refine ⟨15296734449874002211243939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81582583732661345126634341 15296734449874002211243939)
            ·
              refine ⟨22945101674811003316865909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15296734449874002211243939 22945101674811003316865909)
              ·
                refine ⟨2151103282013531560956179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22945101674811003316865909 2151103282013531560956179)
                ·
                  refine ⟨3226654923020297341434269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151103282013531560956179 3226654923020297341434269)
                  ·
                    refine ⟨1209995596132611503037851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226654923020297341434269 1209995596132611503037851)
                    ·
                      rfl

theorem cell22_3534687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 3].length) (baseStart_3534687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534687 prefixEnd_3534687 := by exact prefixLift 3534687
  have htrace : WordTrace (prefixWord ++ tailWord_3534687) baseStart_3534687 baseEnd_3534687 := by
    simpa [prefixWord, tailWord_3534687, baseEnd_3534687] using wordTrace_append hprefix tailTrace_3534687
  have hstable : (prefixWord ++ tailWord_3534687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534687).length < 2 ^ (prefixWord ++ tailWord_3534687).sum := by decide
  have hdescent : baseEnd_3534687 < baseStart_3534687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534700 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 5]
def baseStart_3534700 : Nat := 118140960795 + 3534700 * 2 ^ 59
def prefixEnd_3534700 : Nat := 4983230072969 + 3 ^ 40 * 3534700 * 2
def baseEnd_3534700 : Nat := 403333348766094600820937

theorem tailTrace_3534700 : CollatzResearch.WordTrace tailWord_3534700 prefixEnd_3534700 403333348766094600820937 := by
  unfold tailWord_3534700
  simp only [CollatzResearch.WordTrace]
  refine ⟨64460550147196526771896777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85947400196262035695862369 64460550147196526771896777)
  ·
    refine ⟨48345412610397395078922583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64460550147196526771896777 48345412610397395078922583)
    ·
      refine ⟨72518118915596092618383875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48345412610397395078922583 72518118915596092618383875)
      ·
        refine ⟨108777178373394138927575813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72518118915596092618383875 108777178373394138927575813)
        ·
          refine ⟨20395720945011401048920465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108777178373394138927575813 20395720945011401048920465)
          ·
            refine ⟨15296790708758550786690349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20395720945011401048920465 15296790708758550786690349)
            ·
              refine ⟨5736296515784456545008881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15296790708758550786690349 5736296515784456545008881)
              ·
                refine ⟨4302222386838342408756661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736296515784456545008881 4302222386838342408756661)
                ·
                  refine ⟨403333348766094600820937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302222386838342408756661 403333348766094600820937)
                  ·
                    rfl

theorem cell22_3534700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_3534700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534700 prefixEnd_3534700 := by exact prefixLift 3534700
  have htrace : WordTrace (prefixWord ++ tailWord_3534700) baseStart_3534700 baseEnd_3534700 := by
    simpa [prefixWord, tailWord_3534700, baseEnd_3534700] using wordTrace_append hprefix tailTrace_3534700
  have hstable : (prefixWord ++ tailWord_3534700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534700).length < 2 ^ (prefixWord ++ tailWord_3534700).sum := by decide
  have hdescent : baseEnd_3534700 < baseStart_3534700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534777 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 2, 3]
def baseStart_3534777 : Nat := 118140960795 + 3534777 * 2 ^ 59
def prefixEnd_3534777 : Nat := 4983230072969 + 3 ^ 40 * 3534777 * 2
def baseEnd_3534777 : Nat := 1210026404971881268287575

theorem tailTrace_3534777 : CollatzResearch.WordTrace tailWord_3534777 prefixEnd_3534777 1210026404971881268287575 := by
  unfold tailWord_3534777
  simp only [CollatzResearch.WordTrace]
  refine ⟨128923908715114095694346585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85949272476742730462897723 128923908715114095694346585)
  ·
    refine ⟨96692931536335571770759939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128923908715114095694346585 96692931536335571770759939)
    ·
      refine ⟨145039397304503357656139909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96692931536335571770759939 145039397304503357656139909)
      ·
        refine ⟨27194886994594379560526233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145039397304503357656139909 27194886994594379560526233)
        ·
          refine ⟨20396165245945784670394675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27194886994594379560526233 20396165245945784670394675)
          ·
            refine ⟨30594247868918677005592013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20396165245945784670394675 30594247868918677005592013)
            ·
              refine ⟨11472842950844503877097005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30594247868918677005592013 11472842950844503877097005)
              ·
                refine ⟨4302316106566688953911377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11472842950844503877097005 4302316106566688953911377)
                ·
                  refine ⟨3226737079925016715433533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4302316106566688953911377 3226737079925016715433533)
                  ·
                    refine ⟨1210026404971881268287575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226737079925016715433533 1210026404971881268287575)
                    ·
                      rfl

theorem cell22_3534777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_3534777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534777 prefixEnd_3534777 := by exact prefixLift 3534777
  have htrace : WordTrace (prefixWord ++ tailWord_3534777) baseStart_3534777 baseEnd_3534777 := by
    simpa [prefixWord, tailWord_3534777, baseEnd_3534777] using wordTrace_append hprefix tailTrace_3534777
  have hstable : (prefixWord ++ tailWord_3534777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534777).length < 2 ^ (prefixWord ++ tailWord_3534777).sum := by decide
  have hdescent : baseEnd_3534777 < baseStart_3534777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534792 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_3534792 : Nat := 118140960795 + 3534792 * 2 ^ 59
def prefixEnd_3534792 : Nat := 4983230072969 + 3 ^ 40 * 3534792 * 2
def baseEnd_3534792 : Nat := 1210031539778426229162529

theorem tailTrace_3534792 : CollatzResearch.WordTrace tailWord_3534792 prefixEnd_3534792 1210031539778426229162529 := by
  unfold tailWord_3534792
  simp only [CollatzResearch.WordTrace]
  refine ⟨64462227905029876628071315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85949637206706502170761753 64462227905029876628071315)
  ·
    refine ⟨96693341857544814942106973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64462227905029876628071315 96693341857544814942106973)
    ·
      refine ⟨36260003196579305603290115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96693341857544814942106973 36260003196579305603290115)
      ·
        refine ⟨54390004794868958404935173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36260003196579305603290115 54390004794868958404935173)
        ·
          refine ⟨10198125899037929700925345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54390004794868958404935173 10198125899037929700925345)
          ·
            refine ⟨7648594424278447275694009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10198125899037929700925345 7648594424278447275694009)
            ·
              refine ⟨5736445818208835456770507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7648594424278447275694009 5736445818208835456770507)
              ·
                refine ⟨8604668727313253185155761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736445818208835456770507 8604668727313253185155761)
                ·
                  refine ⟨6453501545484939888866821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604668727313253185155761 6453501545484939888866821)
                  ·
                    refine ⟨1210031539778426229162529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6453501545484939888866821 1210031539778426229162529)
                    ·
                      rfl

theorem cell22_3534792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_3534792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534792 prefixEnd_3534792 := by exact prefixLift 3534792
  have htrace : WordTrace (prefixWord ++ tailWord_3534792) baseStart_3534792 baseEnd_3534792 := by
    simpa [prefixWord, tailWord_3534792, baseEnd_3534792] using wordTrace_append hprefix tailTrace_3534792
  have hstable : (prefixWord ++ tailWord_3534792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534792).length < 2 ^ (prefixWord ++ tailWord_3534792).sum := by decide
  have hdescent : baseEnd_3534792 < baseStart_3534792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534813 : List Nat := [1, 4, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3534813 : Nat := 118140960795 + 3534813 * 2 ^ 59
def prefixEnd_3534813 : Nat := 4983230072969 + 3 ^ 40 * 3534813 * 2
def baseEnd_3534813 : Nat := 403346242835863058129155

theorem tailTrace_3534813 : CollatzResearch.WordTrace tailWord_3534813 prefixEnd_3534813 403346242835863058129155 := by
  unfold tailWord_3534813
  simp only [CollatzResearch.WordTrace]
  refine ⟨128925221742983673842657093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85950147828655782561771395 128925221742983673842657093)
  ·
    refine ⟨24173479076809438845498205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128925221742983673842657093 24173479076809438845498205)
    ·
      refine ⟨9065054653803539567061827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24173479076809438845498205 9065054653803539567061827)
      ·
        refine ⟨13597581980705309350592741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065054653803539567061827 13597581980705309350592741)
        ·
          refine ⟨2549546621382245503236139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13597581980705309350592741 2549546621382245503236139)
          ·
            refine ⟨3824319932073368254854209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549546621382245503236139 3824319932073368254854209)
            ·
              refine ⟨2868239949055026191140657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3824319932073368254854209 2868239949055026191140657)
              ·
                refine ⟨2151179961791269643355493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868239949055026191140657 2151179961791269643355493)
                ·
                  refine ⟨403346242835863058129155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151179961791269643355493 403346242835863058129155)
                  ·
                    rfl

theorem cell22_3534813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3534813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534813 prefixEnd_3534813 := by exact prefixLift 3534813
  have htrace : WordTrace (prefixWord ++ tailWord_3534813) baseStart_3534813 baseEnd_3534813 := by
    simpa [prefixWord, tailWord_3534813, baseEnd_3534813] using wordTrace_append hprefix tailTrace_3534813
  have hstable : (prefixWord ++ tailWord_3534813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534813).length < 2 ^ (prefixWord ++ tailWord_3534813).sum := by decide
  have hdescent : baseEnd_3534813 < baseStart_3534813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534869 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 5]
def baseStart_3534869 : Nat := 118140960795 + 3534869 * 2 ^ 59
def prefixEnd_3534869 : Nat := 4983230072969 + 3 ^ 40 * 3534869 * 2
def baseEnd_3534869 : Nat := 403352632817341231662431

theorem tailTrace_3534869 : CollatzResearch.WordTrace tailWord_3534869 prefixEnd_3534869 403352632817341231662431 := by
  unfold tailWord_3534869
  simp only [CollatzResearch.WordTrace]
  refine ⟨128927264230780795406695661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85951509487187196937797107 128927264230780795406695661)
  ·
    refine ⟨48347724086542798277510873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128927264230780795406695661 48347724086542798277510873)
    ·
      refine ⟨36260793064907098708133155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48347724086542798277510873 36260793064907098708133155)
      ·
        refine ⟨54391189597360648062199733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36260793064907098708133155 54391189597360648062199733)
        ·
          refine ⟨5099174024752560755831225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54391189597360648062199733 5099174024752560755831225)
          ·
            refine ⟨3824380518564420566873419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5099174024752560755831225 3824380518564420566873419)
            ·
              refine ⟨5736570777846630850310129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824380518564420566873419 5736570777846630850310129)
              ·
                refine ⟨4302428083384973137732597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736570777846630850310129 4302428083384973137732597)
                ·
                  refine ⟨403352632817341231662431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302428083384973137732597 403352632817341231662431)
                  ·
                    rfl

theorem cell22_3534869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_3534869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534869 prefixEnd_3534869 := by exact prefixLift 3534869
  have htrace : WordTrace (prefixWord ++ tailWord_3534869) baseStart_3534869 baseEnd_3534869 := by
    simpa [prefixWord, tailWord_3534869, baseEnd_3534869] using wordTrace_append hprefix tailTrace_3534869
  have hstable : (prefixWord ++ tailWord_3534869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534869).length < 2 ^ (prefixWord ++ tailWord_3534869).sum := by decide
  have hdescent : baseEnd_3534869 < baseStart_3534869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534895 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 1, 5]
def baseStart_3534895 : Nat := 118140960795 + 3534895 * 2 ^ 59
def prefixEnd_3534895 : Nat := 4983230072969 + 3 ^ 40 * 3534895 * 2
def baseEnd_3534895 : Nat := 1210066798783368293837213

theorem tailTrace_3534895 : CollatzResearch.WordTrace tailWord_3534895 prefixEnd_3534895 1210066798783368293837213 := by
  unfold tailWord_3534895
  simp only [CollatzResearch.WordTrace]
  refine ⟨128928212528686601847142139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85952141685791067898094759 128928212528686601847142139)
  ·
    refine ⟨193392318793029902770713209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128928212528686601847142139 193392318793029902770713209)
    ·
      refine ⟨145044239094772427078034907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193392318793029902770713209 145044239094772427078034907)
      ·
        refine ⟨217566358642158640617052361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145044239094772427078034907 217566358642158640617052361)
        ·
          refine ⟨163174768981618980462789271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217566358642158640617052361 163174768981618980462789271)
          ·
            refine ⟨244762153472428470694183907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163174768981618980462789271 244762153472428470694183907)
            ·
              refine ⟨367143230208642706041275861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244762153472428470694183907 367143230208642706041275861)
              ·
                refine ⟨8604919458015063422842403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 367143230208642706041275861 8604919458015063422842403)
                ·
                  refine ⟨12907379187022595134263605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604919458015063422842403 12907379187022595134263605)
                  ·
                    refine ⟨1210066798783368293837213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12907379187022595134263605 1210066798783368293837213)
                    ·
                      rfl

theorem cell22_3534895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_3534895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534895 prefixEnd_3534895 := by exact prefixLift 3534895
  have htrace : WordTrace (prefixWord ++ tailWord_3534895) baseStart_3534895 baseEnd_3534895 := by
    simpa [prefixWord, tailWord_3534895, baseEnd_3534895] using wordTrace_append hprefix tailTrace_3534895
  have hstable : (prefixWord ++ tailWord_3534895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534895).length < 2 ^ (prefixWord ++ tailWord_3534895).sum := by decide
  have hdescent : baseEnd_3534895 < baseStart_3534895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534912 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 4, 3]
def baseStart_3534912 : Nat := 118140960795 + 3534912 * 2 ^ 59
def prefixEnd_3534912 : Nat := 4983230072969 + 3 ^ 40 * 3534912 * 2
def baseEnd_3534912 : Nat := 1210072618230785916162161

theorem tailTrace_3534912 : CollatzResearch.WordTrace tailWord_3534912 prefixEnd_3534912 1210072618230785916162161 := by
  unfold tailWord_3534912
  simp only [CollatzResearch.WordTrace]
  refine ⟨64464416284812506875255495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85952555046416675833673993 64464416284812506875255495)
  ·
    refine ⟨96696624427218760312883243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64464416284812506875255495 96696624427218760312883243)
    ·
      refine ⟨145044936640828140469324865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96696624427218760312883243 145044936640828140469324865)
      ·
        refine ⟨108783702480621105351993649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145044936640828140469324865 108783702480621105351993649)
        ·
          refine ⟨81587776860465829013995237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108783702480621105351993649 81587776860465829013995237)
          ·
            refine ⟨15297708161337342940124107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81587776860465829013995237 15297708161337342940124107)
            ·
              refine ⟨22946562242006014410186161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15297708161337342940124107 22946562242006014410186161)
              ·
                refine ⟨17209921681504510807639621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22946562242006014410186161 17209921681504510807639621)
                ·
                  refine ⟨3226860315282095776432429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17209921681504510807639621 3226860315282095776432429)
                  ·
                    refine ⟨1210072618230785916162161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3226860315282095776432429 1210072618230785916162161)
                    ·
                      rfl

theorem cell22_3534912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_3534912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3534912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3534912 prefixEnd_3534912 := by exact prefixLift 3534912
  have htrace : WordTrace (prefixWord ++ tailWord_3534912) baseStart_3534912 baseEnd_3534912 := by
    simpa [prefixWord, tailWord_3534912, baseEnd_3534912] using wordTrace_append hprefix tailTrace_3534912
  have hstable : (prefixWord ++ tailWord_3534912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534912).length < 2 ^ (prefixWord ++ tailWord_3534912).sum := by decide
  have hdescent : baseEnd_3534912 < baseStart_3534912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535038 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_3535038 : Nat := 118140960795 + 3535038 * 2 ^ 59
def prefixEnd_3535038 : Nat := 4983230072969 + 3 ^ 40 * 3535038 * 2
def baseEnd_3535038 : Nat := 403371916868587862503925

theorem tailTrace_3535038 : CollatzResearch.WordTrace tailWord_3535038 prefixEnd_3535038 403371916868587862503925 := by
  unfold tailWord_3535038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16116678520896067158699721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85955618778112358179731845 16116678520896067158699721)
  ·
    refine ⟨12087508890672050369024791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16116678520896067158699721 12087508890672050369024791)
    ·
      refine ⟨18131263336008075553537187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12087508890672050369024791 18131263336008075553537187)
      ·
        refine ⟨27196895004012113330305781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18131263336008075553537187 27196895004012113330305781)
        ·
          refine ⟨2549708906626135624716167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27196895004012113330305781 2549708906626135624716167)
          ·
            refine ⟨3824563359939203437074251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549708906626135624716167 3824563359939203437074251)
            ·
              refine ⟨5736845039908805155611377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824563359939203437074251 5736845039908805155611377)
              ·
                refine ⟨4302633779931603866708533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736845039908805155611377 4302633779931603866708533)
                ·
                  refine ⟨403371916868587862503925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302633779931603866708533 403371916868587862503925)
                  ·
                    rfl

theorem cell22_3535038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_3535038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535038 prefixEnd_3535038 := by exact prefixLift 3535038
  have htrace : WordTrace (prefixWord ++ tailWord_3535038) baseStart_3535038 baseEnd_3535038 := by
    simpa [prefixWord, tailWord_3535038, baseEnd_3535038] using wordTrace_append hprefix tailTrace_3535038
  have hstable : (prefixWord ++ tailWord_3535038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535038).length < 2 ^ (prefixWord ++ tailWord_3535038).sum := by decide
  have hdescent : baseEnd_3535038 < baseStart_3535038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535064 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_3535064 : Nat := 118140960795 + 3535064 * 2 ^ 59
def prefixEnd_3535064 : Nat := 4983230072969 + 3 ^ 40 * 3535064 * 2
def baseEnd_3535064 : Nat := 1210124650937108186361695

theorem tailTrace_3535064 : CollatzResearch.WordTrace tailWord_3535064 prefixEnd_3535064 1210124650937108186361695 := by
  unfold tailWord_3535064
  simp only [CollatzResearch.WordTrace]
  refine ⟨64467188232537171855022123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85956250976716229140029497 64467188232537171855022123)
  ·
    refine ⟨96700782348805757782533185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64467188232537171855022123 96700782348805757782533185)
    ·
      refine ⟨72525586761604318336899889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96700782348805757782533185 72525586761604318336899889)
      ·
        refine ⟨54394190071203238752674917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72525586761604318336899889 54394190071203238752674917)
        ·
          refine ⟨10198910638350607266126547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54394190071203238752674917 10198910638350607266126547)
          ·
            refine ⟨15298365957525910899189821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10198910638350607266126547 15298365957525910899189821)
            ·
              refine ⟨5736887234072216587196183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15298365957525910899189821 5736887234072216587196183)
              ·
                refine ⟨8605330851108324880794275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736887234072216587196183 8605330851108324880794275)
                ·
                  refine ⟨12907996276662487321191413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605330851108324880794275 12907996276662487321191413)
                  ·
                    refine ⟨1210124650937108186361695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12907996276662487321191413 1210124650937108186361695)
                    ·
                      rfl

theorem cell22_3535064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_3535064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535064 prefixEnd_3535064 := by exact prefixLift 3535064
  have htrace : WordTrace (prefixWord ++ tailWord_3535064) baseStart_3535064 baseEnd_3535064 := by
    simpa [prefixWord, tailWord_3535064, baseEnd_3535064] using wordTrace_append hprefix tailTrace_3535064
  have hstable : (prefixWord ++ tailWord_3535064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535064).length < 2 ^ (prefixWord ++ tailWord_3535064).sum := by decide
  have hdescent : baseEnd_3535064 < baseStart_3535064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535079 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3535079 : Nat := 118140960795 + 3535079 * 2 ^ 59
def prefixEnd_3535079 : Nat := 4983230072969 + 3 ^ 40 * 3535079 * 2
def baseEnd_3535079 : Nat := 1210129785743653147236649

theorem tailTrace_3535079 : CollatzResearch.WordTrace tailWord_3535079 prefixEnd_3535079 1210129785743653147236649 := by
  unfold tailWord_3535079
  simp only [CollatzResearch.WordTrace]
  refine ⟨128934923560020001271840291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85956615706680000847893527 128934923560020001271840291)
  ·
    refine ⟨193402385340030001907760437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128934923560020001271840291 193402385340030001907760437)
    ·
      refine ⟨18131473625627812678852541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193402385340030001907760437 18131473625627812678852541)
      ·
        refine ⟨6799302609610429754569703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18131473625627812678852541 6799302609610429754569703)
        ·
          refine ⟨10198953914415644631854555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799302609610429754569703 10198953914415644631854555)
          ·
            refine ⟨15298430871623466947781833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10198953914415644631854555 15298430871623466947781833)
            ·
              refine ⟨11473823153717600210836375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15298430871623466947781833 11473823153717600210836375)
              ·
                refine ⟨17210734730576400316254563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11473823153717600210836375 17210734730576400316254563)
                ·
                  refine ⟨25816102095864600474381845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17210734730576400316254563 25816102095864600474381845)
                  ·
                    refine ⟨1210129785743653147236649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25816102095864600474381845 1210129785743653147236649)
                    ·
                      rfl

theorem cell22_3535079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3535079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535079 prefixEnd_3535079 := by exact prefixLift 3535079
  have htrace : WordTrace (prefixWord ++ tailWord_3535079) baseStart_3535079 baseEnd_3535079 := by
    simpa [prefixWord, tailWord_3535079, baseEnd_3535079] using wordTrace_append hprefix tailTrace_3535079
  have hstable : (prefixWord ++ tailWord_3535079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535079).length < 2 ^ (prefixWord ++ tailWord_3535079).sum := by decide
  have hdescent : baseEnd_3535079 < baseStart_3535079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535107 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 2, 6]
def baseStart_3535107 : Nat := 118140960795 + 3535107 * 2 ^ 59
def prefixEnd_3535107 : Nat := 4983230072969 + 3 ^ 40 * 3535107 * 2
def baseEnd_3535107 : Nat := 1210139370715870407536563

theorem tailTrace_3535107 : CollatzResearch.WordTrace tailWord_3535107 prefixEnd_3535107 1210139370715870407536563 := by
  unfold tailWord_3535107
  simp only [CollatzResearch.WordTrace]
  refine ⟨128935944803918562053859575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85957296535945708035906383 128935944803918562053859575)
  ·
    refine ⟨193403917205877843080789363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128935944803918562053859575 193403917205877843080789363)
    ·
      refine ⟨290105875808816764621184045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193403917205877843080789363 290105875808816764621184045)
      ·
        refine ⟨108789703428306286732944017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290105875808816764621184045 108789703428306286732944017)
        ·
          refine ⟨81592277571229715049708013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108789703428306286732944017 81592277571229715049708013)
          ·
            refine ⟨30597104089211143143640505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81592277571229715049708013 30597104089211143143640505)
            ·
              refine ⟨22947828066908357357730379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30597104089211143143640505 22947828066908357357730379)
              ·
                refine ⟨34421742100362536036595569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22947828066908357357730379 34421742100362536036595569)
                ·
                  refine ⟨25816306575271902027446677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34421742100362536036595569 25816306575271902027446677)
                  ·
                    refine ⟨1210139370715870407536563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25816306575271902027446677 1210139370715870407536563)
                    ·
                      rfl

theorem cell22_3535107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_3535107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535107 prefixEnd_3535107 := by exact prefixLift 3535107
  have htrace : WordTrace (prefixWord ++ tailWord_3535107) baseStart_3535107 baseEnd_3535107 := by
    simpa [prefixWord, tailWord_3535107, baseEnd_3535107] using wordTrace_append hprefix tailTrace_3535107
  have hstable : (prefixWord ++ tailWord_3535107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535107).length < 2 ^ (prefixWord ++ tailWord_3535107).sum := by decide
  have hdescent : baseEnd_3535107 < baseStart_3535107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535109 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_3535109 : Nat := 118140960795 + 3535109 * 2 ^ 59
def prefixEnd_3535109 : Nat := 4983230072969 + 3 ^ 40 * 3535109 * 2
def baseEnd_3535109 : Nat := 1210140055356743068986557

theorem tailTrace_3535109 : CollatzResearch.WordTrace tailWord_3535109 prefixEnd_3535109 1210140055356743068986557 := by
  unfold tailWord_3535109
  simp only [CollatzResearch.WordTrace]
  refine ⟨128936017749911316395432381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85957345166607544263621587 128936017749911316395432381)
  ·
    refine ⟨48351006656216743648287143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128936017749911316395432381 48351006656216743648287143)
    ·
      refine ⟨72526509984325115472430715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48351006656216743648287143 72526509984325115472430715)
      ·
        refine ⟨108789764976487673208646073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72526509984325115472430715 108789764976487673208646073)
        ·
          refine ⟨81592323732365754906484555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108789764976487673208646073 81592323732365754906484555)
          ·
            refine ⟨122388485598548632359726833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81592323732365754906484555 122388485598548632359726833)
            ·
              refine ⟨91791364198911474269795125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122388485598548632359726833 91791364198911474269795125)
              ·
                refine ⟨8605440393647950712793293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91791364198911474269795125 8605440393647950712793293)
                ·
                  refine ⟨3227040147617981517297485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8605440393647950712793293 3227040147617981517297485)
                  ·
                    refine ⟨1210140055356743068986557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227040147617981517297485 1210140055356743068986557)
                    ·
                      rfl

theorem cell22_3535109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_3535109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535109 prefixEnd_3535109 := by exact prefixLift 3535109
  have htrace : WordTrace (prefixWord ++ tailWord_3535109) baseStart_3535109 baseEnd_3535109 := by
    simpa [prefixWord, tailWord_3535109, baseEnd_3535109] using wordTrace_append hprefix tailTrace_3535109
  have hstable : (prefixWord ++ tailWord_3535109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535109).length < 2 ^ (prefixWord ++ tailWord_3535109).sum := by decide
  have hdescent : baseEnd_3535109 < baseStart_3535109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535111 : List Nat := [1, 1, 4, 5, 1, 1, 2, 7]
def baseStart_3535111 : Nat := 118140960795 + 3535111 * 2 ^ 59
def prefixEnd_3535111 : Nat := 4983230072969 + 3 ^ 40 * 3535111 * 2
def baseEnd_3535111 : Nat := 134460082221957303381839

theorem tailTrace_3535111 : CollatzResearch.WordTrace tailWord_3535111 prefixEnd_3535111 134460082221957303381839 := by
  unfold tailWord_3535111
  simp only [CollatzResearch.WordTrace]
  refine ⟨128936090695904070737005187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85957393797269380491336791 128936090695904070737005187)
  ·
    refine ⟨193404136043856106105507781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128936090695904070737005187 193404136043856106105507781)
    ·
      refine ⟨36263275508223019894782709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193404136043856106105507781 36263275508223019894782709)
      ·
        refine ⟨3399682078895908115135879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36263275508223019894782709 3399682078895908115135879)
        ·
          refine ⟨5099523118343862172703819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399682078895908115135879 5099523118343862172703819)
          ·
            refine ⟨7649284677515793259055729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099523118343862172703819 7649284677515793259055729)
            ·
              refine ⟨5736963508136844944291797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649284677515793259055729 5736963508136844944291797)
              ·
                refine ⟨134460082221957303381839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5736963508136844944291797 134460082221957303381839)
                ·
                  rfl

theorem cell22_3535111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 7].length) (baseStart_3535111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535111 prefixEnd_3535111 := by exact prefixLift 3535111
  have htrace : WordTrace (prefixWord ++ tailWord_3535111) baseStart_3535111 baseEnd_3535111 := by
    simpa [prefixWord, tailWord_3535111, baseEnd_3535111] using wordTrace_append hprefix tailTrace_3535111
  have hstable : (prefixWord ++ tailWord_3535111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535111).length < 2 ^ (prefixWord ++ tailWord_3535111).sum := by decide
  have hdescent : baseEnd_3535111 < baseStart_3535111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535156 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3535156 : Nat := 118140960795 + 3535156 * 2 ^ 59
def prefixEnd_3535156 : Nat := 4983230072969 + 3 ^ 40 * 3535156 * 2
def baseEnd_3535156 : Nat := 403385381472416871020471

theorem tailTrace_3535156 : CollatzResearch.WordTrace tailWord_3535156 prefixEnd_3535156 403385381472416871020471 := by
  unfold tailWord_3535156
  simp only [CollatzResearch.WordTrace]
  refine ⟨64468865990370521711196661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85958487987160695614928881 64468865990370521711196661)
  ·
    refine ⟨6043956186597236410424687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64468865990370521711196661 6043956186597236410424687)
    ·
      refine ⟨9065934279895854615637031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043956186597236410424687 9065934279895854615637031)
      ·
        refine ⟨13598901419843781923455547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065934279895854615637031 13598901419843781923455547)
        ·
          refine ⟨20398352129765672885183321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13598901419843781923455547 20398352129765672885183321)
          ·
            refine ⟨15298764097324254663887491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20398352129765672885183321 15298764097324254663887491)
            ·
              refine ⟨22948146145986381995831237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15298764097324254663887491 22948146145986381995831237)
              ·
                refine ⟨4302777402372446624218357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22948146145986381995831237 4302777402372446624218357)
                ·
                  refine ⟨403385381472416871020471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4302777402372446624218357 403385381472416871020471)
                  ·
                    rfl

theorem cell22_3535156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3535156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535156 prefixEnd_3535156 := by exact prefixLift 3535156
  have htrace : WordTrace (prefixWord ++ tailWord_3535156) baseStart_3535156 baseEnd_3535156 := by
    simpa [prefixWord, tailWord_3535156, baseEnd_3535156] using wordTrace_append hprefix tailTrace_3535156
  have hstable : (prefixWord ++ tailWord_3535156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535156).length < 2 ^ (prefixWord ++ tailWord_3535156).sum := by decide
  have hdescent : baseEnd_3535156 < baseStart_3535156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535184 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 6]
def baseStart_3535184 : Nat := 118140960795 + 3535184 * 2 ^ 59
def prefixEnd_3535184 : Nat := 4983230072969 + 3 ^ 40 * 3535184 * 2
def baseEnd_3535184 : Nat := 403388576463155957787109

theorem tailTrace_3535184 : CollatzResearch.WordTrace tailWord_3535184 prefixEnd_3535184 403388576463155957787109 := by
  unfold tailWord_3535184
  simp only [CollatzResearch.WordTrace]
  refine ⟨64469376612319802102206303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85959168816426402802941737 64469376612319802102206303)
  ·
    refine ⟨96704064918479703153309455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64469376612319802102206303 96704064918479703153309455)
    ·
      refine ⟨145056097377719554729964183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96704064918479703153309455 145056097377719554729964183)
      ·
        refine ⟨217584146066579332094946275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145056097377719554729964183 217584146066579332094946275)
        ·
          refine ⟨326376219099868998142419413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217584146066579332094946275 326376219099868998142419413)
          ·
            refine ⟨7649442635153179643962955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 326376219099868998142419413 7649442635153179643962955)
            ·
              refine ⟨11474163952729769465944433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649442635153179643962955 11474163952729769465944433)
              ·
                refine ⟨8605622964547327099458325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474163952729769465944433 8605622964547327099458325)
                ·
                  refine ⟨403388576463155957787109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8605622964547327099458325 403388576463155957787109)
                  ·
                    rfl

theorem cell22_3535184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_3535184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535184 prefixEnd_3535184 := by exact prefixLift 3535184
  have htrace : WordTrace (prefixWord ++ tailWord_3535184) baseStart_3535184 baseEnd_3535184 := by
    simpa [prefixWord, tailWord_3535184, baseEnd_3535184] using wordTrace_append hprefix tailTrace_3535184
  have hstable : (prefixWord ++ tailWord_3535184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535184).length < 2 ^ (prefixWord ++ tailWord_3535184).sum := by decide
  have hdescent : baseEnd_3535184 < baseStart_3535184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535199 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 1, 5]
def baseStart_3535199 : Nat := 118140960795 + 3535199 * 2 ^ 59
def prefixEnd_3535199 : Nat := 4983230072969 + 3 ^ 40 * 3535199 * 2
def baseEnd_3535199 : Nat := 1210170864196012834236281

theorem tailTrace_3535199 : CollatzResearch.WordTrace tailWord_3535199 prefixEnd_3535199 1210170864196012834236281 := by
  unfold tailWord_3535199
  simp only [CollatzResearch.WordTrace]
  refine ⟨128939300319585261766208651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85959533546390174510805767 128939300319585261766208651)
  ·
    refine ⟨193408950479377892649312977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128939300319585261766208651 193408950479377892649312977)
    ·
      refine ⟨145056712859533419486984733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193408950479377892649312977 145056712859533419486984733)
      ·
        refine ⟨54396267322325032307619275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145056712859533419486984733 54396267322325032307619275)
        ·
          refine ⟨81594400983487548461428913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54396267322325032307619275 81594400983487548461428913)
          ·
            refine ⟨61195800737615661346071685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81594400983487548461428913 61195800737615661346071685)
            ·
              refine ⟨11474212638302936502388441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61195800737615661346071685 11474212638302936502388441)
              ·
                refine ⟨8605659478727202376791331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11474212638302936502388441 8605659478727202376791331)
                ·
                  refine ⟨12908489218090803565186997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605659478727202376791331 12908489218090803565186997)
                  ·
                    refine ⟨1210170864196012834236281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12908489218090803565186997 1210170864196012834236281)
                    ·
                      rfl

theorem cell22_3535199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_3535199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535199 prefixEnd_3535199 := by exact prefixLift 3535199
  have htrace : WordTrace (prefixWord ++ tailWord_3535199) baseStart_3535199 baseEnd_3535199 := by
    simpa [prefixWord, tailWord_3535199, baseEnd_3535199] using wordTrace_append hprefix tailTrace_3535199
  have hstable : (prefixWord ++ tailWord_3535199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535199).length < 2 ^ (prefixWord ++ tailWord_3535199).sum := by decide
  have hdescent : baseEnd_3535199 < baseStart_3535199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535216 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 4, 3]
def baseStart_3535216 : Nat := 118140960795 + 3535216 * 2 ^ 59
def prefixEnd_3535216 : Nat := 4983230072969 + 3 ^ 40 * 3535216 * 2
def baseEnd_3535216 : Nat := 1210176683643430456561229

theorem tailTrace_3535216 : CollatzResearch.WordTrace tailWord_3535216 prefixEnd_3535216 1210176683643430456561229 := by
  unfold tailWord_3535216
  simp only [CollatzResearch.WordTrace]
  refine ⟨64469960180261836834788751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85959946907015782446385001 64469960180261836834788751)
  ·
    refine ⟨96704940270392755252183127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64469960180261836834788751 96704940270392755252183127)
    ·
      refine ⟨145057410405589132878274691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96704940270392755252183127 145057410405589132878274691)
      ·
        refine ⟨217586115608383699317412037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145057410405589132878274691 217586115608383699317412037)
        ·
          refine ⟨40797396676571943622014757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217586115608383699317412037 40797396676571943622014757)
          ·
            refine ⟨7649511876857239429127767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40797396676571943622014757 7649511876857239429127767)
            ·
              refine ⟨11474267815285859143691651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649511876857239429127767 11474267815285859143691651)
              ·
                refine ⟨17211401722928788715537477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11474267815285859143691651 17211401722928788715537477)
                ·
                  refine ⟨3227137823049147884163277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17211401722928788715537477 3227137823049147884163277)
                  ·
                    refine ⟨1210176683643430456561229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227137823049147884163277 1210176683643430456561229)
                    ·
                      rfl

theorem cell22_3535216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_3535216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535216 prefixEnd_3535216 := by exact prefixLift 3535216
  have htrace : WordTrace (prefixWord ++ tailWord_3535216) baseStart_3535216 baseEnd_3535216 := by
    simpa [prefixWord, tailWord_3535216, baseEnd_3535216] using wordTrace_append hprefix tailTrace_3535216
  have hstable : (prefixWord ++ tailWord_3535216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535216).length < 2 ^ (prefixWord ++ tailWord_3535216).sum := by decide
  have hdescent : baseEnd_3535216 < baseStart_3535216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535233 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 1, 5]
def baseStart_3535233 : Nat := 118140960795 + 3535233 * 2 ^ 59
def prefixEnd_3535233 : Nat := 4983230072969 + 3 ^ 40 * 3535233 * 2
def baseEnd_3535233 : Nat := 1210182503090848078886177

theorem tailTrace_3535233 : CollatzResearch.WordTrace tailWord_3535233 prefixEnd_3535233 1210182503090848078886177 := by
  unfold tailWord_3535233
  simp only [CollatzResearch.WordTrace]
  refine ⟨128940540401462085572946353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85960360267641390381964235 128940540401462085572946353)
  ·
    refine ⟨96705405301096564179709765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128940540401462085572946353 96705405301096564179709765)
    ·
      refine ⟨18132263493955605783695581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96705405301096564179709765 18132263493955605783695581)
      ·
        refine ⟨6799598810233352168885843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18132263493955605783695581 6799598810233352168885843)
        ·
          refine ⟨10199398215350028253328765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799598810233352168885843 10199398215350028253328765)
          ·
            refine ⟨3824774330756260594998287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10199398215350028253328765 3824774330756260594998287)
            ·
              refine ⟨5737161496134390892497431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824774330756260594998287 5737161496134390892497431)
              ·
                refine ⟨8605742244201586338746147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5737161496134390892497431 8605742244201586338746147)
                ·
                  refine ⟨12908613366302379508119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8605742244201586338746147 12908613366302379508119221)
                  ·
                    refine ⟨1210182503090848078886177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12908613366302379508119221 1210182503090848078886177)
                    ·
                      rfl

theorem cell22_3535233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_3535233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535233 prefixEnd_3535233 := by exact prefixLift 3535233
  have htrace : WordTrace (prefixWord ++ tailWord_3535233) baseStart_3535233 baseEnd_3535233 := by
    simpa [prefixWord, tailWord_3535233, baseEnd_3535233] using wordTrace_append hprefix tailTrace_3535233
  have hstable : (prefixWord ++ tailWord_3535233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535233).length < 2 ^ (prefixWord ++ tailWord_3535233).sum := by decide
  have hdescent : baseEnd_3535233 < baseStart_3535233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535246 : List Nat := [4, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3535246 : Nat := 118140960795 + 3535246 * 2 ^ 59
def prefixEnd_3535246 : Nat := 4983230072969 + 3 ^ 40 * 3535246 * 2
def baseEnd_3535246 : Nat := 134465217028502264256793

theorem tailTrace_3535246 : CollatzResearch.WordTrace tailWord_3535246 prefixEnd_3535246 134465217028502264256793 := by
  unfold tailWord_3535246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16117626818801873599146199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85960676366943325862113061 16117626818801873599146199)
  ·
    refine ⟨24176440228202810398719299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16117626818801873599146199 24176440228202810398719299)
    ·
      refine ⟨36264660342304215598078949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24176440228202810398719299 36264660342304215598078949)
      ·
        refine ⟨6799623814182040424639803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36264660342304215598078949 6799623814182040424639803)
        ·
          refine ⟨10199435721273060636959705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799623814182040424639803 10199435721273060636959705)
          ·
            refine ⟨7649576790954795477719779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10199435721273060636959705 7649576790954795477719779)
            ·
              refine ⟨11474365186432193216579669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649576790954795477719779 11474365186432193216579669)
              ·
                refine ⟨134465217028502264256793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11474365186432193216579669 134465217028502264256793)
                ·
                  rfl

theorem cell22_3535246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3535246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535246 prefixEnd_3535246 := by exact prefixLift 3535246
  have htrace : WordTrace (prefixWord ++ tailWord_3535246) baseStart_3535246 baseEnd_3535246 := by
    simpa [prefixWord, tailWord_3535246, baseEnd_3535246] using wordTrace_append hprefix tailTrace_3535246
  have hstable : (prefixWord ++ tailWord_3535246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535246).length < 2 ^ (prefixWord ++ tailWord_3535246).sum := by decide
  have hdescent : baseEnd_3535246 < baseStart_3535246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535252 : List Nat := [2, 4, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3535252 : Nat := 118140960795 + 3535252 * 2 ^ 59
def prefixEnd_3535252 : Nat := 4983230072969 + 3 ^ 40 * 3535252 * 2
def baseEnd_3535252 : Nat := 403396335726379454220373

theorem tailTrace_3535252 : CollatzResearch.WordTrace tailWord_3535252 prefixEnd_3535252 403396335726379454220373 := by
  unfold tailWord_3535252
  simp only [CollatzResearch.WordTrace]
  refine ⟨64470616694196625908944005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85960822258928834545258673 64470616694196625908944005)
  ·
    refine ⟨12088240630161867357927001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64470616694196625908944005 12088240630161867357927001)
    ·
      refine ⟨9066180472621400518445251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12088240630161867357927001 9066180472621400518445251)
      ·
        refine ⟨13599270708932100777667877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9066180472621400518445251 13599270708932100777667877)
        ·
          refine ⟨2549863257924768895812727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13599270708932100777667877 2549863257924768895812727)
          ·
            refine ⟨3824794886887153343719091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549863257924768895812727 3824794886887153343719091)
            ·
              refine ⟨5737192330330730015578637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824794886887153343719091 5737192330330730015578637)
              ·
                refine ⟨2151447123874023755841989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5737192330330730015578637 2151447123874023755841989)
                ·
                  refine ⟨403396335726379454220373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151447123874023755841989 403396335726379454220373)
                  ·
                    rfl

theorem cell22_3535252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3535252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535252 prefixEnd_3535252 := by exact prefixLift 3535252
  have htrace : WordTrace (prefixWord ++ tailWord_3535252) baseStart_3535252 baseEnd_3535252 := by
    simpa [prefixWord, tailWord_3535252, baseEnd_3535252] using wordTrace_append hprefix tailTrace_3535252
  have hstable : (prefixWord ++ tailWord_3535252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535252).length < 2 ^ (prefixWord ++ tailWord_3535252).sum := by decide
  have hdescent : baseEnd_3535252 < baseStart_3535252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535402 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3535402 : Nat := 118140960795 + 3535402 * 2 ^ 59
def prefixEnd_3535402 : Nat := 4983230072969 + 3 ^ 40 * 3535402 * 2
def baseEnd_3535402 : Nat := 1210240355244587971410659

theorem tailTrace_3535402 : CollatzResearch.WordTrace tailWord_3535402 prefixEnd_3535402 1210240355244587971410659 := by
  unfold tailWord_3535402
  simp only [CollatzResearch.WordTrace]
  refine ⟨32236676084462456858962115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85964469558566551623898973 32236676084462456858962115)
  ·
    refine ⟨48355014126693685288443173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32236676084462456858962115 48355014126693685288443173)
    ·
      refine ⟨9066565148755065991583095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48355014126693685288443173 9066565148755065991583095)
      ·
        refine ⟨13599847723132598987374643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9066565148755065991583095 13599847723132598987374643)
        ·
          refine ⟨20399771584698898481061965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13599847723132598987374643 20399771584698898481061965)
          ·
            refine ⟨7649914344262086930398237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20399771584698898481061965 7649914344262086930398237)
            ·
              refine ⟨2868717879098282598899339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7649914344262086930398237 2868717879098282598899339)
              ·
                refine ⟨4303076818647423898349009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868717879098282598899339 4303076818647423898349009)
                ·
                  refine ⟨3227307613985567923761757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303076818647423898349009 3227307613985567923761757)
                  ·
                    refine ⟨1210240355244587971410659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227307613985567923761757 1210240355244587971410659)
                    ·
                      rfl

theorem cell22_3535402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3535402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535402 prefixEnd_3535402 := by exact prefixLift 3535402
  have htrace : WordTrace (prefixWord ++ tailWord_3535402) baseStart_3535402 baseEnd_3535402 := by
    simpa [prefixWord, tailWord_3535402, baseEnd_3535402] using wordTrace_append hprefix tailTrace_3535402
  have hstable : (prefixWord ++ tailWord_3535402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535402).length < 2 ^ (prefixWord ++ tailWord_3535402).sum := by decide
  have hdescent : baseEnd_3535402 < baseStart_3535402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535413 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3535413 : Nat := 118140960795 + 3535413 * 2 ^ 59
def prefixEnd_3535413 : Nat := 4983230072969 + 3 ^ 40 * 3535413 * 2
def baseEnd_3535413 : Nat := 1210244120769387609385625

theorem tailTrace_3535413 : CollatzResearch.WordTrace tailWord_3535413 prefixEnd_3535413 1210244120769387609385625 := by
  unfold tailWord_3535413
  simp only [CollatzResearch.WordTrace]
  refine ⟨128947105540809976314498893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85964737027206650876332595 128947105540809976314498893)
  ·
    refine ⟨48355164577803741117937085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128947105540809976314498893 48355164577803741117937085)
    ·
      refine ⟨18133186716676402919226407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48355164577803741117937085 18133186716676402919226407)
      ·
        refine ⟨27199780075014604378839611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133186716676402919226407 27199780075014604378839611)
        ·
          refine ⟨40799670112521906568259417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27199780075014604378839611 40799670112521906568259417)
          ·
            refine ⟨30599752584391429926194563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40799670112521906568259417 30599752584391429926194563)
            ·
              refine ⟨45899628876587144889291845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30599752584391429926194563 45899628876587144889291845)
              ·
                refine ⟨8606180414360089666742221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45899628876587144889291845 8606180414360089666742221)
                ·
                  refine ⟨3227317655385033625028333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8606180414360089666742221 3227317655385033625028333)
                  ·
                    refine ⟨1210244120769387609385625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227317655385033625028333 1210244120769387609385625)
                    ·
                      rfl

theorem cell22_3535413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3535413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535413 prefixEnd_3535413 := by exact prefixLift 3535413
  have htrace : WordTrace (prefixWord ++ tailWord_3535413) baseStart_3535413 baseEnd_3535413 := by
    simpa [prefixWord, tailWord_3535413, baseEnd_3535413] using wordTrace_append hprefix tailTrace_3535413
  have hstable : (prefixWord ++ tailWord_3535413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535413).length < 2 ^ (prefixWord ++ tailWord_3535413).sum := by decide
  have hdescent : baseEnd_3535413 < baseStart_3535413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535447 : List Nat := [1, 1, 3, 2, 2, 2, 5, 2, 1, 3]
def baseStart_3535447 : Nat := 118140960795 + 3535447 * 2 ^ 59
def prefixEnd_3535447 : Nat := 4983230072969 + 3 ^ 40 * 3535447 * 2
def baseEnd_3535447 : Nat := 1210255759664222854035521

theorem tailTrace_3535447 : CollatzResearch.WordTrace tailWord_3535447 prefixEnd_3535447 1210255759664222854035521 := by
  unfold tailWord_3535447
  simp only [CollatzResearch.WordTrace]
  refine ⟨128948345622686800121236595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85965563748457866747491063 128948345622686800121236595)
  ·
    refine ⟨193422518434030200181854893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128948345622686800121236595 193422518434030200181854893)
    ·
      refine ⟨72533444412761325068195585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193422518434030200181854893 72533444412761325068195585)
      ·
        refine ⟨54400083309570993801146689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72533444412761325068195585 54400083309570993801146689)
        ·
          refine ⟨40800062482178245350860017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54400083309570993801146689 40800062482178245350860017)
          ·
            refine ⟨30600046861633684013145013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40800062482178245350860017 30600046861633684013145013)
            ·
              refine ⟨2868754393278157876232345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30600046861633684013145013 2868754393278157876232345)
              ·
                refine ⟨2151565794958618407174259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2868754393278157876232345 2151565794958618407174259)
                ·
                  refine ⟨3227348692437927610761389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151565794958618407174259 3227348692437927610761389)
                  ·
                    refine ⟨1210255759664222854035521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227348692437927610761389 1210255759664222854035521)
                    ·
                      rfl

theorem cell22_3535447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_3535447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535447 prefixEnd_3535447 := by exact prefixLift 3535447
  have htrace : WordTrace (prefixWord ++ tailWord_3535447) baseStart_3535447 baseEnd_3535447 := by
    simpa [prefixWord, tailWord_3535447, baseEnd_3535447] using wordTrace_append hprefix tailTrace_3535447
  have hstable : (prefixWord ++ tailWord_3535447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535447).length < 2 ^ (prefixWord ++ tailWord_3535447).sum := by decide
  have hdescent : baseEnd_3535447 < baseStart_3535447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535471 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 6]
def baseStart_3535471 : Nat := 118140960795 + 3535471 * 2 ^ 59
def prefixEnd_3535471 : Nat := 4983230072969 + 3 ^ 40 * 3535471 * 2
def baseEnd_3535471 : Nat := 403421325118231597145149

theorem tailTrace_3535471 : CollatzResearch.WordTrace tailWord_3535471 prefixEnd_3535471 403421325118231597145149 := by
  unfold tailWord_3535471
  simp only [CollatzResearch.WordTrace]
  refine ⟨128949220974599852220110267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85966147316399901480073511 128949220974599852220110267)
  ·
    refine ⟨193423831461899778330165401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128949220974599852220110267 193423831461899778330165401)
    ·
      refine ⟨145067873596424833747624051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193423831461899778330165401 145067873596424833747624051)
      ·
        refine ⟨217601810394637250621436077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145067873596424833747624051 217601810394637250621436077)
        ·
          refine ⟨81600678897988968983038529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217601810394637250621436077 81600678897988968983038529)
          ·
            refine ⟨61200509173491726737278897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81600678897988968983038529 61200509173491726737278897)
            ·
              refine ⟨45900381880118795052959173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61200509173491726737278897 45900381880118795052959173)
              ·
                refine ⟨8606321602522274072429845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45900381880118795052959173 8606321602522274072429845)
                ·
                  refine ⟨403421325118231597145149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8606321602522274072429845 403421325118231597145149)
                  ·
                    rfl

theorem cell22_3535471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 6].length) (baseStart_3535471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535471 prefixEnd_3535471 := by exact prefixLift 3535471
  have htrace : WordTrace (prefixWord ++ tailWord_3535471) baseStart_3535471 baseEnd_3535471 := by
    simpa [prefixWord, tailWord_3535471, baseEnd_3535471] using wordTrace_append hprefix tailTrace_3535471
  have hstable : (prefixWord ++ tailWord_3535471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535471).length < 2 ^ (prefixWord ++ tailWord_3535471).sum := by decide
  have hdescent : baseEnd_3535471 < baseStart_3535471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535520 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_3535520 : Nat := 118140960795 + 3535520 * 2 ^ 59
def prefixEnd_3535520 : Nat := 4983230072969 + 3 ^ 40 * 3535520 * 2
def baseEnd_3535520 : Nat := 1210280749056074996960297

theorem tailTrace_3535520 : CollatzResearch.WordTrace tailWord_3535520 prefixEnd_3535520 1210280749056074996960297 := by
  unfold tailWord_3535520
  simp only [CollatzResearch.WordTrace]
  refine ⟨64475504075711166794322007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85967338767614889059096009 64475504075711166794322007)
  ·
    refine ⟨96713256113566750191483011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64475504075711166794322007 96713256113566750191483011)
    ·
      refine ⟨145069884170350125287224517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96713256113566750191483011 145069884170350125287224517)
      ·
        refine ⟨27200603281940648491354597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145069884170350125287224517 27200603281940648491354597)
        ·
          refine ⟨5100113115363871592128987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27200603281940648491354597 5100113115363871592128987)
          ·
            refine ⟨7650169673045807388193481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100113115363871592128987 7650169673045807388193481)
            ·
              refine ⟨5737627254784355541145111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7650169673045807388193481 5737627254784355541145111)
              ·
                refine ⟨8606440882176533311717667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5737627254784355541145111 8606440882176533311717667)
                ·
                  refine ⟨12909661323264799967576501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8606440882176533311717667 12909661323264799967576501)
                  ·
                    refine ⟨1210280749056074996960297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12909661323264799967576501 1210280749056074996960297)
                    ·
                      rfl

theorem cell22_3535520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_3535520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535520 prefixEnd_3535520 := by exact prefixLift 3535520
  have htrace : WordTrace (prefixWord ++ tailWord_3535520) baseStart_3535520 baseEnd_3535520 := by
    simpa [prefixWord, tailWord_3535520, baseEnd_3535520] using wordTrace_append hprefix tailTrace_3535520
  have hstable : (prefixWord ++ tailWord_3535520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535520).length < 2 ^ (prefixWord ++ tailWord_3535520).sum := by decide
  have hdescent : baseEnd_3535520 < baseStart_3535520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535535 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 2, 4]
def baseStart_3535535 : Nat := 118140960795 + 3535535 * 2 ^ 59
def prefixEnd_3535535 : Nat := 4983230072969 + 3 ^ 40 * 3535535 * 2
def baseEnd_3535535 : Nat := 1210285883862619957835251

theorem tailTrace_3535535 : CollatzResearch.WordTrace tailWord_3535535 prefixEnd_3535535 1210285883862619957835251 := by
  unfold tailWord_3535535
  simp only [CollatzResearch.WordTrace]
  refine ⟨128951555246367991150440059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85967703497578660766960039 128951555246367991150440059)
  ·
    refine ⟨193427332869551986725660089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128951555246367991150440059 193427332869551986725660089)
    ·
      refine ⟨145070499652163990044245067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193427332869551986725660089 145070499652163990044245067)
      ·
        refine ⟨217605749478245985066367601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145070499652163990044245067 217605749478245985066367601)
        ·
          refine ⟨163204312108684488799775701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217605749478245985066367601 163204312108684488799775701)
          ·
            refine ⟨3825101065047292706244743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 163204312108684488799775701 3825101065047292706244743)
            ·
              refine ⟨5737651597570939059367115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825101065047292706244743 5737651597570939059367115)
              ·
                refine ⟨8606477396356408589050673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5737651597570939059367115 8606477396356408589050673)
                ·
                  refine ⟨6454858047267306441788005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8606477396356408589050673 6454858047267306441788005)
                  ·
                    refine ⟨1210285883862619957835251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6454858047267306441788005 1210285883862619957835251)
                    ·
                      rfl

theorem cell22_3535535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_3535535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535535 prefixEnd_3535535 := by exact prefixLift 3535535
  have htrace : WordTrace (prefixWord ++ tailWord_3535535) baseStart_3535535 baseEnd_3535535 := by
    simpa [prefixWord, tailWord_3535535, baseEnd_3535535] using wordTrace_append hprefix tailTrace_3535535
  have hstable : (prefixWord ++ tailWord_3535535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535535).length < 2 ^ (prefixWord ++ tailWord_3535535).sum := by decide
  have hdescent : baseEnd_3535535 < baseStart_3535535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535599 : List Nat := [1, 1, 2, 1, 5, 4, 1, 3, 1, 3]
def baseStart_3535599 : Nat := 118140960795 + 3535599 * 2 ^ 59
def prefixEnd_3535599 : Nat := 4983230072969 + 3 ^ 40 * 3535599 * 2
def baseEnd_3535599 : Nat := 1210307792370545124235055

theorem tailTrace_3535599 : CollatzResearch.WordTrace tailWord_3535599 prefixEnd_3535599 1210307792370545124235055 := by
  unfold tailWord_3535599
  simp only [CollatzResearch.WordTrace]
  refine ⟨128953889518136130080769851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85969259678757420053846567 128953889518136130080769851)
  ·
    refine ⟨193430834277204195121154777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128953889518136130080769851 193430834277204195121154777)
    ·
      refine ⟨145073125707903146340866083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193430834277204195121154777 145073125707903146340866083)
      ·
        refine ⟨217609688561854719511299125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145073125707903146340866083 217609688561854719511299125)
        ·
          refine ⟨20400908302673879954184293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217609688561854719511299125 20400908302673879954184293)
          ·
            refine ⟨3825170306751352491409555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20400908302673879954184293 3825170306751352491409555)
            ·
              refine ⟨5737755460127028737114333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825170306751352491409555 5737755460127028737114333)
              ·
                refine ⟨2151658297547635776417875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5737755460127028737114333 2151658297547635776417875)
                ·
                  refine ⟨3227487446321453664626813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151658297547635776417875 3227487446321453664626813)
                  ·
                    refine ⟨1210307792370545124235055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227487446321453664626813 1210307792370545124235055)
                    ·
                      rfl

theorem cell22_3535599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 1, 3].length) (baseStart_3535599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535599 prefixEnd_3535599 := by exact prefixLift 3535599
  have htrace : WordTrace (prefixWord ++ tailWord_3535599) baseStart_3535599 baseEnd_3535599 := by
    simpa [prefixWord, tailWord_3535599, baseEnd_3535599] using wordTrace_append hprefix tailTrace_3535599
  have hstable : (prefixWord ++ tailWord_3535599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535599).length < 2 ^ (prefixWord ++ tailWord_3535599).sum := by decide
  have hdescent : baseEnd_3535599 < baseStart_3535599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535672 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 2, 3]
def baseStart_3535672 : Nat := 118140960795 + 3535672 * 2 ^ 59
def prefixEnd_3535672 : Nat := 4983230072969 + 3 ^ 40 * 3535672 * 2
def baseEnd_3535672 : Nat := 1210332781762397267159831

theorem tailTrace_3535672 : CollatzResearch.WordTrace tailWord_3535672 prefixEnd_3535672 1210332781762397267159831 := by
  unfold tailWord_3535672
  simp only [CollatzResearch.WordTrace]
  refine ⟨64478276023435831774088635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85971034697914442365451513 64478276023435831774088635)
  ·
    refine ⟨96717414035153747661132953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64478276023435831774088635 96717414035153747661132953)
    ·
      refine ⟨72538060526365310745849715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96717414035153747661132953 72538060526365310745849715)
      ·
        refine ⟨108807090789547966118774573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72538060526365310745849715 108807090789547966118774573)
        ·
          refine ⟨40802659046080487294540465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108807090789547966118774573 40802659046080487294540465)
          ·
            refine ⟨30601994284560365470905349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40802659046080487294540465 30601994284560365470905349)
            ·
              refine ⟨5737873928355068525794753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30601994284560365470905349 5737873928355068525794753)
              ·
                refine ⟨4303405446266301394346065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5737873928355068525794753 4303405446266301394346065)
                ·
                  refine ⟨3227554084699726045759549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303405446266301394346065 3227554084699726045759549)
                  ·
                    refine ⟨1210332781762397267159831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227554084699726045759549 1210332781762397267159831)
                    ·
                      rfl

theorem cell22_3535672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_3535672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535672 prefixEnd_3535672 := by exact prefixLift 3535672
  have htrace : WordTrace (prefixWord ++ tailWord_3535672) baseStart_3535672 baseEnd_3535672 := by
    simpa [prefixWord, tailWord_3535672, baseEnd_3535672] using wordTrace_append hprefix tailTrace_3535672
  have hstable : (prefixWord ++ tailWord_3535672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535672).length < 2 ^ (prefixWord ++ tailWord_3535672).sum := by decide
  have hdescent : baseEnd_3535672 < baseStart_3535672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535734 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_3535734 : Nat := 118140960795 + 3535734 * 2 ^ 59
def prefixEnd_3535734 : Nat := 4983230072969 + 3 ^ 40 * 3535734 * 2
def baseEnd_3535734 : Nat := 1210354005629449772109641

theorem tailTrace_3535734 : CollatzResearch.WordTrace tailWord_3535734 prefixEnd_3535734 1210354005629449772109641 := by
  unfold tailWord_3535734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059925835790440508558391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85972542248431365424622837 8059925835790440508558391)
  ·
    refine ⟨12089888753685660762837587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8059925835790440508558391 12089888753685660762837587)
    ·
      refine ⟨18134833130528491144256381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12089888753685660762837587 18134833130528491144256381)
      ·
        refine ⟨6800562423948184179096143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18134833130528491144256381 6800562423948184179096143)
        ·
          refine ⟨10200843635922276268644215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800562423948184179096143 10200843635922276268644215)
          ·
            refine ⟨15301265453883414402966323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10200843635922276268644215 15301265453883414402966323)
            ·
              refine ⟨22951898180825121604449485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301265453883414402966323 22951898180825121604449485)
              ·
                refine ⟨8606961817809420601668557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22951898180825121604449485 8606961817809420601668557)
                ·
                  refine ⟨3227610681678532725625709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8606961817809420601668557 3227610681678532725625709)
                  ·
                    refine ⟨1210354005629449772109641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227610681678532725625709 1210354005629449772109641)
                    ·
                      rfl

theorem cell22_3535734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_3535734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535734 prefixEnd_3535734 := by exact prefixLift 3535734
  have htrace : WordTrace (prefixWord ++ tailWord_3535734) baseStart_3535734 baseEnd_3535734 := by
    simpa [prefixWord, tailWord_3535734, baseEnd_3535734] using wordTrace_append hprefix tailTrace_3535734
  have hstable : (prefixWord ++ tailWord_3535734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535734).length < 2 ^ (prefixWord ++ tailWord_3535734).sum := by decide
  have hdescent : baseEnd_3535734 < baseStart_3535734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535747 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 5]
def baseStart_3535747 : Nat := 118140960795 + 3535747 * 2 ^ 59
def prefixEnd_3535747 : Nat := 4983230072969 + 3 ^ 40 * 3535747 * 2
def baseEnd_3535747 : Nat := 403452818598374023844867

theorem tailTrace_3535747 : CollatzResearch.WordTrace tailWord_3535747 prefixEnd_3535747 403452818598374023844867 := by
  unfold tailWord_3535747
  simp only [CollatzResearch.WordTrace]
  refine ⟨128959287521599951357157495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85972858347733300904771663 128959287521599951357157495)
  ·
    refine ⟨193438931282399927035736243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128959287521599951357157495 193438931282399927035736243)
    ·
      refine ⟨290158396923599890553604365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193438931282399927035736243 290158396923599890553604365)
      ·
        refine ⟨108809398846349958957601637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290158396923599890553604365 108809398846349958957601637)
        ·
          refine ⟨20401762283690617304550307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108809398846349958957601637 20401762283690617304550307)
          ·
            refine ⟨30602643425535925956825461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20401762283690617304550307 30602643425535925956825461)
            ·
              refine ⟨2868997821143993058452387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30602643425535925956825461 2868997821143993058452387)
              ·
                refine ⟨4303496731715989587678581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868997821143993058452387 4303496731715989587678581)
                ·
                  refine ⟨403452818598374023844867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4303496731715989587678581 403452818598374023844867)
                  ·
                    rfl

theorem cell22_3535747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 5].length) (baseStart_3535747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535747 prefixEnd_3535747 := by exact prefixLift 3535747
  have htrace : WordTrace (prefixWord ++ tailWord_3535747) baseStart_3535747 baseEnd_3535747 := by
    simpa [prefixWord, tailWord_3535747, baseEnd_3535747] using wordTrace_append hprefix tailTrace_3535747
  have hstable : (prefixWord ++ tailWord_3535747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535747).length < 2 ^ (prefixWord ++ tailWord_3535747).sum := by decide
  have hdescent : baseEnd_3535747 < baseStart_3535747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535798 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3535798 : Nat := 118140960795 + 3535798 * 2 ^ 59
def prefixEnd_3535798 : Nat := 4983230072969 + 3 ^ 40 * 3535798 * 2
def baseEnd_3535798 : Nat := 403458638045791646169815

theorem tailTrace_3535798 : CollatzResearch.WordTrace tailWord_3535798 prefixEnd_3535798 403458638045791646169815 := by
  unfold tailWord_3535798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8060071727775949191704003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85974098429610124711509365 8060071727775949191704003)
  ·
    refine ⟨12090107591663923787556005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8060071727775949191704003 12090107591663923787556005)
    ·
      refine ⟨2266895173436985710166751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12090107591663923787556005 2266895173436985710166751)
      ·
        refine ⟨3400342760155478565250127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266895173436985710166751 3400342760155478565250127)
        ·
          refine ⟨5100514140233217847875191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400342760155478565250127 5100514140233217847875191)
          ·
            refine ⟨7650771210349826771812787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5100514140233217847875191 7650771210349826771812787)
            ·
              refine ⟨11476156815524740157719181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7650771210349826771812787 11476156815524740157719181)
              ·
                refine ⟨4303558805821777559144693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11476156815524740157719181 4303558805821777559144693)
                ·
                  refine ⟨403458638045791646169815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4303558805821777559144693 403458638045791646169815)
                  ·
                    rfl

theorem cell22_3535798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3535798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535798 prefixEnd_3535798 := by exact prefixLift 3535798
  have htrace : WordTrace (prefixWord ++ tailWord_3535798) baseStart_3535798 baseEnd_3535798 := by
    simpa [prefixWord, tailWord_3535798, baseEnd_3535798] using wordTrace_append hprefix tailTrace_3535798
  have hstable : (prefixWord ++ tailWord_3535798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535798).length < 2 ^ (prefixWord ++ tailWord_3535798).sum := by decide
  have hdescent : baseEnd_3535798 < baseStart_3535798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535820 : List Nat := [2, 2, 1, 4, 1, 1, 1, 10]
def baseStart_3535820 : Nat := 118140960795 + 3535820 * 2 ^ 59
def prefixEnd_3535820 : Nat := 4983230072969 + 3 ^ 40 * 3535820 * 2
def baseEnd_3535820 : Nat := 134487049465219357162153

theorem tailTrace_3535820 : CollatzResearch.WordTrace tailWord_3535820 prefixEnd_3535820 134487049465219357162153 := by
  unfold tailWord_3535820
  simp only [CollatzResearch.WordTrace]
  refine ⟨64480975025167742412282457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85974633366890323216376609 64480975025167742412282457)
  ·
    refine ⟨48360731268875806809211843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64480975025167742412282457 48360731268875806809211843)
    ·
      refine ⟨72541096903313710213817765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48360731268875806809211843 72541096903313710213817765)
      ·
        refine ⟨13601455669371320665090831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72541096903313710213817765 13601455669371320665090831)
        ·
          refine ⟨20402183504056980997636247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13601455669371320665090831 20402183504056980997636247)
          ·
            refine ⟨30603275256085471496454371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20402183504056980997636247 30603275256085471496454371)
            ·
              refine ⟨45904912884128207244681557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30603275256085471496454371 45904912884128207244681557)
              ·
                refine ⟨134487049465219357162153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45904912884128207244681557 134487049465219357162153)
                ·
                  rfl

theorem cell22_3535820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 10].length) (baseStart_3535820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535820 prefixEnd_3535820 := by exact prefixLift 3535820
  have htrace : WordTrace (prefixWord ++ tailWord_3535820) baseStart_3535820 baseEnd_3535820 := by
    simpa [prefixWord, tailWord_3535820, baseEnd_3535820] using wordTrace_append hprefix tailTrace_3535820
  have hstable : (prefixWord ++ tailWord_3535820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535820).length < 2 ^ (prefixWord ++ tailWord_3535820).sum := by decide
  have hdescent : baseEnd_3535820 < baseStart_3535820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535822 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3535822 : Nat := 118140960795 + 3535822 * 2 ^ 59
def prefixEnd_3535822 : Nat := 4983230072969 + 3 ^ 40 * 3535822 * 2
def baseEnd_3535822 : Nat := 1210384129827846875909371

theorem tailTrace_3535822 : CollatzResearch.WordTrace tailWord_3535822 prefixEnd_3535822 1210384129827846875909371 := by
  unfold tailWord_3535822
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120252874541029895767215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85974681997552159444091813 16120252874541029895767215)
  ·
    refine ⟨24180379311811544843650823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16120252874541029895767215 24180379311811544843650823)
    ·
      refine ⟨36270568967717317265476235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24180379311811544843650823 36270568967717317265476235)
      ·
        refine ⟨54405853451575975898214353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36270568967717317265476235 54405853451575975898214353)
        ·
          refine ⟨40804390088681981923660765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54405853451575975898214353 40804390088681981923660765)
          ·
            refine ⟨15301646283255743221372787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40804390088681981923660765 15301646283255743221372787)
            ·
              refine ⟨22952469424883614832059181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301646283255743221372787 22952469424883614832059181)
              ·
                refine ⟨8607176034331355562022193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22952469424883614832059181 8607176034331355562022193)
                ·
                  refine ⟨6455382025748516671516645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8607176034331355562022193 6455382025748516671516645)
                  ·
                    refine ⟨1210384129827846875909371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6455382025748516671516645 1210384129827846875909371)
                    ·
                      rfl

theorem cell22_3535822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3535822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535822 prefixEnd_3535822 := by exact prefixLift 3535822
  have htrace : WordTrace (prefixWord ++ tailWord_3535822) baseStart_3535822 baseEnd_3535822 := by
    simpa [prefixWord, tailWord_3535822, baseEnd_3535822] using wordTrace_append hprefix tailTrace_3535822
  have hstable : (prefixWord ++ tailWord_3535822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535822).length < 2 ^ (prefixWord ++ tailWord_3535822).sum := by decide
  have hdescent : baseEnd_3535822 < baseStart_3535822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535854 : List Nat := [4, 1, 2, 1, 4, 2, 1, 7]
def baseStart_3535854 : Nat := 118140960795 + 3535854 * 2 ^ 59
def prefixEnd_3535854 : Nat := 4983230072969 + 3 ^ 40 * 3535854 * 2
def baseEnd_3535854 : Nat := 134488342675756606567697

theorem tailTrace_3535854 : CollatzResearch.WordTrace tailWord_3535854 prefixEnd_3535854 134488342675756606567697 := by
  unfold tailWord_3535854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120398766526538578912827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85975460088141539087535077 16120398766526538578912827)
  ·
    refine ⟨24180598149789807868369241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16120398766526538578912827 24180598149789807868369241)
    ·
      refine ⟨18135448612342355901276931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24180598149789807868369241 18135448612342355901276931)
      ·
        refine ⟨27203172918513533851915397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18135448612342355901276931 27203172918513533851915397)
        ·
          refine ⟨5100594922221287597234137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27203172918513533851915397 5100594922221287597234137)
          ·
            refine ⟨3825446191665965697925603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5100594922221287597234137 3825446191665965697925603)
            ·
              refine ⟨5738169287498948546888405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825446191665965697925603 5738169287498948546888405)
              ·
                refine ⟨134488342675756606567697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5738169287498948546888405 134488342675756606567697)
                ·
                  rfl

theorem cell22_3535854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_3535854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535854 prefixEnd_3535854 := by exact prefixLift 3535854
  have htrace : WordTrace (prefixWord ++ tailWord_3535854) baseStart_3535854 baseEnd_3535854 := by
    simpa [prefixWord, tailWord_3535854, baseEnd_3535854] using wordTrace_append hprefix tailTrace_3535854
  have hstable : (prefixWord ++ tailWord_3535854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535854).length < 2 ^ (prefixWord ++ tailWord_3535854).sum := by decide
  have hdescent : baseEnd_3535854 < baseStart_3535854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535886 : List Nat := [4, 1, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_3535886 : Nat := 118140960795 + 3535886 * 2 ^ 59
def prefixEnd_3535886 : Nat := 4983230072969 + 3 ^ 40 * 3535886 * 2
def baseEnd_3535886 : Nat := 1210406038335772042309175

theorem tailTrace_3535886 : CollatzResearch.WordTrace tailWord_3535886 prefixEnd_3535886 1210406038335772042309175 := by
  unfold tailWord_3535886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120544658512047262058439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85976238178730918730978341 16120544658512047262058439)
  ·
    refine ⟨24180816987768070893087659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16120544658512047262058439 24180816987768070893087659)
    ·
      refine ⟨36271225481652106339631489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24180816987768070893087659 36271225481652106339631489)
      ·
        refine ⟨27203419111239079754723617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36271225481652106339631489 27203419111239079754723617)
        ·
          refine ⟨20402564333429309816042713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27203419111239079754723617 20402564333429309816042713)
          ·
            refine ⟨15301923250071982362032035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20402564333429309816042713 15301923250071982362032035)
            ·
              refine ⟨22952884875107973543048053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15301923250071982362032035 22952884875107973543048053)
              ·
                refine ⟨2151832957041372519660755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22952884875107973543048053 2151832957041372519660755)
                ·
                  refine ⟨3227749435562058779491133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151832957041372519660755 3227749435562058779491133)
                  ·
                    refine ⟨1210406038335772042309175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227749435562058779491133 1210406038335772042309175)
                    ·
                      rfl

theorem cell22_3535886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_3535886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535886 prefixEnd_3535886 := by exact prefixLift 3535886
  have htrace : WordTrace (prefixWord ++ tailWord_3535886) baseStart_3535886 baseEnd_3535886 := by
    simpa [prefixWord, tailWord_3535886, baseEnd_3535886] using wordTrace_append hprefix tailTrace_3535886
  have hstable : (prefixWord ++ tailWord_3535886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535886).length < 2 ^ (prefixWord ++ tailWord_3535886).sum := by decide
  have hdescent : baseEnd_3535886 < baseStart_3535886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535929 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_3535929 : Nat := 118140960795 + 3535929 * 2 ^ 59
def prefixEnd_3535929 : Nat := 4983230072969 + 3 ^ 40 * 3535929 * 2
def baseEnd_3535929 : Nat := 1210420758114534263484043

theorem tailTrace_3535929 : CollatzResearch.WordTrace tailWord_3535929 prefixEnd_3535929 1210420758114534263484043 := by
  unfold tailWord_3535929
  simp only [CollatzResearch.WordTrace]
  refine ⟨128965925606940596440282841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85977283737960397626855227 128965925606940596440282841)
  ·
    refine ⟨96724444205205447330212131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128965925606940596440282841 96724444205205447330212131)
    ·
      refine ⟨145086666307808170995318197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96724444205205447330212131 145086666307808170995318197)
      ·
        refine ⟨13601874966357016030811081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145086666307808170995318197 13601874966357016030811081)
        ·
          refine ⟨10201406224767762023108311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13601874966357016030811081 10201406224767762023108311)
          ·
            refine ⟨15302109337151643034662467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10201406224767762023108311 15302109337151643034662467)
            ·
              refine ⟨22953164005727464551993701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15302109337151643034662467 22953164005727464551993701)
              ·
                refine ⟨4303718251073899603498819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22953164005727464551993701 4303718251073899603498819)
                ·
                  refine ⟨6455577376610849405248229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4303718251073899603498819 6455577376610849405248229)
                  ·
                    refine ⟨1210420758114534263484043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6455577376610849405248229 1210420758114534263484043)
                    ·
                      rfl

theorem cell22_3535929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_3535929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535929 prefixEnd_3535929 := by exact prefixLift 3535929
  have htrace : WordTrace (prefixWord ++ tailWord_3535929) baseStart_3535929 baseEnd_3535929 := by
    simpa [prefixWord, tailWord_3535929, baseEnd_3535929] using wordTrace_append hprefix tailTrace_3535929
  have hstable : (prefixWord ++ tailWord_3535929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535929).length < 2 ^ (prefixWord ++ tailWord_3535929).sum := by decide
  have hdescent : baseEnd_3535929 < baseStart_3535929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535959 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 2, 3]
def baseStart_3535959 : Nat := 118140960795 + 3535959 * 2 ^ 59
def prefixEnd_3535959 : Nat := 4983230072969 + 3 ^ 40 * 3535959 * 2
def baseEnd_3535959 : Nat := 1210431027727624185233951

theorem tailTrace_3535959 : CollatzResearch.WordTrace tailWord_3535959 prefixEnd_3535959 1210431027727624185233951 := by
  unfold tailWord_3535959
  simp only [CollatzResearch.WordTrace]
  refine ⟨128967019796831911563874931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85978013197887941042583287 128967019796831911563874931)
  ·
    refine ⟨193450529695247867345812397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128967019796831911563874931 193450529695247867345812397)
    ·
      refine ⟨72543948635717950254679649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193450529695247867345812397 72543948635717950254679649)
      ·
        refine ⟨54407961476788462691009737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72543948635717950254679649 54407961476788462691009737)
        ·
          refine ⟨40805971107591347018257303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54407961476788462691009737 40805971107591347018257303)
          ·
            refine ⟨61208956661387020527385955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40805971107591347018257303 61208956661387020527385955)
            ·
              refine ⟨91813434992080530791078933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61208956661387020527385955 91813434992080530791078933)
              ·
                refine ⟨4303754765253774880831825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91813434992080530791078933 4303754765253774880831825)
                ·
                  refine ⟨3227816073940331160623869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4303754765253774880831825 3227816073940331160623869)
                  ·
                    refine ⟨1210431027727624185233951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227816073940331160623869 1210431027727624185233951)
                    ·
                      rfl

theorem cell22_3535959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_3535959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3535959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3535959 prefixEnd_3535959 := by exact prefixLift 3535959
  have htrace : WordTrace (prefixWord ++ tailWord_3535959) baseStart_3535959 baseEnd_3535959 := by
    simpa [prefixWord, tailWord_3535959, baseEnd_3535959] using wordTrace_append hprefix tailTrace_3535959
  have hstable : (prefixWord ++ tailWord_3535959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535959).length < 2 ^ (prefixWord ++ tailWord_3535959).sum := by decide
  have hdescent : baseEnd_3535959 < baseStart_3535959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536068 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3536068 : Nat := 118140960795 + 3536068 * 2 ^ 59
def prefixEnd_3536068 : Nat := 4983230072969 + 3 ^ 40 * 3536068 * 2
def baseEnd_3536068 : Nat := 403489446885061411419539

theorem tailTrace_3536068 : CollatzResearch.WordTrace tailWord_3536068 prefixEnd_3536068 403489446885061411419539 := by
  unfold tailWord_3536068
  simp only [CollatzResearch.WordTrace]
  refine ⟨64485497676718511589796429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85980663568958015453061905 64485497676718511589796429)
  ·
    refine ⟨24182061628769441846173661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64485497676718511589796429 24182061628769441846173661)
    ·
      refine ⟨9068273110788540692315123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24182061628769441846173661 9068273110788540692315123)
      ·
        refine ⟨13602409666182811038472685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068273110788540692315123 13602409666182811038472685)
        ·
          refine ⟨5100903624818554139427257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13602409666182811038472685 5100903624818554139427257)
          ·
            refine ⟨3825677718613915604570443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5100903624818554139427257 3825677718613915604570443)
            ·
              refine ⟨5738516577920873406855665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825677718613915604570443 5738516577920873406855665)
              ·
                refine ⟨4303887433440655055141749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5738516577920873406855665 4303887433440655055141749)
                ·
                  refine ⟨403489446885061411419539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4303887433440655055141749 403489446885061411419539)
                  ·
                    rfl

theorem cell22_3536068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3536068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536068 prefixEnd_3536068 := by exact prefixLift 3536068
  have htrace : WordTrace (prefixWord ++ tailWord_3536068) baseStart_3536068 baseEnd_3536068 := by
    simpa [prefixWord, tailWord_3536068, baseEnd_3536068] using wordTrace_append hprefix tailTrace_3536068
  have hstable : (prefixWord ++ tailWord_3536068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536068).length < 2 ^ (prefixWord ++ tailWord_3536068).sum := by decide
  have hdescent : baseEnd_3536068 < baseStart_3536068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536126 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3536126 : Nat := 118140960795 + 3536126 * 2 ^ 59
def prefixEnd_3536126 : Nat := 4983230072969 + 3 ^ 40 * 3536126 * 2
def baseEnd_3536126 : Nat := 1210488195240491416308439

theorem tailTrace_3536126 : CollatzResearch.WordTrace tailWord_3536126 prefixEnd_3536126 1210488195240491416308439 := by
  unfold tailWord_3536126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16121638848403362385650529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85982073858151266056802821 16121638848403362385650529)
  ·
    refine ⟨12091229136302521789237897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16121638848403362385650529 12091229136302521789237897)
    ·
      refine ⟨9068421852226891341928423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12091229136302521789237897 9068421852226891341928423)
      ·
        refine ⟨13602632778340337012892635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068421852226891341928423 13602632778340337012892635)
        ·
          refine ⟨20403949167510505519338953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13602632778340337012892635 20403949167510505519338953)
          ·
            refine ⟨15302961875632879139504215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20403949167510505519338953 15302961875632879139504215)
            ·
              refine ⟨22954442813449318709256323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15302961875632879139504215 22954442813449318709256323)
              ·
                refine ⟨34431664220173978063884485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22954442813449318709256323 34431664220173978063884485)
                ·
                  refine ⟨6455937041282620886978341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34431664220173978063884485 6455937041282620886978341)
                  ·
                    refine ⟨1210488195240491416308439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6455937041282620886978341 1210488195240491416308439)
                    ·
                      rfl

theorem cell22_3536126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3536126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536126 prefixEnd_3536126 := by exact prefixLift 3536126
  have htrace : WordTrace (prefixWord ++ tailWord_3536126) baseStart_3536126 baseEnd_3536126 := by
    simpa [prefixWord, tailWord_3536126, baseEnd_3536126] using wordTrace_append hprefix tailTrace_3536126
  have hstable : (prefixWord ++ tailWord_3536126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536126).length < 2 ^ (prefixWord ++ tailWord_3536126).sum := by decide
  have hdescent : baseEnd_3536126 < baseStart_3536126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536130 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3536130 : Nat := 118140960795 + 3536130 * 2 ^ 59
def prefixEnd_3536130 : Nat := 4983230072969 + 3 ^ 40 * 3536130 * 2
def baseEnd_3536130 : Nat := 403496521507412246402809

theorem tailTrace_3536130 : CollatzResearch.WordTrace tailWord_3536130 prefixEnd_3536130 403496521507412246402809 := by
  unfold tailWord_3536130
  simp only [CollatzResearch.WordTrace]
  refine ⟨32243314169803101942087461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85982171119474938512233229 32243314169803101942087461)
  ·
    refine ⟨6045621406838081614141399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32243314169803101942087461 6045621406838081614141399)
    ·
      refine ⟨9068432110257122421212099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6045621406838081614141399 9068432110257122421212099)
      ·
        refine ⟨13602648165385683631818149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9068432110257122421212099 13602648165385683631818149)
        ·
          refine ⟨2550496531009815680965903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13602648165385683631818149 2550496531009815680965903)
          ·
            refine ⟨3825744796514723521448855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550496531009815680965903 3825744796514723521448855)
            ·
              refine ⟨5738617194772085282173283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825744796514723521448855 5738617194772085282173283)
              ·
                refine ⟨8607925792158127923259925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738617194772085282173283 8607925792158127923259925)
                ·
                  refine ⟨403496521507412246402809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8607925792158127923259925 403496521507412246402809)
                  ·
                    rfl

theorem cell22_3536130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3536130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536130 prefixEnd_3536130 := by exact prefixLift 3536130
  have htrace : WordTrace (prefixWord ++ tailWord_3536130) baseStart_3536130 baseEnd_3536130 := by
    simpa [prefixWord, tailWord_3536130, baseEnd_3536130] using wordTrace_append hprefix tailTrace_3536130
  have hstable : (prefixWord ++ tailWord_3536130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536130).length < 2 ^ (prefixWord ++ tailWord_3536130).sum := by decide
  have hdescent : baseEnd_3536130 < baseStart_3536130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536156 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_3536156 : Nat := 118140960795 + 3536156 * 2 ^ 59
def prefixEnd_3536156 : Nat := 4983230072969 + 3 ^ 40 * 3536156 * 2
def baseEnd_3536156 : Nat := 1210498464853581338058347

theorem tailTrace_3536156 : CollatzResearch.WordTrace tailWord_3536156 prefixEnd_3536156 1210498464853581338058347 := by
  unfold tailWord_3536156
  simp only [CollatzResearch.WordTrace]
  refine ⟨64487102488559107104398161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85982803318078809472530881 64487102488559107104398161)
  ·
    refine ⟨48365326866419330328298621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64487102488559107104398161 48365326866419330328298621)
    ·
      refine ⟨18136997574907248873111983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48365326866419330328298621 18136997574907248873111983)
      ·
        refine ⟨27205496362360873309667975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18136997574907248873111983 27205496362360873309667975)
        ·
          refine ⟨40808244543541309964501963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27205496362360873309667975 40808244543541309964501963)
          ·
            refine ⟨61212366815311964946752945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40808244543541309964501963 61212366815311964946752945)
            ·
              refine ⟨45909275111483973710064709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61212366815311964946752945 45909275111483973710064709)
              ·
                refine ⟨8607989083403245070637133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45909275111483973710064709 8607989083403245070637133)
                ·
                  refine ⟨3227995906276216901488925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8607989083403245070637133 3227995906276216901488925)
                  ·
                    refine ⟨1210498464853581338058347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3227995906276216901488925 1210498464853581338058347)
                    ·
                      rfl

theorem cell22_3536156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_3536156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536156 prefixEnd_3536156 := by exact prefixLift 3536156
  have htrace : WordTrace (prefixWord ++ tailWord_3536156) baseStart_3536156 baseEnd_3536156 := by
    simpa [prefixWord, tailWord_3536156, baseEnd_3536156] using wordTrace_append hprefix tailTrace_3536156
  have hstable : (prefixWord ++ tailWord_3536156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536156).length < 2 ^ (prefixWord ++ tailWord_3536156).sum := by decide
  have hdescent : baseEnd_3536156 < baseStart_3536156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536184 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_3536184 : Nat := 118140960795 + 3536184 * 2 ^ 59
def prefixEnd_3536184 : Nat := 4983230072969 + 3 ^ 40 * 3536184 * 2
def baseEnd_3536184 : Nat := 1210508049825798598358261

theorem tailTrace_3536184 : CollatzResearch.WordTrace tailWord_3536184 prefixEnd_3536184 1210508049825798598358261 := by
  unfold tailWord_3536184
  simp only [CollatzResearch.WordTrace]
  refine ⟨64487613110508387495407803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85983484147344516660543737 64487613110508387495407803)
  ·
    refine ⟨96731419665762581243111705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64487613110508387495407803 96731419665762581243111705)
    ·
      refine ⟨72548564749321935932333779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96731419665762581243111705 72548564749321935932333779)
      ·
        refine ⟨108822847123982903898500669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72548564749321935932333779 108822847123982903898500669)
        ·
          refine ⟨40808567671493588961937751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108822847123982903898500669 40808567671493588961937751)
          ·
            refine ⟨61212851507240383442906627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40808567671493588961937751 61212851507240383442906627)
            ·
              refine ⟨91819277260860575164359941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61212851507240383442906627 91819277260860575164359941)
              ·
                refine ⟨17216114486411357843317489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91819277260860575164359941 17216114486411357843317489)
                ·
                  refine ⟨12912085864808518382488117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17216114486411357843317489 12912085864808518382488117)
                  ·
                    refine ⟨1210508049825798598358261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12912085864808518382488117 1210508049825798598358261)
                    ·
                      rfl

theorem cell22_3536184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_3536184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536184 prefixEnd_3536184 := by exact prefixLift 3536184
  have htrace : WordTrace (prefixWord ++ tailWord_3536184) baseStart_3536184 baseEnd_3536184 := by
    simpa [prefixWord, tailWord_3536184, baseEnd_3536184] using wordTrace_append hprefix tailTrace_3536184
  have hstable : (prefixWord ++ tailWord_3536184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536184).length < 2 ^ (prefixWord ++ tailWord_3536184).sum := by decide
  have hdescent : baseEnd_3536184 < baseStart_3536184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536186 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_3536186 : Nat := 118140960795 + 3536186 * 2 ^ 59
def prefixEnd_3536186 : Nat := 4983230072969 + 3 ^ 40 * 3536186 * 2
def baseEnd_3536186 : Nat := 403502911488890419936085

theorem tailTrace_3536186 : CollatzResearch.WordTrace tailWord_3536186 prefixEnd_3536186 403502911488890419936085 := by
  unfold tailWord_3536186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32243824791752382333097103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85983532778006352888258941 32243824791752382333097103)
  ·
    refine ⟨48365737187628573499645655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32243824791752382333097103 48365737187628573499645655)
    ·
      refine ⟨72548605781442860249468483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48365737187628573499645655 72548605781442860249468483)
      ·
        refine ⟨108822908672164290374202725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72548605781442860249468483 108822908672164290374202725)
        ·
          refine ⟨20404295376030804445163011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108822908672164290374202725 20404295376030804445163011)
          ·
            refine ⟨30606443064046206667744517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20404295376030804445163011 30606443064046206667744517)
            ·
              refine ⟨5738708074508663750202097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30606443064046206667744517 5738708074508663750202097)
              ·
                refine ⟨4304031055881497812651573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5738708074508663750202097 4304031055881497812651573)
                ·
                  refine ⟨403502911488890419936085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4304031055881497812651573 403502911488890419936085)
                  ·
                    rfl

theorem cell22_3536186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_3536186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536186 prefixEnd_3536186 := by exact prefixLift 3536186
  have htrace : WordTrace (prefixWord ++ tailWord_3536186) baseStart_3536186 baseEnd_3536186 := by
    simpa [prefixWord, tailWord_3536186, baseEnd_3536186] using wordTrace_append hprefix tailTrace_3536186
  have hstable : (prefixWord ++ tailWord_3536186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536186).length < 2 ^ (prefixWord ++ tailWord_3536186).sum := by decide
  have hdescent : baseEnd_3536186 < baseStart_3536186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536190 : List Nat := [4, 2, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_3536190 : Nat := 118140960795 + 3536190 * 2 ^ 59
def prefixEnd_3536190 : Nat := 4983230072969 + 3 ^ 40 * 3536190 * 2
def baseEnd_3536190 : Nat := 1210510103748416582708243

theorem tailTrace_3536190 : CollatzResearch.WordTrace tailWord_3536190 prefixEnd_3536190 1210510103748416582708243 := by
  unfold tailWord_3536190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16121930632374379751941753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85983630039330025343689349 16121930632374379751941753)
  ·
    refine ⟨12091447974280784813956315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16121930632374379751941753 12091447974280784813956315)
    ·
      refine ⟨18137171961421177220934473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12091447974280784813956315 18137171961421177220934473)
      ·
        refine ⟨13602878971065882915700855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18137171961421177220934473 13602878971065882915700855)
        ·
          refine ⟨20404318456598824373551283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13602878971065882915700855 20404318456598824373551283)
          ·
            refine ⟨30606477684898236560326925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20404318456598824373551283 30606477684898236560326925)
            ·
              refine ⟨11477429131836838710122597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30606477684898236560326925 11477429131836838710122597)
              ·
                refine ⟨2152017962219407258147987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11477429131836838710122597 2152017962219407258147987)
                ·
                  refine ⟨3228026943329110887221981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152017962219407258147987 3228026943329110887221981)
                  ·
                    refine ⟨1210510103748416582708243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3228026943329110887221981 1210510103748416582708243)
                    ·
                      rfl

theorem cell22_3536190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_3536190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536190 prefixEnd_3536190 := by exact prefixLift 3536190
  have htrace : WordTrace (prefixWord ++ tailWord_3536190) baseStart_3536190 baseEnd_3536190 := by
    simpa [prefixWord, tailWord_3536190, baseEnd_3536190] using wordTrace_append hprefix tailTrace_3536190
  have hstable : (prefixWord ++ tailWord_3536190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536190).length < 2 ^ (prefixWord ++ tailWord_3536190).sum := by decide
  have hdescent : baseEnd_3536190 < baseStart_3536190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536216 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_3536216 : Nat := 118140960795 + 3536216 * 2 ^ 59
def prefixEnd_3536216 : Nat := 4983230072969 + 3 ^ 40 * 3536216 * 2
def baseEnd_3536216 : Nat := 1210519004079761181558163

theorem tailTrace_3536216 : CollatzResearch.WordTrace tailWord_3536216 prefixEnd_3536216 1210519004079761181558163 := by
  unfold tailWord_3536216
  simp only [CollatzResearch.WordTrace]
  refine ⟨64488196678450422227990251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85984262237933896303987001 64488196678450422227990251)
  ·
    refine ⟨96732295017675633341985377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64488196678450422227990251 96732295017675633341985377)
    ·
      refine ⟨72549221263256725006489033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96732295017675633341985377 72549221263256725006489033)
      ·
        refine ⟨54411915947442543754866775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72549221263256725006489033 54411915947442543754866775)
        ·
          refine ⟨81617873921163815632300163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54411915947442543754866775 81617873921163815632300163)
          ·
            refine ⟨122426810881745723448450245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81617873921163815632300163 122426810881745723448450245)
            ·
              refine ⟨22955027040327323146584421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122426810881745723448450245 22955027040327323146584421)
              ·
                refine ⟨4304067570061373089984579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22955027040327323146584421 4304067570061373089984579)
                ·
                  refine ⟨6456101355092059634976869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304067570061373089984579 6456101355092059634976869)
                  ·
                    refine ⟨1210519004079761181558163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6456101355092059634976869 1210519004079761181558163)
                    ·
                      rfl

theorem cell22_3536216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_3536216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536216 prefixEnd_3536216 := by exact prefixLift 3536216
  have htrace : WordTrace (prefixWord ++ tailWord_3536216) baseStart_3536216 baseEnd_3536216 := by
    simpa [prefixWord, tailWord_3536216, baseEnd_3536216] using wordTrace_append hprefix tailTrace_3536216
  have hstable : (prefixWord ++ tailWord_3536216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536216).length < 2 ^ (prefixWord ++ tailWord_3536216).sum := by decide
  have hdescent : baseEnd_3536216 < baseStart_3536216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536263 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3536263 : Nat := 118140960795 + 3536263 * 2 ^ 59
def prefixEnd_3536263 : Nat := 4983230072969 + 3 ^ 40 * 3536263 * 2
def baseEnd_3536263 : Nat := 1210535093140268725633019

theorem tailTrace_3536263 : CollatzResearch.WordTrace tailWord_3536263 prefixEnd_3536263 1210535093140268725633019 := by
  unfold tailWord_3536263
  simp only [CollatzResearch.WordTrace]
  refine ⟨128978107587730571482941443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85985405058487047655294295 128978107587730571482941443)
  ·
    refine ⟨193467161381595857224412165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128978107587730571482941443 193467161381595857224412165)
    ·
      refine ⟨36275092759049223229577281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193467161381595857224412165 36275092759049223229577281)
      ·
        refine ⟨27206319569286917422182961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36275092759049223229577281 27206319569286917422182961)
        ·
          refine ⟨20404739676965188066637221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27206319569286917422182961 20404739676965188066637221)
          ·
            refine ⟨3825888689430972762494479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20404739676965188066637221 3825888689430972762494479)
            ·
              refine ⟨5738833034146459143741719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825888689430972762494479 5738833034146459143741719)
              ·
                refine ⟨8608249551219688715612579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5738833034146459143741719 8608249551219688715612579)
                ·
                  refine ⟨12912374326829533073418869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8608249551219688715612579 12912374326829533073418869)
                  ·
                    refine ⟨1210535093140268725633019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12912374326829533073418869 1210535093140268725633019)
                    ·
                      rfl

theorem cell22_3536263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3536263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536263 prefixEnd_3536263 := by exact prefixLift 3536263
  have htrace : WordTrace (prefixWord ++ tailWord_3536263) baseStart_3536263 baseEnd_3536263 := by
    simpa [prefixWord, tailWord_3536263, baseEnd_3536263] using wordTrace_append hprefix tailTrace_3536263
  have hstable : (prefixWord ++ tailWord_3536263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536263).length < 2 ^ (prefixWord ++ tailWord_3536263).sum := by decide
  have hdescent : baseEnd_3536263 < baseStart_3536263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536359 : List Nat := [1, 1, 5, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3536359 : Nat := 118140960795 + 3536359 * 2 ^ 59
def prefixEnd_3536359 : Nat := 4983230072969 + 3 ^ 40 * 3536359 * 2
def baseEnd_3536359 : Nat := 1210567955902156475232725

theorem tailTrace_3536359 : CollatzResearch.WordTrace tailWord_3536359 prefixEnd_3536359 1210567955902156475232725 := by
  unfold tailWord_3536359
  simp only [CollatzResearch.WordTrace]
  refine ⟨128981608995382779878436131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85987739330255186585624087 128981608995382779878436131)
  ·
    refine ⟨193472413493074169817654197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128981608995382779878436131 193472413493074169817654197)
    ·
      refine ⟨18138038764975703420405081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193472413493074169817654197 18138038764975703420405081)
      ·
        refine ⟨13603529073731777565303811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18138038764975703420405081 13603529073731777565303811)
        ·
          refine ⟨20405293610597666347955717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13603529073731777565303811 20405293610597666347955717)
          ·
            refine ⟨3825992551987062440241697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20405293610597666347955717 3825992551987062440241697)
            ·
              refine ⟨2869494413990296830181273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3825992551987062440241697 2869494413990296830181273)
              ·
                refine ⟨2152120810492722622635955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2869494413990296830181273 2152120810492722622635955)
                ·
                  refine ⟨3228181215739083933953933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152120810492722622635955 3228181215739083933953933)
                  ·
                    refine ⟨1210567955902156475232725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3228181215739083933953933 1210567955902156475232725)
                    ·
                      rfl

theorem cell22_3536359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3536359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536359 prefixEnd_3536359 := by exact prefixLift 3536359
  have htrace : WordTrace (prefixWord ++ tailWord_3536359) baseStart_3536359 baseEnd_3536359 := by
    simpa [prefixWord, tailWord_3536359, baseEnd_3536359] using wordTrace_append hprefix tailTrace_3536359
  have hstable : (prefixWord ++ tailWord_3536359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536359).length < 2 ^ (prefixWord ++ tailWord_3536359).sum := by decide
  have hdescent : baseEnd_3536359 < baseStart_3536359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536413 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_3536413 : Nat := 118140960795 + 3536413 * 2 ^ 59
def prefixEnd_3536413 : Nat := 4983230072969 + 3 ^ 40 * 3536413 * 2
def baseEnd_3536413 : Nat := 1210586441205718334382559

theorem tailTrace_3536413 : CollatzResearch.WordTrace tailWord_3536413 prefixEnd_3536413 1210586441205718334382559 := by
  unfold tailWord_3536413
  simp only [CollatzResearch.WordTrace]
  refine ⟨128983578537187147100901893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85989052358124764733934595 128983578537187147100901893)
  ·
    refine ⟨24184420975722590081419105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128983578537187147100901893 24184420975722590081419105)
    ·
      refine ⟨18138315731791942561064329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24184420975722590081419105 18138315731791942561064329)
      ·
        refine ⟨13603736798843956920798247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18138315731791942561064329 13603736798843956920798247)
        ·
          refine ⟨20405605198265935381197371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13603736798843956920798247 20405605198265935381197371)
          ·
            refine ⟨30608407797398903071796057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20405605198265935381197371 30608407797398903071796057)
            ·
              refine ⟨22956305848049177303847043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30608407797398903071796057 22956305848049177303847043)
              ·
                refine ⟨34434458772073765955770565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22956305848049177303847043 34434458772073765955770565)
                ·
                  refine ⟨6456461019763831116706981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34434458772073765955770565 6456461019763831116706981)
                  ·
                    refine ⟨1210586441205718334382559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6456461019763831116706981 1210586441205718334382559)
                    ·
                      rfl

theorem cell22_3536413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_3536413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536413 prefixEnd_3536413 := by exact prefixLift 3536413
  have htrace : WordTrace (prefixWord ++ tailWord_3536413) baseStart_3536413 baseEnd_3536413 := by
    simpa [prefixWord, tailWord_3536413, baseEnd_3536413] using wordTrace_append hprefix tailTrace_3536413
  have hstable : (prefixWord ++ tailWord_3536413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536413).length < 2 ^ (prefixWord ++ tailWord_3536413).sum := by decide
  have hdescent : baseEnd_3536413 < baseStart_3536413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536415 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 2, 3]
def baseStart_3536415 : Nat := 118140960795 + 3536415 * 2 ^ 59
def prefixEnd_3536415 : Nat := 4983230072969 + 3 ^ 40 * 3536415 * 2
def baseEnd_3536415 : Nat := 1210587125846590995832553

theorem tailTrace_3536415 : CollatzResearch.WordTrace tailWord_3536415 prefixEnd_3536415 1210587125846590995832553 := by
  unfold tailWord_3536415
  simp only [CollatzResearch.WordTrace]
  refine ⟨128983651483179901442474699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85989100988786600961649799 128983651483179901442474699)
  ·
    refine ⟨193475477224769852163712049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128983651483179901442474699 193475477224769852163712049)
    ·
      refine ⟨145106607918577389122784037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193475477224769852163712049 145106607918577389122784037)
      ·
        refine ⟨27207488984733260460522007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145106607918577389122784037 27207488984733260460522007)
        ·
          refine ⟨40811233477099890690783011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27207488984733260460522007 40811233477099890690783011)
          ·
            refine ⟨61216850215649836036174517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40811233477099890690783011 61216850215649836036174517)
            ·
              refine ⟨5739079707717172128391361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61216850215649836036174517 5739079707717172128391361)
              ·
                refine ⟨4304309780787879096293521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5739079707717172128391361 4304309780787879096293521)
                ·
                  refine ⟨3228232335590909322220141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4304309780787879096293521 3228232335590909322220141)
                  ·
                    refine ⟨1210587125846590995832553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3228232335590909322220141 1210587125846590995832553)
                    ·
                      rfl

theorem cell22_3536415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_3536415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536415 prefixEnd_3536415 := by exact prefixLift 3536415
  have htrace : WordTrace (prefixWord ++ tailWord_3536415) baseStart_3536415 baseEnd_3536415 := by
    simpa [prefixWord, tailWord_3536415, baseEnd_3536415] using wordTrace_append hprefix tailTrace_3536415
  have hstable : (prefixWord ++ tailWord_3536415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536415).length < 2 ^ (prefixWord ++ tailWord_3536415).sum := by decide
  have hdescent : baseEnd_3536415 < baseStart_3536415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536490 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_3536490 : Nat := 118140960795 + 3536490 * 2 ^ 59
def prefixEnd_3536490 : Nat := 4983230072969 + 3 ^ 40 * 3536490 * 2
def baseEnd_3536490 : Nat := 403537599959771933402441

theorem tailTrace_3536490 : CollatzResearch.WordTrace tailWord_3536490 prefixEnd_3536490 403537599959771933402441 := by
  unfold tailWord_3536490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32246596739477047312863731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85990924638605459500969949 32246596739477047312863731)
  ·
    refine ⟨48369895109215570969295597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32246596739477047312863731 48369895109215570969295597)
    ·
      refine ⟨18138710665955839113485849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48369895109215570969295597 18138710665955839113485849)
      ·
        refine ⟨13604032999466879335114387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18138710665955839113485849 13604032999466879335114387)
        ·
          refine ⟨20406049499200319002671581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13604032999466879335114387 20406049499200319002671581)
          ·
            refine ⟨7652268562200119626001843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20406049499200319002671581 7652268562200119626001843)
            ·
              refine ⟨11478402843300179439002765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7652268562200119626001843 11478402843300179439002765)
              ·
                refine ⟨4304401066237567289626037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11478402843300179439002765 4304401066237567289626037)
                ·
                  refine ⟨403537599959771933402441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4304401066237567289626037 403537599959771933402441)
                  ·
                    rfl

theorem cell22_3536490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_3536490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536490 prefixEnd_3536490 := by exact prefixLift 3536490
  have htrace : WordTrace (prefixWord ++ tailWord_3536490) baseStart_3536490 baseEnd_3536490 := by
    simpa [prefixWord, tailWord_3536490, baseEnd_3536490] using wordTrace_append hprefix tailTrace_3536490
  have hstable : (prefixWord ++ tailWord_3536490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536490).length < 2 ^ (prefixWord ++ tailWord_3536490).sum := by decide
  have hdescent : baseEnd_3536490 < baseStart_3536490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536642 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3536642 : Nat := 118140960795 + 3536642 * 2 ^ 59
def prefixEnd_3536642 : Nat := 4983230072969 + 3 ^ 40 * 3536642 * 2
def baseEnd_3536642 : Nat := 403554944195212690135619

theorem tailTrace_3536642 : CollatzResearch.WordTrace tailWord_3536642 prefixEnd_3536642 403554944195212690135619 := by
  unfold tailWord_3536642
  simp only [CollatzResearch.WordTrace]
  refine ⟨32247982713339379802747045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85994620568905012807325453 32247982713339379802747045)
  ·
    refine ⟨6046496758751133713015071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32247982713339379802747045 6046496758751133713015071)
    ·
      refine ⟨9069745138126700569522607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046496758751133713015071 9069745138126700569522607)
      ·
        refine ⟨13604617707190050854283911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9069745138126700569522607 13604617707190050854283911)
        ·
          refine ⟨20406926560785076281425867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13604617707190050854283911 20406926560785076281425867)
          ·
            refine ⟨30610389841177614422138801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20406926560785076281425867 30610389841177614422138801)
            ·
              refine ⟨22957792380883210816604101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30610389841177614422138801 22957792380883210816604101)
              ·
                refine ⟨4304586071415602028113269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22957792380883210816604101 4304586071415602028113269)
                ·
                  refine ⟨403554944195212690135619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4304586071415602028113269 403554944195212690135619)
                  ·
                    rfl

theorem cell22_3536642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3536642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536642 prefixEnd_3536642 := by exact prefixLift 3536642
  have htrace : WordTrace (prefixWord ++ tailWord_3536642) baseStart_3536642 baseEnd_3536642 := by
    simpa [prefixWord, tailWord_3536642, baseEnd_3536642] using wordTrace_append hprefix tailTrace_3536642
  have hstable : (prefixWord ++ tailWord_3536642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536642).length < 2 ^ (prefixWord ++ tailWord_3536642).sum := by decide
  have hdescent : baseEnd_3536642 < baseStart_3536642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536689 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 1, 4]
def baseStart_3536689 : Nat := 118140960795 + 3536689 * 2 ^ 59
def prefixEnd_3536689 : Nat := 4983230072969 + 3 ^ 40 * 3536689 * 2
def baseEnd_3536689 : Nat := 1210680921646145614481713

theorem tailTrace_3536689 : CollatzResearch.WordTrace tailWord_3536689 prefixEnd_3536689 1210680921646145614481713 := by
  unfold tailWord_3536689
  simp only [CollatzResearch.WordTrace]
  refine ⟨128993645084187246237949121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85995763389458164158632747 128993645084187246237949121)
  ·
    refine ⟨96745233813140434678461841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128993645084187246237949121 96745233813140434678461841)
    ·
      refine ⟨72558925359855326008846381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96745233813140434678461841 72558925359855326008846381)
      ·
        refine ⟨27209597009945747253317393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72558925359855326008846381 27209597009945747253317393)
        ·
          refine ⟨20407197757459310439988045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27209597009945747253317393 20407197757459310439988045)
          ·
            refine ⟨7652699159047241414995517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20407197757459310439988045 7652699159047241414995517)
            ·
              refine ⟨2869762184642715530623319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7652699159047241414995517 2869762184642715530623319)
              ·
                refine ⟨4304643276964073295934979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869762184642715530623319 4304643276964073295934979)
                ·
                  refine ⟨6456964915446109943902469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304643276964073295934979 6456964915446109943902469)
                  ·
                    refine ⟨1210680921646145614481713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6456964915446109943902469 1210680921646145614481713)
                    ·
                      rfl

theorem cell22_3536689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_3536689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536689 prefixEnd_3536689 := by exact prefixLift 3536689
  have htrace : WordTrace (prefixWord ++ tailWord_3536689) baseStart_3536689 baseEnd_3536689 := by
    simpa [prefixWord, tailWord_3536689, baseEnd_3536689] using wordTrace_append hprefix tailTrace_3536689
  have hstable : (prefixWord ++ tailWord_3536689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536689).length < 2 ^ (prefixWord ++ tailWord_3536689).sum := by decide
  have hdescent : baseEnd_3536689 < baseStart_3536689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536805 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 8]
def baseStart_3536805 : Nat := 118140960795 + 3536805 * 2 ^ 59
def prefixEnd_3536805 : Nat := 4983230072969 + 3 ^ 40 * 3536805 * 2
def baseEnd_3536805 : Nat := 403573543605586659527119

theorem tailTrace_3536805 : CollatzResearch.WordTrace tailWord_3536805 prefixEnd_3536805 403573543605586659527119 := by
  unfold tailWord_3536805
  simp only [CollatzResearch.WordTrace]
  refine ⟨128997875951766998049171869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85998583967844665366114579 128997875951766998049171869)
  ·
    refine ⟨48374203481912624268439451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128997875951766998049171869 48374203481912624268439451)
    ·
      refine ⟨72561305222868936402659177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48374203481912624268439451 72561305222868936402659177)
      ·
        refine ⟨54420978917151702301994383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72561305222868936402659177 54420978917151702301994383)
        ·
          refine ⟨81631468375727553452991575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54420978917151702301994383 81631468375727553452991575)
          ·
            refine ⟨122447202563591330179487363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81631468375727553452991575 122447202563591330179487363)
            ·
              refine ⟨183670803845386995269231045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122447202563591330179487363 183670803845386995269231045)
              ·
                refine ⟨34438275721010061612980821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183670803845386995269231045 34438275721010061612980821)
                ·
                  refine ⟨403573543605586659527119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34438275721010061612980821 403573543605586659527119)
                  ·
                    rfl

theorem cell22_3536805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_3536805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536805 prefixEnd_3536805 := by exact prefixLift 3536805
  have htrace : WordTrace (prefixWord ++ tailWord_3536805) baseStart_3536805 baseEnd_3536805 := by
    simpa [prefixWord, tailWord_3536805, baseEnd_3536805] using wordTrace_append hprefix tailTrace_3536805
  have hstable : (prefixWord ++ tailWord_3536805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536805).length < 2 ^ (prefixWord ++ tailWord_3536805).sum := by decide
  have hdescent : baseEnd_3536805 < baseStart_3536805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536828 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 5]
def baseStart_3536828 : Nat := 118140960795 + 3536828 * 2 ^ 59
def prefixEnd_3536828 : Nat := 4983230072969 + 3 ^ 40 * 3536828 * 2
def baseEnd_3536828 : Nat := 403576168062265195085429

theorem tailTrace_3536828 : CollatzResearch.WordTrace tailWord_3536828 prefixEnd_3536828 403576168062265195085429 := by
  unfold tailWord_3536828
  simp only [CollatzResearch.WordTrace]
  refine ⟨64499357415341836488629569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85999143220455781984839425 64499357415341836488629569)
  ·
    refine ⟨48374518061506377366472177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64499357415341836488629569 48374518061506377366472177)
    ·
      refine ⟨36280888546129783024854133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48374518061506377366472177 36280888546129783024854133)
      ·
        refine ⟨3401333301199667158580075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36280888546129783024854133 3401333301199667158580075)
        ·
          refine ⟨5101999951799500737870113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401333301199667158580075 5101999951799500737870113)
          ·
            refine ⟨3826499963849625553402585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5101999951799500737870113 3826499963849625553402585)
            ·
              refine ⟨2869874972887219165051939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826499963849625553402585 2869874972887219165051939)
              ·
                refine ⟨4304812459330828747577909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869874972887219165051939 4304812459330828747577909)
                ·
                  refine ⟨403576168062265195085429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4304812459330828747577909 403576168062265195085429)
                  ·
                    rfl

theorem cell22_3536828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_3536828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536828 prefixEnd_3536828 := by exact prefixLift 3536828
  have htrace : WordTrace (prefixWord ++ tailWord_3536828) baseStart_3536828 baseEnd_3536828 := by
    simpa [prefixWord, tailWord_3536828, baseEnd_3536828] using wordTrace_append hprefix tailTrace_3536828
  have hstable : (prefixWord ++ tailWord_3536828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536828).length < 2 ^ (prefixWord ++ tailWord_3536828).sum := by decide
  have hdescent : baseEnd_3536828 < baseStart_3536828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536837 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_3536837 : Nat := 118140960795 + 3536837 * 2 ^ 59
def prefixEnd_3536837 : Nat := 4983230072969 + 3 ^ 40 * 3536837 * 2
def baseEnd_3536837 : Nat := 1210731585070722561781259

theorem tailTrace_3536837 : CollatzResearch.WordTrace tailWord_3536837 prefixEnd_3536837 1210731585070722561781259 := by
  unfold tailWord_3536837
  simp only [CollatzResearch.WordTrace]
  refine ⟨128999043087651067514336765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85999362058434045009557843 128999043087651067514336765)
  ·
    refine ⟨48374641157869150317876287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128999043087651067514336765 48374641157869150317876287)
    ·
      refine ⟨72561961736803725476814431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48374641157869150317876287 72561961736803725476814431)
      ·
        refine ⟨108842942605205588215221647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72561961736803725476814431 108842942605205588215221647)
        ·
          refine ⟨163264413907808382322832471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108842942605205588215221647 163264413907808382322832471)
          ·
            refine ⟨244896620861712573484248707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163264413907808382322832471 244896620861712573484248707)
            ·
              refine ⟨367344931292568860226373061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244896620861712573484248707 367344931292568860226373061)
              ·
                refine ⟨68877174617356661292444949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 367344931292568860226373061 68877174617356661292444949)
                ·
                  refine ⟨3228617560188593498083357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68877174617356661292444949 3228617560188593498083357)
                  ·
                    refine ⟨1210731585070722561781259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3228617560188593498083357 1210731585070722561781259)
                    ·
                      rfl

theorem cell22_3536837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_3536837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536837 prefixEnd_3536837 := by exact prefixLift 3536837
  have htrace : WordTrace (prefixWord ++ tailWord_3536837) baseStart_3536837 baseEnd_3536837 := by
    simpa [prefixWord, tailWord_3536837, baseEnd_3536837] using wordTrace_append hprefix tailTrace_3536837
  have hstable : (prefixWord ++ tailWord_3536837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536837).length < 2 ^ (prefixWord ++ tailWord_3536837).sum := by decide
  have hdescent : baseEnd_3536837 < baseStart_3536837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536897 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3536897 : Nat := 118140960795 + 3536897 * 2 ^ 59
def prefixEnd_3536897 : Nat := 4983230072969 + 3 ^ 40 * 3536897 * 2
def baseEnd_3536897 : Nat := 1210752124296902405281075

theorem tailTrace_3536897 : CollatzResearch.WordTrace tailWord_3536897 prefixEnd_3536897 1210752124296902405281075 := by
  unfold tailWord_3536897
  simp only [CollatzResearch.WordTrace]
  refine ⟨129001231467433697761520945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86000820978289131841013963 129001231467433697761520945)
  ·
    refine ⟨96750923600575273321140709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129001231467433697761520945 96750923600575273321140709)
    ·
      refine ⟨18140798175107863747713883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96750923600575273321140709 18140798175107863747713883)
      ·
        refine ⟨27211197262661795621570825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18140798175107863747713883 27211197262661795621570825)
        ·
          refine ⟨20408397946996346716178119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27211197262661795621570825 20408397946996346716178119)
          ·
            refine ⟨30612596920494520074267179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20408397946996346716178119 30612596920494520074267179)
            ·
              refine ⟨45918895380741780111400769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30612596920494520074267179 45918895380741780111400769)
              ·
                refine ⟨34439171535556335083550577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45918895380741780111400769 34439171535556335083550577)
                ·
                  refine ⟨25829378651667251312662933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34439171535556335083550577 25829378651667251312662933)
                  ·
                    refine ⟨1210752124296902405281075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25829378651667251312662933 1210752124296902405281075)
                    ·
                      rfl

theorem cell22_3536897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3536897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536897 prefixEnd_3536897 := by exact prefixLift 3536897
  have htrace : WordTrace (prefixWord ++ tailWord_3536897) baseStart_3536897 baseEnd_3536897 := by
    simpa [prefixWord, tailWord_3536897, baseEnd_3536897] using wordTrace_append hprefix tailTrace_3536897
  have hstable : (prefixWord ++ tailWord_3536897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536897).length < 2 ^ (prefixWord ++ tailWord_3536897).sum := by decide
  have hdescent : baseEnd_3536897 < baseStart_3536897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536909 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3536909 : Nat := 118140960795 + 3536909 * 2 ^ 59
def prefixEnd_3536909 : Nat := 4983230072969 + 3 ^ 40 * 3536909 * 2
def baseEnd_3536909 : Nat := 1210756232142138373981039

theorem tailTrace_3536909 : CollatzResearch.WordTrace tailWord_3536909 prefixEnd_3536909 1210756232142138373981039 := by
  unfold tailWord_3536909
  simp only [CollatzResearch.WordTrace]
  refine ⟨129001669143390223810957781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86001112762260149207305187 129001669143390223810957781)
  ·
    refine ⟨3023476620548208370569323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 129001669143390223810957781 3023476620548208370569323)
    ·
      refine ⟨4535214930822312555853985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023476620548208370569323 4535214930822312555853985)
      ·
        refine ⟨3401411198116734416890489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4535214930822312555853985 3401411198116734416890489)
        ·
          refine ⟨2551058398587550812667867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401411198116734416890489 2551058398587550812667867)
          ·
            refine ⟨3826587597881326219001801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551058398587550812667867 3826587597881326219001801)
            ·
              refine ⟨2869940698410994664251351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826587597881326219001801 2869940698410994664251351)
              ·
                refine ⟨4304911047616491996377027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869940698410994664251351 4304911047616491996377027)
                ·
                  refine ⟨6457366571424737994565541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304911047616491996377027 6457366571424737994565541)
                  ·
                    refine ⟨1210756232142138373981039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457366571424737994565541 1210756232142138373981039)
                    ·
                      rfl

theorem cell22_3536909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3536909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536909 prefixEnd_3536909 := by exact prefixLift 3536909
  have htrace : WordTrace (prefixWord ++ tailWord_3536909) baseStart_3536909 baseEnd_3536909 := by
    simpa [prefixWord, tailWord_3536909, baseEnd_3536909] using wordTrace_append hprefix tailTrace_3536909
  have hstable : (prefixWord ++ tailWord_3536909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536909).length < 2 ^ (prefixWord ++ tailWord_3536909).sum := by decide
  have hdescent : baseEnd_3536909 < baseStart_3536909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536927 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 4, 5]
def baseStart_3536927 : Nat := 118140960795 + 3536927 * 2 ^ 59
def prefixEnd_3536927 : Nat := 4983230072969 + 3 ^ 40 * 3536927 * 2
def baseEnd_3536927 : Nat := 1210762393909992327030983

theorem tailTrace_3536927 : CollatzResearch.WordTrace tailWord_3536927 prefixEnd_3536927 1210762393909992327030983 := by
  unfold tailWord_3536927
  simp only [CollatzResearch.WordTrace]
  refine ⟨129002325657325012885113035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86001550438216675256742023 129002325657325012885113035)
  ·
    refine ⟨193503488485987519327669553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129002325657325012885113035 193503488485987519327669553)
    ·
      refine ⟨145127616364490639495752165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193503488485987519327669553 145127616364490639495752165)
      ·
        refine ⟨27211428068341994905453531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145127616364490639495752165 27211428068341994905453531)
        ·
          refine ⟨40817142102512992358180297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27211428068341994905453531 40817142102512992358180297)
          ·
            refine ⟨30612856576884744268635223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40817142102512992358180297 30612856576884744268635223)
            ·
              refine ⟨45919284865327116402952835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30612856576884744268635223 45919284865327116402952835)
              ·
                refine ⟨68878927297990674604429253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45919284865327116402952835 68878927297990674604429253)
                ·
                  refine ⟨12914798868373251488330485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68878927297990674604429253 12914798868373251488330485)
                  ·
                    refine ⟨1210762393909992327030983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12914798868373251488330485 1210762393909992327030983)
                    ·
                      rfl

theorem cell22_3536927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_3536927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536927 prefixEnd_3536927 := by exact prefixLift 3536927
  have htrace : WordTrace (prefixWord ++ tailWord_3536927) baseStart_3536927 baseEnd_3536927 := by
    simpa [prefixWord, tailWord_3536927, baseEnd_3536927] using wordTrace_append hprefix tailTrace_3536927
  have hstable : (prefixWord ++ tailWord_3536927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536927).length < 2 ^ (prefixWord ++ tailWord_3536927).sum := by decide
  have hdescent : baseEnd_3536927 < baseStart_3536927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536929 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 7]
def baseStart_3536929 : Nat := 118140960795 + 3536929 * 2 ^ 59
def prefixEnd_3536929 : Nat := 4983230072969 + 3 ^ 40 * 3536929 * 2
def baseEnd_3536929 : Nat := 403587692850288329493659

theorem tailTrace_3536929 : CollatzResearch.WordTrace tailWord_3536929 prefixEnd_3536929 403587692850288329493659 := by
  unfold tailWord_3536929
  simp only [CollatzResearch.WordTrace]
  refine ⟨129002398603317767226685841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86001599068878511484457227 129002398603317767226685841)
  ·
    refine ⟨96751798952488325420014381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129002398603317767226685841 96751798952488325420014381)
    ·
      refine ⟨36281924607183122032505393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96751798952488325420014381 36281924607183122032505393)
      ·
        refine ⟨27211443455387341524379045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36281924607183122032505393 27211443455387341524379045)
        ·
          refine ⟨5102145647885126535821071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27211443455387341524379045 5102145647885126535821071)
          ·
            refine ⟨7653218471827689803731607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102145647885126535821071 7653218471827689803731607)
            ·
              refine ⟨11479827707741534705597411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7653218471827689803731607 11479827707741534705597411)
              ·
                refine ⟨17219741561612302058396117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11479827707741534705597411 17219741561612302058396117)
                ·
                  refine ⟨403587692850288329493659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17219741561612302058396117 403587692850288329493659)
                  ·
                    rfl

theorem cell22_3536929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_3536929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536929 prefixEnd_3536929 := by exact prefixLift 3536929
  have htrace : WordTrace (prefixWord ++ tailWord_3536929) baseStart_3536929 baseEnd_3536929 := by
    simpa [prefixWord, tailWord_3536929, baseEnd_3536929] using wordTrace_append hprefix tailTrace_3536929
  have hstable : (prefixWord ++ tailWord_3536929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536929).length < 2 ^ (prefixWord ++ tailWord_3536929).sum := by decide
  have hdescent : baseEnd_3536929 < baseStart_3536929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536946 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_3536946 : Nat := 118140960795 + 3536946 * 2 ^ 59
def prefixEnd_3536946 : Nat := 4983230072969 + 3 ^ 40 * 3536946 * 2
def baseEnd_3536946 : Nat := 403589632666094203601975

theorem tailTrace_3536946 : CollatzResearch.WordTrace tailWord_3536946 prefixEnd_3536946 403589632666094203601975 := by
  unfold tailWord_3536946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32250754661064044782513673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86002012429504119420036461 32250754661064044782513673)
  ·
    refine ⟨24188065995798033586885255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32250754661064044782513673 24188065995798033586885255)
    ·
      refine ⟨36282098993697050380327883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24188065995798033586885255 36282098993697050380327883)
      ·
        refine ⟨54423148490545575570491825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36282098993697050380327883 54423148490545575570491825)
        ·
          refine ⟨40817361367909181677868869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54423148490545575570491825 40817361367909181677868869)
          ·
            refine ⟨7653255256482971564600413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40817361367909181677868869 7653255256482971564600413)
            ·
              refine ⟨2869970721181114336725155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7653255256482971564600413 2869970721181114336725155)
              ·
                refine ⟨4304956081771671505087733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2869970721181114336725155 4304956081771671505087733)
                ·
                  refine ⟨403589632666094203601975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4304956081771671505087733 403589632666094203601975)
                  ·
                    rfl

theorem cell22_3536946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_3536946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536946 prefixEnd_3536946 := by exact prefixLift 3536946
  have htrace : WordTrace (prefixWord ++ tailWord_3536946) baseStart_3536946 baseEnd_3536946 := by
    simpa [prefixWord, tailWord_3536946, baseEnd_3536946] using wordTrace_append hprefix tailTrace_3536946
  have hstable : (prefixWord ++ tailWord_3536946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536946).length < 2 ^ (prefixWord ++ tailWord_3536946).sum := by decide
  have hdescent : baseEnd_3536946 < baseStart_3536946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3536959 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 1, 4]
def baseStart_3536959 : Nat := 118140960795 + 3536959 * 2 ^ 59
def prefixEnd_3536959 : Nat := 4983230072969 + 3 ^ 40 * 3536959 * 2
def baseEnd_3536959 : Nat := 1210773348163954910230885

theorem tailTrace_3536959 : CollatzResearch.WordTrace tailWord_3536959 prefixEnd_3536959 1210773348163954910230885 := by
  unfold tailWord_3536959
  simp only [CollatzResearch.WordTrace]
  refine ⟨129003492793209082350277931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86002328528806054900185287 129003492793209082350277931)
  ·
    refine ⟨193505239189813623525416897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129003492793209082350277931 193505239189813623525416897)
    ·
      refine ⟨145128929392360217644062673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193505239189813623525416897 145128929392360217644062673)
      ·
        refine ⟨108846697044270163233047005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145128929392360217644062673 108846697044270163233047005)
        ·
          refine ⟨40817511391601311212392627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108846697044270163233047005 40817511391601311212392627)
          ·
            refine ⟨61226267087401966818588941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40817511391601311212392627 61226267087401966818588941)
            ·
              refine ⟨22959850157775737556970853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61226267087401966818588941 22959850157775737556970853)
              ·
                refine ⟨4304971904582950791932035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22959850157775737556970853 4304971904582950791932035)
                ·
                  refine ⟨6457457856874426187898053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4304971904582950791932035 6457457856874426187898053)
                  ·
                    refine ⟨1210773348163954910230885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457457856874426187898053 1210773348163954910230885)
                    ·
                      rfl

theorem cell22_3536959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_3536959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3536959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3536959 prefixEnd_3536959 := by exact prefixLift 3536959
  have htrace : WordTrace (prefixWord ++ tailWord_3536959) baseStart_3536959 baseEnd_3536959 := by
    simpa [prefixWord, tailWord_3536959, baseEnd_3536959] using wordTrace_append hprefix tailTrace_3536959
  have hstable : (prefixWord ++ tailWord_3536959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3536959).length < 2 ^ (prefixWord ++ tailWord_3536959).sum := by decide
  have hdescent : baseEnd_3536959 < baseStart_3536959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3536959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537021 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_3537021 : Nat := 118140960795 + 3537021 * 2 ^ 59
def prefixEnd_3537021 : Nat := 4983230072969 + 3 ^ 40 * 3537021 * 2
def baseEnd_3537021 : Nat := 1210794572031007415180695

theorem tailTrace_3537021 : CollatzResearch.WordTrace tailWord_3537021 prefixEnd_3537021 1210794572031007415180695 := by
  unfold tailWord_3537021
  simp only [CollatzResearch.WordTrace]
  refine ⟨129005754118984466939034917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86003836079322977959356611 129005754118984466939034917)
  ·
    refine ⟨24188578897309587551069047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129005754118984466939034917 24188578897309587551069047)
    ·
      refine ⟨36282868345964381326603571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24188578897309587551069047 36282868345964381326603571)
      ·
        refine ⟨54424302518946571989905357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36282868345964381326603571 54424302518946571989905357)
        ·
          refine ⟨20409113444604964496214509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54424302518946571989905357 20409113444604964496214509)
          ·
            refine ⟨7653417541726861686080441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20409113444604964496214509 7653417541726861686080441)
            ·
              refine ⟨5740063156295146264560331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653417541726861686080441 5740063156295146264560331)
              ·
                refine ⟨8610094734442719396840497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740063156295146264560331 8610094734442719396840497)
                ·
                  refine ⟨6457571050832039547630373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8610094734442719396840497 6457571050832039547630373)
                  ·
                    refine ⟨1210794572031007415180695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457571050832039547630373 1210794572031007415180695)
                    ·
                      rfl

theorem cell22_3537021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_3537021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537021 prefixEnd_3537021 := by exact prefixLift 3537021
  have htrace : WordTrace (prefixWord ++ tailWord_3537021) baseStart_3537021 baseEnd_3537021 := by
    simpa [prefixWord, tailWord_3537021, baseEnd_3537021] using wordTrace_append hprefix tailTrace_3537021
  have hstable : (prefixWord ++ tailWord_3537021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537021).length < 2 ^ (prefixWord ++ tailWord_3537021).sum := by decide
  have hdescent : baseEnd_3537021 < baseStart_3537021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537070 : List Nat := [4, 1, 4, 2, 1, 1, 3, 6]
def baseStart_3537070 : Nat := 118140960795 + 3537070 * 2 ^ 59
def prefixEnd_3537070 : Nat := 4983230072969 + 3 ^ 40 * 3537070 * 2
def baseEnd_3537070 : Nat := 134534593970265291189505

theorem tailTrace_3537070 : CollatzResearch.WordTrace tailWord_3537070 prefixEnd_3537070 134534593970265291189505 := by
  unfold tailWord_3537070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16125942661975868538446083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86005027530537965538379109 16125942661975868538446083)
  ·
    refine ⟨24188913992963802807669125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16125942661975868538446083 24188913992963802807669125)
    ·
      refine ⟨4535421373680713026437961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24188913992963802807669125 4535421373680713026437961)
      ·
        refine ⟨3401566030260534769828471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4535421373680713026437961 3401566030260534769828471)
        ·
          refine ⟨5102349045390802154742707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3401566030260534769828471 5102349045390802154742707)
          ·
            refine ⟨7653523568086203232114061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5102349045390802154742707 7653523568086203232114061)
            ·
              refine ⟨2870071338032326212042773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7653523568086203232114061 2870071338032326212042773)
              ·
                refine ⟨134534593970265291189505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2870071338032326212042773 134534593970265291189505)
                ·
                  rfl

theorem cell22_3537070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_3537070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537070 prefixEnd_3537070 := by exact prefixLift 3537070
  have htrace : WordTrace (prefixWord ++ tailWord_3537070) baseStart_3537070 baseEnd_3537070 := by
    simpa [prefixWord, tailWord_3537070, baseEnd_3537070] using wordTrace_append hprefix tailTrace_3537070
  have hstable : (prefixWord ++ tailWord_3537070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537070).length < 2 ^ (prefixWord ++ tailWord_3537070).sum := by decide
  have hdescent : baseEnd_3537070 < baseStart_3537070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537128 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3537128 : Nat := 118140960795 + 3537128 * 2 ^ 59
def prefixEnd_3537128 : Nat := 4983230072969 + 3 ^ 40 * 3537128 * 2
def baseEnd_3537128 : Nat := 1210831200317694802755367

theorem tailTrace_3537128 : CollatzResearch.WordTrace tailWord_3537128 prefixEnd_3537128 1210831200317694802755367 := by
  unfold tailWord_3537128
  simp only [CollatzResearch.WordTrace]
  refine ⟨64504828364798412106590019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86006437819731216142120025 64504828364798412106590019)
  ·
    refine ⟨96757242547197618159885029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64504828364798412106590019 96757242547197618159885029)
    ·
      refine ⟨18141982977599553404978443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96757242547197618159885029 18141982977599553404978443)
      ·
        refine ⟨27212974466399330107467665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18141982977599553404978443 27212974466399330107467665)
        ·
          refine ⟨20409730849799497580600749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27212974466399330107467665 20409730849799497580600749)
          ·
            refine ⟨7653649068674811592725281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20409730849799497580600749 7653649068674811592725281)
            ·
              refine ⟨5740236801506108694543961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7653649068674811592725281 5740236801506108694543961)
              ·
                refine ⟨4305177601129581520907971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5740236801506108694543961 4305177601129581520907971)
                ·
                  refine ⟨6457766401694372281361957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305177601129581520907971 6457766401694372281361957)
                  ·
                    refine ⟨1210831200317694802755367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6457766401694372281361957 1210831200317694802755367)
                    ·
                      rfl

theorem cell22_3537128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3537128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537128 prefixEnd_3537128 := by exact prefixLift 3537128
  have htrace : WordTrace (prefixWord ++ tailWord_3537128) baseStart_3537128 baseEnd_3537128 := by
    simpa [prefixWord, tailWord_3537128, baseEnd_3537128] using wordTrace_append hprefix tailTrace_3537128
  have hstable : (prefixWord ++ tailWord_3537128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537128).length < 2 ^ (prefixWord ++ tailWord_3537128).sum := by decide
  have hdescent : baseEnd_3537128 < baseStart_3537128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537139 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 1, 6]
def baseStart_3537139 : Nat := 118140960795 + 3537139 * 2 ^ 59
def prefixEnd_3537139 : Nat := 4983230072969 + 3 ^ 40 * 3537139 * 2
def baseEnd_3537139 : Nat := 1210834965842494440730333

theorem tailTrace_3537139 : CollatzResearch.WordTrace tailWord_3537139 prefixEnd_3537139 1210834965842494440730333 := by
  unfold tailWord_3537139
  simp only [CollatzResearch.WordTrace]
  refine ⟨129010057932556973091830471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86006705288371315394553647 129010057932556973091830471)
  ·
    refine ⟨193515086898835459637745707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129010057932556973091830471 193515086898835459637745707)
    ·
      refine ⟨290272630348253189456618561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193515086898835459637745707 290272630348253189456618561)
      ·
        refine ⟨217704472761189892092463921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290272630348253189456618561 217704472761189892092463921)
        ·
          refine ⟨163278354570892419069347941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217704472761189892092463921 163278354570892419069347941)
          ·
            refine ⟨30614691482042328575502739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163278354570892419069347941 30614691482042328575502739)
            ·
              refine ⟨45922037223063492863254109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30614691482042328575502739 45922037223063492863254109)
              ·
                refine ⟨17220763958648809823720291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45922037223063492863254109 17220763958648809823720291)
                ·
                  refine ⟨25831145937973214735580437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17220763958648809823720291 25831145937973214735580437)
                  ·
                    refine ⟨1210834965842494440730333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25831145937973214735580437 1210834965842494440730333)
                    ·
                      rfl

theorem cell22_3537139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_3537139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537139 prefixEnd_3537139 := by exact prefixLift 3537139
  have htrace : WordTrace (prefixWord ++ tailWord_3537139) baseStart_3537139 baseEnd_3537139 := by
    simpa [prefixWord, tailWord_3537139, baseEnd_3537139] using wordTrace_append hprefix tailTrace_3537139
  have hstable : (prefixWord ++ tailWord_3537139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537139).length < 2 ^ (prefixWord ++ tailWord_3537139).sum := by decide
  have hdescent : baseEnd_3537139 < baseStart_3537139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537160 : List Nat := [2, 1, 3, 2, 3, 2, 3, 2, 4]
def baseStart_3537160 : Nat := 118140960795 + 3537160 * 2 ^ 59
def prefixEnd_3537160 : Nat := 4983230072969 + 3 ^ 40 * 3537160 * 2
def baseEnd_3537160 : Nat := 403614051523885795318423

theorem tailTrace_3537160 : CollatzResearch.WordTrace tailWord_3537160 prefixEnd_3537160 403614051523885795318423 := by
  unfold tailWord_3537160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64505411932740446839172467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86007215910320595785563289 64505411932740446839172467)
  ·
    refine ⟨96758117899110670258758701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64505411932740446839172467 96758117899110670258758701)
    ·
      refine ⟨36284294212166501347034513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96758117899110670258758701 36284294212166501347034513)
      ·
        refine ⟨27213220659124876010275885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36284294212166501347034513 27213220659124876010275885)
        ·
          refine ⟨10204957747171828503853457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27213220659124876010275885 10204957747171828503853457)
          ·
            refine ⟨7653718310378871377890093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10204957747171828503853457 7653718310378871377890093)
            ·
              refine ⟨2870144366392076766708785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7653718310378871377890093 2870144366392076766708785)
              ·
                refine ⟨2152608274794057575031589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2870144366392076766708785 2152608274794057575031589)
                ·
                  refine ⟨403614051523885795318423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152608274794057575031589 403614051523885795318423)
                  ·
                    rfl

theorem cell22_3537160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_3537160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537160 prefixEnd_3537160 := by exact prefixLift 3537160
  have htrace : WordTrace (prefixWord ++ tailWord_3537160) baseStart_3537160 baseEnd_3537160 := by
    simpa [prefixWord, tailWord_3537160, baseEnd_3537160] using wordTrace_append hprefix tailTrace_3537160
  have hstable : (prefixWord ++ tailWord_3537160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537160).length < 2 ^ (prefixWord ++ tailWord_3537160).sum := by decide
  have hdescent : baseEnd_3537160 < baseStart_3537160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537175 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 2, 3]
def baseStart_3537175 : Nat := 118140960795 + 3537175 * 2 ^ 59
def prefixEnd_3537175 : Nat := 4983230072969 + 3 ^ 40 * 3537175 * 2
def baseEnd_3537175 : Nat := 1210847289378202346830223

theorem tailTrace_3537175 : CollatzResearch.WordTrace tailWord_3537175 prefixEnd_3537175 1210847289378202346830223 := by
  unfold tailWord_3537175
  simp only [CollatzResearch.WordTrace]
  refine ⟨129011370960426551240140979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86007580640284367493427319 129011370960426551240140979)
  ·
    refine ⟨193517056440639826860211469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129011370960426551240140979 193517056440639826860211469)
    ·
      refine ⟨72568896165239935072579301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193517056440639826860211469 72568896165239935072579301)
      ·
        refine ⟨13606668030982487826108619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72568896165239935072579301 13606668030982487826108619)
        ·
          refine ⟨20410002046473731739162929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13606668030982487826108619 20410002046473731739162929)
          ·
            refine ⟨15307501534855298804372197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20410002046473731739162929 15307501534855298804372197)
            ·
              refine ⟨2870156537785368525819787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15307501534855298804372197 2870156537785368525819787)
              ·
                refine ⟨4305234806678052788729681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870156537785368525819787 4305234806678052788729681)
                ·
                  refine ⟨3228926105008539591547261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305234806678052788729681 3228926105008539591547261)
                  ·
                    refine ⟨1210847289378202346830223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3228926105008539591547261 1210847289378202346830223)
                    ·
                      rfl

theorem cell22_3537175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_3537175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537175 prefixEnd_3537175 := by exact prefixLift 3537175
  have htrace : WordTrace (prefixWord ++ tailWord_3537175) baseStart_3537175 baseEnd_3537175 := by
    simpa [prefixWord, tailWord_3537175, baseEnd_3537175] using wordTrace_append hprefix tailTrace_3537175
  have hstable : (prefixWord ++ tailWord_3537175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537175).length < 2 ^ (prefixWord ++ tailWord_3537175).sum := by decide
  have hdescent : baseEnd_3537175 < baseStart_3537175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537199 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 9]
def baseStart_3537199 : Nat := 118140960795 + 3537199 * 2 ^ 59
def prefixEnd_3537199 : Nat := 4983230072969 + 3 ^ 40 * 3537199 * 2
def baseEnd_3537199 : Nat := 403618501689558094743383

theorem tailTrace_3537199 : CollatzResearch.WordTrace tailWord_3537199 prefixEnd_3537199 403618501689558094743383 := by
  unfold tailWord_3537199
  simp only [CollatzResearch.WordTrace]
  refine ⟨129012246312339603339014651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86008164208226402226009767 129012246312339603339014651)
  ·
    refine ⟨193518369468509405008521977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129012246312339603339014651 193518369468509405008521977)
    ·
      refine ⟨145138777101382053756391483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193518369468509405008521977 145138777101382053756391483)
      ·
        refine ⟨217708165652073080634587225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145138777101382053756391483 217708165652073080634587225)
        ·
          refine ⟨163281124239054810475940419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217708165652073080634587225 163281124239054810475940419)
          ·
            refine ⟨244921686358582215713910629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163281124239054810475940419 244921686358582215713910629)
            ·
              refine ⟨45922816192234165446358243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244921686358582215713910629 45922816192234165446358243)
              ·
                refine ⟨68884224288351248169537365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45922816192234165446358243 68884224288351248169537365)
                ·
                  refine ⟨403618501689558094743383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68884224288351248169537365 403618501689558094743383)
                  ·
                    rfl

theorem cell22_3537199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 9].length) (baseStart_3537199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537199 prefixEnd_3537199 := by exact prefixLift 3537199
  have htrace : WordTrace (prefixWord ++ tailWord_3537199) baseStart_3537199 baseEnd_3537199 := by
    simpa [prefixWord, tailWord_3537199, baseEnd_3537199] using wordTrace_append hprefix tailTrace_3537199
  have hstable : (prefixWord ++ tailWord_3537199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537199).length < 2 ^ (prefixWord ++ tailWord_3537199).sum := by decide
  have hdescent : baseEnd_3537199 < baseStart_3537199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537261 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3537261 : Nat := 118140960795 + 3537261 * 2 ^ 59
def prefixEnd_3537261 : Nat := 4983230072969 + 3 ^ 40 * 3537261 * 2
def baseEnd_3537261 : Nat := 403625576311908929726653

theorem tailTrace_3537261 : CollatzResearch.WordTrace tailWord_3537261 prefixEnd_3537261 403625576311908929726653 := by
  unfold tailWord_3537261
  simp only [CollatzResearch.WordTrace]
  refine ⟨129014507638114987927771637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86009671758743325285181091 129014507638114987927771637)
  ·
    refine ⟨12095110091073280118228591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129014507638114987927771637 12095110091073280118228591)
    ·
      refine ⟨18142665136609920177342887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12095110091073280118228591 18142665136609920177342887)
      ·
        refine ⟨27213997704914880266014331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18142665136609920177342887 27213997704914880266014331)
        ·
          refine ⟨40820996557372320399021497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27213997704914880266014331 40820996557372320399021497)
          ·
            refine ⟨30615747418029240299266123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40820996557372320399021497 30615747418029240299266123)
            ·
              refine ⟨45923621127043860448899185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30615747418029240299266123 45923621127043860448899185)
              ·
                refine ⟨34442715845282895336674389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45923621127043860448899185 34442715845282895336674389)
                ·
                  refine ⟨403625576311908929726653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34442715845282895336674389 403625576311908929726653)
                  ·
                    rfl

theorem cell22_3537261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3537261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537261 prefixEnd_3537261 := by exact prefixLift 3537261
  have htrace : WordTrace (prefixWord ++ tailWord_3537261) baseStart_3537261 baseEnd_3537261 := by
    simpa [prefixWord, tailWord_3537261, baseEnd_3537261] using wordTrace_append hprefix tailTrace_3537261
  have hstable : (prefixWord ++ tailWord_3537261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537261).length < 2 ^ (prefixWord ++ tailWord_3537261).sum := by decide
  have hdescent : baseEnd_3537261 < baseStart_3537261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537291 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 1, 6]
def baseStart_3537291 : Nat := 118140960795 + 3537291 * 2 ^ 59
def prefixEnd_3537291 : Nat := 4983230072969 + 3 ^ 40 * 3537291 * 2
def baseEnd_3537291 : Nat := 1210886998548816710929867

theorem tailTrace_3537291 : CollatzResearch.WordTrace tailWord_3537291 prefixEnd_3537291 1210886998548816710929867 := by
  unfold tailWord_3537291
  simp only [CollatzResearch.WordTrace]
  refine ⟨129015601828006303051363727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86010401218670868700909151 129015601828006303051363727)
  ·
    refine ⟨193523402742009454577045591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129015601828006303051363727 193523402742009454577045591)
    ·
      refine ⟨290285104113014181865568387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193523402742009454577045591 290285104113014181865568387)
      ·
        refine ⟨435427656169521272798352581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290285104113014181865568387 435427656169521272798352581)
        ·
          refine ⟨81642685531785238649691109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435427656169521272798352581 81642685531785238649691109)
          ·
            refine ⟨15308003537209732246817083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81642685531785238649691109 15308003537209732246817083)
            ·
              refine ⟨22962005305814598370225625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15308003537209732246817083 22962005305814598370225625)
              ·
                refine ⟨17221503979360948777669219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22962005305814598370225625 17221503979360948777669219)
                ·
                  refine ⟨25832255969041423166503829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17221503979360948777669219 25832255969041423166503829)
                  ·
                    refine ⟨1210886998548816710929867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25832255969041423166503829 1210886998548816710929867)
                    ·
                      rfl

theorem cell22_3537291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_3537291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537291 prefixEnd_3537291 := by exact prefixLift 3537291
  have htrace : WordTrace (prefixWord ++ tailWord_3537291) baseStart_3537291 baseEnd_3537291 := by
    simpa [prefixWord, tailWord_3537291, baseEnd_3537291] using wordTrace_append hprefix tailTrace_3537291
  have hstable : (prefixWord ++ tailWord_3537291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537291).length < 2 ^ (prefixWord ++ tailWord_3537291).sum := by decide
  have hdescent : baseEnd_3537291 < baseStart_3537291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537336 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_3537336 : Nat := 118140960795 + 3537336 * 2 ^ 59
def prefixEnd_3537336 : Nat := 4983230072969 + 3 ^ 40 * 3537336 * 2
def baseEnd_3537336 : Nat := 1210902402968451593554729

theorem tailTrace_3537336 : CollatzResearch.WordTrace tailWord_3537336 prefixEnd_3537336 1210902402968451593554729 := by
  unfold tailWord_3537336
  simp only [CollatzResearch.WordTrace]
  refine ⟨64508621556421637868375931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86011495408562183824501241 64508621556421637868375931)
  ·
    refine ⟨96762932334632456802563897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64508621556421637868375931 96762932334632456802563897)
    ·
      refine ⟨72572199250974342601922923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96762932334632456802563897 72572199250974342601922923)
      ·
        refine ⟨108858298876461513902884385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72572199250974342601922923 108858298876461513902884385)
        ·
          refine ⟨81643724157346135427163289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108858298876461513902884385 81643724157346135427163289)
          ·
            refine ⟨61232793118009601570372467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81643724157346135427163289 61232793118009601570372467)
            ·
              refine ⟨91849189677014402355558701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61232793118009601570372467 91849189677014402355558701)
              ·
                refine ⟨34443446128880400883334513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91849189677014402355558701 34443446128880400883334513)
                ·
                  refine ⟨25832584596660300662500885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34443446128880400883334513 25832584596660300662500885)
                  ·
                    refine ⟨1210902402968451593554729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25832584596660300662500885 1210902402968451593554729)
                    ·
                      rfl

theorem cell22_3537336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_3537336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537336 prefixEnd_3537336 := by exact prefixLift 3537336
  have htrace : WordTrace (prefixWord ++ tailWord_3537336) baseStart_3537336 baseEnd_3537336 := by
    simpa [prefixWord, tailWord_3537336, baseEnd_3537336] using wordTrace_append hprefix tailTrace_3537336
  have hstable : (prefixWord ++ tailWord_3537336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537336).length < 2 ^ (prefixWord ++ tailWord_3537336).sum := by decide
  have hdescent : baseEnd_3537336 < baseStart_3537336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537383 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3537383 : Nat := 118140960795 + 3537383 * 2 ^ 59
def prefixEnd_3537383 : Nat := 4983230072969 + 3 ^ 40 * 3537383 * 2
def baseEnd_3537383 : Nat := 1210918492028959137629585

theorem tailTrace_3537383 : CollatzResearch.WordTrace tailWord_3537383 prefixEnd_3537383 1210918492028959137629585 := by
  unfold tailWord_3537383
  simp only [CollatzResearch.WordTrace]
  refine ⟨129018957343673002763712803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86012638229115335175808535 129018957343673002763712803)
  ·
    refine ⟨193528436015509504145569205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129018957343673002763712803 193528436015509504145569205)
    ·
      refine ⟨18143290876454016013647113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193528436015509504145569205 18143290876454016013647113)
      ·
        refine ⟨13607468157340512010235335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18143290876454016013647113 13607468157340512010235335)
        ·
          refine ⟨20411202236010768015353003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13607468157340512010235335 20411202236010768015353003)
          ·
            refine ⟨30616803354016152023029505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20411202236010768015353003 30616803354016152023029505)
            ·
              refine ⟨22962602515512114017272129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30616803354016152023029505 22962602515512114017272129)
              ·
                refine ⟨17221951886634085512954097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22962602515512114017272129 17221951886634085512954097)
                ·
                  refine ⟨12916463914975564134715573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17221951886634085512954097 12916463914975564134715573)
                  ·
                    refine ⟨1210918492028959137629585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12916463914975564134715573 1210918492028959137629585)
                    ·
                      rfl

theorem cell22_3537383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3537383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537383 prefixEnd_3537383 := by exact prefixLift 3537383
  have htrace : WordTrace (prefixWord ++ tailWord_3537383) baseStart_3537383 baseEnd_3537383 := by
    simpa [prefixWord, tailWord_3537383, baseEnd_3537383] using wordTrace_append hprefix tailTrace_3537383
  have hstable : (prefixWord ++ tailWord_3537383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537383).length < 2 ^ (prefixWord ++ tailWord_3537383).sum := by decide
  have hdescent : baseEnd_3537383 < baseStart_3537383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537389 : List Nat := [1, 5, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_3537389 : Nat := 118140960795 + 3537389 * 2 ^ 59
def prefixEnd_3537389 : Nat := 4983230072969 + 3 ^ 40 * 3537389 * 2
def baseEnd_3537389 : Nat := 1210920545951577121979567

theorem tailTrace_3537389 : CollatzResearch.WordTrace tailWord_3537389 prefixEnd_3537389 1210920545951577121979567 := by
  unfold tailWord_3537389
  simp only [CollatzResearch.WordTrace]
  refine ⟨129019176181651265788431221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86012784121100843858954147 129019176181651265788431221)
  ·
    refine ⟨12095547767029806167665427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129019176181651265788431221 12095547767029806167665427)
    ·
      refine ⟨18143321650544709251498141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12095547767029806167665427 18143321650544709251498141)
      ·
        refine ⟨6803745618954265969311803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18143321650544709251498141 6803745618954265969311803)
        ·
          refine ⟨10205618428431398953967705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6803745618954265969311803 10205618428431398953967705)
          ·
            refine ⟨7654213821323549215475779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10205618428431398953967705 7654213821323549215475779)
            ·
              refine ⟨11481320731985323823213669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7654213821323549215475779 11481320731985323823213669)
              ·
                refine ⟨2152747637247248216852563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11481320731985323823213669 2152747637247248216852563)
                ·
                  refine ⟨3229121455870872325278845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2152747637247248216852563 3229121455870872325278845)
                  ·
                    refine ⟨1210920545951577121979567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229121455870872325278845 1210920545951577121979567)
                    ·
                      rfl

theorem cell22_3537389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_3537389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537389 prefixEnd_3537389 := by exact prefixLift 3537389
  have htrace : WordTrace (prefixWord ++ tailWord_3537389) baseStart_3537389 baseEnd_3537389 := by
    simpa [prefixWord, tailWord_3537389, baseEnd_3537389] using wordTrace_append hprefix tailTrace_3537389
  have hstable : (prefixWord ++ tailWord_3537389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537389).length < 2 ^ (prefixWord ++ tailWord_3537389).sum := by decide
  have hdescent : baseEnd_3537389 < baseStart_3537389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537432 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 1, 4]
def baseStart_3537432 : Nat := 118140960795 + 3537432 * 2 ^ 59
def prefixEnd_3537432 : Nat := 4983230072969 + 3 ^ 40 * 3537432 * 2
def baseEnd_3537432 : Nat := 1210935265730339343154435

theorem tailTrace_3537432 : CollatzResearch.WordTrace tailWord_3537432 prefixEnd_3537432 1210935265730339343154435 := by
  unfold tailWord_3537432
  simp only [CollatzResearch.WordTrace]
  refine ⟨64510372260247742066123275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86013829680330322754831033 64510372260247742066123275)
  ·
    refine ⟨96765558390371613099184913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64510372260247742066123275 96765558390371613099184913)
    ·
      refine ⟨72574168792778709824388685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96765558390371613099184913 72574168792778709824388685)
      ·
        refine ⟨27215313297292016184145757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72574168792778709824388685 27215313297292016184145757)
        ·
          refine ⟨10205742486484506069054659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27215313297292016184145757 10205742486484506069054659)
          ·
            refine ⟨15308613729726759103581989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10205742486484506069054659 15308613729726759103581989)
            ·
              refine ⟨2870365074323767331921623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15308613729726759103581989 2870365074323767331921623)
              ·
                refine ⟨4305547611485650997882435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870365074323767331921623 4305547611485650997882435)
                ·
                  refine ⟨6458321417228476496823653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305547611485650997882435 6458321417228476496823653)
                  ·
                    refine ⟨1210935265730339343154435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6458321417228476496823653 1210935265730339343154435)
                    ·
                      rfl

theorem cell22_3537432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_3537432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537432 prefixEnd_3537432 := by exact prefixLift 3537432
  have htrace : WordTrace (prefixWord ++ tailWord_3537432) baseStart_3537432 baseEnd_3537432 := by
    simpa [prefixWord, tailWord_3537432, baseEnd_3537432] using wordTrace_append hprefix tailTrace_3537432
  have hstable : (prefixWord ++ tailWord_3537432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537432).length < 2 ^ (prefixWord ++ tailWord_3537432).sum := by decide
  have hdescent : baseEnd_3537432 < baseStart_3537432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537462 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3537462 : Nat := 118140960795 + 3537462 * 2 ^ 59
def prefixEnd_3537462 : Nat := 4983230072969 + 3 ^ 40 * 3537462 * 2
def baseEnd_3537462 : Nat := 1210945535343429264904343

theorem tailTrace_3537462 : CollatzResearch.WordTrace tailWord_3537462 prefixEnd_3537462 1210945535343429264904343 := by
  unfold tailWord_3537462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8063864919399174953489915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86014559140257866170559093 8063864919399174953489915)
  ·
    refine ⟨12095797379098762430234873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8063864919399174953489915 12095797379098762430234873)
    ·
      refine ⟨9071848034324071822676155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12095797379098762430234873 9071848034324071822676155)
      ·
        refine ⟨13607772051486107734014233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9071848034324071822676155 13607772051486107734014233)
        ·
          refine ⟨10205829038614580800510675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13607772051486107734014233 10205829038614580800510675)
          ·
            refine ⟨15308743557921871200766013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10205829038614580800510675 15308743557921871200766013)
            ·
              refine ⟨5740778834220701700287255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15308743557921871200766013 5740778834220701700287255)
              ·
                refine ⟨8611168251331052550430883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5740778834220701700287255 8611168251331052550430883)
                ·
                  refine ⟨12916752376996578825646325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8611168251331052550430883 12916752376996578825646325)
                  ·
                    refine ⟨1210945535343429264904343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12916752376996578825646325 1210945535343429264904343)
                    ·
                      rfl

theorem cell22_3537462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3537462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537462 prefixEnd_3537462 := by exact prefixLift 3537462
  have htrace : WordTrace (prefixWord ++ tailWord_3537462) baseStart_3537462 baseEnd_3537462 := by
    simpa [prefixWord, tailWord_3537462, baseEnd_3537462] using wordTrace_append hprefix tailTrace_3537462
  have hstable : (prefixWord ++ tailWord_3537462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537462).length < 2 ^ (prefixWord ++ tailWord_3537462).sum := by decide
  have hdescent : baseEnd_3537462 < baseStart_3537462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537548 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 10]
def baseStart_3537548 : Nat := 118140960795 + 3537548 * 2 ^ 59
def prefixEnd_3537548 : Nat := 4983230072969 + 3 ^ 40 * 3537548 * 2
def baseEnd_3537548 : Nat := 403658324966984569084693

theorem tailTrace_3537548 : CollatzResearch.WordTrace tailWord_3537548 prefixEnd_3537548 403658324966984569084693 := by
  unfold tailWord_3537548
  simp only [CollatzResearch.WordTrace]
  refine ⟨64512487694037617971734649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86016650258716823962312865 64512487694037617971734649)
  ·
    refine ⟨48384365770528213478800987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64512487694037617971734649 48384365770528213478800987)
    ·
      refine ⟨72576548655792320218201481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48384365770528213478800987 72576548655792320218201481)
      ·
        refine ⟨54432411491844240163651111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72576548655792320218201481 54432411491844240163651111)
        ·
          refine ⟨81648617237766360245476667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54432411491844240163651111 81648617237766360245476667)
          ·
            refine ⟨122472925856649540368215001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81648617237766360245476667 122472925856649540368215001)
            ·
              refine ⟨91854694392487155276161251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122472925856649540368215001 91854694392487155276161251)
              ·
                refine ⟨137782041588730732914241877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91854694392487155276161251 137782041588730732914241877)
                ·
                  refine ⟨403658324966984569084693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 137782041588730732914241877 403658324966984569084693)
                  ·
                    rfl

theorem cell22_3537548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_3537548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537548 prefixEnd_3537548 := by exact prefixLift 3537548
  have htrace : WordTrace (prefixWord ++ tailWord_3537548) baseStart_3537548 baseEnd_3537548 := by
    simpa [prefixWord, tailWord_3537548, baseEnd_3537548] using wordTrace_append hprefix tailTrace_3537548
  have hstable : (prefixWord ++ tailWord_3537548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537548).length < 2 ^ (prefixWord ++ tailWord_3537548).sum := by decide
  have hdescent : baseEnd_3537548 < baseStart_3537548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537582 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_3537582 : Nat := 118140960795 + 3537582 * 2 ^ 59
def prefixEnd_3537582 : Nat := 4983230072969 + 3 ^ 40 * 3537582 * 2
def baseEnd_3537582 : Nat := 403662204598596317301325

theorem tailTrace_3537582 : CollatzResearch.WordTrace tailWord_3537582 prefixEnd_3537582 403662204598596317301325 := by
  unfold tailWord_3537582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16128276933744007468775875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86017476979968039833471333 16128276933744007468775875)
  ·
    refine ⟨24192415400616011203163813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16128276933744007468775875 24192415400616011203163813)
    ·
      refine ⟨4536077887615502100593215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24192415400616011203163813 4536077887615502100593215)
      ·
        refine ⟨6804116831423253150889823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4536077887615502100593215 6804116831423253150889823)
        ·
          refine ⟨10206175247134879726334735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6804116831423253150889823 10206175247134879726334735)
          ·
            refine ⟨15309262870702319589502103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206175247134879726334735 15309262870702319589502103)
            ·
              refine ⟨22963894306053479384253155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15309262870702319589502103 22963894306053479384253155)
              ·
                refine ⟨34445841459080219076379733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22963894306053479384253155 34445841459080219076379733)
                ·
                  refine ⟨403662204598596317301325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34445841459080219076379733 403662204598596317301325)
                  ·
                    rfl

theorem cell22_3537582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_3537582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537582 prefixEnd_3537582 := by exact prefixLift 3537582
  have htrace : WordTrace (prefixWord ++ tailWord_3537582) baseStart_3537582 baseEnd_3537582 := by
    simpa [prefixWord, tailWord_3537582, baseEnd_3537582] using wordTrace_append hprefix tailTrace_3537582
  have hstable : (prefixWord ++ tailWord_3537582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537582).length < 2 ^ (prefixWord ++ tailWord_3537582).sum := by decide
  have hdescent : baseEnd_3537582 < baseStart_3537582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537601 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3537601 : Nat := 118140960795 + 3537601 * 2 ^ 59
def prefixEnd_3537601 : Nat := 4983230072969 + 3 ^ 40 * 3537601 * 2
def baseEnd_3537601 : Nat := 1210993117884079235678917

theorem tailTrace_3537601 : CollatzResearch.WordTrace tailWord_3537601 prefixEnd_3537601 1210993117884079235678917 := by
  unfold tailWord_3537601
  simp only [CollatzResearch.WordTrace]
  refine ⟨129026908456883225995148657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86017938971255483996765771 129026908456883225995148657)
  ·
    refine ⟨96770181342662419496361493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129026908456883225995148657 96770181342662419496361493)
    ·
      refine ⟨4536102250437300913891945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96770181342662419496361493 4536102250437300913891945)
      ·
        refine ⟨3402076687827975685418959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4536102250437300913891945 3402076687827975685418959)
        ·
          refine ⟨5103115031741963528128439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402076687827975685418959 5103115031741963528128439)
          ·
            refine ⟨7654672547612945292192659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103115031741963528128439 7654672547612945292192659)
            ·
              refine ⟨11482008821419417938288989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7654672547612945292192659 11482008821419417938288989)
              ·
                refine ⟨4305753308032281726858371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11482008821419417938288989 4305753308032281726858371)
                ·
                  refine ⟨6458629962048422590287557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305753308032281726858371 6458629962048422590287557)
                  ·
                    refine ⟨1210993117884079235678917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6458629962048422590287557 1210993117884079235678917)
                    ·
                      rfl

theorem cell22_3537601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3537601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537601 prefixEnd_3537601 := by exact prefixLift 3537601
  have htrace : WordTrace (prefixWord ++ tailWord_3537601) baseStart_3537601 baseEnd_3537601 := by
    simpa [prefixWord, tailWord_3537601, baseEnd_3537601] using wordTrace_append hprefix tailTrace_3537601
  have hstable : (prefixWord ++ tailWord_3537601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537601).length < 2 ^ (prefixWord ++ tailWord_3537601).sum := by decide
  have hdescent : baseEnd_3537601 < baseStart_3537601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537610 : List Nat := [3, 1, 2, 1, 4, 2, 9]
def baseStart_3537610 : Nat := 118140960795 + 3537610 * 2 ^ 59
def prefixEnd_3537610 : Nat := 4983230072969 + 3 ^ 40 * 3537610 * 2
def baseEnd_3537610 : Nat := 44851711065481711563107

theorem tailTrace_3537610 : CollatzResearch.WordTrace tailWord_3537610 prefixEnd_3537610 44851711065481711563107 := by
  unfold tailWord_3537610
  simp only [CollatzResearch.WordTrace]
  refine ⟨32256809178462655133056571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86018157809233747021484189 32256809178462655133056571)
  ·
    refine ⟨48385213767693982699584857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32256809178462655133056571 48385213767693982699584857)
    ·
      refine ⟨36288910325770487024688643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48385213767693982699584857 36288910325770487024688643)
      ·
        refine ⟨54433365488655730537032965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36288910325770487024688643 54433365488655730537032965)
        ·
          refine ⟨10206256029122949475693681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54433365488655730537032965 10206256029122949475693681)
          ·
            refine ⟨7654692021842212106770261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10206256029122949475693681 7654692021842212106770261)
            ·
              refine ⟨44851711065481711563107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7654692021842212106770261 44851711065481711563107)
              ·
                rfl

theorem cell22_3537610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 9].length) (baseStart_3537610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537610 prefixEnd_3537610 := by exact prefixLift 3537610
  have htrace : WordTrace (prefixWord ++ tailWord_3537610) baseStart_3537610 baseEnd_3537610 := by
    simpa [prefixWord, tailWord_3537610, baseEnd_3537610] using wordTrace_append hprefix tailTrace_3537610
  have hstable : (prefixWord ++ tailWord_3537610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537610).length < 2 ^ (prefixWord ++ tailWord_3537610).sum := by decide
  have hdescent : baseEnd_3537610 < baseStart_3537610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537614 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_3537614 : Nat := 118140960795 + 3537614 * 2 ^ 59
def prefixEnd_3537614 : Nat := 4983230072969 + 3 ^ 40 * 3537614 * 2
def baseEnd_3537614 : Nat := 1210997568049751535103877

theorem tailTrace_3537614 : CollatzResearch.WordTrace tailWord_3537614 prefixEnd_3537614 1210997568049751535103877 := by
  unfold tailWord_3537614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16128422825729516151921487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86018255070557419476914597 16128422825729516151921487)
  ·
    refine ⟨24192634238594274227882231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16128422825729516151921487 24192634238594274227882231)
    ·
      refine ⟨36288951357891411341823347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24192634238594274227882231 36288951357891411341823347)
      ·
        refine ⟨54433427036837117012735021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36288951357891411341823347 54433427036837117012735021)
        ·
          refine ⟨20412535138813918879775633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54433427036837117012735021 20412535138813918879775633)
          ·
            refine ⟨15309401354110439159831725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20412535138813918879775633 15309401354110439159831725)
            ·
              refine ⟨5741025507791414684936897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15309401354110439159831725 5741025507791414684936897)
              ·
                refine ⟨4305769130843561013702673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741025507791414684936897 4305769130843561013702673)
                ·
                  refine ⟨3229326848132670760277005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305769130843561013702673 3229326848132670760277005)
                  ·
                    refine ⟨1210997568049751535103877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229326848132670760277005 1210997568049751535103877)
                    ·
                      rfl

theorem cell22_3537614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_3537614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537614 prefixEnd_3537614 := by exact prefixLift 3537614
  have htrace : WordTrace (prefixWord ++ tailWord_3537614) baseStart_3537614 baseEnd_3537614 := by
    simpa [prefixWord, tailWord_3537614, baseEnd_3537614] using wordTrace_append hprefix tailTrace_3537614
  have hstable : (prefixWord ++ tailWord_3537614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537614).length < 2 ^ (prefixWord ++ tailWord_3537614).sum := by decide
  have hdescent : baseEnd_3537614 < baseStart_3537614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537719 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 1, 4]
def baseStart_3537719 : Nat := 118140960795 + 3537719 * 2 ^ 59
def prefixEnd_3537719 : Nat := 4983230072969 + 3 ^ 40 * 3537719 * 2
def baseEnd_3537719 : Nat := 1211033511695566261228555

theorem tailTrace_3537719 : CollatzResearch.WordTrace tailWord_3537719 prefixEnd_3537719 1211033511695566261228555 := by
  unfold tailWord_3537719
  simp only [CollatzResearch.WordTrace]
  refine ⟨129031212270455732147944211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86020808180303821431962807 129031212270455732147944211)
  ·
    refine ⟨193546818405683598221916317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129031212270455732147944211 193546818405683598221916317)
    ·
      refine ⟨72580056902131349333218619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193546818405683598221916317 72580056902131349333218619)
      ·
        refine ⟨108870085353197023999827929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72580056902131349333218619 108870085353197023999827929)
        ·
          refine ⟨81652564014897767999870947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108870085353197023999827929 81652564014897767999870947)
          ·
            refine ⟨122478846022346651999806421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81652564014897767999870947 122478846022346651999806421)
            ·
              refine ⟨2870597953648749656245463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 122478846022346651999806421 2870597953648749656245463)
              ·
                refine ⟨4305896930473124484368195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870597953648749656245463 4305896930473124484368195)
                ·
                  refine ⟨6458845395709686726552293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4305896930473124484368195 6458845395709686726552293)
                  ·
                    refine ⟨1211033511695566261228555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6458845395709686726552293 1211033511695566261228555)
                    ·
                      rfl

theorem cell22_3537719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_3537719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537719 prefixEnd_3537719 := by exact prefixLift 3537719
  have htrace : WordTrace (prefixWord ++ tailWord_3537719) baseStart_3537719 baseEnd_3537719 := by
    simpa [prefixWord, tailWord_3537719, baseEnd_3537719] using wordTrace_append hprefix tailTrace_3537719
  have hstable : (prefixWord ++ tailWord_3537719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537719).length < 2 ^ (prefixWord ++ tailWord_3537719).sum := by decide
  have hdescent : baseEnd_3537719 < baseStart_3537719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537749 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3537749 : Nat := 118140960795 + 3537749 * 2 ^ 59
def prefixEnd_3537749 : Nat := 4983230072969 + 3 ^ 40 * 3537749 * 2
def baseEnd_3537749 : Nat := 1211043781308656182978463

theorem tailTrace_3537749 : CollatzResearch.WordTrace tailWord_3537749 prefixEnd_3537749 1211043781308656182978463 := by
  unfold tailWord_3537749
  simp only [CollatzResearch.WordTrace]
  refine ⟨129032306460347047271536301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86021537640231364847690867 129032306460347047271536301)
  ·
    refine ⟨48387114922630142726826113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129032306460347047271536301 48387114922630142726826113)
    ·
      refine ⟨36290336191972607045119585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48387114922630142726826113 36290336191972607045119585)
      ·
        refine ⟨27217752143979455283839689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36290336191972607045119585 27217752143979455283839689)
        ·
          refine ⟨20413314107984591462879767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27217752143979455283839689 20413314107984591462879767)
          ·
            refine ⟨30619971161976887194319651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20413314107984591462879767 30619971161976887194319651)
            ·
              refine ⟨45929956742965330791479477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30619971161976887194319651 45929956742965330791479477)
              ·
                refine ⟨4305933444652999761701201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45929956742965330791479477 4305933444652999761701201)
                ·
                  refine ⟨3229450083489749821275901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4305933444652999761701201 3229450083489749821275901)
                  ·
                    refine ⟨1211043781308656182978463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229450083489749821275901 1211043781308656182978463)
                    ·
                      rfl

theorem cell22_3537749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3537749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537749 prefixEnd_3537749 := by exact prefixLift 3537749
  have htrace : WordTrace (prefixWord ++ tailWord_3537749) baseStart_3537749 baseEnd_3537749 := by
    simpa [prefixWord, tailWord_3537749, baseEnd_3537749] using wordTrace_append hprefix tailTrace_3537749
  have hstable : (prefixWord ++ tailWord_3537749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537749).length < 2 ^ (prefixWord ++ tailWord_3537749).sum := by decide
  have hdescent : baseEnd_3537749 < baseStart_3537749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537764 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_3537764 : Nat := 118140960795 + 3537764 * 2 ^ 59
def prefixEnd_3537764 : Nat := 4983230072969 + 3 ^ 40 * 3537764 * 2
def baseEnd_3537764 : Nat := 1211048916115201143853417

theorem tailTrace_3537764 : CollatzResearch.WordTrace tailWord_3537764 prefixEnd_3537764 1211048916115201143853417 := by
  unfold tailWord_3537764
  simp only [CollatzResearch.WordTrace]
  refine ⟨64516426777646352416666173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86021902370195136555554897 64516426777646352416666173)
  ·
    refine ⟨24193660041617382156249815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64516426777646352416666173 24193660041617382156249815)
    ·
      refine ⟨36290490062426073234374723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24193660041617382156249815 36290490062426073234374723)
      ·
        refine ⟨54435735093639109851562085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36290490062426073234374723 54435735093639109851562085)
        ·
          refine ⟨10206700330057333097167891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54435735093639109851562085 10206700330057333097167891)
          ·
            refine ⟨15310050495085999645751837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10206700330057333097167891 15310050495085999645751837)
            ·
              refine ⟨5741268935657249867156939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15310050495085999645751837 5741268935657249867156939)
              ·
                refine ⟨8611903403485874800735409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741268935657249867156939 8611903403485874800735409)
                ·
                  refine ⟨6458927552614406100551557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8611903403485874800735409 6458927552614406100551557)
                  ·
                    refine ⟨1211048916115201143853417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6458927552614406100551557 1211048916115201143853417)
                    ·
                      rfl

theorem cell22_3537764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_3537764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537764 prefixEnd_3537764 := by exact prefixLift 3537764
  have htrace : WordTrace (prefixWord ++ tailWord_3537764) baseStart_3537764 baseEnd_3537764 := by
    simpa [prefixWord, tailWord_3537764, baseEnd_3537764] using wordTrace_append hprefix tailTrace_3537764
  have hstable : (prefixWord ++ tailWord_3537764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537764).length < 2 ^ (prefixWord ++ tailWord_3537764).sum := by decide
  have hdescent : baseEnd_3537764 < baseStart_3537764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537854 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3537854 : Nat := 118140960795 + 3537854 * 2 ^ 59
def prefixEnd_3537854 : Nat := 4983230072969 + 3 ^ 40 * 3537854 * 2
def baseEnd_3537854 : Nat := 1211079724954470909103141

theorem tailTrace_3537854 : CollatzResearch.WordTrace tailWord_3537854 prefixEnd_3537854 1211079724954470909103141 := by
  unfold tailWord_3537854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16129517015620831275513577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86024090749977766802739077 16129517015620831275513577)
  ·
    refine ⟨12097137761715623456635183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16129517015620831275513577 12097137761715623456635183)
    ·
      refine ⟨18145706642573435184952775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12097137761715623456635183 18145706642573435184952775)
      ·
        refine ⟨27218559963860152777429163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18145706642573435184952775 27218559963860152777429163)
        ·
          refine ⟨40827839945790229166143745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27218559963860152777429163 40827839945790229166143745)
          ·
            refine ⟨30620879959342671874607809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40827839945790229166143745 30620879959342671874607809)
            ·
              refine ⟨22965659969507003905955857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30620879959342671874607809 22965659969507003905955857)
              ·
                refine ⟨17224244977130252929466893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22965659969507003905955857 17224244977130252929466893)
                ·
                  refine ⟨6459091866423844848550085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17224244977130252929466893 6459091866423844848550085)
                  ·
                    refine ⟨1211079724954470909103141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6459091866423844848550085 1211079724954470909103141)
                    ·
                      rfl

theorem cell22_3537854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3537854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537854 prefixEnd_3537854 := by exact prefixLift 3537854
  have htrace : WordTrace (prefixWord ++ tailWord_3537854) baseStart_3537854 baseEnd_3537854 := by
    simpa [prefixWord, tailWord_3537854, baseEnd_3537854] using wordTrace_append hprefix tailTrace_3537854
  have hstable : (prefixWord ++ tailWord_3537854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537854).length < 2 ^ (prefixWord ++ tailWord_3537854).sum := by decide
  have hdescent : baseEnd_3537854 < baseStart_3537854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537871 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 1, 4]
def baseStart_3537871 : Nat := 118140960795 + 3537871 * 2 ^ 59
def prefixEnd_3537871 : Nat := 4983230072969 + 3 ^ 40 * 3537871 * 2
def baseEnd_3537871 : Nat := 1211085544401888531428089

theorem tailTrace_3537871 : CollatzResearch.WordTrace tailWord_3537871 prefixEnd_3537871 1211085544401888531428089 := by
  unfold tailWord_3537871
  simp only [CollatzResearch.WordTrace]
  refine ⟨129036756165905062107477467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86024504110603374738318311 129036756165905062107477467)
  ·
    refine ⟨193555134248857593161216201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129036756165905062107477467 193555134248857593161216201)
    ·
      refine ⟨145166350686643194870912151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193555134248857593161216201 145166350686643194870912151)
      ·
        refine ⟨217749526029964792306368227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145166350686643194870912151 217749526029964792306368227)
        ·
          refine ⟨326624289044947188459552341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217749526029964792306368227 326624289044947188459552341)
          ·
            refine ⟨3827628387245474864760379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 326624289044947188459552341 3827628387245474864760379)
            ·
              refine ⟨5741442580868212297140569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827628387245474864760379 5741442580868212297140569)
              ·
                refine ⟨4306081935651159222855427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741442580868212297140569 4306081935651159222855427)
                ·
                  refine ⟨6459122903476738834283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306081935651159222855427 6459122903476738834283141)
                  ·
                    refine ⟨1211085544401888531428089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6459122903476738834283141 1211085544401888531428089)
                    ·
                      rfl

theorem cell22_3537871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_3537871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537871 prefixEnd_3537871 := by exact prefixLift 3537871
  have htrace : WordTrace (prefixWord ++ tailWord_3537871) baseStart_3537871 baseEnd_3537871 := by
    simpa [prefixWord, tailWord_3537871, baseEnd_3537871] using wordTrace_append hprefix tailTrace_3537871
  have hstable : (prefixWord ++ tailWord_3537871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537871).length < 2 ^ (prefixWord ++ tailWord_3537871).sum := by decide
  have hdescent : baseEnd_3537871 < baseStart_3537871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537903 : List Nat := [1, 1, 2, 1, 4, 5, 2, 2, 4]
def baseStart_3537903 : Nat := 118140960795 + 3537903 * 2 ^ 59
def prefixEnd_3537903 : Nat := 4983230072969 + 3 ^ 40 * 3537903 * 2
def baseEnd_3537903 : Nat := 403698832885283704875997

theorem tailTrace_3537903 : CollatzResearch.WordTrace tailWord_3537903 prefixEnd_3537903 403698832885283704875997 := by
  unfold tailWord_3537903
  simp only [CollatzResearch.WordTrace]
  refine ⟨129037923301789131572642363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86025282201192754381761575 129037923301789131572642363)
  ·
    refine ⟨193556884952683697358963545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129037923301789131572642363 193556884952683697358963545)
    ·
      refine ⟨145167663714512773019222659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193556884952683697358963545 145167663714512773019222659)
      ·
        refine ⟨217751495571769159528833989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145167663714512773019222659 217751495571769159528833989)
        ·
          refine ⟨40828405419706717411656373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217751495571769159528833989 40828405419706717411656373)
          ·
            refine ⟨3827663008097504757342785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40828405419706717411656373 3827663008097504757342785)
            ·
              refine ⟨2870747256073128568007089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3827663008097504757342785 2870747256073128568007089)
              ·
                refine ⟨2153060442054846426005317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2870747256073128568007089 2153060442054846426005317)
                ·
                  refine ⟨403698832885283704875997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153060442054846426005317 403698832885283704875997)
                  ·
                    rfl

theorem cell22_3537903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 4].length) (baseStart_3537903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537903 prefixEnd_3537903 := by exact prefixLift 3537903
  have htrace : WordTrace (prefixWord ++ tailWord_3537903) baseStart_3537903 baseEnd_3537903 := by
    simpa [prefixWord, tailWord_3537903, baseEnd_3537903] using wordTrace_append hprefix tailTrace_3537903
  have hstable : (prefixWord ++ tailWord_3537903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537903).length < 2 ^ (prefixWord ++ tailWord_3537903).sum := by decide
  have hdescent : baseEnd_3537903 < baseStart_3537903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537912 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_3537912 : Nat := 118140960795 + 3537912 * 2 ^ 59
def prefixEnd_3537912 : Nat := 4983230072969 + 3 ^ 40 * 3537912 * 2
def baseEnd_3537912 : Nat := 1211099579539778091152963

theorem tailTrace_3537912 : CollatzResearch.WordTrace tailWord_3537912 prefixEnd_3537912 1211099579539778091152963 := by
  unfold tailWord_3537912
  simp only [CollatzResearch.WordTrace]
  refine ⟨64519125779378263054859995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86025501039171017406479993 64519125779378263054859995)
  ·
    refine ⟨96778688669067394582289993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64519125779378263054859995 96778688669067394582289993)
    ·
      refine ⟨72584016501800545936717495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96778688669067394582289993 72584016501800545936717495)
      ·
        refine ⟨108876024752700818905076243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72584016501800545936717495 108876024752700818905076243)
        ·
          refine ⟨163314037129051228357614365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108876024752700818905076243 163314037129051228357614365)
          ·
            refine ⟨61242763923394210634105387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163314037129051228357614365 61242763923394210634105387)
            ·
              refine ⟨91864145885091315951158081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61242763923394210634105387 91864145885091315951158081)
              ·
                refine ⟨68898109413818486963368561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91864145885091315951158081 68898109413818486963368561)
                ·
                  refine ⟨51673582060363865222526421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68898109413818486963368561 51673582060363865222526421)
                  ·
                    refine ⟨1211099579539778091152963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51673582060363865222526421 1211099579539778091152963)
                    ·
                      rfl

theorem cell22_3537912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_3537912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537912 prefixEnd_3537912 := by exact prefixLift 3537912
  have htrace : WordTrace (prefixWord ++ tailWord_3537912) baseStart_3537912 baseEnd_3537912 := by
    simpa [prefixWord, tailWord_3537912, baseEnd_3537912] using wordTrace_append hprefix tailTrace_3537912
  have hstable : (prefixWord ++ tailWord_3537912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537912).length < 2 ^ (prefixWord ++ tailWord_3537912).sum := by decide
  have hdescent : baseEnd_3537912 < baseStart_3537912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537918 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3537918 : Nat := 118140960795 + 3537918 * 2 ^ 59
def prefixEnd_3537918 : Nat := 4983230072969 + 3 ^ 40 * 3537918 * 2
def baseEnd_3537918 : Nat := 1211101633462396075502945

theorem tailTrace_3537918 : CollatzResearch.WordTrace tailWord_3537918 prefixEnd_3537918 1211101633462396075502945 := by
  unfold tailWord_3537918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16129808799591848641804801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86025646931156526089625605 16129808799591848641804801)
  ·
    refine ⟨12097356599693886481353601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16129808799591848641804801 12097356599693886481353601)
    ·
      refine ⟨9073017449770414861015201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12097356599693886481353601 9073017449770414861015201)
      ·
        refine ⟨6804763087327811145761401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9073017449770414861015201 6804763087327811145761401)
        ·
          refine ⟨5103572315495858359321051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6804763087327811145761401 5103572315495858359321051)
          ·
            refine ⟨7655358473243787538981577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103572315495858359321051 7655358473243787538981577)
            ·
              refine ⟨5741518854932840654236183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7655358473243787538981577 5741518854932840654236183)
              ·
                refine ⟨8612278282399260981354275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741518854932840654236183 8612278282399260981354275)
                ·
                  refine ⟨12918417423598891472031413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8612278282399260981354275 12918417423598891472031413)
                  ·
                    refine ⟨1211101633462396075502945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12918417423598891472031413 1211101633462396075502945)
                    ·
                      rfl

theorem cell22_3537918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3537918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537918 prefixEnd_3537918 := by exact prefixLift 3537918
  have htrace : WordTrace (prefixWord ++ tailWord_3537918) baseStart_3537918 baseEnd_3537918 := by
    simpa [prefixWord, tailWord_3537918, baseEnd_3537918] using wordTrace_append hprefix tailTrace_3537918
  have hstable : (prefixWord ++ tailWord_3537918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537918).length < 2 ^ (prefixWord ++ tailWord_3537918).sum := by decide
  have hdescent : baseEnd_3537918 < baseStart_3537918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537952 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 2, 3]
def baseStart_3537952 : Nat := 118140960795 + 3537952 * 2 ^ 59
def prefixEnd_3537952 : Nat := 4983230072969 + 3 ^ 40 * 3537952 * 2
def baseEnd_3537952 : Nat := 1211113272357231320152841

theorem tailTrace_3537952 : CollatzResearch.WordTrace tailWord_3537952 prefixEnd_3537952 1211113272357231320152841 := by
  unfold tailWord_3537952
  simp only [CollatzResearch.WordTrace]
  refine ⟨64519855239305806470588055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86026473652407741960784073 64519855239305806470588055)
  ·
    refine ⟨96779782858958709705882083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64519855239305806470588055 96779782858958709705882083)
    ·
      refine ⟨145169674288438064558823125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96779782858958709705882083 145169674288438064558823125)
      ·
        refine ⟨3402414241135267138097417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 145169674288438064558823125 3402414241135267138097417)
        ·
          refine ⟨2551810680851450353573063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3402414241135267138097417 2551810680851450353573063)
          ·
            refine ⟨3827716021277175530359595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551810680851450353573063 3827716021277175530359595)
            ·
              refine ⟨5741574031915763295539393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827716021277175530359595 5741574031915763295539393)
              ·
                refine ⟨4306180523936822471654545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5741574031915763295539393 4306180523936822471654545)
                ·
                  refine ⟨3229635392952616853740909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4306180523936822471654545 3229635392952616853740909)
                  ·
                    refine ⟨1211113272357231320152841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229635392952616853740909 1211113272357231320152841)
                    ·
                      rfl

theorem cell22_3537952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_3537952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537952 prefixEnd_3537952 := by exact prefixLift 3537952
  have htrace : WordTrace (prefixWord ++ tailWord_3537952) baseStart_3537952 baseEnd_3537952 := by
    simpa [prefixWord, tailWord_3537952, baseEnd_3537952] using wordTrace_append hprefix tailTrace_3537952
  have hstable : (prefixWord ++ tailWord_3537952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537952).length < 2 ^ (prefixWord ++ tailWord_3537952).sum := by decide
  have hdescent : baseEnd_3537952 < baseStart_3537952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537989 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_3537989 : Nat := 118140960795 + 3537989 * 2 ^ 59
def prefixEnd_3537989 : Nat := 4983230072969 + 3 ^ 40 * 3537989 * 2
def baseEnd_3537989 : Nat := 1211125938213375556977727

theorem tailTrace_3537989 : CollatzResearch.WordTrace tailWord_3537989 prefixEnd_3537989 1211125938213375556977727 := by
  unfold tailWord_3537989
  simp only [CollatzResearch.WordTrace]
  refine ⟨129041059979477568260273021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86027373319651712173515347 129041059979477568260273021)
  ·
    refine ⟨48390397492304088097602383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129041059979477568260273021 48390397492304088097602383)
    ·
      refine ⟨72585596238456132146403575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48390397492304088097602383 72585596238456132146403575)
      ·
        refine ⟨108878394357684198219605363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72585596238456132146403575 108878394357684198219605363)
        ·
          refine ⟨163317591536526297329408045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108878394357684198219605363 163317591536526297329408045)
          ·
            refine ⟨61244096826197361498528017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163317591536526297329408045 61244096826197361498528017)
            ·
              refine ⟨45933072619648021123896013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61244096826197361498528017 45933072619648021123896013)
              ·
                refine ⟨17224902232368007921461005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45933072619648021123896013 17224902232368007921461005)
                ·
                  refine ⟨6459338337138002970547877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17224902232368007921461005 6459338337138002970547877)
                  ·
                    refine ⟨1211125938213375556977727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6459338337138002970547877 1211125938213375556977727)
                    ·
                      rfl

theorem cell22_3537989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_3537989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537989 prefixEnd_3537989 := by exact prefixLift 3537989
  have htrace : WordTrace (prefixWord ++ tailWord_3537989) baseStart_3537989 baseEnd_3537989 := by
    simpa [prefixWord, tailWord_3537989, baseEnd_3537989] using wordTrace_append hprefix tailTrace_3537989
  have hstable : (prefixWord ++ tailWord_3537989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537989).length < 2 ^ (prefixWord ++ tailWord_3537989).sum := by decide
  have hdescent : baseEnd_3537989 < baseStart_3537989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3537997 : List Nat := [1, 6, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3537997 : Nat := 118140960795 + 3537997 * 2 ^ 59
def prefixEnd_3537997 : Nat := 4983230072969 + 3 ^ 40 * 3537997 * 2
def baseEnd_3537997 : Nat := 1211128676776866202777703

theorem tailTrace_3537997 : CollatzResearch.WordTrace tailWord_3537997 prefixEnd_3537997 1211128676776866202777703 := by
  unfold tailWord_3537997
  simp only [CollatzResearch.WordTrace]
  refine ⟨129041351763448585626564245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86027567842299057084376163 129041351763448585626564245)
  ·
    refine ⟨6048813363911652451245199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129041351763448585626564245 6048813363911652451245199)
    ·
      refine ⟨9073220045867478676867799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6048813363911652451245199 9073220045867478676867799)
      ·
        refine ⟨13609830068801218015301699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9073220045867478676867799 13609830068801218015301699)
        ·
          refine ⟨20414745103201827022952549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13609830068801218015301699 20414745103201827022952549)
          ·
            refine ⟨3827764706850342566803603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20414745103201827022952549 3827764706850342566803603)
            ·
              refine ⟨5741647060275513850205405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3827764706850342566803603 5741647060275513850205405)
              ·
                refine ⟨2153117647603317693827027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5741647060275513850205405 2153117647603317693827027)
                ·
                  refine ⟨3229676471404976540740541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153117647603317693827027 3229676471404976540740541)
                  ·
                    refine ⟨1211128676776866202777703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229676471404976540740541 1211128676776866202777703)
                    ·
                      rfl

theorem cell22_3537997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3537997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3537997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3537997 prefixEnd_3537997 := by exact prefixLift 3537997
  have htrace : WordTrace (prefixWord ++ tailWord_3537997) baseStart_3537997 baseEnd_3537997 := by
    simpa [prefixWord, tailWord_3537997, baseEnd_3537997] using wordTrace_append hprefix tailTrace_3537997
  have hstable : (prefixWord ++ tailWord_3537997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3537997).length < 2 ^ (prefixWord ++ tailWord_3537997).sum := by decide
  have hdescent : baseEnd_3537997 < baseStart_3537997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3537997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538004 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 8]
def baseStart_3538004 : Nat := 118140960795 + 3538004 * 2 ^ 59
def prefixEnd_3538004 : Nat := 4983230072969 + 3 ^ 40 * 3538004 * 2
def baseEnd_3538004 : Nat := 403710357673306839284227

theorem tailTrace_3538004 : CollatzResearch.WordTrace tailWord_3538004 prefixEnd_3538004 403710357673306839284227 := by
  unfold tailWord_3538004
  simp only [CollatzResearch.WordTrace]
  refine ⟨64520803537211612911034533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86027738049615483881379377 64520803537211612911034533)
  ·
    refine ⟨12097650663227177420818975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64520803537211612911034533 12097650663227177420818975)
    ·
      refine ⟨18146475994840766131228463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12097650663227177420818975 18146475994840766131228463)
      ·
        refine ⟨27219713992261149196842695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18146475994840766131228463 27219713992261149196842695)
        ·
          refine ⟨40829570988391723795264043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27219713992261149196842695 40829570988391723795264043)
          ·
            refine ⟨61244356482587585692896065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40829570988391723795264043 61244356482587585692896065)
            ·
              refine ⟨45933267361940689269672049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61244356482587585692896065 45933267361940689269672049)
              ·
                refine ⟨34449950521455516952254037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45933267361940689269672049 34449950521455516952254037)
                ·
                  refine ⟨403710357673306839284227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34449950521455516952254037 403710357673306839284227)
                  ·
                    rfl

theorem cell22_3538004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_3538004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538004 prefixEnd_3538004 := by exact prefixLift 3538004
  have htrace : WordTrace (prefixWord ++ tailWord_3538004) baseStart_3538004 baseEnd_3538004 := by
    simpa [prefixWord, tailWord_3538004, baseEnd_3538004] using wordTrace_append hprefix tailTrace_3538004
  have hstable : (prefixWord ++ tailWord_3538004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538004).length < 2 ^ (prefixWord ++ tailWord_3538004).sum := by decide
  have hdescent : baseEnd_3538004 < baseStart_3538004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538051 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 2, 4]
def baseStart_3538051 : Nat := 118140960795 + 3538051 * 2 ^ 59
def prefixEnd_3538051 : Nat := 4983230072969 + 3 ^ 40 * 3538051 * 2
def baseEnd_3538051 : Nat := 1211147162080428061927537

theorem tailTrace_3538051 : CollatzResearch.WordTrace tailWord_3538051 prefixEnd_3538051 1211147162080428061927537 := by
  unfold tailWord_3538051
  simp only [CollatzResearch.WordTrace]
  refine ⟨129043321305252952849030007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86028880870168635232686671 129043321305252952849030007)
  ·
    refine ⟨193564981957879429273545011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129043321305252952849030007 193564981957879429273545011)
    ·
      refine ⟨290347472936819143910317517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193564981957879429273545011 290347472936819143910317517)
      ·
        refine ⟨108880302351307178966369069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290347472936819143910317517 108880302351307178966369069)
        ·
          refine ⟨40830113381740192112388401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108880302351307178966369069 40830113381740192112388401)
          ·
            refine ⟨30622585036305144084291301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40830113381740192112388401 30622585036305144084291301)
            ·
              refine ⟨5741734694307214515804619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30622585036305144084291301 5741734694307214515804619)
              ·
                refine ⟨8612602041460821773706929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741734694307214515804619 8612602041460821773706929)
                ·
                  refine ⟨6459451531095616330280197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8612602041460821773706929 6459451531095616330280197)
                  ·
                    refine ⟨1211147162080428061927537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6459451531095616330280197 1211147162080428061927537)
                    ·
                      rfl

theorem cell22_3538051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 4].length) (baseStart_3538051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538051 prefixEnd_3538051 := by exact prefixLift 3538051
  have htrace : WordTrace (prefixWord ++ tailWord_3538051) baseStart_3538051 baseEnd_3538051 := by
    simpa [prefixWord, tailWord_3538051, baseEnd_3538051] using wordTrace_append hprefix tailTrace_3538051
  have hstable : (prefixWord ++ tailWord_3538051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538051).length < 2 ^ (prefixWord ++ tailWord_3538051).sum := by decide
  have hdescent : baseEnd_3538051 < baseStart_3538051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538098 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_3538098 : Nat := 118140960795 + 3538098 * 2 ^ 59
def prefixEnd_3538098 : Nat := 4983230072969 + 3 ^ 40 * 3538098 * 2
def baseEnd_3538098 : Nat := 1211163251140935606002393

theorem tailTrace_3538098 : CollatzResearch.WordTrace tailWord_3538098 prefixEnd_3538098 1211163251140935606002393 := by
  unfold tailWord_3538098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32261258884020669968997737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86030023690721786583993965 32261258884020669968997737)
  ·
    refine ⟨24195944163015502476748303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32261258884020669968997737 24195944163015502476748303)
    ·
      refine ⟨36293916244523253715122455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24195944163015502476748303 36293916244523253715122455)
      ·
        refine ⟨54440874366784880572683683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36293916244523253715122455 54440874366784880572683683)
        ·
          refine ⟨81661311550177320859025525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54440874366784880572683683 81661311550177320859025525)
          ·
            refine ⟨7655747957829123830533643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81661311550177320859025525 7655747957829123830533643)
            ·
              refine ⟨11483621936743685745800465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7655747957829123830533643 11483621936743685745800465)
              ·
                refine ⟨8612716452557764309350349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11483621936743685745800465 8612716452557764309350349)
                ·
                  refine ⟨3229768669709161616006381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8612716452557764309350349 3229768669709161616006381)
                  ·
                    refine ⟨1211163251140935606002393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229768669709161616006381 1211163251140935606002393)
                    ·
                      rfl

theorem cell22_3538098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_3538098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538098 prefixEnd_3538098 := by exact prefixLift 3538098
  have htrace : WordTrace (prefixWord ++ tailWord_3538098) baseStart_3538098 baseEnd_3538098 := by
    simpa [prefixWord, tailWord_3538098, baseEnd_3538098] using wordTrace_append hprefix tailTrace_3538098
  have hstable : (prefixWord ++ tailWord_3538098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538098).length < 2 ^ (prefixWord ++ tailWord_3538098).sum := by decide
  have hdescent : baseEnd_3538098 < baseStart_3538098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538132 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_3538132 : Nat := 118140960795 + 3538132 * 2 ^ 59
def prefixEnd_3538132 : Nat := 4983230072969 + 3 ^ 40 * 3538132 * 2
def baseEnd_3538132 : Nat := 1211174890035770850652289

theorem tailTrace_3538132 : CollatzResearch.WordTrace tailWord_3538132 prefixEnd_3538132 1211174890035770850652289 := by
  unfold tailWord_3538132
  simp only [CollatzResearch.WordTrace]
  refine ⟨64523137808979751841364325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86030850411973002455152433 64523137808979751841364325)
  ·
    refine ⟨12098088339183703470255811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64523137808979751841364325 12098088339183703470255811)
    ·
      refine ⟨18147132508775555205383717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12098088339183703470255811 18147132508775555205383717)
      ·
        refine ⟨3402587345395416601009447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18147132508775555205383717 3402587345395416601009447)
        ·
          refine ⟨5103881018093124901514171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402587345395416601009447 5103881018093124901514171)
          ·
            refine ⟨7655821527139687352271257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5103881018093124901514171 7655821527139687352271257)
            ·
              refine ⟨5741866145354765514203443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7655821527139687352271257 5741866145354765514203443)
              ·
                refine ⟨8612799218032148271305165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5741866145354765514203443 8612799218032148271305165)
                ·
                  refine ⟨3229799706762055601739437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8612799218032148271305165 3229799706762055601739437)
                  ·
                    refine ⟨1211174890035770850652289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229799706762055601739437 1211174890035770850652289)
                    ·
                      rfl

theorem cell22_3538132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_3538132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538132 prefixEnd_3538132 := by exact prefixLift 3538132
  have htrace : WordTrace (prefixWord ++ tailWord_3538132) baseStart_3538132 baseEnd_3538132 := by
    simpa [prefixWord, tailWord_3538132, baseEnd_3538132] using wordTrace_append hprefix tailTrace_3538132
  have hstable : (prefixWord ++ tailWord_3538132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538132).length < 2 ^ (prefixWord ++ tailWord_3538132).sum := by decide
  have hdescent : baseEnd_3538132 < baseStart_3538132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538156 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 6]
def baseStart_3538156 : Nat := 118140960795 + 3538156 * 2 ^ 59
def prefixEnd_3538156 : Nat := 4983230072969 + 3 ^ 40 * 3538156 * 2
def baseEnd_3538156 : Nat := 403727701908747596017405

theorem tailTrace_3538156 : CollatzResearch.WordTrace tailWord_3538156 prefixEnd_3538156 403727701908747596017405 := by
  unfold tailWord_3538156
  simp only [CollatzResearch.WordTrace]
  refine ⟨64523575484936277890801161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86031433979915037187734881 64523575484936277890801161)
  ·
    refine ⟨48392681613702208418100871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64523575484936277890801161 48392681613702208418100871)
    ·
      refine ⟨72589022420553312627151307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48392681613702208418100871 72589022420553312627151307)
      ·
        refine ⟨108883533630829968940726961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72589022420553312627151307 108883533630829968940726961)
        ·
          refine ⟨81662650223122476705545221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108883533630829968940726961 81662650223122476705545221)
          ·
            refine ⟨15311746916835464382289729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81662650223122476705545221 15311746916835464382289729)
            ·
              refine ⟨11483810187626598286717297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15311746916835464382289729 11483810187626598286717297)
              ·
                refine ⟨8612857640719948715037973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11483810187626598286717297 8612857640719948715037973)
                ·
                  refine ⟨403727701908747596017405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8612857640719948715037973 403727701908747596017405)
                  ·
                    rfl

theorem cell22_3538156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_3538156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538156 prefixEnd_3538156 := by exact prefixLift 3538156
  have htrace : WordTrace (prefixWord ++ tailWord_3538156) baseStart_3538156 baseEnd_3538156 := by
    simpa [prefixWord, tailWord_3538156, baseEnd_3538156] using wordTrace_append hprefix tailTrace_3538156
  have hstable : (prefixWord ++ tailWord_3538156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538156).length < 2 ^ (prefixWord ++ tailWord_3538156).sum := by decide
  have hdescent : baseEnd_3538156 < baseStart_3538156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538158 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3538158 : Nat := 118140960795 + 3538158 * 2 ^ 59
def prefixEnd_3538158 : Nat := 4983230072969 + 3 ^ 40 * 3538158 * 2
def baseEnd_3538158 : Nat := 1211183790367115449502209

theorem tailTrace_3538158 : CollatzResearch.WordTrace tailWord_3538158 prefixEnd_3538158 1211183790367115449502209 := by
  unfold tailWord_3538158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16130902989483163765396891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86031482610576873415450085 16130902989483163765396891)
  ·
    refine ⟨24196354484224745648095337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16130902989483163765396891 24196354484224745648095337)
    ·
      refine ⟨18147265863168559236071503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24196354484224745648095337 18147265863168559236071503)
      ·
        refine ⟨27220898794752838854107255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18147265863168559236071503 27220898794752838854107255)
        ·
          refine ⟨40831348192129258281160883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27220898794752838854107255 40831348192129258281160883)
          ·
            refine ⟨61247022288193887421741325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40831348192129258281160883 61247022288193887421741325)
            ·
              refine ⟨22967633358072707783152997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61247022288193887421741325 22967633358072707783152997)
              ·
                refine ⟨4306431254638632709341187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22967633358072707783152997 4306431254638632709341187)
                ·
                  refine ⟨6459646881957949064011781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4306431254638632709341187 6459646881957949064011781)
                  ·
                    refine ⟨1211183790367115449502209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6459646881957949064011781 1211183790367115449502209)
                    ·
                      rfl

theorem cell22_3538158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3538158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538158 prefixEnd_3538158 := by exact prefixLift 3538158
  have htrace : WordTrace (prefixWord ++ tailWord_3538158) baseStart_3538158 baseEnd_3538158 := by
    simpa [prefixWord, tailWord_3538158, baseEnd_3538158] using wordTrace_append hprefix tailTrace_3538158
  have hstable : (prefixWord ++ tailWord_3538158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538158).length < 2 ^ (prefixWord ++ tailWord_3538158).sum := by decide
  have hdescent : baseEnd_3538158 < baseStart_3538158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538188 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_3538188 : Nat := 118140960795 + 3538188 * 2 ^ 59
def prefixEnd_3538188 : Nat := 4983230072969 + 3 ^ 40 * 3538188 * 2
def baseEnd_3538188 : Nat := 1211194059980205371252117

theorem tailTrace_3538188 : CollatzResearch.WordTrace tailWord_3538188 prefixEnd_3538188 1211194059980205371252117 := by
  unfold tailWord_3538188
  simp only [CollatzResearch.WordTrace]
  refine ⟨64524159052878312623383609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86032212070504416831178145 64524159052878312623383609)
  ·
    refine ⟨48393119289658734467537707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64524159052878312623383609 48393119289658734467537707)
    ·
      refine ⟨72589678934488101701306561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48393119289658734467537707 72589678934488101701306561)
      ·
        refine ⟨54442259200866076275979921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72589678934488101701306561 54442259200866076275979921)
        ·
          refine ⟨40831694400649557206984941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54442259200866076275979921 40831694400649557206984941)
          ·
            refine ⟨15311885400243583952619353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40831694400649557206984941 15311885400243583952619353)
            ·
              refine ⟨11483914050182687964464515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15311885400243583952619353 11483914050182687964464515)
              ·
                refine ⟨17225871075274031946696773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11483914050182687964464515 17225871075274031946696773)
                ·
                  refine ⟨3229850826613880990005645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17225871075274031946696773 3229850826613880990005645)
                  ·
                    refine ⟨1211194059980205371252117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3229850826613880990005645 1211194059980205371252117)
                    ·
                      rfl

theorem cell22_3538188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_3538188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538188 prefixEnd_3538188 := by exact prefixLift 3538188
  have htrace : WordTrace (prefixWord ++ tailWord_3538188) baseStart_3538188 baseEnd_3538188 := by
    simpa [prefixWord, tailWord_3538188, baseEnd_3538188] using wordTrace_append hprefix tailTrace_3538188
  have hstable : (prefixWord ++ tailWord_3538188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538188).length < 2 ^ (prefixWord ++ tailWord_3538188).sum := by decide
  have hdescent : baseEnd_3538188 < baseStart_3538188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538218 : List Nat := [3, 1, 4, 2, 1, 1, 2, 8]
def baseStart_3538218 : Nat := 118140960795 + 3538218 * 2 ^ 59
def prefixEnd_3538218 : Nat := 4983230072969 + 3 ^ 40 * 3538218 * 2
def baseEnd_3538218 : Nat := 134578258843699477000225

theorem tailTrace_3538218 : CollatzResearch.WordTrace tailWord_3538218 prefixEnd_3538218 134578258843699477000225 := by
  unfold tailWord_3538218
  simp only [CollatzResearch.WordTrace]
  refine ⟨32262353073911985092589827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86032941530431960246906205 32262353073911985092589827)
  ·
    refine ⟨48393529610867977638884741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32262353073911985092589827 48393529610867977638884741)
    ·
      refine ⟨9073786802037745807290889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48393529610867977638884741 9073786802037745807290889)
      ·
        refine ⟨6805340101528309355468167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9073786802037745807290889 6805340101528309355468167)
        ·
          refine ⟨10208010152292464033202251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6805340101528309355468167 10208010152292464033202251)
          ·
            refine ⟨15312015228438696049803377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10208010152292464033202251 15312015228438696049803377)
            ·
              refine ⟨11484011421329022037352533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15312015228438696049803377 11484011421329022037352533)
              ·
                refine ⟨134578258843699477000225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11484011421329022037352533 134578258843699477000225)
                ·
                  rfl

theorem cell22_3538218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_3538218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538218 prefixEnd_3538218 := by exact prefixLift 3538218
  have htrace : WordTrace (prefixWord ++ tailWord_3538218) baseStart_3538218 baseEnd_3538218 := by
    simpa [prefixWord, tailWord_3538218, baseEnd_3538218] using wordTrace_append hprefix tailTrace_3538218
  have hstable : (prefixWord ++ tailWord_3538218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538218).length < 2 ^ (prefixWord ++ tailWord_3538218).sum := by decide
  have hdescent : baseEnd_3538218 < baseStart_3538218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538263 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 5]
def baseStart_3538263 : Nat := 118140960795 + 3538263 * 2 ^ 59
def prefixEnd_3538263 : Nat := 4983230072969 + 3 ^ 40 * 3538263 * 2
def baseEnd_3538263 : Nat := 403739911337643391875629

theorem tailTrace_3538263 : CollatzResearch.WordTrace tailWord_3538263 prefixEnd_3538263 403739911337643391875629 := by
  unfold tailWord_3538263
  simp only [CollatzResearch.WordTrace]
  refine ⟨129051053580484913055747443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86034035720323275370498295 129051053580484913055747443)
  ·
    refine ⟨193576580370727369583621165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129051053580484913055747443 193576580370727369583621165)
    ·
      refine ⟨72591217639022763593857937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193576580370727369583621165 72591217639022763593857937)
      ·
        refine ⟨54443413229267072695393453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72591217639022763593857937 54443413229267072695393453)
        ·
          refine ⟨20416279960975152260772545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54443413229267072695393453 20416279960975152260772545)
          ·
            refine ⟨15312209970731364195579409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20416279960975152260772545 15312209970731364195579409)
            ·
              refine ⟨11484157478048523146684557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15312209970731364195579409 11484157478048523146684557)
              ·
                refine ⟨4306559054268196180006709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11484157478048523146684557 4306559054268196180006709)
                ·
                  refine ⟨403739911337643391875629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4306559054268196180006709 403739911337643391875629)
                  ·
                    rfl

theorem cell22_3538263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 5].length) (baseStart_3538263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538263 prefixEnd_3538263 := by exact prefixLift 3538263
  have htrace : WordTrace (prefixWord ++ tailWord_3538263) baseStart_3538263 baseEnd_3538263 := by
    simpa [prefixWord, tailWord_3538263, baseEnd_3538263] using wordTrace_append hprefix tailTrace_3538263
  have hstable : (prefixWord ++ tailWord_3538263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538263).length < 2 ^ (prefixWord ++ tailWord_3538263).sum := by decide
  have hdescent : baseEnd_3538263 < baseStart_3538263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538269 : List Nat := [1, 4, 5, 1, 1, 1, 3, 6]
def baseStart_3538269 : Nat := 118140960795 + 3538269 * 2 ^ 59
def prefixEnd_3538269 : Nat := 4983230072969 + 3 ^ 40 * 3538269 * 2
def baseEnd_3538269 : Nat := 134580198659505351108541

theorem tailTrace_3538269 : CollatzResearch.WordTrace tailWord_3538269 prefixEnd_3538269 134580198659505351108541 := by
  unfold tailWord_3538269
  simp only [CollatzResearch.WordTrace]
  refine ⟨129051272418463176080465861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86034181612308784053643907 129051272418463176080465861)
  ·
    refine ⟨24197113578461845515087349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129051272418463176080465861 24197113578461845515087349)
    ·
      refine ⟨2268479397980798017039439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24197113578461845515087349 2268479397980798017039439)
      ·
        refine ⟨3402719096971197025559159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268479397980798017039439 3402719096971197025559159)
        ·
          refine ⟨5104078645456795538338739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3402719096971197025559159 5104078645456795538338739)
          ·
            refine ⟨7656117968185193307508109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104078645456795538338739 7656117968185193307508109)
            ·
              refine ⟨2871044238069447490315541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7656117968185193307508109 2871044238069447490315541)
              ·
                refine ⟨134580198659505351108541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2871044238069447490315541 134580198659505351108541)
                ·
                  rfl

theorem cell22_3538269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 6].length) (baseStart_3538269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538269 prefixEnd_3538269 := by exact prefixLift 3538269
  have htrace : WordTrace (prefixWord ++ tailWord_3538269) baseStart_3538269 baseEnd_3538269 := by
    simpa [prefixWord, tailWord_3538269, baseEnd_3538269] using wordTrace_append hprefix tailTrace_3538269
  have hstable : (prefixWord ++ tailWord_3538269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538269).length < 2 ^ (prefixWord ++ tailWord_3538269).sum := by decide
  have hdescent : baseEnd_3538269 < baseStart_3538269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538308 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 6]
def baseStart_3538308 : Nat := 118140960795 + 3538308 * 2 ^ 59
def prefixEnd_3538308 : Nat := 4983230072969 + 3 ^ 40 * 3538308 * 2
def baseEnd_3538308 : Nat := 403745046144188352750583

theorem tailTrace_3538308 : CollatzResearch.WordTrace tailWord_3538308 prefixEnd_3538308 403745046144188352750583 := by
  unfold tailWord_3538308
  simp only [CollatzResearch.WordTrace]
  refine ⟨64526347432660942870567789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86035129910214590494090385 64526347432660942870567789)
  ·
    refine ⟨24197380287247853576462921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64526347432660942870567789 24197380287247853576462921)
    ·
      refine ⟨18148035215435890182347191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24197380287247853576462921 18148035215435890182347191)
      ·
        refine ⟨27222052823153835273520787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18148035215435890182347191 27222052823153835273520787)
        ·
          refine ⟨40833079234730752910281181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27222052823153835273520787 40833079234730752910281181)
          ·
            refine ⟨15312404713024032341355443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40833079234730752910281181 15312404713024032341355443)
            ·
              refine ⟨22968607069536048512033165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15312404713024032341355443 22968607069536048512033165)
              ·
                refine ⟨8613227651076018192012437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22968607069536048512033165 8613227651076018192012437)
                ·
                  refine ⟨403745046144188352750583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8613227651076018192012437 403745046144188352750583)
                  ·
                    rfl

theorem cell22_3538308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_3538308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538308 prefixEnd_3538308 := by exact prefixLift 3538308
  have htrace : WordTrace (prefixWord ++ tailWord_3538308) baseStart_3538308 baseEnd_3538308 := by
    simpa [prefixWord, tailWord_3538308, baseEnd_3538308] using wordTrace_append hprefix tailTrace_3538308
  have hstable : (prefixWord ++ tailWord_3538308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538308).length < 2 ^ (prefixWord ++ tailWord_3538308).sum := by decide
  have hdescent : baseEnd_3538308 < baseStart_3538308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538537 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 3, 3]
def baseStart_3538537 : Nat := 118140960795 + 3538537 * 2 ^ 59
def prefixEnd_3538537 : Nat := 4983230072969 + 3 ^ 40 * 3538537 * 2
def baseEnd_3538537 : Nat := 1211313529812484794276047

theorem tailTrace_3538537 : CollatzResearch.WordTrace tailWord_3538537 prefixEnd_3538537 1211313529812484794276047 := by
  unfold tailWord_3538537
  simp only [CollatzResearch.WordTrace]
  refine ⟨129061047181492257851221865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86040698120994838567481243 129061047181492257851221865)
  ·
    refine ⟨96795785386119193388416399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129061047181492257851221865 96795785386119193388416399)
    ·
      refine ⟨145193678079178790082624599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96795785386119193388416399 145193678079178790082624599)
      ·
        refine ⟨217790517118768185123936899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145193678079178790082624599 217790517118768185123936899)
        ·
          refine ⟨326685775678152277685905349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217790517118768185123936899 326685775678152277685905349)
          ·
            refine ⟨61253582939653552066107253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 326685775678152277685905349 61253582939653552066107253)
            ·
              refine ⟨5742523400592520506197555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61253582939653552066107253 5742523400592520506197555)
              ·
                refine ⟨8613785100888780759296333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742523400592520506197555 8613785100888780759296333)
                ·
                  refine ⟨3230169412833292784736125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8613785100888780759296333 3230169412833292784736125)
                  ·
                    refine ⟨1211313529812484794276047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230169412833292784736125 1211313529812484794276047)
                    ·
                      rfl

theorem cell22_3538537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_3538537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538537 prefixEnd_3538537 := by exact prefixLift 3538537
  have htrace : WordTrace (prefixWord ++ tailWord_3538537) baseStart_3538537 baseEnd_3538537 := by
    simpa [prefixWord, tailWord_3538537, baseEnd_3538537] using wordTrace_append hprefix tailTrace_3538537
  have hstable : (prefixWord ++ tailWord_3538537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538537).length < 2 ^ (prefixWord ++ tailWord_3538537).sum := by decide
  have hdescent : baseEnd_3538537 < baseStart_3538537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538595 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 6]
def baseStart_3538595 : Nat := 118140960795 + 3538595 * 2 ^ 59
def prefixEnd_3538595 : Nat := 4983230072969 + 3 ^ 40 * 3538595 * 2
def baseEnd_3538595 : Nat := 403777794799263992108623

theorem tailTrace_3538595 : CollatzResearch.WordTrace tailWord_3538595 prefixEnd_3538595 403777794799263992108623 := by
  unfold tailWord_3538595
  simp only [CollatzResearch.WordTrace]
  refine ⟨129063162615282133756833239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86042108410188089171222159 129063162615282133756833239)
  ·
    refine ⟨193594743922923200635249859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129063162615282133756833239 193594743922923200635249859)
    ·
      refine ⟨290392115884384800952874789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193594743922923200635249859 290392115884384800952874789)
      ·
        refine ⟨54448521728322150178664023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290392115884384800952874789 54448521728322150178664023)
        ·
          refine ⟨81672782592483225267996035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54448521728322150178664023 81672782592483225267996035)
          ·
            refine ⟨122509173888724837901994053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81672782592483225267996035 122509173888724837901994053)
            ·
              refine ⟨22970470104135907106623885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122509173888724837901994053 22970470104135907106623885)
              ·
                refine ⟨8613926289050965164983957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22970470104135907106623885 8613926289050965164983957)
                ·
                  refine ⟨403777794799263992108623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8613926289050965164983957 403777794799263992108623)
                  ·
                    rfl

theorem cell22_3538595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 6].length) (baseStart_3538595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538595 prefixEnd_3538595 := by exact prefixLift 3538595
  have htrace : WordTrace (prefixWord ++ tailWord_3538595) baseStart_3538595 baseEnd_3538595 := by
    simpa [prefixWord, tailWord_3538595, baseEnd_3538595] using wordTrace_append hprefix tailTrace_3538595
  have hstable : (prefixWord ++ tailWord_3538595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538595).length < 2 ^ (prefixWord ++ tailWord_3538595).sum := by decide
  have hdescent : baseEnd_3538595 < baseStart_3538595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538661 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_3538661 : Nat := 118140960795 + 3538661 * 2 ^ 59
def prefixEnd_3538661 : Nat := 4983230072969 + 3 ^ 40 * 3538661 * 2
def baseEnd_3538661 : Nat := 1211355977546589804175667

theorem tailTrace_3538661 : CollatzResearch.WordTrace tailWord_3538661 prefixEnd_3538661 1211355977546589804175667 := by
  unfold tailWord_3538661
  simp only [CollatzResearch.WordTrace]
  refine ⟨129065569833043027028735837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86043713222028684685823891 129065569833043027028735837)
  ·
    refine ⟨48399588687391135135775939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129065569833043027028735837 48399588687391135135775939)
    ·
      refine ⟨72599383031086702703663909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48399588687391135135775939 72599383031086702703663909)
      ·
        refine ⟨13612384318328756756936983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72599383031086702703663909 13612384318328756756936983)
        ·
          refine ⟨20418576477493135135405475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13612384318328756756936983 20418576477493135135405475)
          ·
            refine ⟨30627864716239702703108213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20418576477493135135405475 30627864716239702703108213)
            ·
              refine ⟨2871362317147472128416395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30627864716239702703108213 2871362317147472128416395)
              ·
                refine ⟨4307043475721208192624593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871362317147472128416395 4307043475721208192624593)
                ·
                  refine ⟨3230282606790906144468445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307043475721208192624593 3230282606790906144468445)
                  ·
                    refine ⟨1211355977546589804175667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230282606790906144468445 1211355977546589804175667)
                    ·
                      rfl

theorem cell22_3538661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_3538661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538661 prefixEnd_3538661 := by exact prefixLift 3538661
  have htrace : WordTrace (prefixWord ++ tailWord_3538661) baseStart_3538661 baseEnd_3538661 := by
    simpa [prefixWord, tailWord_3538661, baseEnd_3538661] using wordTrace_append hprefix tailTrace_3538661
  have hstable : (prefixWord ++ tailWord_3538661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538661).length < 2 ^ (prefixWord ++ tailWord_3538661).sum := by decide
  have hdescent : baseEnd_3538661 < baseStart_3538661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538672 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 5, 3]
def baseStart_3538672 : Nat := 118140960795 + 3538672 * 2 ^ 59
def prefixEnd_3538672 : Nat := 4983230072969 + 3 ^ 40 * 3538672 * 2
def baseEnd_3538672 : Nat := 1211359743071389442150633

theorem tailTrace_3538672 : CollatzResearch.WordTrace tailWord_3538672 prefixEnd_3538672 1211359743071389442150633 := by
  unfold tailWord_3538672
  simp only [CollatzResearch.WordTrace]
  refine ⟨64532985518001587953693135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86043980690668783938257513 64532985518001587953693135)
  ·
    refine ⟨96799478277002381930539703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64532985518001587953693135 96799478277002381930539703)
    ·
      refine ⟨145199217415503572895809555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96799478277002381930539703 145199217415503572895809555)
      ·
        refine ⟨217798826123255359343714333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145199217415503572895809555 217798826123255359343714333)
        ·
          refine ⟨81674559796220759753892875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217798826123255359343714333 81674559796220759753892875)
          ·
            refine ⟨122511839694331139630839313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81674559796220759753892875 122511839694331139630839313)
            ·
              refine ⟨91883879770748354723129485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122511839694331139630839313 91883879770748354723129485)
              ·
                refine ⟨34456454914030633021173557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91883879770748354723129485 34456454914030633021173557)
                ·
                  refine ⟨3230292648190371845735021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34456454914030633021173557 3230292648190371845735021)
                  ·
                    refine ⟨1211359743071389442150633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230292648190371845735021 1211359743071389442150633)
                    ·
                      rfl

theorem cell22_3538672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_3538672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538672 prefixEnd_3538672 := by exact prefixLift 3538672
  have htrace : WordTrace (prefixWord ++ tailWord_3538672) baseStart_3538672 baseEnd_3538672 := by
    simpa [prefixWord, tailWord_3538672, baseEnd_3538672] using wordTrace_append hprefix tailTrace_3538672
  have hstable : (prefixWord ++ tailWord_3538672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538672).length < 2 ^ (prefixWord ++ tailWord_3538672).sum := by decide
  have hdescent : baseEnd_3538672 < baseStart_3538672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538676 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3538676 : Nat := 118140960795 + 3538676 * 2 ^ 59
def prefixEnd_3538676 : Nat := 4983230072969 + 3 ^ 40 * 3538676 * 2
def baseEnd_3538676 : Nat := 1211361112353134765050621

theorem tailTrace_3538676 : CollatzResearch.WordTrace tailWord_3538676 prefixEnd_3538676 1211361112353134765050621 := by
  unfold tailWord_3538676
  simp only [CollatzResearch.WordTrace]
  refine ⟨64533058463994342295265941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86044077951992456393687921 64533058463994342295265941)
  ·
    refine ⟨3024987115499734795090591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64533058463994342295265941 3024987115499734795090591)
    ·
      refine ⟨4537480673249602192635887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3024987115499734795090591 4537480673249602192635887)
      ·
        refine ⟨6806221009874403288953831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537480673249602192635887 6806221009874403288953831)
        ·
          refine ⟨10209331514811604933430747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806221009874403288953831 10209331514811604933430747)
          ·
            refine ⟨15313997272217407400146121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10209331514811604933430747 15313997272217407400146121)
            ·
              refine ⟨11485497954163055550109591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15313997272217407400146121 11485497954163055550109591)
              ·
                refine ⟨17228246931244583325164387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11485497954163055550109591 17228246931244583325164387)
                ·
                  refine ⟨25842370396866874987746581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17228246931244583325164387 25842370396866874987746581)
                  ·
                    refine ⟨1211361112353134765050621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25842370396866874987746581 1211361112353134765050621)
                    ·
                      rfl

theorem cell22_3538676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3538676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538676 prefixEnd_3538676 := by exact prefixLift 3538676
  have htrace : WordTrace (prefixWord ++ tailWord_3538676) baseStart_3538676 baseEnd_3538676 := by
    simpa [prefixWord, tailWord_3538676, baseEnd_3538676] using wordTrace_append hprefix tailTrace_3538676
  have hstable : (prefixWord ++ tailWord_3538676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538676).length < 2 ^ (prefixWord ++ tailWord_3538676).sum := by decide
  have hdescent : baseEnd_3538676 < baseStart_3538676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538702 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_3538702 : Nat := 118140960795 + 3538702 * 2 ^ 59
def prefixEnd_3538702 : Nat := 4983230072969 + 3 ^ 40 * 3538702 * 2
def baseEnd_3538702 : Nat := 403790004228159787966847

theorem tailTrace_3538702 : CollatzResearch.WordTrace tailWord_3538702 prefixEnd_3538702 403790004228159787966847 := by
  unfold tailWord_3538702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133383153236811378872295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86044710150596327353985573 16133383153236811378872295)
  ·
    refine ⟨24200074729855217068308443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16133383153236811378872295 24200074729855217068308443)
    ·
      refine ⟨36300112094782825602462665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24200074729855217068308443 36300112094782825602462665)
      ·
        refine ⟨27225084071087119201846999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36300112094782825602462665 27225084071087119201846999)
        ·
          refine ⟨40837626106630678802770499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27225084071087119201846999 40837626106630678802770499)
          ·
            refine ⟨61256439159946018204155749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40837626106630678802770499 61256439159946018204155749)
            ·
              refine ⟨11485582342489878413279203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61256439159946018204155749 11485582342489878413279203)
              ·
                refine ⟨17228373513734817619918805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11485582342489878413279203 17228373513734817619918805)
                ·
                  refine ⟨403790004228159787966847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17228373513734817619918805 403790004228159787966847)
                  ·
                    rfl

theorem cell22_3538702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_3538702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538702 prefixEnd_3538702 := by exact prefixLift 3538702
  have htrace : WordTrace (prefixWord ++ tailWord_3538702) baseStart_3538702 baseEnd_3538702 := by
    simpa [prefixWord, tailWord_3538702, baseEnd_3538702] using wordTrace_append hprefix tailTrace_3538702
  have hstable : (prefixWord ++ tailWord_3538702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538702).length < 2 ^ (prefixWord ++ tailWord_3538702).sum := by decide
  have hdescent : baseEnd_3538702 < baseStart_3538702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538708 : List Nat := [2, 4, 4, 1, 1, 1, 2, 7]
def baseStart_3538708 : Nat := 118140960795 + 3538708 * 2 ^ 59
def prefixEnd_3538708 : Nat := 4983230072969 + 3 ^ 40 * 3538708 * 2
def baseEnd_3538708 : Nat := 134596896289677483138947

theorem tailTrace_3538708 : CollatzResearch.WordTrace tailWord_3538708 prefixEnd_3538708 134596896289677483138947 := by
  unfold tailWord_3538708
  simp only [CollatzResearch.WordTrace]
  refine ⟨64533642031936377027848389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86044856042581836037131185 64533642031936377027848389)
  ·
    refine ⟨12100057880988070692721573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64533642031936377027848389 12100057880988070692721573)
    ·
      refine ⟨2268760852685263254885295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12100057880988070692721573 2268760852685263254885295)
      ·
        refine ⟨3403141279027894882327943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268760852685263254885295 3403141279027894882327943)
        ·
          refine ⟨5104711918541842323491915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403141279027894882327943 5104711918541842323491915)
          ·
            refine ⟨7657067877812763485237873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5104711918541842323491915 7657067877812763485237873)
            ·
              refine ⟨5742800908359572613928405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657067877812763485237873 5742800908359572613928405)
              ·
                refine ⟨134596896289677483138947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5742800908359572613928405 134596896289677483138947)
                ·
                  rfl

theorem cell22_3538708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 7].length) (baseStart_3538708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538708 prefixEnd_3538708 := by exact prefixLift 3538708
  have htrace : WordTrace (prefixWord ++ tailWord_3538708) baseStart_3538708 baseEnd_3538708 := by
    simpa [prefixWord, tailWord_3538708, baseEnd_3538708] using wordTrace_append hprefix tailTrace_3538708
  have hstable : (prefixWord ++ tailWord_3538708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538708).length < 2 ^ (prefixWord ++ tailWord_3538708).sum := by decide
  have hdescent : baseEnd_3538708 < baseStart_3538708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538762 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_3538762 : Nat := 118140960795 + 3538762 * 2 ^ 59
def prefixEnd_3538762 : Nat := 4983230072969 + 3 ^ 40 * 3538762 * 2
def baseEnd_3538762 : Nat := 1211390551910659207400357

theorem tailTrace_3538762 : CollatzResearch.WordTrace tailWord_3538762 prefixEnd_3538762 1211390551910659207400357 := by
  unfold tailWord_3538762
  simp only [CollatzResearch.WordTrace]
  refine ⟨32267313401419280319540635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86046169070451414185441693 32267313401419280319540635)
  ·
    refine ⟨48400970102128920479310953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32267313401419280319540635 48400970102128920479310953)
    ·
      refine ⟨36300727576596690359483215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48400970102128920479310953 36300727576596690359483215)
      ·
        refine ⟨54451091364895035539224823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36300727576596690359483215 54451091364895035539224823)
        ·
          refine ⟨81676637047342553308837235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54451091364895035539224823 81676637047342553308837235)
          ·
            refine ⟨122514955571013829963255853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81676637047342553308837235 122514955571013829963255853)
            ·
              refine ⟨45943108339130186236220945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122514955571013829963255853 45943108339130186236220945)
              ·
                refine ⟨34457331254347639677165709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45943108339130186236220945 34457331254347639677165709)
                ·
                  refine ⟨12921499220380364878937141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34457331254347639677165709 12921499220380364878937141)
                  ·
                    refine ⟨1211390551910659207400357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12921499220380364878937141 1211390551910659207400357)
                    ·
                      rfl

theorem cell22_3538762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_3538762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538762 prefixEnd_3538762 := by exact prefixLift 3538762
  have htrace : WordTrace (prefixWord ++ tailWord_3538762) baseStart_3538762 baseEnd_3538762 := by
    simpa [prefixWord, tailWord_3538762, baseEnd_3538762] using wordTrace_append hprefix tailTrace_3538762
  have hstable : (prefixWord ++ tailWord_3538762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538762).length < 2 ^ (prefixWord ++ tailWord_3538762).sum := by decide
  have hdescent : baseEnd_3538762 < baseStart_3538762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538777 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_3538777 : Nat := 118140960795 + 3538777 * 2 ^ 59
def prefixEnd_3538777 : Nat := 4983230072969 + 3 ^ 40 * 3538777 * 2
def baseEnd_3538777 : Nat := 1211395686717204168275311

theorem tailTrace_3538777 : CollatzResearch.WordTrace tailWord_3538777 prefixEnd_3538777 1211395686717204168275311 := by
  unfold tailWord_3538777
  simp only [CollatzResearch.WordTrace]
  refine ⟨129069800700622778839958585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86046533800415185893305723 129069800700622778839958585)
  ·
    refine ⟨96802350525467084129968939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129069800700622778839958585 96802350525467084129968939)
    ·
      refine ⟨145203525788200626194953409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96802350525467084129968939 145203525788200626194953409)
      ·
        refine ⟨108902644341150469646215057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145203525788200626194953409 108902644341150469646215057)
        ·
          refine ⟨81676983255862852234661293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108902644341150469646215057 81676983255862852234661293)
          ·
            refine ⟨30628868720948569587997985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81676983255862852234661293 30628868720948569587997985)
            ·
              refine ⟨22971651540711427190998489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30628868720948569587997985 22971651540711427190998489)
              ·
                refine ⟨17228738655533570393248867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22971651540711427190998489 17228738655533570393248867)
                ·
                  refine ⟨25843107983300355589873301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17228738655533570393248867 25843107983300355589873301)
                  ·
                    refine ⟨1211395686717204168275311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25843107983300355589873301 1211395686717204168275311)
                    ·
                      rfl

theorem cell22_3538777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_3538777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538777 prefixEnd_3538777 := by exact prefixLift 3538777
  have htrace : WordTrace (prefixWord ++ tailWord_3538777) baseStart_3538777 baseEnd_3538777 := by
    simpa [prefixWord, tailWord_3538777, baseEnd_3538777] using wordTrace_append hprefix tailTrace_3538777
  have hstable : (prefixWord ++ tailWord_3538777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538777).length < 2 ^ (prefixWord ++ tailWord_3538777).sum := by decide
  have hdescent : baseEnd_3538777 < baseStart_3538777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538798 : List Nat := [4, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_3538798 : Nat := 118140960795 + 3538798 * 2 ^ 59
def prefixEnd_3538798 : Nat := 4983230072969 + 3 ^ 40 * 3538798 * 2
def baseEnd_3538798 : Nat := 403800958482122371166749

theorem tailTrace_3538798 : CollatzResearch.WordTrace tailWord_3538798 prefixEnd_3538798 403800958482122371166749 := by
  unfold tailWord_3538798
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133820829193337428309131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86047044422364466284315365 16133820829193337428309131)
  ·
    refine ⟨24200731243790006142463697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16133820829193337428309131 24200731243790006142463697)
    ·
      refine ⟨18150548432842504606847773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24200731243790006142463697 18150548432842504606847773)
      ·
        refine ⟨6806455662315939227567915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18150548432842504606847773 6806455662315939227567915)
        ·
          refine ⟨10209683493473908841351873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6806455662315939227567915 10209683493473908841351873)
          ·
            refine ⟨7657262620105431631013905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10209683493473908841351873 7657262620105431631013905)
            ·
              refine ⟨5742946965079073723260429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657262620105431631013905 5742946965079073723260429)
              ·
                refine ⟨2153605111904652646222661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5742946965079073723260429 2153605111904652646222661)
                ·
                  refine ⟨403800958482122371166749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153605111904652646222661 403800958482122371166749)
                  ·
                    rfl

theorem cell22_3538798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_3538798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538798 prefixEnd_3538798 := by exact prefixLift 3538798
  have htrace : WordTrace (prefixWord ++ tailWord_3538798) baseStart_3538798 baseEnd_3538798 := by
    simpa [prefixWord, tailWord_3538798, baseEnd_3538798] using wordTrace_append hprefix tailTrace_3538798
  have hstable : (prefixWord ++ tailWord_3538798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538798).length < 2 ^ (prefixWord ++ tailWord_3538798).sum := by decide
  have hdescent : baseEnd_3538798 < baseStart_3538798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538830 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_3538830 : Nat := 118140960795 + 3538830 * 2 ^ 59
def prefixEnd_3538830 : Nat := 4983230072969 + 3 ^ 40 * 3538830 * 2
def baseEnd_3538830 : Nat := 1211413829700329696700149

theorem tailTrace_3538830 : CollatzResearch.WordTrace tailWord_3538830 prefixEnd_3538830 1211413829700329696700149 := by
  unfold tailWord_3538830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133966721178846111454743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86047822512953845927758629 16133966721178846111454743)
  ·
    refine ⟨24200950081768269167182115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16133966721178846111454743 24200950081768269167182115)
    ·
      refine ⟨36301425122652403750773173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24200950081768269167182115 36301425122652403750773173)
      ·
        refine ⟨3403258605248662851634985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36301425122652403750773173 3403258605248662851634985)
        ·
          refine ⟨2552443953936497138726239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3403258605248662851634985 2552443953936497138726239)
          ·
            refine ⟨3828665930904745708089359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552443953936497138726239 3828665930904745708089359)
            ·
              refine ⟨5742998896357118562134039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828665930904745708089359 5742998896357118562134039)
              ·
                refine ⟨8614498344535677843201059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5742998896357118562134039 8614498344535677843201059)
                ·
                  refine ⟨12921747516803516764801589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8614498344535677843201059 12921747516803516764801589)
                  ·
                    refine ⟨1211413829700329696700149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12921747516803516764801589 1211413829700329696700149)
                    ·
                      rfl

theorem cell22_3538830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_3538830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538830 prefixEnd_3538830 := by exact prefixLift 3538830
  have htrace : WordTrace (prefixWord ++ tailWord_3538830) baseStart_3538830 baseEnd_3538830 := by
    simpa [prefixWord, tailWord_3538830, baseEnd_3538830] using wordTrace_append hprefix tailTrace_3538830
  have hstable : (prefixWord ++ tailWord_3538830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538830).length < 2 ^ (prefixWord ++ tailWord_3538830).sum := by decide
  have hdescent : baseEnd_3538830 < baseStart_3538830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538888 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 5]
def baseStart_3538888 : Nat := 118140960795 + 3538888 * 2 ^ 59
def prefixEnd_3538888 : Nat := 4983230072969 + 3 ^ 40 * 3538888 * 2
def baseEnd_3538888 : Nat := 403811228095212292916657

theorem tailTrace_3538888 : CollatzResearch.WordTrace tailWord_3538888 prefixEnd_3538888 403811228095212292916657 := by
  unfold tailWord_3538888
  simp only [CollatzResearch.WordTrace]
  refine ⟨64536924601610322398624659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86049232802147096531499545 64536924601610322398624659)
  ·
    refine ⟨96805386902415483597936989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64536924601610322398624659 96805386902415483597936989)
    ·
      refine ⟨36302020088405806349226371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96805386902415483597936989 36302020088405806349226371)
      ·
        refine ⟨54453030132608709523839557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36302020088405806349226371 54453030132608709523839557)
        ·
          refine ⟨10209943149864133035719917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54453030132608709523839557 10209943149864133035719917)
          ·
            refine ⟨3828728681199049888394969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10209943149864133035719917 3828728681199049888394969)
            ·
              refine ⟨2871546510899287416296227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3828728681199049888394969 2871546510899287416296227)
              ·
                refine ⟨4307319766348931124444341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2871546510899287416296227 4307319766348931124444341)
                ·
                  refine ⟨403811228095212292916657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4307319766348931124444341 403811228095212292916657)
                  ·
                    rfl

theorem cell22_3538888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_3538888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538888 prefixEnd_3538888 := by exact prefixLift 3538888
  have htrace : WordTrace (prefixWord ++ tailWord_3538888) baseStart_3538888 baseEnd_3538888 := by
    simpa [prefixWord, tailWord_3538888, baseEnd_3538888] using wordTrace_append hprefix tailTrace_3538888
  have hstable : (prefixWord ++ tailWord_3538888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538888).length < 2 ^ (prefixWord ++ tailWord_3538888).sum := by decide
  have hdescent : baseEnd_3538888 < baseStart_3538888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538901 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3538901 : Nat := 118140960795 + 3538901 * 2 ^ 59
def prefixEnd_3538901 : Nat := 4983230072969 + 3 ^ 40 * 3538901 * 2
def baseEnd_3538901 : Nat := 1211438134451309178174931

theorem tailTrace_3538901 : CollatzResearch.WordTrace tailWord_3538901 prefixEnd_3538901 1211438134451309178174931 := by
  unfold tailWord_3538901
  simp only [CollatzResearch.WordTrace]
  refine ⟨129074323352173548017472557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86049548901449032011648371 129074323352173548017472557)
  ·
    refine ⟨48402871257065080506552209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129074323352173548017472557 48402871257065080506552209)
    ·
      refine ⟨36302153442798810379914157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48402871257065080506552209 36302153442798810379914157)
      ·
        refine ⟨13613307541049553892467809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36302153442798810379914157 13613307541049553892467809)
        ·
          refine ⟨10209980655787165419350857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13613307541049553892467809 10209980655787165419350857)
          ·
            refine ⟨7657485491840374064513143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10209980655787165419350857 7657485491840374064513143)
            ·
              refine ⟨11486228237760561096769715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7657485491840374064513143 11486228237760561096769715)
              ·
                refine ⟨17229342356640841645154573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11486228237760561096769715 17229342356640841645154573)
                ·
                  refine ⟨6461003383740315616932965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17229342356640841645154573 6461003383740315616932965)
                  ·
                    refine ⟨1211438134451309178174931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6461003383740315616932965 1211438134451309178174931)
                    ·
                      rfl

theorem cell22_3538901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3538901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538901 prefixEnd_3538901 := by exact prefixLift 3538901
  have htrace : WordTrace (prefixWord ++ tailWord_3538901) baseStart_3538901 baseEnd_3538901 := by
    simpa [prefixWord, tailWord_3538901, baseEnd_3538901] using wordTrace_append hprefix tailTrace_3538901
  have hstable : (prefixWord ++ tailWord_3538901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538901).length < 2 ^ (prefixWord ++ tailWord_3538901).sum := by decide
  have hdescent : baseEnd_3538901 < baseStart_3538901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538916 : List Nat := [2, 3, 1, 1, 1, 1, 4, 5, 4]
def baseStart_3538916 : Nat := 118140960795 + 3538916 * 2 ^ 59
def prefixEnd_3538916 : Nat := 4983230072969 + 3 ^ 40 * 3538916 * 2
def baseEnd_3538916 : Nat := 403814423085951379683295

theorem tailTrace_3538916 : CollatzResearch.WordTrace tailWord_3538916 prefixEnd_3538916 403814423085951379683295 := by
  unfold tailWord_3538916
  simp only [CollatzResearch.WordTrace]
  refine ⟨64537435223559602789634301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86049913631412803719512401 64537435223559602789634301)
  ·
    refine ⟨24201538208834851046112863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64537435223559602789634301 24201538208834851046112863)
    ·
      refine ⟨36302307313252276569169295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24201538208834851046112863 36302307313252276569169295)
      ·
        refine ⟨54453460969878414853753943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36302307313252276569169295 54453460969878414853753943)
        ·
          refine ⟨81680191454817622280630915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54453460969878414853753943 81680191454817622280630915)
          ·
            refine ⟨122520287182226433420946373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81680191454817622280630915 122520287182226433420946373)
            ·
              refine ⟨22972553846667456266427445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122520287182226433420946373 22972553846667456266427445)
              ·
                refine ⟨2153676923125074024977573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22972553846667456266427445 2153676923125074024977573)
                ·
                  refine ⟨403814423085951379683295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153676923125074024977573 403814423085951379683295)
                  ·
                    rfl

theorem cell22_3538916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_3538916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538916 prefixEnd_3538916 := by exact prefixLift 3538916
  have htrace : WordTrace (prefixWord ++ tailWord_3538916) baseStart_3538916 baseEnd_3538916 := by
    simpa [prefixWord, tailWord_3538916, baseEnd_3538916] using wordTrace_append hprefix tailTrace_3538916
  have hstable : (prefixWord ++ tailWord_3538916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538916).length < 2 ^ (prefixWord ++ tailWord_3538916).sum := by decide
  have hdescent : baseEnd_3538916 < baseStart_3538916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3538993 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 3, 3]
def baseStart_3538993 : Nat := 118140960795 + 3538993 * 2 ^ 59
def prefixEnd_3538993 : Nat := 4983230072969 + 3 ^ 40 * 3538993 * 2
def baseEnd_3538993 : Nat := 1211469627931451604874649

theorem tailTrace_3538993 : CollatzResearch.WordTrace tailWord_3538993 prefixEnd_3538993 1211469627931451604874649 := by
  unfold tailWord_3538993
  simp only [CollatzResearch.WordTrace]
  refine ⟨129077678867840247729821633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86051785911893498486547755 129077678867840247729821633)
  ·
    refine ⟨96808259150880185797366225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129077678867840247729821633 96808259150880185797366225)
    ·
      refine ⟨72606194363160139348024669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96808259150880185797366225 72606194363160139348024669)
      ·
        refine ⟨27227322886185052255509251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72606194363160139348024669 27227322886185052255509251)
        ·
          refine ⟨40840984329277578383263877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27227322886185052255509251 40840984329277578383263877)
          ·
            refine ⟨7657684561739545946861977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40840984329277578383263877 7657684561739545946861977)
            ·
              refine ⟨5743263421304659460146483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7657684561739545946861977 5743263421304659460146483)
              ·
                refine ⟨8614895131956989190219725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5743263421304659460146483 8614895131956989190219725)
                ·
                  refine ⟨3230585674483870946332397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8614895131956989190219725 3230585674483870946332397)
                  ·
                    refine ⟨1211469627931451604874649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230585674483870946332397 1211469627931451604874649)
                    ·
                      rfl

theorem cell22_3538993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_3538993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3538993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3538993 prefixEnd_3538993 := by exact prefixLift 3538993
  have htrace : WordTrace (prefixWord ++ tailWord_3538993) baseStart_3538993 baseEnd_3538993 := by
    simpa [prefixWord, tailWord_3538993, baseEnd_3538993] using wordTrace_append hprefix tailTrace_3538993
  have hstable : (prefixWord ++ tailWord_3538993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3538993).length < 2 ^ (prefixWord ++ tailWord_3538993).sum := by decide
  have hdescent : baseEnd_3538993 < baseStart_3538993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3538993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539096 : List Nat := [2, 1, 2, 4, 3, 10]
def baseStart_3539096 : Nat := 118140960795 + 3539096 * 2 ^ 59
def prefixEnd_3539096 : Nat := 4983230072969 + 3 ^ 40 * 3539096 * 2
def baseEnd_3539096 : Nat := 14956850456004860117893

theorem tailTrace_3539096 : CollatzResearch.WordTrace tailWord_3539096 prefixEnd_3539096 14956850456004860117893 := by
  unfold tailWord_3539096
  simp only [CollatzResearch.WordTrace]
  refine ⟨64540717793233548160410571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86054290390978064213880761 64540717793233548160410571)
  ·
    refine ⟨96811076689850322240615857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64540717793233548160410571 96811076689850322240615857)
    ·
      refine ⟨72608307517387741680461893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96811076689850322240615857 72608307517387741680461893)
      ·
        refine ⟨13614057659510201565086605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72608307517387741680461893 13614057659510201565086605)
        ·
          refine ⟨5105271622316325586907477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13614057659510201565086605 5105271622316325586907477)
          ·
            refine ⟨14956850456004860117893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5105271622316325586907477 14956850456004860117893)
            ·
              rfl

theorem cell22_3539096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 10].length) (baseStart_3539096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539096 prefixEnd_3539096 := by exact prefixLift 3539096
  have htrace : WordTrace (prefixWord ++ tailWord_3539096) baseStart_3539096 baseEnd_3539096 := by
    simpa [prefixWord, tailWord_3539096, baseEnd_3539096] using wordTrace_append hprefix tailTrace_3539096
  have hstable : (prefixWord ++ tailWord_3539096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539096).length < 2 ^ (prefixWord ++ tailWord_3539096).sum := by decide
  have hdescent : baseEnd_3539096 < baseStart_3539096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539100 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_3539100 : Nat := 118140960795 + 3539100 * 2 ^ 59
def prefixEnd_3539100 : Nat := 4983230072969 + 3 ^ 40 * 3539100 * 2
def baseEnd_3539100 : Nat := 1211506256218138992449321

theorem tailTrace_3539100 : CollatzResearch.WordTrace tailWord_3539100 prefixEnd_3539100 1211506256218138992449321 := by
  unfold tailWord_3539100
  simp only [CollatzResearch.WordTrace]
  refine ⟨64540790739226302501983377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86054387652301736669311169 64540790739226302501983377)
  ·
    refine ⟨48405593054419726876487533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64540790739226302501983377 48405593054419726876487533)
    ·
      refine ⟨18152097395407397578682825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48405593054419726876487533 18152097395407397578682825)
      ·
        refine ⟨13614073046555548184012119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18152097395407397578682825 13614073046555548184012119)
        ·
          refine ⟨20421109569833322276018179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13614073046555548184012119 20421109569833322276018179)
          ·
            refine ⟨30631664354749983414027269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20421109569833322276018179 30631664354749983414027269)
            ·
              refine ⟨5743437066515621890130113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30631664354749983414027269 5743437066515621890130113)
              ·
                refine ⟨4307577799886716417597585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5743437066515621890130113 4307577799886716417597585)
                ·
                  refine ⟨3230683349915037313198189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307577799886716417597585 3230683349915037313198189)
                  ·
                    refine ⟨1211506256218138992449321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230683349915037313198189 1211506256218138992449321)
                    ·
                      rfl

theorem cell22_3539100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_3539100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539100 prefixEnd_3539100 := by exact prefixLift 3539100
  have htrace : WordTrace (prefixWord ++ tailWord_3539100) baseStart_3539100 baseEnd_3539100 := by
    simpa [prefixWord, tailWord_3539100, baseEnd_3539100] using wordTrace_append hprefix tailTrace_3539100
  have hstable : (prefixWord ++ tailWord_3539100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539100).length < 2 ^ (prefixWord ++ tailWord_3539100).sum := by decide
  have hdescent : baseEnd_3539100 < baseStart_3539100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539102 : List Nat := [4, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3539102 : Nat := 118140960795 + 3539102 * 2 ^ 59
def prefixEnd_3539102 : Nat := 4983230072969 + 3 ^ 40 * 3539102 * 2
def baseEnd_3539102 : Nat := 403835646953003884633105

theorem tailTrace_3539102 : CollatzResearch.WordTrace tailWord_3539102 prefixEnd_3539102 403835646953003884633105 := by
  unfold tailWord_3539102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16135206803055669918192445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86054436282963572897026373 16135206803055669918192445)
  ·
    refine ⟨6050702551145876219322167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16135206803055669918192445 6050702551145876219322167)
    ·
      refine ⟨9076053826718814328983251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6050702551145876219322167 9076053826718814328983251)
      ·
        refine ⟨13614080740078221493474877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9076053826718814328983251 13614080740078221493474877)
        ·
          refine ⟨5105280277529333060053079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13614080740078221493474877 5105280277529333060053079)
          ·
            refine ⟨7657920416293999590079619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105280277529333060053079 7657920416293999590079619)
            ·
              refine ⟨11486880624440999385119429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7657920416293999590079619 11486880624440999385119429)
              ·
                refine ⟨2153790117082687384709893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11486880624440999385119429 2153790117082687384709893)
                ·
                  refine ⟨403835646953003884633105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153790117082687384709893 403835646953003884633105)
                  ·
                    rfl

theorem cell22_3539102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3539102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539102 prefixEnd_3539102 := by exact prefixLift 3539102
  have htrace : WordTrace (prefixWord ++ tailWord_3539102) baseStart_3539102 baseEnd_3539102 := by
    simpa [prefixWord, tailWord_3539102, baseEnd_3539102] using wordTrace_append hprefix tailTrace_3539102
  have hstable : (prefixWord ++ tailWord_3539102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539102).length < 2 ^ (prefixWord ++ tailWord_3539102).sum := by decide
  have hdescent : baseEnd_3539102 < baseStart_3539102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539128 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 3, 3]
def baseStart_3539128 : Nat := 118140960795 + 3539128 * 2 ^ 59
def prefixEnd_3539128 : Nat := 4983230072969 + 3 ^ 40 * 3539128 * 2
def baseEnd_3539128 : Nat := 1211515841190356252749235

theorem tailTrace_3539128 : CollatzResearch.WordTrace tailWord_3539128 prefixEnd_3539128 1211515841190356252749235 := by
  unfold tailWord_3539128
  simp only [CollatzResearch.WordTrace]
  refine ⟨64541301361175582892993019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86055068481567443857324025 64541301361175582892993019)
  ·
    refine ⟨96811952041763374339489529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64541301361175582892993019 96811952041763374339489529)
    ·
      refine ⟨72608964031322530754617147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96811952041763374339489529 72608964031322530754617147)
      ·
        refine ⟨108913446046983796131925721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72608964031322530754617147 108913446046983796131925721)
        ·
          refine ⟨81685084535237847098944291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108913446046983796131925721 81685084535237847098944291)
          ·
            refine ⟨122527626802856770648416437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81685084535237847098944291 122527626802856770648416437)
            ·
              refine ⟨11486965012767822248289041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122527626802856770648416437 11486965012767822248289041)
              ·
                refine ⟨8615223759575866686216781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11486965012767822248289041 8615223759575866686216781)
                ·
                  refine ⟨3230708909840950007331293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8615223759575866686216781 3230708909840950007331293)
                  ·
                    refine ⟨1211515841190356252749235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230708909840950007331293 1211515841190356252749235)
                    ·
                      rfl

theorem cell22_3539128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_3539128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539128 prefixEnd_3539128 := by exact prefixLift 3539128
  have htrace : WordTrace (prefixWord ++ tailWord_3539128) baseStart_3539128 baseEnd_3539128 := by
    simpa [prefixWord, tailWord_3539128, baseEnd_3539128] using wordTrace_append hprefix tailTrace_3539128
  have hstable : (prefixWord ++ tailWord_3539128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539128).length < 2 ^ (prefixWord ++ tailWord_3539128).sum := by decide
  have hdescent : baseEnd_3539128 < baseStart_3539128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539132 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_3539132 : Nat := 118140960795 + 3539132 * 2 ^ 59
def prefixEnd_3539132 : Nat := 4983230072969 + 3 ^ 40 * 3539132 * 2
def baseEnd_3539132 : Nat := 1211517210472101575649223

theorem tailTrace_3539132 : CollatzResearch.WordTrace tailWord_3539132 prefixEnd_3539132 1211517210472101575649223 := by
  unfold tailWord_3539132
  simp only [CollatzResearch.WordTrace]
  refine ⟨64541374307168337234565825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86055165742891116312754433 64541374307168337234565825)
  ·
    refine ⟨48406030730376252925924369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64541374307168337234565825 48406030730376252925924369)
    ·
      refine ⟨36304523047782189694443277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48406030730376252925924369 36304523047782189694443277)
      ·
        refine ⟨13614196142918321135416229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36304523047782189694443277 13614196142918321135416229)
        ·
          refine ⟨2552661776797185212890543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13614196142918321135416229 2552661776797185212890543)
          ·
            refine ⟨3828992665195777819335815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552661776797185212890543 3828992665195777819335815)
            ·
              refine ⟨5743488997793666729003723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3828992665195777819335815 5743488997793666729003723)
              ·
                refine ⟨8615233496690500093505585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5743488997793666729003723 8615233496690500093505585)
                ·
                  refine ⟨6461425122517875070129189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8615233496690500093505585 6461425122517875070129189)
                  ·
                    refine ⟨1211517210472101575649223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6461425122517875070129189 1211517210472101575649223)
                    ·
                      rfl

theorem cell22_3539132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_3539132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539132 prefixEnd_3539132 := by exact prefixLift 3539132
  have htrace : WordTrace (prefixWord ++ tailWord_3539132) baseStart_3539132 baseEnd_3539132 := by
    simpa [prefixWord, tailWord_3539132, baseEnd_3539132] using wordTrace_append hprefix tailTrace_3539132
  have hstable : (prefixWord ++ tailWord_3539132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539132).length < 2 ^ (prefixWord ++ tailWord_3539132).sum := by decide
  have hdescent : baseEnd_3539132 < baseStart_3539132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539173 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_3539173 : Nat := 118140960795 + 3539173 * 2 ^ 59
def prefixEnd_3539173 : Nat := 4983230072969 + 3 ^ 40 * 3539173 * 2
def baseEnd_3539173 : Nat := 1211531245609991135374097

theorem tailTrace_3539173 : CollatzResearch.WordTrace tailWord_3539173 prefixEnd_3539173 1211531245609991135374097 := by
  unfold tailWord_3539173
  simp only [CollatzResearch.WordTrace]
  refine ⟨129084244007188138471374173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86056162671458758980916115 129084244007188138471374173)
  ·
    refine ⟨48406591502695551926765315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129084244007188138471374173 48406591502695551926765315)
    ·
      refine ⟨72609887254043327890147973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48406591502695551926765315 72609887254043327890147973)
      ·
        refine ⟨13614353860133123979402745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72609887254043327890147973 13614353860133123979402745)
        ·
          refine ⟨10210765395099842984552059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13614353860133123979402745 10210765395099842984552059)
          ·
            refine ⟨15316148092649764476828089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10210765395099842984552059 15316148092649764476828089)
            ·
              refine ⟨11487111069487323357621067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15316148092649764476828089 11487111069487323357621067)
              ·
                refine ⟨17230666604230985036431601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11487111069487323357621067 17230666604230985036431601)
                ·
                  refine ⟨12922999953173238777323701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17230666604230985036431601 12922999953173238777323701)
                  ·
                    refine ⟨1211531245609991135374097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12922999953173238777323701 1211531245609991135374097)
                    ·
                      rfl

theorem cell22_3539173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_3539173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539173 prefixEnd_3539173 := by exact prefixLift 3539173
  have htrace : WordTrace (prefixWord ++ tailWord_3539173) baseStart_3539173 baseEnd_3539173 := by
    simpa [prefixWord, tailWord_3539173, baseEnd_3539173] using wordTrace_append hprefix tailTrace_3539173
  have hstable : (prefixWord ++ tailWord_3539173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539173).length < 2 ^ (prefixWord ++ tailWord_3539173).sum := by decide
  have hdescent : baseEnd_3539173 < baseStart_3539173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539235 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 2, 3]
def baseStart_3539235 : Nat := 118140960795 + 3539235 * 2 ^ 59
def prefixEnd_3539235 : Nat := 4983230072969 + 3 ^ 40 * 3539235 * 2
def baseEnd_3539235 : Nat := 1211552469477043640323907

theorem tailTrace_3539235 : CollatzResearch.WordTrace tailWord_3539235 prefixEnd_3539235 1211552469477043640323907 := by
  unfold tailWord_3539235
  simp only [CollatzResearch.WordTrace]
  refine ⟨129086505332963523060131159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86057670221975682040087439 129086505332963523060131159)
  ·
    refine ⟨193629757999445284590196739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129086505332963523060131159 193629757999445284590196739)
    ·
      refine ⟨290444636999167926885295109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193629757999445284590196739 290444636999167926885295109)
      ·
        refine ⟨54458369437343986290992833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290444636999167926885295109 54458369437343986290992833)
        ·
          refine ⟨40843777078007989718244625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54458369437343986290992833 40843777078007989718244625)
          ·
            refine ⟨30632832808505992288683469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40843777078007989718244625 30632832808505992288683469)
            ·
              refine ⟨11487312303189747108256301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30632832808505992288683469 11487312303189747108256301)
              ·
                refine ⟨4307742113696155165596113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11487312303189747108256301 4307742113696155165596113)
                ·
                  refine ⟨3230806585272116374197085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307742113696155165596113 3230806585272116374197085)
                  ·
                    refine ⟨1211552469477043640323907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230806585272116374197085 1211552469477043640323907)
                    ·
                      rfl

theorem cell22_3539235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 3].length) (baseStart_3539235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539235 prefixEnd_3539235 := by exact prefixLift 3539235
  have htrace : WordTrace (prefixWord ++ tailWord_3539235) baseStart_3539235 baseEnd_3539235 := by
    simpa [prefixWord, tailWord_3539235, baseEnd_3539235] using wordTrace_append hprefix tailTrace_3539235
  have hstable : (prefixWord ++ tailWord_3539235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539235).length < 2 ^ (prefixWord ++ tailWord_3539235).sum := by decide
  have hdescent : baseEnd_3539235 < baseStart_3539235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539239 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3539239 : Nat := 118140960795 + 3539239 * 2 ^ 59
def prefixEnd_3539239 : Nat := 4983230072969 + 3 ^ 40 * 3539239 * 2
def baseEnd_3539239 : Nat := 1211553838758788963223895

theorem tailTrace_3539239 : CollatzResearch.WordTrace tailWord_3539239 prefixEnd_3539239 1211553838758788963223895 := by
  unfold tailWord_3539239
  simp only [CollatzResearch.WordTrace]
  refine ⟨129086651224949031743276771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86057767483299354495517847 129086651224949031743276771)
  ·
    refine ⟨193629976837423547614915157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129086651224949031743276771 193629976837423547614915157)
    ·
      refine ⟨2269101291063557198612287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 193629976837423547614915157 2269101291063557198612287)
      ·
        refine ⟨3403651936595335797918431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269101291063557198612287 3403651936595335797918431)
        ·
          refine ⟨5105477904893003696877647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403651936595335797918431 5105477904893003696877647)
          ·
            refine ⟨7658216857339505545316471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105477904893003696877647 7658216857339505545316471)
            ·
              refine ⟨11487325286009258317974707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7658216857339505545316471 11487325286009258317974707)
              ·
                refine ⟨17230987929013887476962061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11487325286009258317974707 17230987929013887476962061)
                ·
                  refine ⟨6461620473380207803860773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17230987929013887476962061 6461620473380207803860773)
                  ·
                    refine ⟨1211553838758788963223895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6461620473380207803860773 1211553838758788963223895)
                    ·
                      rfl

theorem cell22_3539239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3539239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539239 prefixEnd_3539239 := by exact prefixLift 3539239
  have htrace : WordTrace (prefixWord ++ tailWord_3539239) baseStart_3539239 baseEnd_3539239 := by
    simpa [prefixWord, tailWord_3539239, baseEnd_3539239] using wordTrace_append hprefix tailTrace_3539239
  have hstable : (prefixWord ++ tailWord_3539239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539239).length < 2 ^ (prefixWord ++ tailWord_3539239).sum := by decide
  have hdescent : baseEnd_3539239 < baseStart_3539239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539265 : List Nat := [1, 2, 5, 2, 3, 9]
def baseStart_3539265 : Nat := 118140960795 + 3539265 * 2 ^ 59
def prefixEnd_3539265 : Nat := 4983230072969 + 3 ^ 40 * 3539265 * 2
def baseEnd_3539265 : Nat := 14957564680125105704615

theorem tailTrace_3539265 : CollatzResearch.WordTrace tailWord_3539265 prefixEnd_3539265 14957564680125105704615 := by
  unfold tailWord_3539265
  simp only [CollatzResearch.WordTrace]
  refine ⟨129087599522854838183723249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86058399681903225455815499 129087599522854838183723249)
  ·
    refine ⟨96815699642141128637792437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129087599522854838183723249 96815699642141128637792437)
    ·
      refine ⟨9076471841450730809793041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96815699642141128637792437 9076471841450730809793041)
      ·
        refine ⟨6807353881088048107344781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9076471841450730809793041 6807353881088048107344781)
        ·
          refine ⟨2552757705408018040254293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6807353881088048107344781 2552757705408018040254293)
          ·
            refine ⟨14957564680125105704615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2552757705408018040254293 14957564680125105704615)
            ·
              rfl

theorem cell22_3539265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 9].length) (baseStart_3539265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539265 prefixEnd_3539265 := by exact prefixLift 3539265
  have htrace : WordTrace (prefixWord ++ tailWord_3539265) baseStart_3539265 baseEnd_3539265 := by
    simpa [prefixWord, tailWord_3539265, baseEnd_3539265] using wordTrace_append hprefix tailTrace_3539265
  have hstable : (prefixWord ++ tailWord_3539265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539265).length < 2 ^ (prefixWord ++ tailWord_3539265).sum := by decide
  have hdescent : baseEnd_3539265 < baseStart_3539265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539314 : List Nat := [3, 2, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_3539314 : Nat := 118140960795 + 3539314 * 2 ^ 59
def prefixEnd_3539314 : Nat := 4983230072969 + 3 ^ 40 * 3539314 * 2
def baseEnd_3539314 : Nat := 1211579512791513767598665

theorem tailTrace_3539314 : CollatzResearch.WordTrace tailWord_3539314 prefixEnd_3539314 1211579512791513767598665 := by
  unfold tailWord_3539314
  simp only [CollatzResearch.WordTrace]
  refine ⟨32272346674919329888064249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86059591133118213034837997 32272346674919329888064249)
  ·
    refine ⟨24204260006189497416048187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32272346674919329888064249 24204260006189497416048187)
    ·
      refine ⟨36306390009284246124072281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24204260006189497416048187 36306390009284246124072281)
      ·
        refine ⟨27229792506963184593054211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36306390009284246124072281 27229792506963184593054211)
        ·
          refine ⟨40844688760444776889581317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27229792506963184593054211 40844688760444776889581317)
          ·
            refine ⟨7658379142583395666796497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40844688760444776889581317 7658379142583395666796497)
            ·
              refine ⟨5743784356937546750097373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658379142583395666796497 5743784356937546750097373)
              ·
                refine ⟨2153919133851580031286515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5743784356937546750097373 2153919133851580031286515)
                ·
                  refine ⟨3230878700777370046929773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2153919133851580031286515 3230878700777370046929773)
                  ·
                    refine ⟨1211579512791513767598665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230878700777370046929773 1211579512791513767598665)
                    ·
                      rfl

theorem cell22_3539314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_3539314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539314 prefixEnd_3539314 := by exact prefixLift 3539314
  have htrace : WordTrace (prefixWord ++ tailWord_3539314) baseStart_3539314 baseEnd_3539314 := by
    simpa [prefixWord, tailWord_3539314, baseEnd_3539314] using wordTrace_append hprefix tailTrace_3539314
  have hstable : (prefixWord ++ tailWord_3539314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539314).length < 2 ^ (prefixWord ++ tailWord_3539314).sum := by decide
  have hdescent : baseEnd_3539314 < baseStart_3539314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539383 : List Nat := [1, 1, 3, 1, 3, 3, 10]
def baseStart_3539383 : Nat := 118140960795 + 3539383 * 2 ^ 59
def prefixEnd_3539383 : Nat := 4983230072969 + 3 ^ 40 * 3539383 * 2
def baseEnd_3539383 : Nat := 44874190107467429171239

theorem tailTrace_3539383 : CollatzResearch.WordTrace tailWord_3539383 prefixEnd_3539383 44874190107467429171239 := by
  unfold tailWord_3539383
  simp only [CollatzResearch.WordTrace]
  refine ⟨129091903336427344336518803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86061268890951562891012535 129091903336427344336518803)
  ·
    refine ⟨193637855004641016504778205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129091903336427344336518803 193637855004641016504778205)
    ·
      refine ⟨72614195626740381189291827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193637855004641016504778205 72614195626740381189291827)
      ·
        refine ⟨108921293440110571783937741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72614195626740381189291827 108921293440110571783937741)
        ·
          refine ⟨40845485040041464418976653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108921293440110571783937741 40845485040041464418976653)
          ·
            refine ⟨15317056890015549157116245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40845485040041464418976653 15317056890015549157116245)
            ·
              refine ⟨44874190107467429171239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15317056890015549157116245 44874190107467429171239)
              ·
                rfl

theorem cell22_3539383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 10].length) (baseStart_3539383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539383 prefixEnd_3539383 := by exact prefixLift 3539383
  have htrace : WordTrace (prefixWord ++ tailWord_3539383) baseStart_3539383 baseEnd_3539383 := by
    simpa [prefixWord, tailWord_3539383, baseEnd_3539383] using wordTrace_append hprefix tailTrace_3539383
  have hstable : (prefixWord ++ tailWord_3539383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539383).length < 2 ^ (prefixWord ++ tailWord_3539383).sum := by decide
  have hdescent : baseEnd_3539383 < baseStart_3539383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539385 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_3539385 : Nat := 118140960795 + 3539385 * 2 ^ 59
def prefixEnd_3539385 : Nat := 4983230072969 + 3 ^ 40 * 3539385 * 2
def baseEnd_3539385 : Nat := 1211603817542493249073447

theorem tailTrace_3539385 : CollatzResearch.WordTrace tailWord_3539385 prefixEnd_3539385 1211603817542493249073447 := by
  unfold tailWord_3539385
  simp only [CollatzResearch.WordTrace]
  refine ⟨129091976282420098678091609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86061317521613399118727739 129091976282420098678091609)
  ·
    refine ⟨96818982211815074008568707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129091976282420098678091609 96818982211815074008568707)
    ·
      refine ⟨145228473317722611012853061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96818982211815074008568707 145228473317722611012853061)
      ·
        refine ⟨27230338747072989564909949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145228473317722611012853061 27230338747072989564909949)
        ·
          refine ⟨10211377030152371086841231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27230338747072989564909949 10211377030152371086841231)
          ·
            refine ⟨15317065545228556630261847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10211377030152371086841231 15317065545228556630261847)
            ·
              refine ⟨22975598317842834945392771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15317065545228556630261847 22975598317842834945392771)
              ·
                refine ⟨34463397476764252418089157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22975598317842834945392771 34463397476764252418089157)
                ·
                  refine ⟨6461887026893297328391717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34463397476764252418089157 6461887026893297328391717)
                  ·
                    refine ⟨1211603817542493249073447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6461887026893297328391717 1211603817542493249073447)
                    ·
                      rfl

theorem cell22_3539385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_3539385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539385 prefixEnd_3539385 := by exact prefixLift 3539385
  have htrace : WordTrace (prefixWord ++ tailWord_3539385) baseStart_3539385 baseEnd_3539385 := by
    simpa [prefixWord, tailWord_3539385, baseEnd_3539385] using wordTrace_append hprefix tailTrace_3539385
  have hstable : (prefixWord ++ tailWord_3539385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539385).length < 2 ^ (prefixWord ++ tailWord_3539385).sum := by decide
  have hdescent : baseEnd_3539385 < baseStart_3539385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539389 : List Nat := [1, 4, 1, 2, 2, 3, 3, 2, 4]
def baseStart_3539389 : Nat := 118140960795 + 3539389 * 2 ^ 59
def prefixEnd_3539389 : Nat := 4983230072969 + 3 ^ 40 * 3539389 * 2
def baseEnd_3539389 : Nat := 403868395608079523991145

theorem tailTrace_3539389 : CollatzResearch.WordTrace tailWord_3539389 prefixEnd_3539389 403868395608079523991145 := by
  unfold tailWord_3539389
  simp only [CollatzResearch.WordTrace]
  refine ⟨129092122174405607361237221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86061414782937071574158147 129092122174405607361237221)
  ·
    refine ⟨24204772907701051380231979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129092122174405607361237221 24204772907701051380231979)
    ·
      refine ⟨36307159361551577070347969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24204772907701051380231979 36307159361551577070347969)
      ·
        refine ⟨27230369521163682802760977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36307159361551577070347969 27230369521163682802760977)
        ·
          refine ⟨20422777140872762102070733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27230369521163682802760977 20422777140872762102070733)
          ·
            refine ⟨7658541427827285788276525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20422777140872762102070733 7658541427827285788276525)
            ·
              refine ⟨2871953035435232170603697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7658541427827285788276525 2871953035435232170603697)
              ·
                refine ⟨2153964776576424127952773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871953035435232170603697 2153964776576424127952773)
                ·
                  refine ⟨403868395608079523991145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2153964776576424127952773 403868395608079523991145)
                  ·
                    rfl

theorem cell22_3539389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_3539389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539389 prefixEnd_3539389 := by exact prefixLift 3539389
  have htrace : WordTrace (prefixWord ++ tailWord_3539389) baseStart_3539389 baseEnd_3539389 := by
    simpa [prefixWord, tailWord_3539389, baseEnd_3539389] using wordTrace_append hprefix tailTrace_3539389
  have hstable : (prefixWord ++ tailWord_3539389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539389).length < 2 ^ (prefixWord ++ tailWord_3539389).sum := by decide
  have hdescent : baseEnd_3539389 < baseStart_3539389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539400 : List Nat := [2, 1, 3, 1, 3, 3, 2, 7]
def baseStart_3539400 : Nat := 118140960795 + 3539400 * 2 ^ 59
def prefixEnd_3539400 : Nat := 4983230072969 + 3 ^ 40 * 3539400 * 2
def baseEnd_3539400 : Nat := 134623216927670912216489

theorem tailTrace_3539400 : CollatzResearch.WordTrace tailWord_3539400 prefixEnd_3539400 134623216927670912216489 := by
  unfold tailWord_3539400
  simp only [CollatzResearch.WordTrace]
  refine ⟨64546261688682878119943827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86061682251577170826591769 64546261688682878119943827)
  ·
    refine ⟨96819392533024317179915741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64546261688682878119943827 96819392533024317179915741)
    ·
      refine ⟨36307272199884118942468403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96819392533024317179915741 36307272199884118942468403)
      ·
        refine ⟨54460908299826178413702605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36307272199884118942468403 54460908299826178413702605)
        ·
          refine ⟨20422840612434816905138477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54460908299826178413702605 20422840612434816905138477)
          ·
            refine ⟨7658565229663056339426929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20422840612434816905138477 7658565229663056339426929)
            ·
              refine ⟨5743923922247292254570197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7658565229663056339426929 5743923922247292254570197)
              ·
                refine ⟨134623216927670912216489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5743923922247292254570197 134623216927670912216489)
                ·
                  rfl

theorem cell22_3539400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_3539400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539400 prefixEnd_3539400 := by exact prefixLift 3539400
  have htrace : WordTrace (prefixWord ++ tailWord_3539400) baseStart_3539400 baseEnd_3539400 := by
    simpa [prefixWord, tailWord_3539400, baseEnd_3539400] using wordTrace_append hprefix tailTrace_3539400
  have hstable : (prefixWord ++ tailWord_3539400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539400).length < 2 ^ (prefixWord ++ tailWord_3539400).sum := by decide
  have hdescent : baseEnd_3539400 < baseStart_3539400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539404 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_3539404 : Nat := 118140960795 + 3539404 * 2 ^ 59
def prefixEnd_3539404 : Nat := 4983230072969 + 3 ^ 40 * 3539404 * 2
def baseEnd_3539404 : Nat := 1211610321630783532848389

theorem tailTrace_3539404 : CollatzResearch.WordTrace tailWord_3539404 prefixEnd_3539404 1211610321630783532848389 := by
  unfold tailWord_3539404
  simp only [CollatzResearch.WordTrace]
  refine ⟨64546334634675632461516633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86061779512900843282022177 64546334634675632461516633)
  ·
    refine ⟨48409750976006724346137475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64546334634675632461516633 48409750976006724346137475)
    ·
      refine ⟨72614626464010086519206213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48409750976006724346137475 72614626464010086519206213)
      ·
        refine ⟨13615242462001891222351165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72614626464010086519206213 13615242462001891222351165)
        ·
          refine ⟨5105715923250709208381687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13615242462001891222351165 5105715923250709208381687)
          ·
            refine ⟨7658573884876063812572531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105715923250709208381687 7658573884876063812572531)
            ·
              refine ⟨11487860827314095718858797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7658573884876063812572531 11487860827314095718858797)
              ·
                refine ⟨4307947810242785894572049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11487860827314095718858797 4307947810242785894572049)
                ·
                  refine ⟨3230960857682089420929037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4307947810242785894572049 3230960857682089420929037)
                  ·
                    refine ⟨1211610321630783532848389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3230960857682089420929037 1211610321630783532848389)
                    ·
                      rfl

theorem cell22_3539404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_3539404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539404 prefixEnd_3539404 := by exact prefixLift 3539404
  have htrace : WordTrace (prefixWord ++ tailWord_3539404) baseStart_3539404 baseEnd_3539404 := by
    simpa [prefixWord, tailWord_3539404, baseEnd_3539404] using wordTrace_append hprefix tailTrace_3539404
  have hstable : (prefixWord ++ tailWord_3539404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539404).length < 2 ^ (prefixWord ++ tailWord_3539404).sum := by decide
  have hdescent : baseEnd_3539404 < baseStart_3539404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539475 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 3, 4]
def baseStart_3539475 : Nat := 118140960795 + 3539475 * 2 ^ 59
def prefixEnd_3539475 : Nat := 4983230072969 + 3 ^ 40 * 3539475 * 2
def baseEnd_3539475 : Nat := 1211634626381763014323171

theorem tailTrace_3539475 : CollatzResearch.WordTrace tailWord_3539475 prefixEnd_3539475 1211634626381763014323171 := by
  unfold tailWord_3539475
  simp only [CollatzResearch.WordTrace]
  refine ⟨129095258852094044048867879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86063505901396029365911919 129095258852094044048867879)
  ·
    refine ⟨193642888278141066073301819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129095258852094044048867879 193642888278141066073301819)
    ·
      refine ⟨290464332417211599109952729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193642888278141066073301819 290464332417211599109952729)
      ·
        refine ⟨217848249312908699332464547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290464332417211599109952729 217848249312908699332464547)
        ·
          refine ⟨326772373969363048998696821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217848249312908699332464547 326772373969363048998696821)
          ·
            refine ⟨30634910059627785843627827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 326772373969363048998696821 30634910059627785843627827)
            ·
              refine ⟨45952365089441678765441741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30634910059627785843627827 45952365089441678765441741)
              ·
                refine ⟨17232136908540629537040653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45952365089441678765441741 17232136908540629537040653)
                ·
                  refine ⟨6462051340702736076390245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17232136908540629537040653 6462051340702736076390245)
                  ·
                    refine ⟨1211634626381763014323171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6462051340702736076390245 1211634626381763014323171)
                    ·
                      rfl

theorem cell22_3539475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_3539475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539475 prefixEnd_3539475 := by exact prefixLift 3539475
  have htrace : WordTrace (prefixWord ++ tailWord_3539475) baseStart_3539475 baseEnd_3539475 := by
    simpa [prefixWord, tailWord_3539475, baseEnd_3539475] using wordTrace_append hprefix tailTrace_3539475
  have hstable : (prefixWord ++ tailWord_3539475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539475).length < 2 ^ (prefixWord ++ tailWord_3539475).sum := by decide
  have hdescent : baseEnd_3539475 < baseStart_3539475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539490 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3539490 : Nat := 118140960795 + 3539490 * 2 ^ 59
def prefixEnd_3539490 : Nat := 4983230072969 + 3 ^ 40 * 3539490 * 2
def baseEnd_3539490 : Nat := 403879920396102658399375

theorem tailTrace_3539490 : CollatzResearch.WordTrace tailWord_3539490 prefixEnd_3539490 403879920396102658399375 := by
  unfold tailWord_3539490
  simp only [CollatzResearch.WordTrace]
  refine ⟨32273951486759925402665981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86063870631359801073775949 32273951486759925402665981)
  ·
    refine ⟨12102731807534972025999743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32273951486759925402665981 12102731807534972025999743)
    ·
      refine ⟨18154097711302458038999615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12102731807534972025999743 18154097711302458038999615)
      ·
        refine ⟨27231146566953687058499423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18154097711302458038999615 27231146566953687058499423)
        ·
          refine ⟨40846719850430530587749135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27231146566953687058499423 40846719850430530587749135)
          ·
            refine ⟨61270079775645795881623703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40846719850430530587749135 61270079775645795881623703)
            ·
              refine ⟨91905119663468693822435555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61270079775645795881623703 91905119663468693822435555)
              ·
                refine ⟨137857679495203040733653333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91905119663468693822435555 137857679495203040733653333)
                ·
                  refine ⟨403879920396102658399375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 137857679495203040733653333 403879920396102658399375)
                  ·
                    rfl

theorem cell22_3539490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3539490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539490 prefixEnd_3539490 := by exact prefixLift 3539490
  have htrace : WordTrace (prefixWord ++ tailWord_3539490) baseStart_3539490 baseEnd_3539490 := by
    simpa [prefixWord, tailWord_3539490, baseEnd_3539490] using wordTrace_append hprefix tailTrace_3539490
  have hstable : (prefixWord ++ tailWord_3539490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539490).length < 2 ^ (prefixWord ++ tailWord_3539490).sum := by decide
  have hdescent : baseEnd_3539490 < baseStart_3539490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539505 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3539505 : Nat := 118140960795 + 3539505 * 2 ^ 59
def prefixEnd_3539505 : Nat := 4983230072969 + 3 ^ 40 * 3539505 * 2
def baseEnd_3539505 : Nat := 1211644895994852936073079

theorem tailTrace_3539505 : CollatzResearch.WordTrace tailWord_3539505 prefixEnd_3539505 1211644895994852936073079 := by
  unfold tailWord_3539505
  simp only [CollatzResearch.WordTrace]
  refine ⟨129096353041985359172459969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86064235361323572781639979 129096353041985359172459969)
  ·
    refine ⟨96822264781489019379344977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129096353041985359172459969 96822264781489019379344977)
    ·
      refine ⟨72616698586116764534508733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96822264781489019379344977 72616698586116764534508733)
      ·
        refine ⟨27231261969793786700440775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72616698586116764534508733 27231261969793786700440775)
        ·
          refine ⟨40846892954690680050661163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27231261969793786700440775 40846892954690680050661163)
          ·
            refine ⟨61270339432036020075991745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40846892954690680050661163 61270339432036020075991745)
            ·
              refine ⟨45952754574027015056993809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61270339432036020075991745 45952754574027015056993809)
              ·
                refine ⟨34464565930520261292745357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45952754574027015056993809 34464565930520261292745357)
                ·
                  refine ⟨12924212223945097984779509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34464565930520261292745357 12924212223945097984779509)
                  ·
                    refine ⟨1211644895994852936073079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12924212223945097984779509 1211644895994852936073079)
                    ·
                      rfl

theorem cell22_3539505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3539505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539505 prefixEnd_3539505 := by exact prefixLift 3539505
  have htrace : WordTrace (prefixWord ++ tailWord_3539505) baseStart_3539505 baseEnd_3539505 := by
    simpa [prefixWord, tailWord_3539505, baseEnd_3539505] using wordTrace_append hprefix tailTrace_3539505
  have hstable : (prefixWord ++ tailWord_3539505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539505).length < 2 ^ (prefixWord ++ tailWord_3539505).sum := by decide
  have hdescent : baseEnd_3539505 < baseStart_3539505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539507 : List Nat := [1, 1, 1, 2, 4, 2, 1, 6, 4]
def baseStart_3539507 : Nat := 118140960795 + 3539507 * 2 ^ 59
def prefixEnd_3539507 : Nat := 4983230072969 + 3 ^ 40 * 3539507 * 2
def baseEnd_3539507 : Nat := 403881860211908532507691

theorem tailTrace_3539507 : CollatzResearch.WordTrace tailWord_3539507 prefixEnd_3539507 403881860211908532507691 := by
  unfold tailWord_3539507
  simp only [CollatzResearch.WordTrace]
  refine ⟨129096425987978113514032775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86064283991985409009355183 129096425987978113514032775)
  ·
    refine ⟨193644638981967170271049163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129096425987978113514032775 193644638981967170271049163)
    ·
      refine ⟨290466958472950755406573745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193644638981967170271049163 290466958472950755406573745)
      ·
        refine ⟨217850218854713066554930309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290466958472950755406573745 217850218854713066554930309)
        ·
          refine ⟨40846916035258699979049433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217850218854713066554930309 40846916035258699979049433)
          ·
            refine ⟨30635187026444024984287075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40846916035258699979049433 30635187026444024984287075)
            ·
              refine ⟨45952780539666037476430613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30635187026444024984287075 45952780539666037476430613)
              ·
                refine ⟨2154036587796845506707685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45952780539666037476430613 2154036587796845506707685)
                ·
                  refine ⟨403881860211908532507691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154036587796845506707685 403881860211908532507691)
                  ·
                    rfl

theorem cell22_3539507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 4].length) (baseStart_3539507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539507 prefixEnd_3539507 := by exact prefixLift 3539507
  have htrace : WordTrace (prefixWord ++ tailWord_3539507) baseStart_3539507 baseEnd_3539507 := by
    simpa [prefixWord, tailWord_3539507, baseEnd_3539507] using wordTrace_append hprefix tailTrace_3539507
  have hstable : (prefixWord ++ tailWord_3539507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539507).length < 2 ^ (prefixWord ++ tailWord_3539507).sum := by decide
  have hdescent : baseEnd_3539507 < baseStart_3539507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539520 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_3539520 : Nat := 118140960795 + 3539520 * 2 ^ 59
def prefixEnd_3539520 : Nat := 4983230072969 + 3 ^ 40 * 3539520 * 2
def baseEnd_3539520 : Nat := 1211650030801397896948033

theorem tailTrace_3539520 : CollatzResearch.WordTrace tailWord_3539520 prefixEnd_3539520 1211650030801397896948033 := by
  unfold tailWord_3539520
  simp only [CollatzResearch.WordTrace]
  refine ⟨64548450068465508367128007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86064600091287344489504009 64548450068465508367128007)
  ·
    refine ⟨96822675102698262550692011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64548450068465508367128007 96822675102698262550692011)
    ·
      refine ⟨145234012654047393826038017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96822675102698262550692011 145234012654047393826038017)
      ·
        refine ⟨108925509490535545369528513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145234012654047393826038017 108925509490535545369528513)
        ·
          refine ⟨81694132117901659027146385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108925509490535545369528513 81694132117901659027146385)
          ·
            refine ⟨61270599088426244270359789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81694132117901659027146385 61270599088426244270359789)
            ·
              refine ⟨22976474658159841601384921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61270599088426244270359789 22976474658159841601384921)
              ·
                refine ⟨17232355993619881201038691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22976474658159841601384921 17232355993619881201038691)
                ·
                  refine ⟨25848533990429821801558037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17232355993619881201038691 25848533990429821801558037)
                  ·
                    refine ⟨1211650030801397896948033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25848533990429821801558037 1211650030801397896948033)
                    ·
                      rfl

theorem cell22_3539520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_3539520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539520 prefixEnd_3539520 := by exact prefixLift 3539520
  have htrace : WordTrace (prefixWord ++ tailWord_3539520) baseStart_3539520 baseEnd_3539520 := by
    simpa [prefixWord, tailWord_3539520, baseEnd_3539520] using wordTrace_append hprefix tailTrace_3539520
  have hstable : (prefixWord ++ tailWord_3539520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539520).length < 2 ^ (prefixWord ++ tailWord_3539520).sum := by decide
  have hdescent : baseEnd_3539520 < baseStart_3539520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539526 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3539526 : Nat := 118140960795 + 3539526 * 2 ^ 59
def prefixEnd_3539526 : Nat := 4983230072969 + 3 ^ 40 * 3539526 * 2
def baseEnd_3539526 : Nat := 1211652084724015881298015

theorem tailTrace_3539526 : CollatzResearch.WordTrace tailWord_3539526 prefixEnd_3539526 1211652084724015881298015 := by
  unfold tailWord_3539526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034284967965914992467951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 86064745983272853172649621 4034284967965914992467951)
  ·
    refine ⟨6051427451948872488701927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4034284967965914992467951 6051427451948872488701927)
    ·
      refine ⟨9077141177923308733052891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6051427451948872488701927 9077141177923308733052891)
      ·
        refine ⟨13615711766884963099579337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077141177923308733052891 13615711766884963099579337)
        ·
          refine ⟨10211783825163722324684503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13615711766884963099579337 10211783825163722324684503)
          ·
            refine ⟨15317675737745583487026755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10211783825163722324684503 15317675737745583487026755)
            ·
              refine ⟨22976513606618375230540133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15317675737745583487026755 22976513606618375230540133)
              ·
                refine ⟨4308096301240945355726275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22976513606618375230540133 4308096301240945355726275)
                ·
                  refine ⟨6462144451861418033589413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308096301240945355726275 6462144451861418033589413)
                  ·
                    refine ⟨1211652084724015881298015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6462144451861418033589413 1211652084724015881298015)
                    ·
                      rfl

theorem cell22_3539526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3539526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539526 prefixEnd_3539526 := by exact prefixLift 3539526
  have htrace : WordTrace (prefixWord ++ tailWord_3539526) baseStart_3539526 baseEnd_3539526 := by
    simpa [prefixWord, tailWord_3539526, baseEnd_3539526] using wordTrace_append hprefix tailTrace_3539526
  have hstable : (prefixWord ++ tailWord_3539526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539526).length < 2 ^ (prefixWord ++ tailWord_3539526).sum := by decide
  have hdescent : baseEnd_3539526 < baseStart_3539526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539595 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 3, 7]
def baseStart_3539595 : Nat := 118140960795 + 3539595 * 2 ^ 59
def prefixEnd_3539595 : Nat := 4983230072969 + 3 ^ 40 * 3539595 * 2
def baseEnd_3539595 : Nat := 1211675704834122701322803

theorem tailTrace_3539595 : CollatzResearch.WordTrace tailWord_3539595 prefixEnd_3539595 1211675704834122701322803 := by
  unfold tailWord_3539595
  simp only [CollatzResearch.WordTrace]
  refine ⟨129099635611659304543236239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86066423741106203028824159 129099635611659304543236239)
  ·
    refine ⟨193649453417488956814854359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129099635611659304543236239 193649453417488956814854359)
    ·
      refine ⟨290474180126233435222281539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193649453417488956814854359 290474180126233435222281539)
      ·
        refine ⟨435711270189350152833422309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290474180126233435222281539 435711270189350152833422309)
        ·
          refine ⟨81695863160503153656266683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435711270189350152833422309 81695863160503153656266683)
          ·
            refine ⟨122543794740754730484400025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81695863160503153656266683 122543794740754730484400025)
            ·
              refine ⟨91907846055566047863300019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122543794740754730484400025 91907846055566047863300019)
              ·
                refine ⟨137861769083349071794950029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91907846055566047863300019 137861769083349071794950029)
                ·
                  refine ⟨51698163406255901923106261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137861769083349071794950029 51698163406255901923106261)
                  ·
                    refine ⟨1211675704834122701322803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51698163406255901923106261 1211675704834122701322803)
                    ·
                      rfl

theorem cell22_3539595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_3539595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539595 prefixEnd_3539595 := by exact prefixLift 3539595
  have htrace : WordTrace (prefixWord ++ tailWord_3539595) baseStart_3539595 baseEnd_3539595 := by
    simpa [prefixWord, tailWord_3539595, baseEnd_3539595] using wordTrace_append hprefix tailTrace_3539595
  have hstable : (prefixWord ++ tailWord_3539595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539595).length < 2 ^ (prefixWord ++ tailWord_3539595).sum := by decide
  have hdescent : baseEnd_3539595 < baseStart_3539595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539629 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3539629 : Nat := 118140960795 + 3539629 * 2 ^ 59
def prefixEnd_3539629 : Nat := 4983230072969 + 3 ^ 40 * 3539629 * 2
def baseEnd_3539629 : Nat := 1211687343728957945972699

theorem tailTrace_3539629 : CollatzResearch.WordTrace tailWord_3539629 prefixEnd_3539629 1211687343728957945972699 := by
  unfold tailWord_3539629
  simp only [CollatzResearch.WordTrace]
  refine ⟨129100875693536128349973941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86067250462357418899982627 129100875693536128349973941)
  ·
    refine ⟨12103207096269012032810057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129100875693536128349973941 12103207096269012032810057)
    ·
      refine ⟨9077405322201759024607543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12103207096269012032810057 9077405322201759024607543)
      ·
        refine ⟨13616107983302638536911315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077405322201759024607543 13616107983302638536911315)
        ·
          refine ⟨20424161974953957805366973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13616107983302638536911315 20424161974953957805366973)
          ·
            refine ⟨7659060740607734177012615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20424161974953957805366973 7659060740607734177012615)
            ·
              refine ⟨11488591110911601265518923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7659060740607734177012615 11488591110911601265518923)
              ·
                refine ⟨17232886666367401898278385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11488591110911601265518923 17232886666367401898278385)
                ·
                  refine ⟨12924664999775551423708789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17232886666367401898278385 12924664999775551423708789)
                  ·
                    refine ⟨1211687343728957945972699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12924664999775551423708789 1211687343728957945972699)
                    ·
                      rfl

theorem cell22_3539629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3539629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539629 prefixEnd_3539629 := by exact prefixLift 3539629
  have htrace : WordTrace (prefixWord ++ tailWord_3539629) baseStart_3539629 baseEnd_3539629 := by
    simpa [prefixWord, tailWord_3539629, baseEnd_3539629] using wordTrace_append hprefix tailTrace_3539629
  have hstable : (prefixWord ++ tailWord_3539629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539629).length < 2 ^ (prefixWord ++ tailWord_3539629).sum := by decide
  have hdescent : baseEnd_3539629 < baseStart_3539629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539642 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_3539642 : Nat := 118140960795 + 3539642 * 2 ^ 59
def prefixEnd_3539642 : Nat := 4983230072969 + 3 ^ 40 * 3539642 * 2
def baseEnd_3539642 : Nat := 403897264631543415132553

theorem tailTrace_3539642 : CollatzResearch.WordTrace tailWord_3539642 prefixEnd_3539642 403897264631543415132553 := by
  unfold tailWord_3539642
  simp only [CollatzResearch.WordTrace]
  refine ⟨32275337460622257892549295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86067566561659354380131453 32275337460622257892549295)
  ·
    refine ⟨48413006190933386838823943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32275337460622257892549295 48413006190933386838823943)
    ·
      refine ⟨72619509286400080258235915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48413006190933386838823943 72619509286400080258235915)
      ·
        refine ⟨108929263929600120387353873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72619509286400080258235915 108929263929600120387353873)
        ·
          refine ⟨81696947947200090290515405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108929263929600120387353873 81696947947200090290515405)
          ·
            refine ⟨30636355480200033858943277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81696947947200090290515405 30636355480200033858943277)
            ·
              refine ⟨11488633305075012697103729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30636355480200033858943277 11488633305075012697103729)
              ·
                refine ⟨8616474978806259522827797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11488633305075012697103729 8616474978806259522827797)
                ·
                  refine ⟨403897264631543415132553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8616474978806259522827797 403897264631543415132553)
                  ·
                    rfl

theorem cell22_3539642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_3539642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539642 prefixEnd_3539642 := by exact prefixLift 3539642
  have htrace : WordTrace (prefixWord ++ tailWord_3539642) baseStart_3539642 baseEnd_3539642 := by
    simpa [prefixWord, tailWord_3539642, baseEnd_3539642] using wordTrace_append hprefix tailTrace_3539642
  have hstable : (prefixWord ++ tailWord_3539642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539642).length < 2 ^ (prefixWord ++ tailWord_3539642).sum := by decide
  have hdescent : baseEnd_3539642 < baseStart_3539642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539644 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3539644 : Nat := 118140960795 + 3539644 * 2 ^ 59
def prefixEnd_3539644 : Nat := 4983230072969 + 3 ^ 40 * 3539644 * 2
def baseEnd_3539644 : Nat := 1211692478535502906847653

theorem tailTrace_3539644 : CollatzResearch.WordTrace tailWord_3539644 prefixEnd_3539644 1211692478535502906847653 := by
  unfold tailWord_3539644
  simp only [CollatzResearch.WordTrace]
  refine ⟨64550711394240892955884993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86067615192321190607846657 64550711394240892955884993)
  ·
    refine ⟨48413033545680669716913745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64550711394240892955884993 48413033545680669716913745)
    ·
      refine ⟨36309775159260502287685309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48413033545680669716913745 36309775159260502287685309)
      ·
        refine ⟨13616165684722688357881991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36309775159260502287685309 13616165684722688357881991)
        ·
          refine ⟨20424248527084032536822987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13616165684722688357881991 20424248527084032536822987)
          ·
            refine ⟨30636372790626048805234481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20424248527084032536822987 30636372790626048805234481)
            ·
              refine ⟨22977279592969536603925861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30636372790626048805234481 22977279592969536603925861)
              ·
                refine ⟨4308239923681788113236099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22977279592969536603925861 4308239923681788113236099)
                ·
                  refine ⟨6462359885522682169854149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308239923681788113236099 6462359885522682169854149)
                  ·
                    refine ⟨1211692478535502906847653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6462359885522682169854149 1211692478535502906847653)
                    ·
                      rfl

theorem cell22_3539644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3539644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539644 prefixEnd_3539644 := by exact prefixLift 3539644
  have htrace : WordTrace (prefixWord ++ tailWord_3539644) baseStart_3539644 baseEnd_3539644 := by
    simpa [prefixWord, tailWord_3539644, baseEnd_3539644] using wordTrace_append hprefix tailTrace_3539644
  have hstable : (prefixWord ++ tailWord_3539644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539644).length < 2 ^ (prefixWord ++ tailWord_3539644).sum := by decide
  have hdescent : baseEnd_3539644 < baseStart_3539644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539674 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_3539674 : Nat := 118140960795 + 3539674 * 2 ^ 59
def prefixEnd_3539674 : Nat := 4983230072969 + 3 ^ 40 * 3539674 * 2
def baseEnd_3539674 : Nat := 1211702748148592828597561

theorem tailTrace_3539674 : CollatzResearch.WordTrace tailWord_3539674 prefixEnd_3539674 1211702748148592828597561 := by
  unfold tailWord_3539674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32275629244593275258840519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86068344652248734023574717 32275629244593275258840519)
  ·
    refine ⟨48413443866889912888260779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32275629244593275258840519 48413443866889912888260779)
    ·
      refine ⟨72620165800334869332391169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48413443866889912888260779 72620165800334869332391169)
      ·
        refine ⟨54465124350251151999293377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72620165800334869332391169 54465124350251151999293377)
        ·
          refine ⟨40848843262688363999470033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54465124350251151999293377 40848843262688363999470033)
          ·
            refine ⟨30636632447016272999602525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40848843262688363999470033 30636632447016272999602525)
            ·
              refine ⟨11488737167631102374850947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30636632447016272999602525 11488737167631102374850947)
              ·
                refine ⟨17233105751446653562276421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11488737167631102374850947 17233105751446653562276421)
                ·
                  refine ⟨3231207328396247542926829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17233105751446653562276421 3231207328396247542926829)
                  ·
                    refine ⟨1211702748148592828597561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3231207328396247542926829 1211702748148592828597561)
                    ·
                      rfl

theorem cell22_3539674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_3539674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539674 prefixEnd_3539674 := by exact prefixLift 3539674
  have htrace : WordTrace (prefixWord ++ tailWord_3539674) baseStart_3539674 baseEnd_3539674 := by
    simpa [prefixWord, tailWord_3539674, baseEnd_3539674] using wordTrace_append hprefix tailTrace_3539674
  have hstable : (prefixWord ++ tailWord_3539674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539674).length < 2 ^ (prefixWord ++ tailWord_3539674).sum := by decide
  have hdescent : baseEnd_3539674 < baseStart_3539674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539676 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 6]
def baseStart_3539676 : Nat := 118140960795 + 3539676 * 2 ^ 59
def prefixEnd_3539676 : Nat := 4983230072969 + 3 ^ 40 * 3539676 * 2
def baseEnd_3539676 : Nat := 403901144263155163349185

theorem tailTrace_3539676 : CollatzResearch.WordTrace tailWord_3539676 prefixEnd_3539676 403901144263155163349185 := by
  unfold tailWord_3539676
  simp only [CollatzResearch.WordTrace]
  refine ⟨64551294962182927688467441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86068393282910570251289921 64551294962182927688467441)
  ·
    refine ⟨48413471221637195766350581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64551294962182927688467441 48413471221637195766350581)
    ·
      refine ⟨4538762927028487103095367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48413471221637195766350581 4538762927028487103095367)
      ·
        refine ⟨6808144390542730654643051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4538762927028487103095367 6808144390542730654643051)
        ·
          refine ⟨10212216585814095981964577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808144390542730654643051 10212216585814095981964577)
          ·
            refine ⟨7659162439360571986473433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10212216585814095981964577 7659162439360571986473433)
            ·
              refine ⟨5744371829520428989855075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659162439360571986473433 5744371829520428989855075)
              ·
                refine ⟨8616557744280643484782613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744371829520428989855075 8616557744280643484782613)
                ·
                  refine ⟨403901144263155163349185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8616557744280643484782613 403901144263155163349185)
                  ·
                    rfl

theorem cell22_3539676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_3539676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539676 prefixEnd_3539676 := by exact prefixLift 3539676
  have htrace : WordTrace (prefixWord ++ tailWord_3539676) baseStart_3539676 baseEnd_3539676 := by
    simpa [prefixWord, tailWord_3539676, baseEnd_3539676] using wordTrace_append hprefix tailTrace_3539676
  have hstable : (prefixWord ++ tailWord_3539676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539676).length < 2 ^ (prefixWord ++ tailWord_3539676).sum := by decide
  have hdescent : baseEnd_3539676 < baseStart_3539676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539747 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 1, 7]
def baseStart_3539747 : Nat := 118140960795 + 3539747 * 2 ^ 59
def prefixEnd_3539747 : Nat := 4983230072969 + 3 ^ 40 * 3539747 * 2
def baseEnd_3539747 : Nat := 1211727737540444971522337

theorem tailTrace_3539747 : CollatzResearch.WordTrace tailWord_3539747 prefixEnd_3539747 1211727737540444971522337 := by
  unfold tailWord_3539747
  simp only [CollatzResearch.WordTrace]
  refine ⟨129105179507108634502769495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86070119671405756335179663 129105179507108634502769495)
  ·
    refine ⟨193657769260662951754154243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129105179507108634502769495 193657769260662951754154243)
    ·
      refine ⟨290486653890994427631231365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193657769260662951754154243 290486653890994427631231365)
      ·
        refine ⟨54466247604561455180855881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290486653890994427631231365 54466247604561455180855881)
        ·
          refine ⟨40849685703421091385641911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54466247604561455180855881 40849685703421091385641911)
          ·
            refine ⟨61274528555131637078462867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40849685703421091385641911 61274528555131637078462867)
            ·
              refine ⟨91911792832697455617694301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61274528555131637078462867 91911792832697455617694301)
              ·
                refine ⟨34466922312261545856635363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91911792832697455617694301 34466922312261545856635363)
                ·
                  refine ⟨51700383468392318784953045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34466922312261545856635363 51700383468392318784953045)
                  ·
                    refine ⟨1211727737540444971522337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51700383468392318784953045 1211727737540444971522337)
                    ·
                      rfl

theorem cell22_3539747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_3539747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539747 prefixEnd_3539747 := by exact prefixLift 3539747
  have htrace : WordTrace (prefixWord ++ tailWord_3539747) baseStart_3539747 baseEnd_3539747 := by
    simpa [prefixWord, tailWord_3539747, baseEnd_3539747] using wordTrace_append hprefix tailTrace_3539747
  have hstable : (prefixWord ++ tailWord_3539747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539747).length < 2 ^ (prefixWord ++ tailWord_3539747).sum := by decide
  have hdescent : baseEnd_3539747 < baseStart_3539747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539749 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 5]
def baseStart_3539749 : Nat := 118140960795 + 3539749 * 2 ^ 59
def prefixEnd_3539749 : Nat := 4983230072969 + 3 ^ 40 * 3539749 * 2
def baseEnd_3539749 : Nat := 403909474060439210990777

theorem tailTrace_3539749 : CollatzResearch.WordTrace tailWord_3539749 prefixEnd_3539749 403909474060439210990777 := by
  unfold tailWord_3539749
  simp only [CollatzResearch.WordTrace]
  refine ⟨129105252453101388844342301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86070168302067592562894867 129105252453101388844342301)
  ·
    refine ⟨48414469669913020816628363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129105252453101388844342301 48414469669913020816628363)
    ·
      refine ⟨72621704504869531224942545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48414469669913020816628363 72621704504869531224942545)
      ·
        refine ⟨54466278378652148418706909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72621704504869531224942545 54466278378652148418706909)
        ·
          refine ⟨20424854391994555657015091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54466278378652148418706909 20424854391994555657015091)
          ·
            refine ⟨30637281587991833485522637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20424854391994555657015091 30637281587991833485522637)
            ·
              refine ⟨11488980595496937557070989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30637281587991833485522637 11488980595496937557070989)
              ·
                refine ⟨4308367723311351583901621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11488980595496937557070989 4308367723311351583901621)
                ·
                  refine ⟨403909474060439210990777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4308367723311351583901621 403909474060439210990777)
                  ·
                    rfl

theorem cell22_3539749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_3539749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539749 prefixEnd_3539749 := by exact prefixLift 3539749
  have htrace : WordTrace (prefixWord ++ tailWord_3539749) baseStart_3539749 baseEnd_3539749 := by
    simpa [prefixWord, tailWord_3539749, baseEnd_3539749] using wordTrace_append hprefix tailTrace_3539749
  have hstable : (prefixWord ++ tailWord_3539749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539749).length < 2 ^ (prefixWord ++ tailWord_3539749).sum := by decide
  have hdescent : baseEnd_3539749 < baseStart_3539749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539794 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3539794 : Nat := 118140960795 + 3539794 * 2 ^ 59
def prefixEnd_3539794 : Nat := 4983230072969 + 3 ^ 40 * 3539794 * 2
def baseEnd_3539794 : Nat := 403914608866984171865731

theorem tailTrace_3539794 : CollatzResearch.WordTrace tailWord_3539794 prefixEnd_3539794 403914608866984171865731 := by
  unfold tailWord_3539794
  simp only [CollatzResearch.WordTrace]
  refine ⟨32276723434484590382432609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86071262491958907686486957 32276723434484590382432609)
  ·
    refine ⟨24207542575863442786824457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32276723434484590382432609 24207542575863442786824457)
    ·
      refine ⟨18155656931897582090118343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24207542575863442786824457 18155656931897582090118343)
      ·
        refine ⟨27233485397846373135177515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18155656931897582090118343 27233485397846373135177515)
        ·
          refine ⟨40850228096769559702766273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27233485397846373135177515 40850228096769559702766273)
          ·
            refine ⟨30637671072577169777074705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40850228096769559702766273 30637671072577169777074705)
            ·
              refine ⟨22978253304432877332806029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30637671072577169777074705 22978253304432877332806029)
              ·
                refine ⟨8616844989162328999802261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22978253304432877332806029 8616844989162328999802261)
                ·
                  refine ⟨403914608866984171865731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8616844989162328999802261 403914608866984171865731)
                  ·
                    rfl

theorem cell22_3539794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3539794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539794 prefixEnd_3539794 := by exact prefixLift 3539794
  have htrace : WordTrace (prefixWord ++ tailWord_3539794) baseStart_3539794 baseEnd_3539794 := by
    simpa [prefixWord, tailWord_3539794, baseEnd_3539794] using wordTrace_append hprefix tailTrace_3539794
  have hstable : (prefixWord ++ tailWord_3539794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539794).length < 2 ^ (prefixWord ++ tailWord_3539794).sum := by decide
  have hdescent : baseEnd_3539794 < baseStart_3539794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539830 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_3539830 : Nat := 118140960795 + 3539830 * 2 ^ 59
def prefixEnd_3539830 : Nat := 4983230072969 + 3 ^ 40 * 3539830 * 2
def baseEnd_3539830 : Nat := 1211756150136660421697083

theorem tailTrace_3539830 : CollatzResearch.WordTrace tailWord_3539830 prefixEnd_3539830 1211756150136660421697083 := by
  unfold tailWord_3539830
  simp only [CollatzResearch.WordTrace]
  refine ⟨8069262922862996229877559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86072137843871959785360629 8069262922862996229877559)
  ·
    refine ⟨12103894384294494344816339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8069262922862996229877559 12103894384294494344816339)
    ·
      refine ⟨18155841576441741517224509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12103894384294494344816339 18155841576441741517224509)
      ·
        refine ⟨6808440591165653068959191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18155841576441741517224509 6808440591165653068959191)
        ·
          refine ⟨10212660886748479603438787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808440591165653068959191 10212660886748479603438787)
          ·
            refine ⟨15318991330122719405158181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10212660886748479603438787 15318991330122719405158181)
            ·
              refine ⟨2872310874398009888467159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15318991330122719405158181 2872310874398009888467159)
              ·
                refine ⟨4308466311597014832700739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872310874398009888467159 4308466311597014832700739)
                ·
                  refine ⟨6462699467395522249051109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308466311597014832700739 6462699467395522249051109)
                  ·
                    refine ⟨1211756150136660421697083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6462699467395522249051109 1211756150136660421697083)
                    ·
                      rfl

theorem cell22_3539830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_3539830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539830 prefixEnd_3539830 := by exact prefixLift 3539830
  have htrace : WordTrace (prefixWord ++ tailWord_3539830) baseStart_3539830 baseEnd_3539830 := by
    simpa [prefixWord, tailWord_3539830, baseEnd_3539830] using wordTrace_append hprefix tailTrace_3539830
  have hstable : (prefixWord ++ tailWord_3539830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539830).length < 2 ^ (prefixWord ++ tailWord_3539830).sum := by decide
  have hdescent : baseEnd_3539830 < baseStart_3539830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539860 : List Nat := [2, 4, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3539860 : Nat := 118140960795 + 3539860 * 2 ^ 59
def prefixEnd_3539860 : Nat := 4983230072969 + 3 ^ 40 * 3539860 * 2
def baseEnd_3539860 : Nat := 1211766419749750343446991

theorem tailTrace_3539860 : CollatzResearch.WordTrace tailWord_3539860 prefixEnd_3539860 1211766419749750343446991 := by
  unfold tailWord_3539860
  simp only [CollatzResearch.WordTrace]
  refine ⟨64554650477849627400816517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86072867303799503201088689 64554650477849627400816517)
  ·
    refine ⟨12103996964596805137653097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64554650477849627400816517 12103996964596805137653097)
    ·
      refine ⟨9077997723447603853239823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12103996964596805137653097 9077997723447603853239823)
      ·
        refine ⟨13616996585171405779859735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9077997723447603853239823 13616996585171405779859735)
        ·
          refine ⟨20425494877757108669789603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13616996585171405779859735 20425494877757108669789603)
          ·
            refine ⟨30638242316635663004684405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20425494877757108669789603 30638242316635663004684405)
            ·
              refine ⟨2872335217184593406689163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30638242316635663004684405 2872335217184593406689163)
              ·
                refine ⟨4308502825776890110033745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872335217184593406689163 4308502825776890110033745)
                ·
                  refine ⟨3231377119332667582525309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4308502825776890110033745 3231377119332667582525309)
                  ·
                    refine ⟨1211766419749750343446991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3231377119332667582525309 1211766419749750343446991)
                    ·
                      rfl

theorem cell22_3539860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3539860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539860 prefixEnd_3539860 := by exact prefixLift 3539860
  have htrace : WordTrace (prefixWord ++ tailWord_3539860) baseStart_3539860 baseEnd_3539860 := by
    simpa [prefixWord, tailWord_3539860, baseEnd_3539860] using wordTrace_append hprefix tailTrace_3539860
  have hstable : (prefixWord ++ tailWord_3539860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539860).length < 2 ^ (prefixWord ++ tailWord_3539860).sum := by decide
  have hdescent : baseEnd_3539860 < baseStart_3539860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539873 : List Nat := [1, 2, 3, 4, 1, 3, 2, 6]
def baseStart_3539873 : Nat := 118140960795 + 3539873 * 2 ^ 59
def prefixEnd_3539873 : Nat := 4983230072969 + 3 ^ 40 * 3539873 * 2
def baseEnd_3539873 : Nat := 134641207768380293652439

theorem tailTrace_3539873 : CollatzResearch.WordTrace tailWord_3539873 prefixEnd_3539873 134641207768380293652439 := by
  unfold tailWord_3539873
  simp only [CollatzResearch.WordTrace]
  refine ⟨129109775104652158021856273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86073183403101438681237515 129109775104652158021856273)
  ·
    refine ⟨96832331328489118516392205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129109775104652158021856273 96832331328489118516392205)
    ·
      refine ⟨36312124248183419443647077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96832331328489118516392205 36312124248183419443647077)
      ·
        refine ⟨6808523296534391145683827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36312124248183419443647077 6808523296534391145683827)
        ·
          refine ⟨10212784944801586718525741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6808523296534391145683827 10212784944801586718525741)
          ·
            refine ⟨3829794354300595019447153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10212784944801586718525741 3829794354300595019447153)
            ·
              refine ⟨2872345765725446264585365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829794354300595019447153 2872345765725446264585365)
              ·
                refine ⟨134641207768380293652439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2872345765725446264585365 134641207768380293652439)
                ·
                  rfl

theorem cell22_3539873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 6].length) (baseStart_3539873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539873 prefixEnd_3539873 := by exact prefixLift 3539873
  have htrace : WordTrace (prefixWord ++ tailWord_3539873) baseStart_3539873 baseEnd_3539873 := by
    simpa [prefixWord, tailWord_3539873, baseEnd_3539873] using wordTrace_append hprefix tailTrace_3539873
  have hstable : (prefixWord ++ tailWord_3539873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539873).length < 2 ^ (prefixWord ++ tailWord_3539873).sum := by decide
  have hdescent : baseEnd_3539873 < baseStart_3539873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539914 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_3539914 : Nat := 118140960795 + 3539914 * 2 ^ 59
def prefixEnd_3539914 : Nat := 4983230072969 + 3 ^ 40 * 3539914 * 2
def baseEnd_3539914 : Nat := 1211784905053312202596825

theorem tailTrace_3539914 : CollatzResearch.WordTrace tailWord_3539914 prefixEnd_3539914 1211784905053312202596825 := by
  unfold tailWord_3539914
  simp only [CollatzResearch.WordTrace]
  refine ⟨32277817624375905506024699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86074180331669081349399197 32277817624375905506024699)
  ·
    refine ⟨48416726436563858259037049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32277817624375905506024699 48416726436563858259037049)
    ·
      refine ⟨36312544827422893694277787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48416726436563858259037049 36312544827422893694277787)
      ·
        refine ⟨54468817241134340541416681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36312544827422893694277787 54468817241134340541416681)
        ·
          refine ⟨40851612930850755406062511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54468817241134340541416681 40851612930850755406062511)
          ·
            refine ⟨61277419396276133109093767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40851612930850755406062511 61277419396276133109093767)
            ·
              refine ⟨91916129094414199663640651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61277419396276133109093767 91916129094414199663640651)
              ·
                refine ⟨137874193641621299495460977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91916129094414199663640651 137874193641621299495460977)
                ·
                  refine ⟨103405645231215974621595733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137874193641621299495460977 103405645231215974621595733)
                  ·
                    refine ⟨1211784905053312202596825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103405645231215974621595733 1211784905053312202596825)
                    ·
                      rfl

theorem cell22_3539914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_3539914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539914 prefixEnd_3539914 := by exact prefixLift 3539914
  have htrace : WordTrace (prefixWord ++ tailWord_3539914) baseStart_3539914 baseEnd_3539914 := by
    simpa [prefixWord, tailWord_3539914, baseEnd_3539914] using wordTrace_append hprefix tailTrace_3539914
  have hstable : (prefixWord ++ tailWord_3539914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539914).length < 2 ^ (prefixWord ++ tailWord_3539914).sum := by decide
  have hdescent : baseEnd_3539914 < baseStart_3539914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539918 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_3539918 : Nat := 118140960795 + 3539918 * 2 ^ 59
def prefixEnd_3539918 : Nat := 4983230072969 + 3 ^ 40 * 3539918 * 2
def baseEnd_3539918 : Nat := 403928758111685841832271

theorem tailTrace_3539918 : CollatzResearch.WordTrace tailWord_3539918 prefixEnd_3539918 403928758111685841832271 := by
  unfold tailWord_3539918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16138927048686141338405551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86074277592992753804829605 16138927048686141338405551)
  ·
    refine ⟨24208390573029212007608327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16138927048686141338405551 24208390573029212007608327)
    ·
      refine ⟨36312585859543818011412491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24208390573029212007608327 36312585859543818011412491)
      ·
        refine ⟨54468878789315727017118737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36312585859543818011412491 54468878789315727017118737)
        ·
          refine ⟨40851659091986795262839053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54468878789315727017118737 40851659091986795262839053)
          ·
            refine ⟨15319372159495048223564645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40851659091986795262839053 15319372159495048223564645)
            ·
              refine ⟨2872382279905321541918371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15319372159495048223564645 2872382279905321541918371)
              ·
                refine ⟨4308573419857982312877557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872382279905321541918371 4308573419857982312877557)
                ·
                  refine ⟨403928758111685841832271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4308573419857982312877557 403928758111685841832271)
                  ·
                    rfl

theorem cell22_3539918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_3539918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539918 prefixEnd_3539918 := by exact prefixLift 3539918
  have htrace : WordTrace (prefixWord ++ tailWord_3539918) baseStart_3539918 baseEnd_3539918 := by
    simpa [prefixWord, tailWord_3539918, baseEnd_3539918] using wordTrace_append hprefix tailTrace_3539918
  have hstable : (prefixWord ++ tailWord_3539918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539918).length < 2 ^ (prefixWord ++ tailWord_3539918).sum := by decide
  have hdescent : baseEnd_3539918 < baseStart_3539918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3539978 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_3539978 : Nat := 118140960795 + 3539978 * 2 ^ 59
def prefixEnd_3539978 : Nat := 4983230072969 + 3 ^ 40 * 3539978 * 2
def baseEnd_3539978 : Nat := 1211806813561237368996629

theorem tailTrace_3539978 : CollatzResearch.WordTrace tailWord_3539978 prefixEnd_3539978 1211806813561237368996629 := by
  unfold tailWord_3539978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32278401192317940238607147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86075736512847840636285725 32278401192317940238607147)
  ·
    refine ⟨48417601788476910357910721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32278401192317940238607147 48417601788476910357910721)
    ·
      refine ⟨36313201341357682768433041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48417601788476910357910721 36313201341357682768433041)
      ·
        refine ⟨27234901006018262076324781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36313201341357682768433041 27234901006018262076324781)
        ·
          refine ⟨10213087877256848278621793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27234901006018262076324781 10213087877256848278621793)
          ·
            refine ⟨7659815907942636208966345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213087877256848278621793 7659815907942636208966345)
            ·
              refine ⟨5744861930956977156724759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7659815907942636208966345 5744861930956977156724759)
              ·
                refine ⟨8617292896435465735087139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5744861930956977156724759 8617292896435465735087139)
                ·
                  refine ⟨12925939344653198602630709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8617292896435465735087139 12925939344653198602630709)
                  ·
                    refine ⟨1211806813561237368996629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12925939344653198602630709 1211806813561237368996629)
                    ·
                      rfl

theorem cell22_3539978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_3539978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3539978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3539978 prefixEnd_3539978 := by exact prefixLift 3539978
  have htrace : WordTrace (prefixWord ++ tailWord_3539978) baseStart_3539978 baseEnd_3539978 := by
    simpa [prefixWord, tailWord_3539978, baseEnd_3539978] using wordTrace_append hprefix tailTrace_3539978
  have hstable : (prefixWord ++ tailWord_3539978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3539978).length < 2 ^ (prefixWord ++ tailWord_3539978).sum := by decide
  have hdescent : baseEnd_3539978 < baseStart_3539978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3539978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540074 : List Nat := [3, 1, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3540074 : Nat := 118140960795 + 3540074 * 2 ^ 59
def prefixEnd_3540074 : Nat := 4983230072969 + 3 ^ 40 * 3540074 * 2
def baseEnd_3540074 : Nat := 1211839676323125118596335

theorem tailTrace_3540074 : CollatzResearch.WordTrace tailWord_3540074 prefixEnd_3540074 1211839676323125118596335 := by
  unfold tailWord_3540074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32279276544230992337480819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86078070784615979566615517 32279276544230992337480819)
  ·
    refine ⟨48418914816346488506221229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32279276544230992337480819 48418914816346488506221229)
    ·
      refine ⟨18157093056129933189832961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48418914816346488506221229 18157093056129933189832961)
      ·
        refine ⟨13617819792097449892374721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18157093056129933189832961 13617819792097449892374721)
        ·
          refine ⟨10213364844073087419281041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13617819792097449892374721 10213364844073087419281041)
          ·
            refine ⟨7660023633054815564460781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10213364844073087419281041 7660023633054815564460781)
            ·
              refine ⟨2872508862395555836672793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7660023633054815564460781 2872508862395555836672793)
              ·
                refine ⟨2154381646796666877504595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872508862395555836672793 2154381646796666877504595)
                ·
                  refine ⟨3231572470195000316256893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154381646796666877504595 3231572470195000316256893)
                  ·
                    refine ⟨1211839676323125118596335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3231572470195000316256893 1211839676323125118596335)
                    ·
                      rfl

theorem cell22_3540074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3540074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540074 prefixEnd_3540074 := by exact prefixLift 3540074
  have htrace : WordTrace (prefixWord ++ tailWord_3540074) baseStart_3540074 baseEnd_3540074 := by
    simpa [prefixWord, tailWord_3540074, baseEnd_3540074] using wordTrace_append hprefix tailTrace_3540074
  have hstable : (prefixWord ++ tailWord_3540074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540074).length < 2 ^ (prefixWord ++ tailWord_3540074).sum := by decide
  have hdescent : baseEnd_3540074 < baseStart_3540074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540081 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 6]
def baseStart_3540081 : Nat := 118140960795 + 3540081 * 2 ^ 59
def prefixEnd_3540081 : Nat := 4983230072969 + 3 ^ 40 * 3540081 * 2
def baseEnd_3540081 : Nat := 403947357522059811223771

theorem tailTrace_3540081 : CollatzResearch.WordTrace tailWord_3540081 prefixEnd_3540081 403947357522059811223771 := by
  unfold tailWord_3540081
  simp only [CollatzResearch.WordTrace]
  refine ⟨129117361487898609545428097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86078240991932406363618731 129117361487898609545428097)
  ·
    refine ⟨96838021115923957159071073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129117361487898609545428097 96838021115923957159071073)
    ·
      refine ⟨72628515836942967869303305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96838021115923957159071073 72628515836942967869303305)
      ·
        refine ⟨54471386877707225901977479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72628515836942967869303305 54471386877707225901977479)
        ·
          refine ⟨81707080316560838852966219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54471386877707225901977479 81707080316560838852966219)
          ·
            refine ⟨122560620474841258279449329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81707080316560838852966219 122560620474841258279449329)
            ·
              refine ⟨91920465356130943709586997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122560620474841258279449329 91920465356130943709586997)
              ·
                refine ⟨8617543627137275972773781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91920465356130943709586997 8617543627137275972773781)
                ·
                  refine ⟨403947357522059811223771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8617543627137275972773781 403947357522059811223771)
                  ·
                    rfl

theorem cell22_3540081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_3540081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540081 prefixEnd_3540081 := by exact prefixLift 3540081
  have htrace : WordTrace (prefixWord ++ tailWord_3540081) baseStart_3540081 baseEnd_3540081 := by
    simpa [prefixWord, tailWord_3540081, baseEnd_3540081] using wordTrace_append hprefix tailTrace_3540081
  have hstable : (prefixWord ++ tailWord_3540081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540081).length < 2 ^ (prefixWord ++ tailWord_3540081).sum := by decide
  have hdescent : baseEnd_3540081 < baseStart_3540081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540100 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3540100 : Nat := 118140960795 + 3540100 * 2 ^ 59
def prefixEnd_3540100 : Nat := 4983230072969 + 3 ^ 40 * 3540100 * 2
def baseEnd_3540100 : Nat := 1211848576654469717446255

theorem tailTrace_3540100 : CollatzResearch.WordTrace tailWord_3540100 prefixEnd_3540100 1211848576654469717446255 := by
  unfold tailWord_3540100
  simp only [CollatzResearch.WordTrace]
  refine ⟨64559027237414887895184877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86078702983219850526913169 64559027237414887895184877)
  ·
    refine ⟨24209635214030582960694329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64559027237414887895184877 24209635214030582960694329)
    ·
      refine ⟨18157226410522937220520747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24209635214030582960694329 18157226410522937220520747)
      ·
        refine ⟨27235839615784405830781121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18157226410522937220520747 27235839615784405830781121)
        ·
          refine ⟨20426879711838304373085841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27235839615784405830781121 20426879711838304373085841)
          ·
            refine ⟨15320159783878728279814381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20426879711838304373085841 15320159783878728279814381)
            ·
              refine ⟨5745059918954523104930393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15320159783878728279814381 5745059918954523104930393)
              ·
                refine ⟨4308794939215892328697795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745059918954523104930393 4308794939215892328697795)
                ·
                  refine ⟨6463192408823838493046693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308794939215892328697795 6463192408823838493046693)
                  ·
                    refine ⟨1211848576654469717446255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6463192408823838493046693 1211848576654469717446255)
                    ·
                      rfl

theorem cell22_3540100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3540100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540100 prefixEnd_3540100 := by exact prefixLift 3540100
  have htrace : WordTrace (prefixWord ++ tailWord_3540100) baseStart_3540100 baseEnd_3540100 := by
    simpa [prefixWord, tailWord_3540100, baseEnd_3540100] using wordTrace_append hprefix tailTrace_3540100
  have hstable : (prefixWord ++ tailWord_3540100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540100).length < 2 ^ (prefixWord ++ tailWord_3540100).sum := by decide
  have hdescent : baseEnd_3540100 < baseStart_3540100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540128 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_3540128 : Nat := 118140960795 + 3540128 * 2 ^ 59
def prefixEnd_3540128 : Nat := 4983230072969 + 3 ^ 40 * 3540128 * 2
def baseEnd_3540128 : Nat := 1211858161626686977746169

theorem tailTrace_3540128 : CollatzResearch.WordTrace tailWord_3540128 prefixEnd_3540128 1211858161626686977746169 := by
  unfold tailWord_3540128
  simp only [CollatzResearch.WordTrace]
  refine ⟨64559537859364168286194519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86079383812485557714926025 64559537859364168286194519)
  ·
    refine ⟨96839306789046252429291779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64559537859364168286194519 96839306789046252429291779)
    ·
      refine ⟨145258960183569378643937669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96839306789046252429291779 145258960183569378643937669)
      ·
        refine ⟨27236055034419258495738313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145258960183569378643937669 27236055034419258495738313)
        ·
          refine ⟨20427041275814443871803735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27236055034419258495738313 20427041275814443871803735)
          ·
            refine ⟨30640561913721665807705603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20427041275814443871803735 30640561913721665807705603)
            ·
              refine ⟨45960842870582498711558405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30640561913721665807705603 45960842870582498711558405)
              ·
                refine ⟨8617658038234218508417201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45960842870582498711558405 8617658038234218508417201)
                ·
                  refine ⟨6463243528675663881312901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8617658038234218508417201 6463243528675663881312901)
                  ·
                    refine ⟨1211858161626686977746169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6463243528675663881312901 1211858161626686977746169)
                    ·
                      rfl

theorem cell22_3540128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_3540128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540128 prefixEnd_3540128 := by exact prefixLift 3540128
  have htrace : WordTrace (prefixWord ++ tailWord_3540128) baseStart_3540128 baseEnd_3540128 := by
    simpa [prefixWord, tailWord_3540128, baseEnd_3540128] using wordTrace_append hprefix tailTrace_3540128
  have hstable : (prefixWord ++ tailWord_3540128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540128).length < 2 ^ (prefixWord ++ tailWord_3540128).sum := by decide
  have hdescent : baseEnd_3540128 < baseStart_3540128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540132 : List Nat := [2, 3, 1, 2, 3, 1, 4, 2, 4]
def baseStart_3540132 : Nat := 118140960795 + 3540132 * 2 ^ 59
def prefixEnd_3540132 : Nat := 4983230072969 + 3 ^ 40 * 3540132 * 2
def baseEnd_3540132 : Nat := 403953176969477433548719

theorem tailTrace_3540132 : CollatzResearch.WordTrace tailWord_3540132 prefixEnd_3540132 403953176969477433548719 := by
  unfold tailWord_3540132
  simp only [CollatzResearch.WordTrace]
  refine ⟨64559610805356922627767325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86079481073809230170356433 64559610805356922627767325)
  ·
    refine ⟨24209854052008845985412747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64559610805356922627767325 24209854052008845985412747)
    ·
      refine ⟨36314781078013268978119121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24209854052008845985412747 36314781078013268978119121)
      ·
        refine ⟨27236085808509951733589341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36314781078013268978119121 27236085808509951733589341)
        ·
          refine ⟨10213532178191231900096003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27236085808509951733589341 10213532178191231900096003)
          ·
            refine ⟨15320298267286847850144005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213532178191231900096003 15320298267286847850144005)
            ·
              refine ⟨2872555925116283971902001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15320298267286847850144005 2872555925116283971902001)
              ·
                refine ⟨2154416943837212978926501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872555925116283971902001 2154416943837212978926501)
                ·
                  refine ⟨403953176969477433548719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154416943837212978926501 403953176969477433548719)
                  ·
                    rfl

theorem cell22_3540132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_3540132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540132 prefixEnd_3540132 := by exact prefixLift 3540132
  have htrace : WordTrace (prefixWord ++ tailWord_3540132) baseStart_3540132 baseEnd_3540132 := by
    simpa [prefixWord, tailWord_3540132, baseEnd_3540132] using wordTrace_append hprefix tailTrace_3540132
  have hstable : (prefixWord ++ tailWord_3540132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540132).length < 2 ^ (prefixWord ++ tailWord_3540132).sum := by decide
  have hdescent : baseEnd_3540132 < baseStart_3540132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540160 : List Nat := [2, 1, 1, 2, 6, 1, 3, 6]
def baseStart_3540160 : Nat := 118140960795 + 3540160 * 2 ^ 59
def prefixEnd_3540160 : Nat := 4983230072969 + 3 ^ 40 * 3540160 * 2
def baseEnd_3540160 : Nat := 134652123986738840105119

theorem tailTrace_3540160 : CollatzResearch.WordTrace tailWord_3540160 prefixEnd_3540160 134652123986738840105119 := by
  unfold tailWord_3540160
  simp only [CollatzResearch.WordTrace]
  refine ⟨64560121427306203018776967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86080161903074937358369289 64560121427306203018776967)
  ·
    refine ⟨96840182140959304528165451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64560121427306203018776967 96840182140959304528165451)
    ·
      refine ⟨145260273211438956792248177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96840182140959304528165451 145260273211438956792248177)
      ·
        refine ⟨108945204908579217594186133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145260273211438956792248177 108945204908579217594186133)
        ·
          refine ⟨5106806480089650824727475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108945204908579217594186133 5106806480089650824727475)
          ·
            refine ⟨7660209720134476237091213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5106806480089650824727475 7660209720134476237091213)
            ·
              refine ⟨2872578645050428588909205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7660209720134476237091213 2872578645050428588909205)
              ·
                refine ⟨134652123986738840105119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2872578645050428588909205 134652123986738840105119)
                ·
                  rfl

theorem cell22_3540160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 6].length) (baseStart_3540160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540160 prefixEnd_3540160 := by exact prefixLift 3540160
  have htrace : WordTrace (prefixWord ++ tailWord_3540160) baseStart_3540160 baseEnd_3540160 := by
    simpa [prefixWord, tailWord_3540160, baseEnd_3540160] using wordTrace_append hprefix tailTrace_3540160
  have hstable : (prefixWord ++ tailWord_3540160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540160).length < 2 ^ (prefixWord ++ tailWord_3540160).sum := by decide
  have hdescent : baseEnd_3540160 < baseStart_3540160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540192 : List Nat := [2, 1, 1, 3, 1, 4, 2, 4, 1, 3]
def baseStart_3540192 : Nat := 118140960795 + 3540192 * 2 ^ 59
def prefixEnd_3540192 : Nat := 4983230072969 + 3 ^ 40 * 3540192 * 2
def baseEnd_3540192 : Nat := 1211880070134612144145973

theorem tailTrace_3540192 : CollatzResearch.WordTrace tailWord_3540192 prefixEnd_3540192 1211880070134612144145973 := by
  unfold tailWord_3540192
  simp only [CollatzResearch.WordTrace]
  refine ⟨64560704995248237751359415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86080939993664317001812553 64560704995248237751359415)
  ·
    refine ⟨96841057492872356627039123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64560704995248237751359415 96841057492872356627039123)
    ·
      refine ⟨145261586239308534940558685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96841057492872356627039123 145261586239308534940558685)
      ·
        refine ⟨54473094839740700602709507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145261586239308534940558685 54473094839740700602709507)
        ·
          refine ⟨81709642259611050904064261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54473094839740700602709507 81709642259611050904064261)
          ·
            refine ⟨15320557923677072044512049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81709642259611050904064261 15320557923677072044512049)
            ·
              refine ⟨11490418442757804033384037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15320557923677072044512049 11490418442757804033384037)
              ·
                refine ⟨2154453458017088256259507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11490418442757804033384037 2154453458017088256259507)
                ·
                  refine ⟨3231680187025632384389261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154453458017088256259507 3231680187025632384389261)
                  ·
                    refine ⟨1211880070134612144145973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3231680187025632384389261 1211880070134612144145973)
                    ·
                      rfl

theorem cell22_3540192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 1, 3].length) (baseStart_3540192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540192 prefixEnd_3540192 := by exact prefixLift 3540192
  have htrace : WordTrace (prefixWord ++ tailWord_3540192) baseStart_3540192 baseEnd_3540192 := by
    simpa [prefixWord, tailWord_3540192, baseEnd_3540192] using wordTrace_append hprefix tailTrace_3540192
  have hstable : (prefixWord ++ tailWord_3540192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540192).length < 2 ^ (prefixWord ++ tailWord_3540192).sum := by decide
  have hdescent : baseEnd_3540192 < baseStart_3540192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540203 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 2, 5]
def baseStart_3540203 : Nat := 118140960795 + 3540203 * 2 ^ 59
def prefixEnd_3540203 : Nat := 4983230072969 + 3 ^ 40 * 3540203 * 2
def baseEnd_3540203 : Nat := 1211883835659411782120939

theorem tailTrace_3540203 : CollatzResearch.WordTrace tailWord_3540203 prefixEnd_3540203 1211883835659411782120939 := by
  unfold tailWord_3540203
  simp only [CollatzResearch.WordTrace]
  refine ⟨129121811193456624381369263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86081207462304416254246175 129121811193456624381369263)
  ·
    refine ⟨193682716790184936572053895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129121811193456624381369263 193682716790184936572053895)
    ·
      refine ⟨290524075185277404858080843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193682716790184936572053895 290524075185277404858080843)
      ·
        refine ⟨435786112777916107287121265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290524075185277404858080843 435786112777916107287121265)
        ·
          refine ⟨326839584583437080465340949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435786112777916107287121265 326839584583437080465340949)
          ·
            refine ⟨15320605527348613146812857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326839584583437080465340949 15320605527348613146812857)
            ·
              refine ⟨11490454145511459860109643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15320605527348613146812857 11490454145511459860109643)
              ·
                refine ⟨17235681218267189790164465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11490454145511459860109643 17235681218267189790164465)
                ·
                  refine ⟨12926760913700392342623349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17235681218267189790164465 12926760913700392342623349)
                  ·
                    refine ⟨1211883835659411782120939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12926760913700392342623349 1211883835659411782120939)
                    ·
                      rfl

theorem cell22_3540203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_3540203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540203 prefixEnd_3540203 := by exact prefixLift 3540203
  have htrace : WordTrace (prefixWord ++ tailWord_3540203) baseStart_3540203 baseEnd_3540203 := by
    simpa [prefixWord, tailWord_3540203, baseEnd_3540203] using wordTrace_append hprefix tailTrace_3540203
  have hstable : (prefixWord ++ tailWord_3540203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540203).length < 2 ^ (prefixWord ++ tailWord_3540203).sum := by decide
  have hdescent : baseEnd_3540203 < baseStart_3540203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540235 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 1, 4]
def baseStart_3540235 : Nat := 118140960795 + 3540235 * 2 ^ 59
def prefixEnd_3540235 : Nat := 4983230072969 + 3 ^ 40 * 3540235 * 2
def baseEnd_3540235 : Nat := 1211894789913374365320841

theorem tailTrace_3540235 : CollatzResearch.WordTrace tailWord_3540235 prefixEnd_3540235 1211894789913374365320841 := by
  unfold tailWord_3540235
  simp only [CollatzResearch.WordTrace]
  refine ⟨129122978329340693846534159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86081985552893795897689439 129122978329340693846534159)
  ·
    refine ⟨193684467494011040769801239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129122978329340693846534159 193684467494011040769801239)
    ·
      refine ⟨290526701241016561154701859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193684467494011040769801239 290526701241016561154701859)
      ·
        refine ⟨435790051861524841732052789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290526701241016561154701859 435790051861524841732052789)
        ·
          refine ⟨40855317362017953912379949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435790051861524841732052789 40855317362017953912379949)
          ·
            refine ⟨15320744010756732717142481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40855317362017953912379949 15320744010756732717142481)
            ·
              refine ⟨11490558008067549537856861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15320744010756732717142481 11490558008067549537856861)
              ·
                refine ⟨4308959253025331076696323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11490558008067549537856861 4308959253025331076696323)
                ·
                  refine ⟨6463438879537996615044485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4308959253025331076696323 6463438879537996615044485)
                  ·
                    refine ⟨1211894789913374365320841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6463438879537996615044485 1211894789913374365320841)
                    ·
                      rfl

theorem cell22_3540235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 4].length) (baseStart_3540235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540235 prefixEnd_3540235 := by exact prefixLift 3540235
  have htrace : WordTrace (prefixWord ++ tailWord_3540235) baseStart_3540235 baseEnd_3540235 := by
    simpa [prefixWord, tailWord_3540235, baseEnd_3540235] using wordTrace_append hprefix tailTrace_3540235
  have hstable : (prefixWord ++ tailWord_3540235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540235).length < 2 ^ (prefixWord ++ tailWord_3540235).sum := by decide
  have hdescent : baseEnd_3540235 < baseStart_3540235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540250 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_3540250 : Nat := 118140960795 + 3540250 * 2 ^ 59
def prefixEnd_3540250 : Nat := 4983230072969 + 3 ^ 40 * 3540250 * 2
def baseEnd_3540250 : Nat := 403966641573306442065265

theorem tailTrace_3540250 : CollatzResearch.WordTrace tailWord_3540250 prefixEnd_3540250 403966641573306442065265 := by
  unfold tailWord_3540250
  simp only [CollatzResearch.WordTrace]
  refine ⟨32280881356071587852082551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86082350282857567605553469 32280881356071587852082551)
  ·
    refine ⟨48421322034107381778123827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32280881356071587852082551 48421322034107381778123827)
    ·
      refine ⟨72631983051161072667185741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48421322034107381778123827 72631983051161072667185741)
      ·
        refine ⟨27236993644185402250194653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72631983051161072667185741 27236993644185402250194653)
        ·
          refine ⟨10213872616569525843822995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27236993644185402250194653 10213872616569525843822995)
          ·
            refine ⟨15320808924854288765734493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213872616569525843822995 15320808924854288765734493)
            ·
              refine ⟨5745303346820358287150435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15320808924854288765734493 5745303346820358287150435)
              ·
                refine ⟨8617955020230537430725653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5745303346820358287150435 8617955020230537430725653)
                ·
                  refine ⟨403966641573306442065265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8617955020230537430725653 403966641573306442065265)
                  ·
                    rfl

theorem cell22_3540250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_3540250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540250 prefixEnd_3540250 := by exact prefixLift 3540250
  have htrace : WordTrace (prefixWord ++ tailWord_3540250) baseStart_3540250 baseEnd_3540250 := by
    simpa [prefixWord, tailWord_3540250, baseEnd_3540250] using wordTrace_append hprefix tailTrace_3540250
  have hstable : (prefixWord ++ tailWord_3540250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540250).length < 2 ^ (prefixWord ++ tailWord_3540250).sum := by decide
  have hdescent : baseEnd_3540250 < baseStart_3540250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540269 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3540269 : Nat := 118140960795 + 3540269 * 2 ^ 59
def prefixEnd_3540269 : Nat := 4983230072969 + 3 ^ 40 * 3540269 * 2
def baseEnd_3540269 : Nat := 1211906428808209609970737

theorem tailTrace_3540269 : CollatzResearch.WordTrace tailWord_3540269 prefixEnd_3540269 1211906428808209609970737 := by
  unfold tailWord_3540269
  simp only [CollatzResearch.WordTrace]
  refine ⟨129124218411217517653271861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86082812274145011768847907 129124218411217517653271861)
  ·
    refine ⟨12105395476051642279994237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129124218411217517653271861 12105395476051642279994237)
    ·
      refine ⟨4539523303519365854997839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12105395476051642279994237 4539523303519365854997839)
      ·
        refine ⟨6809284955279048782496759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4539523303519365854997839 6809284955279048782496759)
        ·
          refine ⟨10213927432918573173745139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6809284955279048782496759 10213927432918573173745139)
          ·
            refine ⟨15320891149377859760617709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10213927432918573173745139 15320891149377859760617709)
            ·
              refine ⟨5745334181016697410231641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15320891149377859760617709 5745334181016697410231641)
              ·
                refine ⟨4309000635762523057673731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745334181016697410231641 4309000635762523057673731)
                ·
                  refine ⟨6463500953643784586510597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309000635762523057673731 6463500953643784586510597)
                  ·
                    refine ⟨1211906428808209609970737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6463500953643784586510597 1211906428808209609970737)
                    ·
                      rfl

theorem cell22_3540269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3540269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540269 prefixEnd_3540269 := by exact prefixLift 3540269
  have htrace : WordTrace (prefixWord ++ tailWord_3540269) baseStart_3540269 baseEnd_3540269 := by
    simpa [prefixWord, tailWord_3540269, baseEnd_3540269] using wordTrace_append hprefix tailTrace_3540269
  have hstable : (prefixWord ++ tailWord_3540269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540269).length < 2 ^ (prefixWord ++ tailWord_3540269).sum := by decide
  have hdescent : baseEnd_3540269 < baseStart_3540269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540301 : List Nat := [1, 6, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3540301 : Nat := 118140960795 + 3540301 * 2 ^ 59
def prefixEnd_3540301 : Nat := 4983230072969 + 3 ^ 40 * 3540301 * 2
def baseEnd_3540301 : Nat := 403972461020724064390213

theorem tailTrace_3540301 : CollatzResearch.WordTrace tailWord_3540301 prefixEnd_3540301 403972461020724064390213 := by
  unfold tailWord_3540301
  simp only [CollatzResearch.WordTrace]
  refine ⟨129125385547101587118436757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86083590364734391412291171 129125385547101587118436757)
  ·
    refine ⟨6052752447520386896176723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129125385547101587118436757 6052752447520386896176723)
    ·
      refine ⟨9079128671280580344265085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6052752447520386896176723 9079128671280580344265085)
      ·
        refine ⟨3404673251730217629099407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9079128671280580344265085 3404673251730217629099407)
        ·
          refine ⟨5107009877595326443649111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3404673251730217629099407 5107009877595326443649111)
          ·
            refine ⟨7660514816392989665473667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107009877595326443649111 7660514816392989665473667)
            ·
              refine ⟨11490772224589484498210501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7660514816392989665473667 11490772224589484498210501)
              ·
                refine ⟨2154519792110528343414469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11490772224589484498210501 2154519792110528343414469)
                ·
                  refine ⟨403972461020724064390213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154519792110528343414469 403972461020724064390213)
                  ·
                    rfl

theorem cell22_3540301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3540301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540301 prefixEnd_3540301 := by exact prefixLift 3540301
  have htrace : WordTrace (prefixWord ++ tailWord_3540301) baseStart_3540301 baseEnd_3540301 := by
    simpa [prefixWord, tailWord_3540301, baseEnd_3540301] using wordTrace_append hprefix tailTrace_3540301
  have hstable : (prefixWord ++ tailWord_3540301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540301).length < 2 ^ (prefixWord ++ tailWord_3540301).sum := by decide
  have hdescent : baseEnd_3540301 < baseStart_3540301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540350 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3540350 : Nat := 118140960795 + 3540350 * 2 ^ 59
def prefixEnd_3540350 : Nat := 4983230072969 + 3 ^ 40 * 3540350 * 2
def baseEnd_3540350 : Nat := 1211934156763552398695489

theorem tailTrace_3540350 : CollatzResearch.WordTrace tailWord_3540350 prefixEnd_3540350 1211934156763552398695489 := by
  unfold tailWord_3540350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16140896590490508560871313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86084781815949378991313669 16140896590490508560871313)
  ·
    refine ⟨12105672442867881420653485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16140896590490508560871313 12105672442867881420653485)
    ·
      refine ⟨4539627166075455532745057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12105672442867881420653485 4539627166075455532745057)
      ·
        refine ⟨3404720374556591649558793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4539627166075455532745057 3404720374556591649558793)
        ·
          refine ⟨2553540280917443737169095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3404720374556591649558793 2553540280917443737169095)
          ·
            refine ⟨3830310421376165605753643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553540280917443737169095 3830310421376165605753643)
            ·
              refine ⟨5745465632064248408630465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830310421376165605753643 5745465632064248408630465)
              ·
                refine ⟨4309099224048186306472849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745465632064248408630465 4309099224048186306472849)
                ·
                  refine ⟨3231824418036139729854637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4309099224048186306472849 3231824418036139729854637)
                  ·
                    refine ⟨1211934156763552398695489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3231824418036139729854637 1211934156763552398695489)
                    ·
                      rfl

theorem cell22_3540350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3540350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540350 prefixEnd_3540350 := by exact prefixLift 3540350
  have htrace : WordTrace (prefixWord ++ tailWord_3540350) baseStart_3540350 baseEnd_3540350 := by
    simpa [prefixWord, tailWord_3540350, baseEnd_3540350] using wordTrace_append hprefix tailTrace_3540350
  have hstable : (prefixWord ++ tailWord_3540350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540350).length < 2 ^ (prefixWord ++ tailWord_3540350).sum := by decide
  have hdescent : baseEnd_3540350 < baseStart_3540350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540355 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 2, 5]
def baseStart_3540355 : Nat := 118140960795 + 3540355 * 2 ^ 59
def prefixEnd_3540355 : Nat := 4983230072969 + 3 ^ 40 * 3540355 * 2
def baseEnd_3540355 : Nat := 1211935868365734052320473

theorem tailTrace_3540355 : CollatzResearch.WordTrace tailWord_3540355 prefixEnd_3540355 1211935868365734052320473 := by
  unfold tailWord_3540355
  simp only [CollatzResearch.WordTrace]
  refine ⟨129127355088905954340902519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86084903392603969560601679 129127355088905954340902519)
  ·
    refine ⟨193691032633358931511353779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129127355088905954340902519 193691032633358931511353779)
    ·
      refine ⟨290536548950038397267030669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193691032633358931511353779 290536548950038397267030669)
      ·
        refine ⟨108951205856264398975136501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290536548950038397267030669 108951205856264398975136501)
        ·
          refine ⟨10214175549024787403919047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108951205856264398975136501 10214175549024787403919047)
          ·
            refine ⟨15321263323537181105878571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214175549024787403919047 15321263323537181105878571)
            ·
              refine ⟨22981894985305771658817857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15321263323537181105878571 22981894985305771658817857)
              ·
                refine ⟨17236421238979328744113393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22981894985305771658817857 17236421238979328744113393)
                ·
                  refine ⟨12927315929234496558085045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17236421238979328744113393 12927315929234496558085045)
                  ·
                    refine ⟨1211935868365734052320473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12927315929234496558085045 1211935868365734052320473)
                    ·
                      rfl

theorem cell22_3540355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_3540355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540355 prefixEnd_3540355 := by exact prefixLift 3540355
  have htrace : WordTrace (prefixWord ++ tailWord_3540355) baseStart_3540355 baseEnd_3540355 := by
    simpa [prefixWord, tailWord_3540355, baseEnd_3540355] using wordTrace_append hprefix tailTrace_3540355
  have hstable : (prefixWord ++ tailWord_3540355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540355).length < 2 ^ (prefixWord ++ tailWord_3540355).sum := by decide
  have hdescent : baseEnd_3540355 < baseStart_3540355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540372 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3540372 : Nat := 118140960795 + 3540372 * 2 ^ 59
def prefixEnd_3540372 : Nat := 4983230072969 + 3 ^ 40 * 3540372 * 2
def baseEnd_3540372 : Nat := 1211941687813151674645421

theorem tailTrace_3540372 : CollatzResearch.WordTrace tailWord_3540372 prefixEnd_3540372 1211941687813151674645421 := by
  unfold tailWord_3540372
  simp only [CollatzResearch.WordTrace]
  refine ⟨64563987564922183122135685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86085316753229577496180913 64563987564922183122135685)
  ·
    refine ⟨12105747668422909335400441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64563987564922183122135685 12105747668422909335400441)
    ·
      refine ⟨9079310751317182001550331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12105747668422909335400441 9079310751317182001550331)
      ·
        refine ⟨13618966126975773002325497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9079310751317182001550331 13618966126975773002325497)
        ·
          refine ⟨10214224595231829751744123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13618966126975773002325497 10214224595231829751744123)
          ·
            refine ⟨15321336892847744627616185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214224595231829751744123 15321336892847744627616185)
            ·
              refine ⟨11491002669635808470712139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15321336892847744627616185 11491002669635808470712139)
              ·
                refine ⟨17236504004453712706068209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491002669635808470712139 17236504004453712706068209)
                ·
                  refine ⟨12927378003340284529551157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17236504004453712706068209 12927378003340284529551157)
                  ·
                    refine ⟨1211941687813151674645421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12927378003340284529551157 1211941687813151674645421)
                    ·
                      rfl

theorem cell22_3540372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3540372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540372 prefixEnd_3540372 := by exact prefixLift 3540372
  have htrace : WordTrace (prefixWord ++ tailWord_3540372) baseStart_3540372 baseEnd_3540372 := by
    simpa [prefixWord, tailWord_3540372, baseEnd_3540372] using wordTrace_append hprefix tailTrace_3540372
  have hstable : (prefixWord ++ tailWord_3540372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540372).length < 2 ^ (prefixWord ++ tailWord_3540372).sum := by decide
  have hdescent : baseEnd_3540372 < baseStart_3540372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540387 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 1, 4]
def baseStart_3540387 : Nat := 118140960795 + 3540387 * 2 ^ 59
def prefixEnd_3540387 : Nat := 4983230072969 + 3 ^ 40 * 3540387 * 2
def baseEnd_3540387 : Nat := 1211946822619696635520375

theorem tailTrace_3540387 : CollatzResearch.WordTrace tailWord_3540387 prefixEnd_3540387 1211946822619696635520375 := by
  unfold tailWord_3540387
  simp only [CollatzResearch.WordTrace]
  refine ⟨129128522224790023806067415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86085681483193349204044943 129128522224790023806067415)
  ·
    refine ⟨193692783337185035709101123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129128522224790023806067415 193692783337185035709101123)
    ·
      refine ⟨290539175005777553563651685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193692783337185035709101123 290539175005777553563651685)
      ·
        refine ⟨54476095313583291293184691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290539175005777553563651685 54476095313583291293184691)
        ·
          refine ⟨81714142970374936939777037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54476095313583291293184691 81714142970374936939777037)
          ·
            refine ⟨30642803613890601352416389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81714142970374936939777037 30642803613890601352416389)
            ·
              refine ⟨5745525677604487753578073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30642803613890601352416389 5745525677604487753578073)
              ·
                refine ⟨4309144258203365815183555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745525677604487753578073 4309144258203365815183555)
                ·
                  refine ⟨6463716387305048722775333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4309144258203365815183555 6463716387305048722775333)
                  ·
                    refine ⟨1211946822619696635520375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6463716387305048722775333 1211946822619696635520375)
                    ·
                      rfl

theorem cell22_3540387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 4].length) (baseStart_3540387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540387 prefixEnd_3540387 := by exact prefixLift 3540387
  have htrace : WordTrace (prefixWord ++ tailWord_3540387) baseStart_3540387 baseEnd_3540387 := by
    simpa [prefixWord, tailWord_3540387, baseEnd_3540387] using wordTrace_append hprefix tailTrace_3540387
  have hstable : (prefixWord ++ tailWord_3540387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540387).length < 2 ^ (prefixWord ++ tailWord_3540387).sum := by decide
  have hdescent : baseEnd_3540387 < baseStart_3540387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540402 : List Nat := [3, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_3540402 : Nat := 118140960795 + 3540402 * 2 ^ 59
def prefixEnd_3540402 : Nat := 4983230072969 + 3 ^ 40 * 3540402 * 2
def baseEnd_3540402 : Nat := 403983985808747198798443

theorem tailTrace_3540402 : CollatzResearch.WordTrace tailWord_3540402 prefixEnd_3540402 403983985808747198798443 := by
  unfold tailWord_3540402
  simp only [CollatzResearch.WordTrace]
  refine ⟨32282267329933920341965865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86086046213157120911908973 32282267329933920341965865)
  ·
    refine ⟨24211700497450440256474399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32282267329933920341965865 24211700497450440256474399)
    ·
      refine ⟨36317550746175660384711599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24211700497450440256474399 36317550746175660384711599)
      ·
        refine ⟨54476326119263490577067399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36317550746175660384711599 54476326119263490577067399)
        ·
          refine ⟨81714489178895235865601099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54476326119263490577067399 81714489178895235865601099)
          ·
            refine ⟨122571733768342853798401649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81714489178895235865601099 122571733768342853798401649)
            ·
              refine ⟨91928800326257140348801237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122571733768342853798401649 91928800326257140348801237)
              ·
                refine ⟨2154581257646651726925029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91928800326257140348801237 2154581257646651726925029)
                ·
                  refine ⟨403983985808747198798443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2154581257646651726925029 403983985808747198798443)
                  ·
                    rfl

theorem cell22_3540402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_3540402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540402 prefixEnd_3540402 := by exact prefixLift 3540402
  have htrace : WordTrace (prefixWord ++ tailWord_3540402) baseStart_3540402 baseEnd_3540402 := by
    simpa [prefixWord, tailWord_3540402, baseEnd_3540402] using wordTrace_append hprefix tailTrace_3540402
  have hstable : (prefixWord ++ tailWord_3540402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540402).length < 2 ^ (prefixWord ++ tailWord_3540402).sum := by decide
  have hdescent : baseEnd_3540402 < baseStart_3540402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540430 : List Nat := [4, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3540430 : Nat := 118140960795 + 3540430 * 2 ^ 59
def prefixEnd_3540430 : Nat := 4983230072969 + 3 ^ 40 * 3540430 * 2
def baseEnd_3540430 : Nat := 134662393599828761855027

theorem tailTrace_3540430 : CollatzResearch.WordTrace tailWord_3540430 prefixEnd_3540430 134662393599828761855027 := by
  unfold tailWord_3540430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16141261320454280268735343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86086727042422828099921829 16141261320454280268735343)
  ·
    refine ⟨24211891980681420403103015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16141261320454280268735343 24211891980681420403103015)
    ·
      refine ⟨36317837971022130604654523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24211891980681420403103015 36317837971022130604654523)
      ·
        refine ⟨54476756956533195906981785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36317837971022130604654523 54476756956533195906981785)
        ·
          refine ⟨40857567717399896930236339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54476756956533195906981785 40857567717399896930236339)
          ·
            refine ⟨61286351576099845395354509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40857567717399896930236339 61286351576099845395354509)
            ·
              refine ⟨22982381841037442023257941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61286351576099845395354509 22982381841037442023257941)
              ·
                refine ⟨134662393599828761855027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22982381841037442023257941 134662393599828761855027)
                ·
                  rfl

theorem cell22_3540430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3540430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540430 prefixEnd_3540430 := by exact prefixLift 3540430
  have htrace : WordTrace (prefixWord ++ tailWord_3540430) baseStart_3540430 baseEnd_3540430 := by
    simpa [prefixWord, tailWord_3540430, baseEnd_3540430] using wordTrace_append hprefix tailTrace_3540430
  have hstable : (prefixWord ++ tailWord_3540430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540430).length < 2 ^ (prefixWord ++ tailWord_3540430).sum := by decide
  have hdescent : baseEnd_3540430 < baseStart_3540430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540526 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_3540526 : Nat := 118140960795 + 3540526 * 2 ^ 59
def prefixEnd_3540526 : Nat := 4983230072969 + 3 ^ 40 * 3540526 * 2
def baseEnd_3540526 : Nat := 403998135053448868764983

theorem tailTrace_3540526 : CollatzResearch.WordTrace tailWord_3540526 prefixEnd_3540526 403998135053448868764983 := by
  unfold tailWord_3540526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16141698996410806318172179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86089061314190967030251621 16141698996410806318172179)
  ·
    refine ⟨24212548494616209477258269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16141698996410806318172179 24212548494616209477258269)
    ·
      refine ⟨9079705685481078553971851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24212548494616209477258269 9079705685481078553971851)
      ·
        refine ⟨13619558528221617830957777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9079705685481078553971851 13619558528221617830957777)
        ·
          refine ⟨10214668896166213373218333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13619558528221617830957777 10214668896166213373218333)
          ·
            refine ⟨3830500836062330014956875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10214668896166213373218333 3830500836062330014956875)
            ·
              refine ⟨5745751254093495022435313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830500836062330014956875 5745751254093495022435313)
              ·
                refine ⟨4309313440570121266826485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5745751254093495022435313 4309313440570121266826485)
                ·
                  refine ⟨403998135053448868764983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309313440570121266826485 403998135053448868764983)
                  ·
                    rfl

theorem cell22_3540526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_3540526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540526 prefixEnd_3540526 := by exact prefixLift 3540526
  have htrace : WordTrace (prefixWord ++ tailWord_3540526) baseStart_3540526 baseEnd_3540526 := by
    simpa [prefixWord, tailWord_3540526, baseEnd_3540526] using wordTrace_append hprefix tailTrace_3540526
  have hstable : (prefixWord ++ tailWord_3540526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540526).length < 2 ^ (prefixWord ++ tailWord_3540526).sum := by decide
  have hdescent : baseEnd_3540526 < baseStart_3540526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540537 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 6]
def baseStart_3540537 : Nat := 118140960795 + 3540537 * 2 ^ 59
def prefixEnd_3540537 : Nat := 4983230072969 + 3 ^ 40 * 3540537 * 2
def baseEnd_3540537 : Nat := 403999390228382081423305

theorem tailTrace_3540537 : CollatzResearch.WordTrace tailWord_3540537 prefixEnd_3540537 403999390228382081423305 := by
  unfold tailWord_3540537
  simp only [CollatzResearch.WordTrace]
  refine ⟨129133993174246599424027865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86089328782831066282685243 129133993174246599424027865)
  ·
    refine ⟨96850494880684949568020899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129133993174246599424027865 96850494880684949568020899)
    ·
      refine ⟨145275742321027424352031349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96850494880684949568020899 145275742321027424352031349)
      ·
        refine ⟨13619600842596321033002939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145275742321027424352031349 13619600842596321033002939)
        ·
          refine ⟨20429401263894481549504409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13619600842596321033002939 20429401263894481549504409)
          ·
            refine ⟨15322050947920861162128307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20429401263894481549504409 15322050947920861162128307)
            ·
              refine ⟨22983076421881291743192461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15322050947920861162128307 22983076421881291743192461)
              ·
                refine ⟨8618653658205484403697173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22983076421881291743192461 8618653658205484403697173)
                ·
                  refine ⟨403999390228382081423305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8618653658205484403697173 403999390228382081423305)
                  ·
                    rfl

theorem cell22_3540537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_3540537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540537 prefixEnd_3540537 := by exact prefixLift 3540537
  have htrace : WordTrace (prefixWord ++ tailWord_3540537) baseStart_3540537 baseEnd_3540537 := by
    simpa [prefixWord, tailWord_3540537, baseEnd_3540537] using wordTrace_append hprefix tailTrace_3540537
  have hstable : (prefixWord ++ tailWord_3540537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540537).length < 2 ^ (prefixWord ++ tailWord_3540537).sum := by decide
  have hdescent : baseEnd_3540537 < baseStart_3540537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540567 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3540567 : Nat := 118140960795 + 3540567 * 2 ^ 59
def prefixEnd_3540567 : Nat := 4983230072969 + 3 ^ 40 * 3540567 * 2
def baseEnd_3540567 : Nat := 1212008440298236166019823

theorem tailTrace_3540567 : CollatzResearch.WordTrace tailWord_3540567 prefixEnd_3540567 1212008440298236166019823 := by
  unfold tailWord_3540567
  simp only [CollatzResearch.WordTrace]
  refine ⟨129135087364137914547619955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86090058242758609698413303 129135087364137914547619955)
  ·
    refine ⟨193702631046206871821429933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129135087364137914547619955 193702631046206871821429933)
    ·
      refine ⟨72638486642327576933036225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193702631046206871821429933 72638486642327576933036225)
      ·
        refine ⟨54478864981745682699777169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72638486642327576933036225 54478864981745682699777169)
        ·
          refine ⟨40859148736309262024832877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54478864981745682699777169 40859148736309262024832877)
          ·
            refine ⟨15322180776115973259312329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40859148736309262024832877 15322180776115973259312329)
            ·
              refine ⟨11491635582086979944484247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15322180776115973259312329 11491635582086979944484247)
              ·
                refine ⟨17237453373130469916726371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491635582086979944484247 17237453373130469916726371)
                ·
                  refine ⟨25856180059695704875089557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17237453373130469916726371 25856180059695704875089557)
                  ·
                    refine ⟨1212008440298236166019823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25856180059695704875089557 1212008440298236166019823)
                    ·
                      rfl

theorem cell22_3540567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3540567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540567 prefixEnd_3540567 := by exact prefixLift 3540567
  have htrace : WordTrace (prefixWord ++ tailWord_3540567) baseStart_3540567 baseEnd_3540567 := by
    simpa [prefixWord, tailWord_3540567, baseEnd_3540567] using wordTrace_append hprefix tailTrace_3540567
  have hstable : (prefixWord ++ tailWord_3540567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540567).length < 2 ^ (prefixWord ++ tailWord_3540567).sum := by decide
  have hdescent : baseEnd_3540567 < baseStart_3540567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540584 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3540584 : Nat := 118140960795 + 3540584 * 2 ^ 59
def prefixEnd_3540584 : Nat := 4983230072969 + 3 ^ 40 * 3540584 * 2
def baseEnd_3540584 : Nat := 1212014259745653788344771

theorem tailTrace_3540584 : CollatzResearch.WordTrace tailWord_3540584 prefixEnd_3540584 1212014259745653788344771 := by
  unfold tailWord_3540584
  simp only [CollatzResearch.WordTrace]
  refine ⟨64567853702538163225494403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86090471603384217633992537 64567853702538163225494403)
  ·
    refine ⟨96851780553807244838241605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64567853702538163225494403 96851780553807244838241605)
    ·
      refine ⟨18159708853838858407170301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96851780553807244838241605 18159708853838858407170301)
      ·
        refine ⟨6809890820189571902688863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18159708853838858407170301 6809890820189571902688863)
        ·
          refine ⟨10214836230284357854033295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6809890820189571902688863 10214836230284357854033295)
          ·
            refine ⟨15322254345426536781049943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214836230284357854033295 15322254345426536781049943)
            ·
              refine ⟨22983381518139805171574915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15322254345426536781049943 22983381518139805171574915)
              ·
                refine ⟨34475072277209707757362373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22983381518139805171574915 34475072277209707757362373)
                ·
                  refine ⟨6464076051976820204505445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34475072277209707757362373 6464076051976820204505445)
                  ·
                    refine ⟨1212014259745653788344771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6464076051976820204505445 1212014259745653788344771)
                    ·
                      rfl

theorem cell22_3540584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3540584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540584 prefixEnd_3540584 := by exact prefixLift 3540584
  have htrace : WordTrace (prefixWord ++ tailWord_3540584) baseStart_3540584 baseEnd_3540584 := by
    simpa [prefixWord, tailWord_3540584, baseEnd_3540584] using wordTrace_append hprefix tailTrace_3540584
  have hstable : (prefixWord ++ tailWord_3540584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540584).length < 2 ^ (prefixWord ++ tailWord_3540584).sum := by decide
  have hdescent : baseEnd_3540584 < baseStart_3540584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540644 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 5]
def baseStart_3540644 : Nat := 118140960795 + 3540644 * 2 ^ 59
def prefixEnd_3540644 : Nat := 4983230072969 + 3 ^ 40 * 3540644 * 2
def baseEnd_3540644 : Nat := 404011599657277877281529

theorem tailTrace_3540644 : CollatzResearch.WordTrace tailWord_3540644 prefixEnd_3540644 404011599657277877281529 := by
  unfold tailWord_3540644
  simp only [CollatzResearch.WordTrace]
  refine ⟨64568947892429478349086493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86091930523239304465448657 64568947892429478349086493)
  ·
    refine ⟨24213355459661054380907435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64568947892429478349086493 24213355459661054380907435)
    ·
      refine ⟨36320033189491581571361153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24213355459661054380907435 36320033189491581571361153)
      ·
        refine ⟨27240024892118686178520865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36320033189491581571361153 27240024892118686178520865)
        ·
          refine ⟨20430018669089014633890649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27240024892118686178520865 20430018669089014633890649)
          ·
            refine ⟨15322514001816760975417987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20430018669089014633890649 15322514001816760975417987)
            ·
              refine ⟨22983771002725141463126981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15322514001816760975417987 22983771002725141463126981)
              ·
                refine ⟨4309457063010964024336309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22983771002725141463126981 4309457063010964024336309)
                ·
                  refine ⟨404011599657277877281529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309457063010964024336309 404011599657277877281529)
                  ·
                    rfl

theorem cell22_3540644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_3540644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540644 prefixEnd_3540644 := by exact prefixLift 3540644
  have htrace : WordTrace (prefixWord ++ tailWord_3540644) baseStart_3540644 baseEnd_3540644 := by
    simpa [prefixWord, tailWord_3540644, baseEnd_3540644] using wordTrace_append hprefix tailTrace_3540644
  have hstable : (prefixWord ++ tailWord_3540644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540644).length < 2 ^ (prefixWord ++ tailWord_3540644).sum := by decide
  have hdescent : baseEnd_3540644 < baseStart_3540644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540721 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 1, 5]
def baseStart_3540721 : Nat := 118140960795 + 3540721 * 2 ^ 59
def prefixEnd_3540721 : Nat := 4983230072969 + 3 ^ 40 * 3540721 * 2
def baseEnd_3540721 : Nat := 1212061157645431097669351

theorem tailTrace_3540721 : CollatzResearch.WordTrace tailWord_3540721 prefixEnd_3540721 1212061157645431097669351 := by
  unfold tailWord_3540721
  simp only [CollatzResearch.WordTrace]
  refine ⟨129140704205579998848726017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86093802803719999232484011 129140704205579998848726017)
  ·
    refine ⟨96855528154184999136544513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129140704205579998848726017 96855528154184999136544513)
    ·
      refine ⟨72641646115638749352408385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96855528154184999136544513 72641646115638749352408385)
      ·
        refine ⟨54481234586729062014306289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72641646115638749352408385 54481234586729062014306289)
        ·
          refine ⟨40860925940046796510729717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54481234586729062014306289 40860925940046796510729717)
          ·
            refine ⟨3830711806879387172880911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40860925940046796510729717 3830711806879387172880911)
            ·
              refine ⟨5746067710319080759321367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3830711806879387172880911 5746067710319080759321367)
              ·
                refine ⟨8619101565478621138982051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5746067710319080759321367 8619101565478621138982051)
                ·
                  refine ⟨12928652348217931708473077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8619101565478621138982051 12928652348217931708473077)
                  ·
                    refine ⟨1212061157645431097669351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12928652348217931708473077 1212061157645431097669351)
                    ·
                      rfl

theorem cell22_3540721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_3540721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540721 prefixEnd_3540721 := by exact prefixLift 3540721
  have htrace : WordTrace (prefixWord ++ tailWord_3540721) baseStart_3540721 baseEnd_3540721 := by
    simpa [prefixWord, tailWord_3540721, baseEnd_3540721] using wordTrace_append hprefix tailTrace_3540721
  have hstable : (prefixWord ++ tailWord_3540721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540721).length < 2 ^ (prefixWord ++ tailWord_3540721).sum := by decide
  have hdescent : baseEnd_3540721 < baseStart_3540721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540764 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3540764 : Nat := 118140960795 + 3540764 * 2 ^ 59
def prefixEnd_3540764 : Nat := 4983230072969 + 3 ^ 40 * 3540764 * 2
def baseEnd_3540764 : Nat := 1212075877424193318844219

theorem tailTrace_3540764 : CollatzResearch.WordTrace tailWord_3540764 prefixEnd_3540764 1212075877424193318844219 := by
  unfold tailWord_3540764
  simp only [CollatzResearch.WordTrace]
  refine ⟨64571136272212108596270673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86094848362949478128360897 64571136272212108596270673)
  ·
    refine ⟨48428352204159081447203005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64571136272212108596270673 48428352204159081447203005)
    ·
      refine ⟨18160632076559655542701127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48428352204159081447203005 18160632076559655542701127)
      ·
        refine ⟨27240948114839483314051691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18160632076559655542701127 27240948114839483314051691)
        ·
          refine ⟨40861422172259224971077537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27240948114839483314051691 40861422172259224971077537)
          ·
            refine ⟨30646066629194418728308153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40861422172259224971077537 30646066629194418728308153)
            ·
              refine ⟨22984549971895814046231115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30646066629194418728308153 22984549971895814046231115)
              ·
                refine ⟨34476824957843721069346673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22984549971895814046231115 34476824957843721069346673)
                ·
                  refine ⟨25857618718382790802010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34476824957843721069346673 25857618718382790802010005)
                  ·
                    refine ⟨1212075877424193318844219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25857618718382790802010005 1212075877424193318844219)
                    ·
                      rfl

theorem cell22_3540764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3540764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540764 prefixEnd_3540764 := by exact prefixLift 3540764
  have htrace : WordTrace (prefixWord ++ tailWord_3540764) baseStart_3540764 baseEnd_3540764 := by
    simpa [prefixWord, tailWord_3540764, baseEnd_3540764] using wordTrace_append hprefix tailTrace_3540764
  have hstable : (prefixWord ++ tailWord_3540764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540764).length < 2 ^ (prefixWord ++ tailWord_3540764).sum := by decide
  have hdescent : baseEnd_3540764 < baseStart_3540764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540813 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3540813 : Nat := 118140960795 + 3540813 * 2 ^ 59
def prefixEnd_3540813 : Nat := 4983230072969 + 3 ^ 40 * 3540813 * 2
def baseEnd_3540813 : Nat := 404030883708524508123023

theorem tailTrace_3540813 : CollatzResearch.WordTrace tailWord_3540813 prefixEnd_3540813 404030883708524508123023 := by
  unfold tailWord_3540813
  simp only [CollatzResearch.WordTrace]
  refine ⟨129144059721246698561075093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86096039814164465707383395 129144059721246698561075093)
  ·
    refine ⟨6053627799433438995050395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129144059721246698561075093 6053627799433438995050395)
    ·
      refine ⟨9080441699150158492575593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053627799433438995050395 9080441699150158492575593)
      ·
        refine ⟨6810331274362618869431695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9080441699150158492575593 6810331274362618869431695)
        ·
          refine ⟨10215496911543928304147543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810331274362618869431695 10215496911543928304147543)
          ·
            refine ⟨15323245367315892456221315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10215496911543928304147543 15323245367315892456221315)
            ·
              refine ⟨22984868050973838684331973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15323245367315892456221315 22984868050973838684331973)
              ·
                refine ⟨4309662759557594753312245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22984868050973838684331973 4309662759557594753312245)
                ·
                  refine ⟨404030883708524508123023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309662759557594753312245 404030883708524508123023)
                  ·
                    rfl

theorem cell22_3540813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3540813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540813 prefixEnd_3540813 := by exact prefixLift 3540813
  have htrace : WordTrace (prefixWord ++ tailWord_3540813) baseStart_3540813 baseEnd_3540813 := by
    simpa [prefixWord, tailWord_3540813, baseEnd_3540813] using wordTrace_append hprefix tailTrace_3540813
  have hstable : (prefixWord ++ tailWord_3540813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540813).length < 2 ^ (prefixWord ++ tailWord_3540813).sum := by decide
  have hdescent : baseEnd_3540813 < baseStart_3540813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540817 : List Nat := [1, 2, 2, 1, 5, 3, 2, 2, 1, 3]
def baseStart_3540817 : Nat := 118140960795 + 3540817 * 2 ^ 59
def prefixEnd_3540817 : Nat := 4983230072969 + 3 ^ 40 * 3540817 * 2
def baseEnd_3540817 : Nat := 1212094020407318847269057

theorem tailTrace_3540817 : CollatzResearch.WordTrace tailWord_3540817 prefixEnd_3540817 1212094020407318847269057 := by
  unfold tailWord_3540817
  simp only [CollatzResearch.WordTrace]
  refine ⟨129144205613232207244220705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86096137075488138162813803 129144205613232207244220705)
  ·
    refine ⟨96858154209924155433165529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129144205613232207244220705 96858154209924155433165529)
    ·
      refine ⟨72643615657443116574874147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96858154209924155433165529 72643615657443116574874147)
      ·
        refine ⟨108965423486164674862311221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72643615657443116574874147 108965423486164674862311221)
        ·
          refine ⟨10215508451827938268341677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108965423486164674862311221 10215508451827938268341677)
          ·
            refine ⟨3830815669435476850628129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10215508451827938268341677 3830815669435476850628129)
            ·
              refine ⟨2873111752076607637971097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3830815669435476850628129 2873111752076607637971097)
              ·
                refine ⟨2154833814057455728478323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873111752076607637971097 2154833814057455728478323)
                ·
                  refine ⟨3232250721086183592717485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2154833814057455728478323 3232250721086183592717485)
                  ·
                    refine ⟨1212094020407318847269057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3232250721086183592717485 1212094020407318847269057)
                    ·
                      rfl

theorem cell22_3540817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_3540817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540817 prefixEnd_3540817 := by exact prefixLift 3540817
  have htrace : WordTrace (prefixWord ++ tailWord_3540817) baseStart_3540817 baseEnd_3540817 := by
    simpa [prefixWord, tailWord_3540817, baseEnd_3540817] using wordTrace_append hprefix tailTrace_3540817
  have hstable : (prefixWord ++ tailWord_3540817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540817).length < 2 ^ (prefixWord ++ tailWord_3540817).sum := by decide
  have hdescent : baseEnd_3540817 < baseStart_3540817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540828 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3540828 : Nat := 118140960795 + 3540828 * 2 ^ 59
def prefixEnd_3540828 : Nat := 4983230072969 + 3 ^ 40 * 3540828 * 2
def baseEnd_3540828 : Nat := 1212097785932118485244023

theorem tailTrace_3540828 : CollatzResearch.WordTrace tailWord_3540828 prefixEnd_3540828 1212097785932118485244023 := by
  unfold tailWord_3540828
  simp only [CollatzResearch.WordTrace]
  refine ⟨64572303408096178061435569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86096404544128237415247425 64572303408096178061435569)
  ·
    refine ⟨48429227556072133546076677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64572303408096178061435569 48429227556072133546076677)
    ·
      refine ⟨9080480166763525039889377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48429227556072133546076677 9080480166763525039889377)
      ·
        refine ⟨6810360125072643779917033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9080480166763525039889377 6810360125072643779917033)
        ·
          refine ⟨5107770093804482834937775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6810360125072643779917033 5107770093804482834937775)
          ·
            refine ⟨7661655140706724252406663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5107770093804482834937775 7661655140706724252406663)
            ·
              refine ⟨11492482711060086378609995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661655140706724252406663 11492482711060086378609995)
              ·
                refine ⟨17238724066590129567914993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11492482711060086378609995 17238724066590129567914993)
                ·
                  refine ⟨12929043049942597175936245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17238724066590129567914993 12929043049942597175936245)
                  ·
                    refine ⟨1212097785932118485244023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12929043049942597175936245 1212097785932118485244023)
                    ·
                      rfl

theorem cell22_3540828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3540828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540828 prefixEnd_3540828 := by exact prefixLift 3540828
  have htrace : WordTrace (prefixWord ++ tailWord_3540828) baseStart_3540828 baseEnd_3540828 := by
    simpa [prefixWord, tailWord_3540828, baseEnd_3540828] using wordTrace_append hprefix tailTrace_3540828
  have hstable : (prefixWord ++ tailWord_3540828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540828).length < 2 ^ (prefixWord ++ tailWord_3540828).sum := by decide
  have hdescent : baseEnd_3540828 < baseStart_3540828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540869 : List Nat := [1, 3, 1, 1, 3, 2, 11]
def baseStart_3540869 : Nat := 118140960795 + 3540869 * 2 ^ 59
def prefixEnd_3540869 : Nat := 4983230072969 + 3 ^ 40 * 3540869 * 2
def baseEnd_3540869 : Nat := 44893030410000297961811

theorem tailTrace_3540869 : CollatzResearch.WordTrace tailWord_3540869 prefixEnd_3540869 44893030410000297961811 := by
  unfold tailWord_3540869
  simp only [CollatzResearch.WordTrace]
  refine ⟨129146102209043820125113661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86097401472695880083409107 129146102209043820125113661)
  ·
    refine ⟨48429788328391432546917623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129146102209043820125113661 48429788328391432546917623)
    ·
      refine ⟨72644682492587148820376435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48429788328391432546917623 72644682492587148820376435)
      ·
        refine ⟨108967023738880723230564653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72644682492587148820376435 108967023738880723230564653)
        ·
          refine ⟨40862633902080271211461745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108967023738880723230564653 40862633902080271211461745)
          ·
            refine ⟨30646975426560203408596309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40862633902080271211461745 30646975426560203408596309)
            ·
              refine ⟨44893030410000297961811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30646975426560203408596309 44893030410000297961811)
              ·
                rfl

theorem cell22_3540869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 11].length) (baseStart_3540869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540869 prefixEnd_3540869 := by exact prefixLift 3540869
  have htrace : WordTrace (prefixWord ++ tailWord_3540869) baseStart_3540869 baseEnd_3540869 := by
    simpa [prefixWord, tailWord_3540869, baseEnd_3540869] using wordTrace_append hprefix tailTrace_3540869
  have hstable : (prefixWord ++ tailWord_3540869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540869).length < 2 ^ (prefixWord ++ tailWord_3540869).sum := by decide
  have hdescent : baseEnd_3540869 < baseStart_3540869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540903 : List Nat := [1, 1, 6, 1, 2, 1, 4, 6]
def baseStart_3540903 : Nat := 118140960795 + 3540903 * 2 ^ 59
def prefixEnd_3540903 : Nat := 4983230072969 + 3 ^ 40 * 3540903 * 2
def baseEnd_3540903 : Nat := 134680384440538143290977

theorem tailTrace_3540903 : CollatzResearch.WordTrace tailWord_3540903 prefixEnd_3540903 134680384440538143290977 := by
  unfold tailWord_3540903
  simp only [CollatzResearch.WordTrace]
  refine ⟨129147342290920643931851363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86098228193947095954567575 129147342290920643931851363)
  ·
    refine ⟨193721013436380965897777045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129147342290920643931851363 193721013436380965897777045)
    ·
      refine ⟨9080672504830357776458299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193721013436380965897777045 9080672504830357776458299)
      ·
        refine ⟨13621008757245536664687449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080672504830357776458299 13621008757245536664687449)
        ·
          refine ⟨10215756567934152498515587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13621008757245536664687449 10215756567934152498515587)
          ·
            refine ⟨15323634851901228747773381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10215756567934152498515587 15323634851901228747773381)
            ·
              refine ⟨2873181534731480390207509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15323634851901228747773381 2873181534731480390207509)
              ·
                refine ⟨134680384440538143290977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2873181534731480390207509 134680384440538143290977)
                ·
                  rfl

theorem cell22_3540903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 6].length) (baseStart_3540903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540903 prefixEnd_3540903 := by exact prefixLift 3540903
  have htrace : WordTrace (prefixWord ++ tailWord_3540903) baseStart_3540903 baseEnd_3540903 := by
    simpa [prefixWord, tailWord_3540903, baseEnd_3540903] using wordTrace_append hprefix tailTrace_3540903
  have hstable : (prefixWord ++ tailWord_3540903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540903).length < 2 ^ (prefixWord ++ tailWord_3540903).sum := by decide
  have hdescent : baseEnd_3540903 < baseStart_3540903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3540948 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 5]
def baseStart_3540948 : Nat := 118140960795 + 3540948 * 2 ^ 59
def prefixEnd_3540948 : Nat := 4983230072969 + 3 ^ 40 * 3540948 * 2
def baseEnd_3540948 : Nat := 404046288128159390747885

theorem tailTrace_3540948 : CollatzResearch.WordTrace tailWord_3540948 prefixEnd_3540948 404046288128159390747885 := by
  unfold tailWord_3540948
  simp only [CollatzResearch.WordTrace]
  refine ⟨64574491787878808308619749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86099322383838411078159665 64574491787878808308619749)
  ·
    refine ⟨12107717210227276557866203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64574491787878808308619749 12107717210227276557866203)
    ·
      refine ⟨18161575815340914836799305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12107717210227276557866203 18161575815340914836799305)
      ·
        refine ⟨13621181861505686127599479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18161575815340914836799305 13621181861505686127599479)
        ·
          refine ⟨20431772792258529191399219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13621181861505686127599479 20431772792258529191399219)
          ·
            refine ⟨30647659188387793787098829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20431772792258529191399219 30647659188387793787098829)
            ·
              refine ⟨11492872195645422670162061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30647659188387793787098829 11492872195645422670162061)
              ·
                refine ⟨4309827073367033501310773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11492872195645422670162061 4309827073367033501310773)
                ·
                  refine ⟨404046288128159390747885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4309827073367033501310773 404046288128159390747885)
                  ·
                    rfl

theorem cell22_3540948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_3540948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3540948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3540948 prefixEnd_3540948 := by exact prefixLift 3540948
  have htrace : WordTrace (prefixWord ++ tailWord_3540948) baseStart_3540948 baseEnd_3540948 := by
    simpa [prefixWord, tailWord_3540948, baseEnd_3540948] using wordTrace_append hprefix tailTrace_3540948
  have hstable : (prefixWord ++ tailWord_3540948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3540948).length < 2 ^ (prefixWord ++ tailWord_3540948).sum := by decide
  have hdescent : baseEnd_3540948 < baseStart_3540948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3540948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541038 : List Nat := [4, 1, 3, 1, 1, 3, 9]
def baseStart_3541038 : Nat := 118140960795 + 3541038 * 2 ^ 59
def prefixEnd_3541038 : Nat := 4983230072969 + 3 ^ 40 * 3541038 * 2
def baseEnd_3541038 : Nat := 44895173082361034721977

theorem tailTrace_3541038 : CollatzResearch.WordTrace tailWord_3541038 prefixEnd_3541038 44895173082361034721977 := by
  unfold tailWord_3541038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144033268178945248501971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86101510763621041325343845 16144033268178945248501971)
  ·
    refine ⟨24216049902268417872752957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16144033268178945248501971 24216049902268417872752957)
    ·
      refine ⟨9081018713350656702282359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24216049902268417872752957 9081018713350656702282359)
      ·
        refine ⟨13621528070025985053423539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9081018713350656702282359 13621528070025985053423539)
        ·
          refine ⟨20432292105038977580135309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13621528070025985053423539 20432292105038977580135309)
          ·
            refine ⟨7662109539389616592550741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20432292105038977580135309 7662109539389616592550741)
            ·
              refine ⟨44895173082361034721977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7662109539389616592550741 44895173082361034721977)
              ·
                rfl

theorem cell22_3541038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 9].length) (baseStart_3541038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541038 prefixEnd_3541038 := by exact prefixLift 3541038
  have htrace : WordTrace (prefixWord ++ tailWord_3541038) baseStart_3541038 baseEnd_3541038 := by
    simpa [prefixWord, tailWord_3541038, baseEnd_3541038] using wordTrace_append hprefix tailTrace_3541038
  have hstable : (prefixWord ++ tailWord_3541038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541038).length < 2 ^ (prefixWord ++ tailWord_3541038).sum := by decide
  have hdescent : baseEnd_3541038 < baseStart_3541038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541042 : List Nat := [3, 2, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_3541042 : Nat := 118140960795 + 3541042 * 2 ^ 59
def prefixEnd_3541042 : Nat := 4983230072969 + 3 ^ 40 * 3541042 * 2
def baseEnd_3541042 : Nat := 1212171042505493260393367

theorem tailTrace_3541042 : CollatzResearch.WordTrace tailWord_3541042 prefixEnd_3541042 1212171042505493260393367 := by
  unfold tailWord_3541042
  simp only [CollatzResearch.WordTrace]
  refine ⟨32288103009354267667790345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86101608024944713780774253 32288103009354267667790345)
  ·
    refine ⟨24216077257015700750842759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32288103009354267667790345 24216077257015700750842759)
    ·
      refine ⟨36324115885523551126264139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24216077257015700750842759 36324115885523551126264139)
      ·
        refine ⟨54486173828285326689396209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36324115885523551126264139 54486173828285326689396209)
        ·
          refine ⟨40864630371213995017047157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54486173828285326689396209 40864630371213995017047157)
          ·
            refine ⟨3831059097301312032848171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40864630371213995017047157 3831059097301312032848171)
            ·
              refine ⟨5746588645951968049272257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831059097301312032848171 5746588645951968049272257)
              ·
                refine ⟨4309941484463976036954193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746588645951968049272257 4309941484463976036954193)
                ·
                  refine ⟨3232456113347982027715645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4309941484463976036954193 3232456113347982027715645)
                  ·
                    refine ⟨1212171042505493260393367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3232456113347982027715645 1212171042505493260393367)
                    ·
                      rfl

theorem cell22_3541042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_3541042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541042 prefixEnd_3541042 := by exact prefixLift 3541042
  have htrace : WordTrace (prefixWord ++ tailWord_3541042) baseStart_3541042 baseEnd_3541042 := by
    simpa [prefixWord, tailWord_3541042, baseEnd_3541042] using wordTrace_append hprefix tailTrace_3541042
  have hstable : (prefixWord ++ tailWord_3541042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541042).length < 2 ^ (prefixWord ++ tailWord_3541042).sum := by decide
  have hdescent : baseEnd_3541042 < baseStart_3541042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541070 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_3541070 : Nat := 118140960795 + 3541070 * 2 ^ 59
def prefixEnd_3541070 : Nat := 4983230072969 + 3 ^ 40 * 3541070 * 2
def baseEnd_3541070 : Nat := 1212180627477710520693281

theorem tailTrace_3541070 : CollatzResearch.WordTrace tailWord_3541070 prefixEnd_3541070 1212180627477710520693281 := by
  unfold tailWord_3541070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144179160164453931647583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 86102288854210420968787109 16144179160164453931647583)
  ·
    refine ⟨24216268740246680897471375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16144179160164453931647583 24216268740246680897471375)
    ·
      refine ⟨36324403110370021346207063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24216268740246680897471375 36324403110370021346207063)
      ·
        refine ⟨54486604665555032019310595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36324403110370021346207063 54486604665555032019310595)
        ·
          refine ⟨81729906998332548028965893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54486604665555032019310595 81729906998332548028965893)
          ·
            refine ⟨15324357562187352755431105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81729906998332548028965893 15324357562187352755431105)
            ·
              refine ⟨11493268171640514566573329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15324357562187352755431105 11493268171640514566573329)
              ·
                refine ⟨8619951128730385924929997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11493268171640514566573329 8619951128730385924929997)
                ·
                  refine ⟨3232481673273894721848749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8619951128730385924929997 3232481673273894721848749)
                  ·
                    refine ⟨1212180627477710520693281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3232481673273894721848749 1212180627477710520693281)
                    ·
                      rfl

theorem cell22_3541070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_3541070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541070 prefixEnd_3541070 := by exact prefixLift 3541070
  have htrace : WordTrace (prefixWord ++ tailWord_3541070) baseStart_3541070 baseEnd_3541070 := by
    simpa [prefixWord, tailWord_3541070, baseEnd_3541070] using wordTrace_append hprefix tailTrace_3541070
  have hstable : (prefixWord ++ tailWord_3541070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541070).length < 2 ^ (prefixWord ++ tailWord_3541070).sum := by decide
  have hdescent : baseEnd_3541070 < baseStart_3541070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541104 : List Nat := [2, 1, 1, 1, 5, 3, 3, 2, 1, 3]
def baseStart_3541104 : Nat := 118140960795 + 3541104 * 2 ^ 59
def prefixEnd_3541104 : Nat := 4983230072969 + 3 ^ 40 * 3541104 * 2
def baseEnd_3541104 : Nat := 1212192266372545765343177

theorem tailTrace_3541104 : CollatzResearch.WordTrace tailWord_3541104 prefixEnd_3541104 1212192266372545765343177 := by
  unfold tailWord_3541104
  simp only [CollatzResearch.WordTrace]
  refine ⟨64577336681596227629959183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86103115575461636839945577 64577336681596227629959183)
  ·
    refine ⟨96866005022394341444938775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64577336681596227629959183 96866005022394341444938775)
    ·
      refine ⟨145299007533591512167408163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96866005022394341444938775 145299007533591512167408163)
      ·
        refine ⟨217948511300387268251112245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145299007533591512167408163 217948511300387268251112245)
        ·
          refine ⟨20432672934411306398541773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217948511300387268251112245 20432672934411306398541773)
          ·
            refine ⟨7662252350404239899453165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20432672934411306398541773 7662252350404239899453165)
            ·
              refine ⟨2873344631401589962294937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7662252350404239899453165 2873344631401589962294937)
              ·
                refine ⟨2155008473551192471721203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2873344631401589962294937 2155008473551192471721203)
                ·
                  refine ⟨3232512710326788707581805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2155008473551192471721203 3232512710326788707581805)
                  ·
                    refine ⟨1212192266372545765343177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3232512710326788707581805 1212192266372545765343177)
                    ·
                      rfl

theorem cell22_3541104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 2, 1, 3].length) (baseStart_3541104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541104 prefixEnd_3541104 := by exact prefixLift 3541104
  have htrace : WordTrace (prefixWord ++ tailWord_3541104) baseStart_3541104 baseEnd_3541104 := by
    simpa [prefixWord, tailWord_3541104, baseEnd_3541104] using wordTrace_append hprefix tailTrace_3541104
  have hstable : (prefixWord ++ tailWord_3541104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541104).length < 2 ^ (prefixWord ++ tailWord_3541104).sum := by decide
  have hdescent : baseEnd_3541104 < baseStart_3541104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3541117 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 5]
def baseStart_3541117 : Nat := 118140960795 + 3541117 * 2 ^ 59
def prefixEnd_3541117 : Nat := 4983230072969 + 3 ^ 40 * 3541117 * 2
def baseEnd_3541117 : Nat := 404065572179406021589379

theorem tailTrace_3541117 : CollatzResearch.WordTrace tailWord_3541117 prefixEnd_3541117 404065572179406021589379 := by
  unfold tailWord_3541117
  simp only [CollatzResearch.WordTrace]
  refine ⟨129155147512145358480141605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86103431674763572320094403 129155147512145358480141605)
  ·
    refine ⟨24216590158527254715026551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129155147512145358480141605 24216590158527254715026551)
    ·
      refine ⟨36324885237790882072539827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24216590158527254715026551 36324885237790882072539827)
      ·
        refine ⟨54487327856686323108809741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36324885237790882072539827 54487327856686323108809741)
        ·
          refine ⟨20432747946257371165803653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54487327856686323108809741 20432747946257371165803653)
          ·
            refine ⟨3831140239923257093588185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20432747946257371165803653 3831140239923257093588185)
            ·
              refine ⟨2873355179942442820191139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3831140239923257093588185 2873355179942442820191139)
              ·
                refine ⟨4310032769913664230286709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2873355179942442820191139 4310032769913664230286709)
                ·
                  refine ⟨404065572179406021589379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4310032769913664230286709 404065572179406021589379)
                  ·
                    rfl

theorem cell22_3541117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_3541117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3541117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3541117 prefixEnd_3541117 := by exact prefixLift 3541117
  have htrace : WordTrace (prefixWord ++ tailWord_3541117) baseStart_3541117 baseEnd_3541117 := by
    simpa [prefixWord, tailWord_3541117, baseEnd_3541117] using wordTrace_append hprefix tailTrace_3541117
  have hstable : (prefixWord ++ tailWord_3541117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3541117).length < 2 ^ (prefixWord ++ tailWord_3541117).sum := by decide
  have hdescent : baseEnd_3541117 < baseStart_3541117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3541117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
