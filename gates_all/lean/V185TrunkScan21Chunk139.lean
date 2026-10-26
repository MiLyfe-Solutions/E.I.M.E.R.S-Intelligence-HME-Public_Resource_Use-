import V185TrunkScan21Chunk138

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1694623 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 4]
def baseStart_1694623 : Nat := 118140960795 + 1694623 * 2 ^ 59
def prefixEnd_1694623 : Nat := 4983230072969 + 3 ^ 40 * 1694623 * 2
def baseEnd_1694623 : Nat := 386736056517434894852923

theorem tailTrace_1694623 : CollatzResearch.WordTrace tailWord_1694623 prefixEnd_1694623 386736056517434894852923 := by
  unfold tailWord_1694623
  simp only [CollatzResearch.WordTrace]
  refine ⟨61807978539677764411720523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41205319026451842941147015 61807978539677764411720523)
  ·
    refine ⟨92711967809516646617580785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61807978539677764411720523 92711967809516646617580785)
    ·
      refine ⟨69533975857137484963185589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92711967809516646617580785 69533975857137484963185589)
      ·
        refine ⟨6518810236606639215298649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69533975857137484963185589 6518810236606639215298649)
        ·
          refine ⟨4889107677454979411473987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6518810236606639215298649 4889107677454979411473987)
          ·
            refine ⟨7333661516182469117210981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889107677454979411473987 7333661516182469117210981)
            ·
              refine ⟨1375061534284212959477059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7333661516182469117210981 1375061534284212959477059)
              ·
                refine ⟨2062592301426319439215589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375061534284212959477059 2062592301426319439215589)
                ·
                  refine ⟨386736056517434894852923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062592301426319439215589 386736056517434894852923)
                  ·
                    rfl

theorem cell21_1694623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 4].length) (baseStart_1694623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694623 prefixEnd_1694623 := by exact prefixLift 1694623
  have htrace : WordTrace (prefixWord ++ tailWord_1694623) baseStart_1694623 baseEnd_1694623 := by
    simpa [prefixWord, tailWord_1694623, baseEnd_1694623] using wordTrace_append hprefix tailTrace_1694623
  have hstable : (prefixWord ++ tailWord_1694623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694623).length < 2 ^ (prefixWord ++ tailWord_1694623).sum := by decide
  have hdescent : baseEnd_1694623 < baseStart_1694623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694660 : List Nat := [2, 3, 3, 3, 2, 1, 2, 2, 3]
def baseStart_1694660 : Nat := 118140960795 + 1694660 * 2 ^ 59
def prefixEnd_1694660 : Nat := 4983230072969 + 3 ^ 40 * 1694660 * 2
def baseEnd_1694660 : Nat := 386744500421531052736181

theorem tailTrace_1694660 : CollatzResearch.WordTrace tailWord_1694660 prefixEnd_1694660 386744500421531052736181 := by
  unfold tailWord_1694660
  simp only [CollatzResearch.WordTrace]
  refine ⟨30904664020271859865408717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41206218693695813153878289 30904664020271859865408717)
  ·
    refine ⟨11589249007601947449528269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30904664020271859865408717 11589249007601947449528269)
    ·
      refine ⟨4345968377850730293573101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11589249007601947449528269 4345968377850730293573101)
      ·
        refine ⟨1629738141694023860089913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4345968377850730293573101 1629738141694023860089913)
        ·
          refine ⟨1222303606270517895067435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1629738141694023860089913 1222303606270517895067435)
          ·
            refine ⟨1833455409405776842601153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222303606270517895067435 1833455409405776842601153)
            ·
              refine ⟨1375091557054332631950865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833455409405776842601153 1375091557054332631950865)
              ·
                refine ⟨1031318667790749473963149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375091557054332631950865 1031318667790749473963149)
                ·
                  refine ⟨386744500421531052736181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031318667790749473963149 386744500421531052736181)
                  ·
                    rfl

theorem cell21_1694660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_1694660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694660 prefixEnd_1694660 := by exact prefixLift 1694660
  have htrace : WordTrace (prefixWord ++ tailWord_1694660) baseStart_1694660 baseEnd_1694660 := by
    simpa [prefixWord, tailWord_1694660, baseEnd_1694660] using wordTrace_append hprefix tailTrace_1694660
  have hstable : (prefixWord ++ tailWord_1694660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694660).length < 2 ^ (prefixWord ++ tailWord_1694660).sum := by decide
  have hdescent : baseEnd_1694660 < baseStart_1694660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694668 : List Nat := [2, 2, 1, 4, 1, 1, 3, 4, 3]
def baseStart_1694668 : Nat := 118140960795 + 1694668 * 2 ^ 59
def prefixEnd_1694668 : Nat := 4983230072969 + 3 ^ 40 * 1694668 * 2
def baseEnd_1694668 : Nat := 386746326130524816602831

theorem tailTrace_1694668 : CollatzResearch.WordTrace tailWord_1694668 prefixEnd_1694668 386746326130524816602831 := by
  unfold tailWord_1694668
  simp only [CollatzResearch.WordTrace]
  refine ⟨30904809912257368548554329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41206413216343158064739105 30904809912257368548554329)
  ·
    refine ⟨23178607434193026411415747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30904809912257368548554329 23178607434193026411415747)
    ·
      refine ⟨34767911151289539617123621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23178607434193026411415747 34767911151289539617123621)
      ·
        refine ⟨6518983340866788678210679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34767911151289539617123621 6518983340866788678210679)
        ·
          refine ⟨9778475011300183017316019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518983340866788678210679 9778475011300183017316019)
          ·
            refine ⟨14667712516950274525974029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778475011300183017316019 14667712516950274525974029)
            ·
              refine ⟨5500392193856352947240261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14667712516950274525974029 5500392193856352947240261)
              ·
                refine ⟨1031323536348066177607549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5500392193856352947240261 1031323536348066177607549)
                ·
                  refine ⟨386746326130524816602831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031323536348066177607549 386746326130524816602831)
                  ·
                    rfl

theorem cell21_1694668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_1694668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694668 prefixEnd_1694668 := by exact prefixLift 1694668
  have htrace : WordTrace (prefixWord ++ tailWord_1694668) baseStart_1694668 baseEnd_1694668 := by
    simpa [prefixWord, tailWord_1694668, baseEnd_1694668] using wordTrace_append hprefix tailTrace_1694668
  have hstable : (prefixWord ++ tailWord_1694668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694668).length < 2 ^ (prefixWord ++ tailWord_1694668).sum := by decide
  have hdescent : baseEnd_1694668 < baseStart_1694668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694679 : List Nat := [1, 1, 3, 2, 1, 1, 2, 10]
def baseStart_1694679 : Nat := 118140960795 + 1694679 * 2 ^ 59
def prefixEnd_1694679 : Nat := 4983230072969 + 3 ^ 40 * 1694679 * 2
def baseEnd_1694679 : Nat := 128916278826797080639825

theorem tailTrace_1694679 : CollatzResearch.WordTrace tailWord_1694679 prefixEnd_1694679 128916278826797080639825 := by
  unfold tailWord_1694679
  simp only [CollatzResearch.WordTrace]
  refine ⟨61810021027474885975759091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41206680684983257317172727 61810021027474885975759091)
  ·
    refine ⟨92715031541212328963638637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61810021027474885975759091 92715031541212328963638637)
    ·
      refine ⟨34768136827954623361364489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92715031541212328963638637 34768136827954623361364489)
      ·
        refine ⟨26076102620965967521023367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34768136827954623361364489 26076102620965967521023367)
        ·
          refine ⟨39114153931448951281535051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26076102620965967521023367 39114153931448951281535051)
          ·
            refine ⟨58671230897173426922302577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39114153931448951281535051 58671230897173426922302577)
            ·
              refine ⟨44003423172880070191726933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58671230897173426922302577 44003423172880070191726933)
              ·
                refine ⟨128916278826797080639825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44003423172880070191726933 128916278826797080639825)
                ·
                  rfl

theorem cell21_1694679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 10].length) (baseStart_1694679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694679 prefixEnd_1694679 := by exact prefixLift 1694679
  have htrace : WordTrace (prefixWord ++ tailWord_1694679) baseStart_1694679 baseEnd_1694679 := by
    simpa [prefixWord, tailWord_1694679, baseEnd_1694679] using wordTrace_append hprefix tailTrace_1694679
  have hstable : (prefixWord ++ tailWord_1694679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694679).length < 2 ^ (prefixWord ++ tailWord_1694679).sum := by decide
  have hdescent : baseEnd_1694679 < baseStart_1694679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694682 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1694682 : Nat := 118140960795 + 1694682 * 2 ^ 59
def prefixEnd_1694682 : Nat := 4983230072969 + 3 ^ 40 * 1694682 * 2
def baseEnd_1694682 : Nat := 386749521121263903369469

theorem tailTrace_1694682 : CollatzResearch.WordTrace tailWord_1694682 prefixEnd_1694682 386749521121263903369469 := by
  unfold tailWord_1694682
  simp only [CollatzResearch.WordTrace]
  refine ⟨15452532611616004372029575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41206753630976011658745533 15452532611616004372029575)
  ·
    refine ⟨23178798917424006558044363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15452532611616004372029575 23178798917424006558044363)
    ·
      refine ⟨34768198376136009837066545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23178798917424006558044363 34768198376136009837066545)
      ·
        refine ⟨26076148782102007377799909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34768198376136009837066545 26076148782102007377799909)
        ·
          refine ⟨4889277896644126383337483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26076148782102007377799909 4889277896644126383337483)
          ·
            refine ⟨7333916844966189575006225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889277896644126383337483 7333916844966189575006225)
            ·
              refine ⟨5500437633724642181254669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7333916844966189575006225 5500437633724642181254669)
              ·
                refine ⟨2062664112646740817970501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5500437633724642181254669 2062664112646740817970501)
                ·
                  refine ⟨386749521121263903369469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062664112646740817970501 386749521121263903369469)
                  ·
                    rfl

theorem cell21_1694682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1694682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694682 prefixEnd_1694682 := by exact prefixLift 1694682
  have htrace : WordTrace (prefixWord ++ tailWord_1694682) baseStart_1694682 baseEnd_1694682 := by
    simpa [prefixWord, tailWord_1694682, baseEnd_1694682] using wordTrace_append hprefix tailTrace_1694682
  have hstable : (prefixWord ++ tailWord_1694682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694682).length < 2 ^ (prefixWord ++ tailWord_1694682).sum := by decide
  have hdescent : baseEnd_1694682 < baseStart_1694682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694727 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 5]
def baseStart_1694727 : Nat := 118140960795 + 1694727 * 2 ^ 59
def prefixEnd_1694727 : Nat := 4983230072969 + 3 ^ 40 * 1694727 * 2
def baseEnd_1694727 : Nat := 386759790734353825119377

theorem tailTrace_1694727 : CollatzResearch.WordTrace tailWord_1694727 prefixEnd_1694727 386759790734353825119377 := by
  unfold tailWord_1694727
  simp only [CollatzResearch.WordTrace]
  refine ⟨61811771731300990173506435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41207847820867326782337623 61811771731300990173506435)
  ·
    refine ⟨92717657596951485260259653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61811771731300990173506435 92717657596951485260259653)
    ·
      refine ⟨17384560799428403486298685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92717657596951485260259653 17384560799428403486298685)
      ·
        refine ⟨6519210299785651307362007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17384560799428403486298685 6519210299785651307362007)
        ·
          refine ⟨9778815449678476961043011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519210299785651307362007 9778815449678476961043011)
          ·
            refine ⟨14668223174517715441564517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778815449678476961043011 14668223174517715441564517)
            ·
              refine ⟨2750291845222071645293347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14668223174517715441564517 2750291845222071645293347)
              ·
                refine ⟨4125437767833107467940021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750291845222071645293347 4125437767833107467940021)
                ·
                  refine ⟨386759790734353825119377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4125437767833107467940021 386759790734353825119377)
                  ·
                    rfl

theorem cell21_1694727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_1694727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694727 prefixEnd_1694727 := by exact prefixLift 1694727
  have htrace : WordTrace (prefixWord ++ tailWord_1694727) baseStart_1694727 baseEnd_1694727 := by
    simpa [prefixWord, tailWord_1694727, baseEnd_1694727] using wordTrace_append hprefix tailTrace_1694727
  have hstable : (prefixWord ++ tailWord_1694727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694727).length < 2 ^ (prefixWord ++ tailWord_1694727).sum := by decide
  have hdescent : baseEnd_1694727 < baseStart_1694727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694834 : List Nat := [3, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1694834 : Nat := 118140960795 + 1694834 * 2 ^ 59
def prefixEnd_1694834 : Nat := 4983230072969 + 3 ^ 40 * 1694834 * 2
def baseEnd_1694834 : Nat := 386784209592145416835825

theorem tailTrace_1694834 : CollatzResearch.WordTrace tailWord_1694834 prefixEnd_1694834 386784209592145416835825 := by
  unfold tailWord_1694834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15453918585478336861912889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41210449561275564965101037 15453918585478336861912889)
  ·
    refine ⟨11590438939108752646434667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15453918585478336861912889 11590438939108752646434667)
    ·
      refine ⟨17385658408663128969652001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11590438939108752646434667 17385658408663128969652001)
      ·
        refine ⟨13039243806497346727239001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17385658408663128969652001 13039243806497346727239001)
        ·
          refine ⟨9779432854873010045429251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13039243806497346727239001 9779432854873010045429251)
          ·
            refine ⟨14669149282309515068143877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9779432854873010045429251 14669149282309515068143877)
            ·
              refine ⟨2750465490433034075276977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14669149282309515068143877 2750465490433034075276977)
              ·
                refine ⟨2062849117824775556457733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750465490433034075276977 2062849117824775556457733)
                ·
                  refine ⟨386784209592145416835825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062849117824775556457733 386784209592145416835825)
                  ·
                    rfl

theorem cell21_1694834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1694834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694834 prefixEnd_1694834 := by exact prefixLift 1694834
  have htrace : WordTrace (prefixWord ++ tailWord_1694834) baseStart_1694834 baseEnd_1694834 := by
    simpa [prefixWord, tailWord_1694834, baseEnd_1694834] using wordTrace_append hprefix tailTrace_1694834
  have hstable : (prefixWord ++ tailWord_1694834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694834).length < 2 ^ (prefixWord ++ tailWord_1694834).sum := by decide
  have hdescent : baseEnd_1694834 < baseStart_1694834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694941 : List Nat := [1, 4, 3, 2, 2, 2, 7]
def baseStart_1694941 : Nat := 118140960795 + 1694941 * 2 ^ 59
def prefixEnd_1694941 : Nat := 4983230072969 + 3 ^ 40 * 1694941 * 2
def baseEnd_1694941 : Nat := 42978736494437445394697

theorem tailTrace_1694941 : CollatzResearch.WordTrace tailWord_1694941 prefixEnd_1694941 42978736494437445394697 := by
  unfold tailWord_1694941
  simp only [CollatzResearch.WordTrace]
  refine ⟨61819576952525704721796677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41213051301683803147864451 61819576952525704721796677)
  ·
    refine ⟨11591170678598569635336877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61819576952525704721796677 11591170678598569635336877)
    ·
      refine ⟨4346689004474463613251329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11591170678598569635336877 4346689004474463613251329)
      ·
        refine ⟨3260016753355847709938497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4346689004474463613251329 3260016753355847709938497)
        ·
          refine ⟨2445012565016885782453873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3260016753355847709938497 2445012565016885782453873)
          ·
            refine ⟨1833759423762664336840405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2445012565016885782453873 1833759423762664336840405)
            ·
              refine ⟨42978736494437445394697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1833759423762664336840405 42978736494437445394697)
              ·
                rfl

theorem cell21_1694941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 7].length) (baseStart_1694941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694941 prefixEnd_1694941 := by exact prefixLift 1694941
  have htrace : WordTrace (prefixWord ++ tailWord_1694941) baseStart_1694941 baseEnd_1694941 := by
    simpa [prefixWord, tailWord_1694941, baseEnd_1694941] using wordTrace_append hprefix tailTrace_1694941
  have hstable : (prefixWord ++ tailWord_1694941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694941).length < 2 ^ (prefixWord ++ tailWord_1694941).sum := by decide
  have hdescent : baseEnd_1694941 < baseStart_1694941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694955 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 5]
def baseStart_1694955 : Nat := 118140960795 + 1694955 * 2 ^ 59
def prefixEnd_1694955 : Nat := 4983230072969 + 3 ^ 40 * 1694955 * 2
def baseEnd_1694955 : Nat := 386811823440676095318911

theorem tailTrace_1694955 : CollatzResearch.WordTrace tailWord_1694955 prefixEnd_1694955 386811823440676095318911 := by
  unfold tailWord_1694955
  simp only [CollatzResearch.WordTrace]
  refine ⟨61820087574474985112806319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41213391716316656741870879 61820087574474985112806319)
  ·
    refine ⟨92730131361712477669209479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61820087574474985112806319 92730131361712477669209479)
    ·
      refine ⟨139095197042568716503814219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92730131361712477669209479 139095197042568716503814219)
      ·
        refine ⟨208642795563853074755721329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139095197042568716503814219 208642795563853074755721329)
        ·
          refine ⟨156482096672889806066790997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208642795563853074755721329 156482096672889806066790997)
          ·
            refine ⟨1833774570385427414845207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 156482096672889806066790997 1833774570385427414845207)
            ·
              refine ⟨2750661855578141122267811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833774570385427414845207 2750661855578141122267811)
              ·
                refine ⟨4125992783367211683401717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750661855578141122267811 4125992783367211683401717)
                ·
                  refine ⟨386811823440676095318911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4125992783367211683401717 386811823440676095318911)
                  ·
                    rfl

theorem cell21_1694955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5].length) (baseStart_1694955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694955 prefixEnd_1694955 := by exact prefixLift 1694955
  have htrace : WordTrace (prefixWord ++ tailWord_1694955) baseStart_1694955 baseEnd_1694955 := by
    simpa [prefixWord, tailWord_1694955, baseEnd_1694955] using wordTrace_append hprefix tailTrace_1694955
  have hstable : (prefixWord ++ tailWord_1694955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694955).length < 2 ^ (prefixWord ++ tailWord_1694955).sum := by decide
  have hdescent : baseEnd_1694955 < baseStart_1694955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1694969 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 4]
def baseStart_1694969 : Nat := 118140960795 + 1694969 * 2 ^ 59
def prefixEnd_1694969 : Nat := 4983230072969 + 3 ^ 40 * 1694969 * 2
def baseEnd_1694969 : Nat := 386815018431415182085549

theorem tailTrace_1694969 : CollatzResearch.WordTrace tailWord_1694969 prefixEnd_1694969 386815018431415182085549 := by
  unfold tailWord_1694969
  simp only [CollatzResearch.WordTrace]
  refine ⟨61820598196424265503815961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41213732130949510335877307 61820598196424265503815961)
  ·
    refine ⟨46365448647318199127861971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61820598196424265503815961 46365448647318199127861971)
    ·
      refine ⟨69548172970977298691792957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46365448647318199127861971 69548172970977298691792957)
      ·
        refine ⟨26080564864116487009422359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69548172970977298691792957 26080564864116487009422359)
        ·
          refine ⟨39120847296174730514133539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26080564864116487009422359 39120847296174730514133539)
          ·
            refine ⟨58681270944262095771200309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39120847296174730514133539 58681270944262095771200309)
            ·
              refine ⟨5501369151024571478550029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58681270944262095771200309 5501369151024571478550029)
              ·
                refine ⟨2063013431634214304456261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5501369151024571478550029 2063013431634214304456261)
                ·
                  refine ⟨386815018431415182085549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2063013431634214304456261 386815018431415182085549)
                  ·
                    rfl

theorem cell21_1694969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_1694969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1694969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1694969 prefixEnd_1694969 := by exact prefixLift 1694969
  have htrace : WordTrace (prefixWord ++ tailWord_1694969) baseStart_1694969 baseEnd_1694969 := by
    simpa [prefixWord, tailWord_1694969, baseEnd_1694969] using wordTrace_append hprefix tailTrace_1694969
  have hstable : (prefixWord ++ tailWord_1694969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1694969).length < 2 ^ (prefixWord ++ tailWord_1694969).sum := by decide
  have hdescent : baseEnd_1694969 < baseStart_1694969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1694969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695006 : List Nat := [4, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1695006 : Nat := 118140960795 + 1695006 * 2 ^ 59
def prefixEnd_1695006 : Nat := 4983230072969 + 3 ^ 40 * 1695006 * 2
def baseEnd_1695006 : Nat := 386823462335511339968807

theorem tailTrace_1695006 : CollatzResearch.WordTrace tailWord_1695006 prefixEnd_1695006 386823462335511339968807 := by
  unfold tailWord_1695006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727743462161277602864109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41214631798193480548608581 7727743462161277602864109)
  ·
    refine ⟨2897903798310479101074041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7727743462161277602864109 2897903798310479101074041)
    ·
      refine ⟨2173427848732859325805531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2897903798310479101074041 2173427848732859325805531)
      ·
        refine ⟨3260141773099288988708297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173427848732859325805531 3260141773099288988708297)
        ·
          refine ⟨2445106329824466741531223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3260141773099288988708297 2445106329824466741531223)
          ·
            refine ⟨3667659494736700112296835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445106329824466741531223 3667659494736700112296835)
            ·
              refine ⟨5501489242105050168445253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667659494736700112296835 5501489242105050168445253)
              ·
                refine ⟨1031529232894696906583485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5501489242105050168445253 1031529232894696906583485)
                ·
                  refine ⟨386823462335511339968807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031529232894696906583485 386823462335511339968807)
                  ·
                    rfl

theorem cell21_1695006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1695006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695006 prefixEnd_1695006 := by exact prefixLift 1695006
  have htrace : WordTrace (prefixWord ++ tailWord_1695006) baseStart_1695006 baseEnd_1695006 := by
    simpa [prefixWord, tailWord_1695006, baseEnd_1695006] using wordTrace_append hprefix tailTrace_1695006
  have hstable : (prefixWord ++ tailWord_1695006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695006).length < 2 ^ (prefixWord ++ tailWord_1695006).sum := by decide
  have hdescent : baseEnd_1695006 < baseStart_1695006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695079 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 4]
def baseStart_1695079 : Nat := 118140960795 + 1695079 * 2 ^ 59
def prefixEnd_1695079 : Nat := 4983230072969 + 3 ^ 40 * 1695079 * 2
def baseEnd_1695079 : Nat := 386840121930079435251991

theorem tailTrace_1695079 : CollatzResearch.WordTrace tailWord_1695079 prefixEnd_1695079 386840121930079435251991 := by
  unfold tailWord_1695079
  simp only [CollatzResearch.WordTrace]
  refine ⟨61824610226025754290320291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41216406817350502860213527 61824610226025754290320291)
  ·
    refine ⟨92736915339038631435480437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61824610226025754290320291 92736915339038631435480437)
    ·
      refine ⟨8694085813034871697076291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92736915339038631435480437 8694085813034871697076291)
      ·
        refine ⟨13041128719552307545614437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8694085813034871697076291 13041128719552307545614437)
        ·
          refine ⟨2445211634916057664802707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13041128719552307545614437 2445211634916057664802707)
          ·
            refine ⟨3667817452374086497204061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445211634916057664802707 3667817452374086497204061)
            ·
              refine ⟨1375431544640282436451523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3667817452374086497204061 1375431544640282436451523)
              ·
                refine ⟨2063147316960423654677285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375431544640282436451523 2063147316960423654677285)
                ·
                  refine ⟨386840121930079435251991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2063147316960423654677285 386840121930079435251991)
                  ·
                    rfl

theorem cell21_1695079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 4].length) (baseStart_1695079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695079 prefixEnd_1695079 := by exact prefixLift 1695079
  have htrace : WordTrace (prefixWord ++ tailWord_1695079) baseStart_1695079 baseEnd_1695079 := by
    simpa [prefixWord, tailWord_1695079, baseEnd_1695079] using wordTrace_append hprefix tailTrace_1695079
  have hstable : (prefixWord ++ tailWord_1695079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695079).length < 2 ^ (prefixWord ++ tailWord_1695079).sum := by decide
  have hdescent : baseEnd_1695079 < baseStart_1695079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695090 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1695090 : Nat := 118140960795 + 1695090 * 2 ^ 59
def prefixEnd_1695090 : Nat := 4983230072969 + 3 ^ 40 * 1695090 * 2
def baseEnd_1695090 : Nat := 386842632279945860568635

theorem tailTrace_1695090 : CollatzResearch.WordTrace tailWord_1695090 prefixEnd_1695090 386842632279945860568635 := by
  unfold tailWord_1695090
  simp only [CollatzResearch.WordTrace]
  refine ⟨15456252857246475792242681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41216674285990602112647149 15456252857246475792242681)
  ·
    refine ⟨11592189642934856844182011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15456252857246475792242681 11592189642934856844182011)
    ·
      refine ⟨17388284464402285266273017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11592189642934856844182011 17388284464402285266273017)
      ·
        refine ⟨13041213348301713949704763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17388284464402285266273017 13041213348301713949704763)
        ·
          refine ⟨19561820022452570924557145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13041213348301713949704763 19561820022452570924557145)
          ·
            refine ⟨14671365016839428193417859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19561820022452570924557145 14671365016839428193417859)
            ·
              refine ⟨22007047525259142290126789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14671365016839428193417859 22007047525259142290126789)
              ·
                refine ⟨4126321410986089179398773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22007047525259142290126789 4126321410986089179398773)
                ·
                  refine ⟨386842632279945860568635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126321410986089179398773 386842632279945860568635)
                  ·
                    rfl

theorem cell21_1695090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1695090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695090 prefixEnd_1695090 := by exact prefixLift 1695090
  have htrace : WordTrace (prefixWord ++ tailWord_1695090) baseStart_1695090 baseEnd_1695090 := by
    simpa [prefixWord, tailWord_1695090, baseEnd_1695090] using wordTrace_append hprefix tailTrace_1695090
  have hstable : (prefixWord ++ tailWord_1695090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695090).length < 2 ^ (prefixWord ++ tailWord_1695090).sum := by decide
  have hdescent : baseEnd_1695090 < baseStart_1695090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695124 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1695124 : Nat := 118140960795 + 1695124 * 2 ^ 59
def prefixEnd_1695124 : Nat := 4983230072969 + 3 ^ 40 * 1695124 * 2
def baseEnd_1695124 : Nat := 386850391543169357001899

theorem tailTrace_1695124 : CollatzResearch.WordTrace tailWord_1695124 prefixEnd_1695124 386850391543169357001899 := by
  unfold tailWord_1695124
  simp only [CollatzResearch.WordTrace]
  refine ⟨30913125755431363487854213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41217501007241817983805617 30913125755431363487854213)
  ·
    refine ⟨5796211079143380653972665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30913125755431363487854213 5796211079143380653972665)
    ·
      refine ⟨4347158309357535490479499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5796211079143380653972665 4347158309357535490479499)
      ·
        refine ⟨6520737464036303235719249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347158309357535490479499 6520737464036303235719249)
        ·
          refine ⟨4890553098027227426789437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6520737464036303235719249 4890553098027227426789437)
          ·
            refine ⟨1833957411760210285046039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4890553098027227426789437 1833957411760210285046039)
            ·
              refine ⟨2750936117640315427569059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1833957411760210285046039 2750936117640315427569059)
              ·
                refine ⟨4126404176460473141353589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750936117640315427569059 4126404176460473141353589)
                ·
                  refine ⟨386850391543169357001899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126404176460473141353589 386850391543169357001899)
                  ·
                    rfl

theorem cell21_1695124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1695124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695124 prefixEnd_1695124 := by exact prefixLift 1695124
  have htrace : WordTrace (prefixWord ++ tailWord_1695124) baseStart_1695124 baseEnd_1695124 := by
    simpa [prefixWord, tailWord_1695124, baseEnd_1695124] using wordTrace_append hprefix tailTrace_1695124
  have hstable : (prefixWord ++ tailWord_1695124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695124).length < 2 ^ (prefixWord ++ tailWord_1695124).sum := by decide
  have hdescent : baseEnd_1695124 < baseStart_1695124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695135 : List Nat := [1, 1, 2, 5, 1, 2, 1, 8]
def baseStart_1695135 : Nat := 118140960795 + 1695135 * 2 ^ 59
def prefixEnd_1695135 : Nat := 4983230072969 + 3 ^ 40 * 1695135 * 2
def baseEnd_1695135 : Nat := 128950967297678594106181

theorem tailTrace_1695135 : CollatzResearch.WordTrace tailWord_1695135 prefixEnd_1695135 128950967297678594106181 := by
  unfold tailWord_1695135
  simp only [CollatzResearch.WordTrace]
  refine ⟨61826652713822875854358859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41217768475881917236239239 61826652713822875854358859)
  ·
    refine ⟨92739979070734313781538289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61826652713822875854358859 92739979070734313781538289)
    ·
      refine ⟨69554984303050735336153717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92739979070734313781538289 69554984303050735336153717)
      ·
        refine ⟨6520779778411006437764411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69554984303050735336153717 6520779778411006437764411)
        ·
          refine ⟨9781169667616509656646617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520779778411006437764411 9781169667616509656646617)
          ·
            refine ⟨7335877250712382242484963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9781169667616509656646617 7335877250712382242484963)
            ·
              refine ⟨11003815876068573363727445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335877250712382242484963 11003815876068573363727445)
              ·
                refine ⟨128950967297678594106181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11003815876068573363727445 128950967297678594106181)
                ·
                  rfl

theorem cell21_1695135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_1695135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695135 prefixEnd_1695135 := by exact prefixLift 1695135
  have htrace : WordTrace (prefixWord ++ tailWord_1695135) baseStart_1695135 baseEnd_1695135 := by
    simpa [prefixWord, tailWord_1695135, baseEnd_1695135] using wordTrace_append hprefix tailTrace_1695135
  have hstable : (prefixWord ++ tailWord_1695135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695135).length < 2 ^ (prefixWord ++ tailWord_1695135).sum := by decide
  have hdescent : baseEnd_1695135 < baseStart_1695135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695138 : List Nat := [3, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1695138 : Nat := 118140960795 + 1695138 * 2 ^ 59
def prefixEnd_1695138 : Nat := 4983230072969 + 3 ^ 40 * 1695138 * 2
def baseEnd_1695138 : Nat := 386853586533908443768537

theorem tailTrace_1695138 : CollatzResearch.WordTrace tailWord_1695138 prefixEnd_1695138 386853586533908443768537 := by
  unfold tailWord_1695138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15456690533203001841679517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41217841421874671577812045 15456690533203001841679517)
  ·
    refine ⟨5796258949951125690629819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15456690533203001841679517 5796258949951125690629819)
    ·
      refine ⟨8694388424926688535944729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5796258949951125690629819 8694388424926688535944729)
      ·
        refine ⟨6520791318695016401958547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8694388424926688535944729 6520791318695016401958547)
        ·
          refine ⟨9781186978042524602937821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520791318695016401958547 9781186978042524602937821)
          ·
            refine ⟨3667945116765946726101683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9781186978042524602937821 3667945116765946726101683)
            ·
              refine ⟨5501917675148920089152525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667945116765946726101683 5501917675148920089152525)
              ·
                refine ⟨2063219128180845033432197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5501917675148920089152525 2063219128180845033432197)
                ·
                  refine ⟨386853586533908443768537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2063219128180845033432197 386853586533908443768537)
                  ·
                    rfl

theorem cell21_1695138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1695138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695138 prefixEnd_1695138 := by exact prefixLift 1695138
  have htrace : WordTrace (prefixWord ++ tailWord_1695138) baseStart_1695138 baseEnd_1695138 := by
    simpa [prefixWord, tailWord_1695138, baseEnd_1695138] using wordTrace_append hprefix tailTrace_1695138
  have hstable : (prefixWord ++ tailWord_1695138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695138).length < 2 ^ (prefixWord ++ tailWord_1695138).sum := by decide
  have hdescent : baseEnd_1695138 < baseStart_1695138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695225 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 9]
def baseStart_1695225 : Nat := 118140960795 + 1695225 * 2 ^ 59
def prefixEnd_1695225 : Nat := 4983230072969 + 3 ^ 40 * 1695225 * 2
def baseEnd_1695225 : Nat := 386873441119215625818359

theorem tailTrace_1695225 : CollatzResearch.WordTrace tailWord_1695225 prefixEnd_1695225 386873441119215625818359 := by
  unfold tailWord_1695225
  simp only [CollatzResearch.WordTrace]
  refine ⟨61829935283496821225135129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41219956855664547483423419 61829935283496821225135129)
  ·
    refine ⟨46372451462622615918851347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61829935283496821225135129 46372451462622615918851347)
    ·
      refine ⟨69558677193933923878277021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46372451462622615918851347 69558677193933923878277021)
      ·
        refine ⟨26084503947725221454353883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69558677193933923878277021 26084503947725221454353883)
        ·
          refine ⟨39126755921587832181530825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26084503947725221454353883 39126755921587832181530825)
          ·
            refine ⟨29345066941190874136148119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39126755921587832181530825 29345066941190874136148119)
            ·
              refine ⟨44017600411786311204222179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29345066941190874136148119 44017600411786311204222179)
              ·
                refine ⟨66026400617679466806333269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44017600411786311204222179 66026400617679466806333269)
                ·
                  refine ⟨386873441119215625818359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66026400617679466806333269 386873441119215625818359)
                  ·
                    rfl

theorem cell21_1695225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_1695225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695225 prefixEnd_1695225 := by exact prefixLift 1695225
  have htrace : WordTrace (prefixWord ++ tailWord_1695225) baseStart_1695225 baseEnd_1695225 := by
    simpa [prefixWord, tailWord_1695225, baseEnd_1695225] using wordTrace_append hprefix tailTrace_1695225
  have hstable : (prefixWord ++ tailWord_1695225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695225).length < 2 ^ (prefixWord ++ tailWord_1695225).sum := by decide
  have hdescent : baseEnd_1695225 < baseStart_1695225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695242 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_1695242 : Nat := 118140960795 + 1695242 * 2 ^ 59
def prefixEnd_1695242 : Nat := 4983230072969 + 3 ^ 40 * 1695242 * 2
def baseEnd_1695242 : Nat := 386877320750827374034991

theorem tailTrace_1695242 : CollatzResearch.WordTrace tailWord_1695242 prefixEnd_1695242 386877320750827374034991 := by
  unfold tailWord_1695242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457638831108808282125995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41220370216290155419002653 15457638831108808282125995)
  ·
    refine ⟨23186458246663212423188993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15457638831108808282125995 23186458246663212423188993)
    ·
      refine ⟨17389843684997409317391745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23186458246663212423188993 17389843684997409317391745)
      ·
        refine ⟨13042382763748056988043809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17389843684997409317391745 13042382763748056988043809)
        ·
          refine ⟨9781787072811042741032857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13042382763748056988043809 9781787072811042741032857)
          ·
            refine ⟨7336340304608282055774643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9781787072811042741032857 7336340304608282055774643)
            ·
              refine ⟨11004510456912423083661965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7336340304608282055774643 11004510456912423083661965)
              ·
                refine ⟨4126691421342158656373237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11004510456912423083661965 4126691421342158656373237)
                ·
                  refine ⟨386877320750827374034991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4126691421342158656373237 386877320750827374034991)
                  ·
                    rfl

theorem cell21_1695242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_1695242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695242 prefixEnd_1695242 := by exact prefixLift 1695242
  have htrace : WordTrace (prefixWord ++ tailWord_1695242) baseStart_1695242 baseEnd_1695242 := by
    simpa [prefixWord, tailWord_1695242, baseEnd_1695242] using wordTrace_append hprefix tailTrace_1695242
  have hstable : (prefixWord ++ tailWord_1695242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695242).length < 2 ^ (prefixWord ++ tailWord_1695242).sum := by decide
  have hdescent : baseEnd_1695242 < baseStart_1695242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695287 : List Nat := [1, 1, 3, 1, 2, 6, 7]
def baseStart_1695287 : Nat := 118140960795 + 1695287 * 2 ^ 59
def prefixEnd_1695287 : Nat := 4983230072969 + 3 ^ 40 * 1695287 * 2
def baseEnd_1695287 : Nat := 42987510040435255087211

theorem tailTrace_1695287 : CollatzResearch.WordTrace tailWord_1695287 prefixEnd_1695287 42987510040435255087211 := by
  unfold tailWord_1695287
  simp only [CollatzResearch.WordTrace]
  refine ⟨61832196609272205813892115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41221464406181470542594743 61832196609272205813892115)
  ·
    refine ⟨92748294913908308720838173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61832196609272205813892115 92748294913908308720838173)
    ·
      refine ⟨34780610592715615770314315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92748294913908308720838173 34780610592715615770314315)
      ·
        refine ⟨52170915889073423655471473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34780610592715615770314315 52170915889073423655471473)
        ·
          refine ⟨39128186916805067741603605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52170915889073423655471473 39128186916805067741603605)
          ·
            refine ⟨1834133761725237550387669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39128186916805067741603605 1834133761725237550387669)
            ·
              refine ⟨42987510040435255087211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1834133761725237550387669 42987510040435255087211)
              ·
                rfl

theorem cell21_1695287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 7].length) (baseStart_1695287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695287 prefixEnd_1695287 := by exact prefixLift 1695287
  have htrace : WordTrace (prefixWord ++ tailWord_1695287) baseStart_1695287 baseEnd_1695287 := by
    simpa [prefixWord, tailWord_1695287, baseEnd_1695287] using wordTrace_append hprefix tailTrace_1695287
  have hstable : (prefixWord ++ tailWord_1695287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695287).length < 2 ^ (prefixWord ++ tailWord_1695287).sum := by decide
  have hdescent : baseEnd_1695287 < baseStart_1695287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695293 : List Nat := [1, 4, 1, 3, 3, 1, 3, 2, 3]
def baseStart_1695293 : Nat := 118140960795 + 1695293 * 2 ^ 59
def prefixEnd_1695293 : Nat := 4983230072969 + 3 ^ 40 * 1695293 * 2
def baseEnd_1695293 : Nat := 386888959645662618684887

theorem tailTrace_1695293 : CollatzResearch.WordTrace tailWord_1695293 prefixEnd_1695293 386888959645662618684887 := by
  unfold tailWord_1695293
  simp only [CollatzResearch.WordTrace]
  refine ⟨61832415447250468838610533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41221610298166979225740355 61832415447250468838610533)
  ·
    refine ⟨11593577896359462907239475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61832415447250468838610533 11593577896359462907239475)
    ·
      refine ⟨17390366844539194360859213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11593577896359462907239475 17390366844539194360859213)
      ·
        refine ⟨6521387566702197885322205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17390366844539194360859213 6521387566702197885322205)
        ·
          refine ⟨2445520337513324206995827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6521387566702197885322205 2445520337513324206995827)
          ·
            refine ⟨3668280506269986310493741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445520337513324206995827 3668280506269986310493741)
            ·
              refine ⟨1375605189851244866435153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3668280506269986310493741 1375605189851244866435153)
              ·
                refine ⟨1031703892388433649826365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1375605189851244866435153 1031703892388433649826365)
                ·
                  refine ⟨386888959645662618684887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031703892388433649826365 386888959645662618684887)
                  ·
                    rfl

theorem cell21_1695293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_1695293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695293 prefixEnd_1695293 := by exact prefixLift 1695293
  have htrace : WordTrace (prefixWord ++ tailWord_1695293) baseStart_1695293 baseEnd_1695293 := by
    simpa [prefixWord, tailWord_1695293, baseEnd_1695293] using wordTrace_append hprefix tailTrace_1695293
  have hstable : (prefixWord ++ tailWord_1695293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695293).length < 2 ^ (prefixWord ++ tailWord_1695293).sum := by decide
  have hdescent : baseEnd_1695293 < baseStart_1695293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695476 : List Nat := [2, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1695476 : Nat := 118140960795 + 1695476 * 2 ^ 59
def prefixEnd_1695476 : Nat := 4983230072969 + 3 ^ 40 * 1695476 * 2
def baseEnd_1695476 : Nat := 386930722738894967134513

theorem tailTrace_1695476 : CollatzResearch.WordTrace tailWord_1695476 prefixEnd_1695476 386930722738894967134513 := by
  unfold tailWord_1695476
  simp only [CollatzResearch.WordTrace]
  refine ⟨30919545002793745546261141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41226060003724994061681521 30919545002793745546261141)
  ·
    refine ⟨1449353672005956822480991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30919545002793745546261141 1449353672005956822480991)
    ·
      refine ⟨2174030508008935233721487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1449353672005956822480991 2174030508008935233721487)
      ·
        refine ⟨3261045762013402850582231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174030508008935233721487 3261045762013402850582231)
        ·
          refine ⟨4891568643020104275873347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261045762013402850582231 4891568643020104275873347)
          ·
            refine ⟨7337352964530156413810021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891568643020104275873347 7337352964530156413810021)
            ·
              refine ⟨1375753680849404327589379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7337352964530156413810021 1375753680849404327589379)
              ·
                refine ⟨2063630521274106491384069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1375753680849404327589379 2063630521274106491384069)
                ·
                  refine ⟨386930722738894967134513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2063630521274106491384069 386930722738894967134513)
                  ·
                    rfl

theorem cell21_1695476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1695476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695476 prefixEnd_1695476 := by exact prefixLift 1695476
  have htrace : WordTrace (prefixWord ++ tailWord_1695476) baseStart_1695476 baseEnd_1695476 := by
    simpa [prefixWord, tailWord_1695476, baseEnd_1695476] using wordTrace_append hprefix tailTrace_1695476
  have hstable : (prefixWord ++ tailWord_1695476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695476).length < 2 ^ (prefixWord ++ tailWord_1695476).sum := by decide
  have hdescent : baseEnd_1695476 < baseStart_1695476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695546 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1695546 : Nat := 118140960795 + 1695546 * 2 ^ 59
def prefixEnd_1695546 : Nat := 4983230072969 + 3 ^ 40 * 1695546 * 2
def baseEnd_1695546 : Nat := 386946697692590400967703

theorem tailTrace_1695546 : CollatzResearch.WordTrace tailWord_1695546 prefixEnd_1695546 386946697692590400967703 := by
  unfold tailWord_1695546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15460410778833473261892623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41227762076889262031713661 15460410778833473261892623)
  ·
    refine ⟨23190616168250209892838935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15460410778833473261892623 23190616168250209892838935)
    ·
      refine ⟨34785924252375314839258403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23190616168250209892838935 34785924252375314839258403)
      ·
        refine ⟨52178886378562972258887605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34785924252375314839258403 52178886378562972258887605)
        ·
          refine ⟨4891770597990278649270713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52178886378562972258887605 4891770597990278649270713)
          ·
            refine ⟨3668827948492708986953035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4891770597990278649270713 3668827948492708986953035)
            ·
              refine ⟨5503241922739063480429553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668827948492708986953035 5503241922739063480429553)
              ·
                refine ⟨4127431442054297610322165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503241922739063480429553 4127431442054297610322165)
                ·
                  refine ⟨386946697692590400967703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4127431442054297610322165 386946697692590400967703)
                  ·
                    rfl

theorem cell21_1695546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1695546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695546 prefixEnd_1695546 := by exact prefixLift 1695546
  have htrace : WordTrace (prefixWord ++ tailWord_1695546) baseStart_1695546 baseEnd_1695546 := by
    simpa [prefixWord, tailWord_1695546, baseEnd_1695546] using wordTrace_append hprefix tailTrace_1695546
  have hstable : (prefixWord ++ tailWord_1695546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695546).length < 2 ^ (prefixWord ++ tailWord_1695546).sum := by decide
  have hdescent : baseEnd_1695546 < baseStart_1695546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695777 : List Nat := [1, 2, 3, 2, 5, 1, 2, 5]
def baseStart_1695777 : Nat := 118140960795 + 1695777 * 2 ^ 59
def prefixEnd_1695777 : Nat := 4983230072969 + 3 ^ 40 * 1695777 * 2
def baseEnd_1695777 : Nat := 128999805013261777539077

theorem tailTrace_1695777 : CollatzResearch.WordTrace tailWord_1695777 prefixEnd_1695777 128999805013261777539077 := by
  unfold tailWord_1695777
  simp only [CollatzResearch.WordTrace]
  refine ⟨61850068377497019499229585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41233378918331346332819723 61850068377497019499229585)
  ·
    refine ⟨46387551283122764624422189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61850068377497019499229585 46387551283122764624422189)
    ·
      refine ⟨17395331731171036734158321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46387551283122764624422189 17395331731171036734158321)
      ·
        refine ⟨13046498798378277550618741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17395331731171036734158321 13046498798378277550618741)
        ·
          refine ⟨1223109262347963520370507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13046498798378277550618741 1223109262347963520370507)
          ·
            refine ⟨1834663893521945280555761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223109262347963520370507 1834663893521945280555761)
            ·
              refine ⟨1375997920141458960416821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834663893521945280555761 1375997920141458960416821)
              ·
                refine ⟨128999805013261777539077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1375997920141458960416821 128999805013261777539077)
                ·
                  rfl

theorem cell21_1695777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 5].length) (baseStart_1695777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695777 prefixEnd_1695777 := by exact prefixLift 1695777
  have htrace : WordTrace (prefixWord ++ tailWord_1695777) baseStart_1695777 baseEnd_1695777 := by
    simpa [prefixWord, tailWord_1695777, baseEnd_1695777] using wordTrace_append hprefix tailTrace_1695777
  have hstable : (prefixWord ++ tailWord_1695777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695777).length < 2 ^ (prefixWord ++ tailWord_1695777).sum := by decide
  have hdescent : baseEnd_1695777 < baseStart_1695777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695822 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1695822 : Nat := 118140960795 + 1695822 * 2 ^ 59
def prefixEnd_1695822 : Nat := 4983230072969 + 3 ^ 40 * 1695822 * 2
def baseEnd_1695822 : Nat := 387009684652875254367139

theorem tailTrace_1695822 : CollatzResearch.WordTrace tailWord_1695822 prefixEnd_1695822 387009684652875254367139 := by
  unfold tailWord_1695822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7731463707791749023077215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41234473108222661456411813 7731463707791749023077215)
  ·
    refine ⟨11597195561687623534615823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7731463707791749023077215 11597195561687623534615823)
    ·
      refine ⟨17395793342531435301923735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11597195561687623534615823 17395793342531435301923735)
      ·
        refine ⟨26093690013797152952885603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17395793342531435301923735 26093690013797152952885603)
        ·
          refine ⟨39140535020695729429328405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26093690013797152952885603 39140535020695729429328405)
          ·
            refine ⟨1834712579095112316999769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39140535020695729429328405 1834712579095112316999769)
            ·
              refine ⟨1376034434321334237749827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834712579095112316999769 1376034434321334237749827)
              ·
                refine ⟨2064051651482001356624741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376034434321334237749827 2064051651482001356624741)
                ·
                  refine ⟨387009684652875254367139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064051651482001356624741 387009684652875254367139)
                  ·
                    rfl

theorem cell21_1695822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1695822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695822 prefixEnd_1695822 := by exact prefixLift 1695822
  have htrace : WordTrace (prefixWord ++ tailWord_1695822) baseStart_1695822 baseEnd_1695822 := by
    simpa [prefixWord, tailWord_1695822, baseEnd_1695822] using wordTrace_append hprefix tailTrace_1695822
  have hstable : (prefixWord ++ tailWord_1695822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695822).length < 2 ^ (prefixWord ++ tailWord_1695822).sum := by decide
  have hdescent : baseEnd_1695822 < baseStart_1695822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1695985 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 5]
def baseStart_1695985 : Nat := 118140960795 + 1695985 * 2 ^ 59
def prefixEnd_1695985 : Nat := 4983230072969 + 3 ^ 40 * 1695985 * 2
def baseEnd_1695985 : Nat := 387046883473623193150139

theorem tailTrace_1695985 : CollatzResearch.WordTrace tailWord_1695985 prefixEnd_1695985 387046883473623193150139 := by
  unfold tailWord_1695985
  simp only [CollatzResearch.WordTrace]
  refine ⟨61857654760743471022801409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41238436507162314015200939 61857654760743471022801409)
  ·
    refine ⟨46393241070557603267101057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61857654760743471022801409 46393241070557603267101057)
    ·
      refine ⟨34794930802918202450325793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46393241070557603267101057 34794930802918202450325793)
      ·
        refine ⟨26096198102188651837744345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34794930802918202450325793 26096198102188651837744345)
        ·
          refine ⟨19572148576641488878308259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26096198102188651837744345 19572148576641488878308259)
          ·
            refine ⟨29358222864962233317462389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19572148576641488878308259 29358222864962233317462389)
            ·
              refine ⟨2752333393590209373512099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29358222864962233317462389 2752333393590209373512099)
              ·
                refine ⟨4128500090385314060268149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752333393590209373512099 4128500090385314060268149)
                ·
                  refine ⟨387046883473623193150139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4128500090385314060268149 387046883473623193150139)
                  ·
                    rfl

theorem cell21_1695985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_1695985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1695985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1695985 prefixEnd_1695985 := by exact prefixLift 1695985
  have htrace : WordTrace (prefixWord ++ tailWord_1695985) baseStart_1695985 baseEnd_1695985 := by
    simpa [prefixWord, tailWord_1695985, baseEnd_1695985] using wordTrace_append hprefix tailTrace_1695985
  have hstable : (prefixWord ++ tailWord_1695985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1695985).length < 2 ^ (prefixWord ++ tailWord_1695985).sum := by decide
  have hdescent : baseEnd_1695985 < baseStart_1695985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1695985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696036 : List Nat := [2, 3, 1, 3, 1, 4, 2, 2, 3]
def baseStart_1696036 : Nat := 118140960795 + 1696036 * 2 ^ 59
def prefixEnd_1696036 : Nat := 4983230072969 + 3 ^ 40 * 1696036 * 2
def baseEnd_1696036 : Nat := 387058522368458437800035

theorem tailTrace_1696036 : CollatzResearch.WordTrace tailWord_1696036 prefixEnd_1696036 387058522368458437800035 := by
  unfold tailWord_1696036
  simp only [CollatzResearch.WordTrace]
  refine ⟨30929757441779353366453981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41239676589039137821938641 30929757441779353366453981)
  ·
    refine ⟨11598659040667257512420243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30929757441779353366453981 11598659040667257512420243)
    ·
      refine ⟨17397988561000886268630365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11598659040667257512420243 17397988561000886268630365)
      ·
        refine ⟨6524245710375332350736387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17397988561000886268630365 6524245710375332350736387)
        ·
          refine ⟨9786368565562998526104581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6524245710375332350736387 9786368565562998526104581)
          ·
            refine ⟨1834944106043062223644609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9786368565562998526104581 1834944106043062223644609)
            ·
              refine ⟨1376208079532296667733457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1834944106043062223644609 1376208079532296667733457)
              ·
                refine ⟨1032156059649222500800093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376208079532296667733457 1032156059649222500800093)
                ·
                  refine ⟨387058522368458437800035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032156059649222500800093 387058522368458437800035)
                  ·
                    rfl

theorem cell21_1696036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_1696036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696036 prefixEnd_1696036 := by exact prefixLift 1696036
  have htrace : WordTrace (prefixWord ++ tailWord_1696036) baseStart_1696036 baseEnd_1696036 := by
    simpa [prefixWord, tailWord_1696036, baseEnd_1696036] using wordTrace_append hprefix tailTrace_1696036
  have hstable : (prefixWord ++ tailWord_1696036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696036).length < 2 ^ (prefixWord ++ tailWord_1696036).sum := by decide
  have hdescent : baseEnd_1696036 < baseStart_1696036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696109 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1696109 : Nat := 118140960795 + 1696109 * 2 ^ 59
def prefixEnd_1696109 : Nat := 4983230072969 + 3 ^ 40 * 1696109 * 2
def baseEnd_1696109 : Nat := 387075181963026533083219

theorem tailTrace_1696109 : CollatzResearch.WordTrace tailWord_1696109 prefixEnd_1696109 387075181963026533083219 := by
  unfold tailWord_1696109
  simp only [CollatzResearch.WordTrace]
  refine ⟨61862177412294240200315381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41241451608196160133543587 61862177412294240200315381)
  ·
    refine ⟨5799579132402585018779567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61862177412294240200315381 5799579132402585018779567)
    ·
      refine ⟨8699368698603877528169351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799579132402585018779567 8699368698603877528169351)
      ·
        refine ⟨13049053047905816292254027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8699368698603877528169351 13049053047905816292254027)
        ·
          refine ⟨19573579571858724438381041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13049053047905816292254027 19573579571858724438381041)
          ·
            refine ⟨14680184678894043328785781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19573579571858724438381041 14680184678894043328785781)
            ·
              refine ⟨1376267313646316562073667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14680184678894043328785781 1376267313646316562073667)
              ·
                refine ⟨2064400970469474843110501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376267313646316562073667 2064400970469474843110501)
                ·
                  refine ⟨387075181963026533083219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064400970469474843110501 387075181963026533083219)
                  ·
                    rfl

theorem cell21_1696109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1696109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696109 prefixEnd_1696109 := by exact prefixLift 1696109
  have htrace : WordTrace (prefixWord ++ tailWord_1696109) baseStart_1696109 baseEnd_1696109 := by
    simpa [prefixWord, tailWord_1696109, baseEnd_1696109] using wordTrace_append hprefix tailTrace_1696109
  have hstable : (prefixWord ++ tailWord_1696109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696109).length < 2 ^ (prefixWord ++ tailWord_1696109).sum := by decide
  have hdescent : baseEnd_1696109 < baseStart_1696109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696123 : List Nat := [1, 1, 1, 1, 1, 9, 2, 5]
def baseStart_1696123 : Nat := 118140960795 + 1696123 * 2 ^ 59
def prefixEnd_1696123 : Nat := 4983230072969 + 3 ^ 40 * 1696123 * 2
def baseEnd_1696123 : Nat := 129026125651255206616619

theorem tailTrace_1696123 : CollatzResearch.WordTrace tailWord_1696123 prefixEnd_1696123 129026125651255206616619 := by
  unfold tailWord_1696123
  simp only [CollatzResearch.WordTrace]
  refine ⟨61862688034243520591325023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41241792022829013727550015 61862688034243520591325023)
  ·
    refine ⟨92794032051365280886987535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61862688034243520591325023 92794032051365280886987535)
    ·
      refine ⟨139191048077047921330481303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92794032051365280886987535 139191048077047921330481303)
      ·
        refine ⟨208786572115571881995721955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139191048077047921330481303 208786572115571881995721955)
        ·
          refine ⟨313179858173357822993582933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208786572115571881995721955 313179858173357822993582933)
          ·
            refine ⟨1835038231484518494103025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 313179858173357822993582933 1835038231484518494103025)
            ·
              refine ⟨1376278673613388870577269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835038231484518494103025 1376278673613388870577269)
              ·
                refine ⟨129026125651255206616619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1376278673613388870577269 129026125651255206616619)
                ·
                  rfl

theorem cell21_1696123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 5].length) (baseStart_1696123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696123 prefixEnd_1696123 := by exact prefixLift 1696123
  have htrace : WordTrace (prefixWord ++ tailWord_1696123) baseStart_1696123 baseEnd_1696123 := by
    simpa [prefixWord, tailWord_1696123, baseEnd_1696123] using wordTrace_append hprefix tailTrace_1696123
  have hstable : (prefixWord ++ tailWord_1696123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696123).length < 2 ^ (prefixWord ++ tailWord_1696123).sum := by decide
  have hdescent : baseEnd_1696123 < baseStart_1696123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696151 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 6]
def baseStart_1696151 : Nat := 118140960795 + 1696151 * 2 ^ 59
def prefixEnd_1696151 : Nat := 4983230072969 + 3 ^ 40 * 1696151 * 2
def baseEnd_1696151 : Nat := 387084766935243793383133

theorem tailTrace_1696151 : CollatzResearch.WordTrace tailWord_1696151 prefixEnd_1696151 387084766935243793383133 := by
  unfold tailWord_1696151
  simp only [CollatzResearch.WordTrace]
  refine ⟨61863709278142081373344307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41242472852094720915562871 61863709278142081373344307)
  ·
    refine ⟨92795563917213122060016461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61863709278142081373344307 92795563917213122060016461)
    ·
      refine ⟨34798336468954920772506173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92795563917213122060016461 34798336468954920772506173)
      ·
        refine ⟨13049376175858095289689815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34798336468954920772506173 13049376175858095289689815)
        ·
          refine ⟨19574064263787142934534723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13049376175858095289689815 19574064263787142934534723)
          ·
            refine ⟨29361096395680714401802085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19574064263787142934534723 29361096395680714401802085)
            ·
              refine ⟨5505205574190133950337891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29361096395680714401802085 5505205574190133950337891)
              ·
                refine ⟨8257808361285200925506837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505205574190133950337891 8257808361285200925506837)
                ·
                  refine ⟨387084766935243793383133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8257808361285200925506837 387084766935243793383133)
                  ·
                    rfl

theorem cell21_1696151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_1696151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696151 prefixEnd_1696151 := by exact prefixLift 1696151
  have htrace : WordTrace (prefixWord ++ tailWord_1696151) baseStart_1696151 baseEnd_1696151 := by
    simpa [prefixWord, tailWord_1696151, baseEnd_1696151] using wordTrace_append hprefix tailTrace_1696151
  have hstable : (prefixWord ++ tailWord_1696151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696151).length < 2 ^ (prefixWord ++ tailWord_1696151).sum := by decide
  have hdescent : baseEnd_1696151 < baseStart_1696151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696154 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_1696154 : Nat := 118140960795 + 1696154 * 2 ^ 59
def prefixEnd_1696154 : Nat := 4983230072969 + 3 ^ 40 * 1696154 * 2
def baseEnd_1696154 : Nat := 387085451576116454833127

theorem tailTrace_1696154 : CollatzResearch.WordTrace tailWord_1696154 prefixEnd_1696154 387085451576116454833127 := by
  unfold tailWord_1696154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15465954674282803221425879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41242545798087475257135677 15465954674282803221425879)
  ·
    refine ⟨23198932011424204832138819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15465954674282803221425879 23198932011424204832138819)
    ·
      refine ⟨34798398017136307248208229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23198932011424204832138819 34798398017136307248208229)
      ·
        refine ⟨6524699628213057609039043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34798398017136307248208229 6524699628213057609039043)
        ·
          refine ⟨9787049442319586413558565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6524699628213057609039043 9787049442319586413558565)
          ·
            refine ⟨1835071770434922452542231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9787049442319586413558565 1835071770434922452542231)
            ·
              refine ⟨2752607655652383678813347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835071770434922452542231 2752607655652383678813347)
              ·
                refine ⟨4128911483478575518220021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752607655652383678813347 4128911483478575518220021)
                ·
                  refine ⟨387085451576116454833127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4128911483478575518220021 387085451576116454833127)
                  ·
                    rfl

theorem cell21_1696154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_1696154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696154 prefixEnd_1696154 := by exact prefixLift 1696154
  have htrace : WordTrace (prefixWord ++ tailWord_1696154) baseStart_1696154 baseEnd_1696154 := by
    simpa [prefixWord, tailWord_1696154, baseEnd_1696154] using wordTrace_append hprefix tailTrace_1696154
  have hstable : (prefixWord ++ tailWord_1696154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696154).length < 2 ^ (prefixWord ++ tailWord_1696154).sum := by decide
  have hdescent : baseEnd_1696154 < baseStart_1696154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696306 : List Nat := [3, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1696306 : Nat := 118140960795 + 1696306 * 2 ^ 59
def prefixEnd_1696306 : Nat := 4983230072969 + 3 ^ 40 * 1696306 * 2
def baseEnd_1696306 : Nat := 387120140046997968299483

theorem tailTrace_1696306 : CollatzResearch.WordTrace tailWord_1696306 prefixEnd_1696306 387120140046997968299483 := by
  unfold tailWord_1696306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467340648145135711309193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41246241728387028563491181 15467340648145135711309193)
  ·
    refine ⟨11600505486108851783481895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15467340648145135711309193 11600505486108851783481895)
    ·
      refine ⟨17400758229163277675222843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11600505486108851783481895 17400758229163277675222843)
      ·
        refine ⟨26101137343744916512834265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17400758229163277675222843 26101137343744916512834265)
        ·
          refine ⟨19575853007808687384625699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26101137343744916512834265 19575853007808687384625699)
          ·
            refine ⟨29363779511713031076938549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19575853007808687384625699 29363779511713031076938549)
            ·
              refine ⟨2752854329223096663462989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29363779511713031076938549 2752854329223096663462989)
              ·
                refine ⟨1032320373458661248798621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2752854329223096663462989 1032320373458661248798621)
                ·
                  refine ⟨387120140046997968299483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032320373458661248798621 387120140046997968299483)
                  ·
                    rfl

theorem cell21_1696306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1696306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696306 prefixEnd_1696306 := by exact prefixLift 1696306
  have htrace : WordTrace (prefixWord ++ tailWord_1696306) baseStart_1696306 baseEnd_1696306 := by
    simpa [prefixWord, tailWord_1696306, baseEnd_1696306] using wordTrace_append hprefix tailTrace_1696306
  have hstable : (prefixWord ++ tailWord_1696306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696306).length < 2 ^ (prefixWord ++ tailWord_1696306).sum := by decide
  have hdescent : baseEnd_1696306 < baseStart_1696306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696337 : List Nat := [1, 2, 2, 1, 3, 5, 2, 1, 4]
def baseStart_1696337 : Nat := 118140960795 + 1696337 * 2 ^ 59
def prefixEnd_1696337 : Nat := 4983230072969 + 3 ^ 40 * 1696337 * 2
def baseEnd_1696337 : Nat := 387127214669348803282753

theorem tailTrace_1696337 : CollatzResearch.WordTrace tailWord_1696337 prefixEnd_1696337 387127214669348803282753 := by
  unfold tailWord_1696337
  simp only [CollatzResearch.WordTrace]
  refine ⟨61870493255468235139615265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41246995503645490093076843 61870493255468235139615265)
  ·
    refine ⟨46402869941601176354711449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61870493255468235139615265 46402869941601176354711449)
    ·
      refine ⟨34802152456200882266033587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46402869941601176354711449 34802152456200882266033587)
      ·
        refine ⟨52203228684301323399050381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34802152456200882266033587 52203228684301323399050381)
        ·
          refine ⟨19576210756612996274643893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52203228684301323399050381 19576210756612996274643893)
          ·
            refine ⟨1835269758432468400747865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19576210756612996274643893 1835269758432468400747865)
            ·
              refine ⟨1376452318824351300560899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835269758432468400747865 1376452318824351300560899)
              ·
                refine ⟨2064678478236526950841349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376452318824351300560899 2064678478236526950841349)
                ·
                  refine ⟨387127214669348803282753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064678478236526950841349 387127214669348803282753)
                  ·
                    rfl

theorem cell21_1696337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_1696337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696337 prefixEnd_1696337 := by exact prefixLift 1696337
  have htrace : WordTrace (prefixWord ++ tailWord_1696337) baseStart_1696337 baseEnd_1696337 := by
    simpa [prefixWord, tailWord_1696337, baseEnd_1696337] using wordTrace_append hprefix tailTrace_1696337
  have hstable : (prefixWord ++ tailWord_1696337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696337).length < 2 ^ (prefixWord ++ tailWord_1696337).sum := by decide
  have hdescent : baseEnd_1696337 < baseStart_1696337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696430 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_1696430 : Nat := 118140960795 + 1696430 * 2 ^ 59
def prefixEnd_1696430 : Nat := 4983230072969 + 3 ^ 40 * 1696430 * 2
def baseEnd_1696430 : Nat := 387148438536401308232563

theorem tailTrace_1696430 : CollatzResearch.WordTrace tailWord_1696430 prefixEnd_1696430 387148438536401308232563 := by
  unfold tailWord_1696430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7734235655516414002843843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41249256829420874681833829 7734235655516414002843843)
  ·
    refine ⟨11601353483274621004265765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7734235655516414002843843 11601353483274621004265765)
    ·
      refine ⟨2175253778113991438299831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11601353483274621004265765 2175253778113991438299831)
      ·
        refine ⟨3262880667170987157449747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175253778113991438299831 3262880667170987157449747)
        ·
          refine ⟨4894321000756480736174621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262880667170987157449747 4894321000756480736174621)
          ·
            refine ⟨1835370375283680276065483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4894321000756480736174621 1835370375283680276065483)
            ·
              refine ⟨2753055562925520414098225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835370375283680276065483 2753055562925520414098225)
              ·
                refine ⟨2064791672194140310573669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753055562925520414098225 2064791672194140310573669)
                ·
                  refine ⟨387148438536401308232563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2064791672194140310573669 387148438536401308232563)
                  ·
                    rfl

theorem cell21_1696430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_1696430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696430 prefixEnd_1696430 := by exact prefixLift 1696430
  have htrace : WordTrace (prefixWord ++ tailWord_1696430) baseStart_1696430 baseEnd_1696430 := by
    simpa [prefixWord, tailWord_1696430, baseEnd_1696430] using wordTrace_append hprefix tailTrace_1696430
  have hstable : (prefixWord ++ tailWord_1696430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696430).length < 2 ^ (prefixWord ++ tailWord_1696430).sum := by decide
  have hdescent : baseEnd_1696430 < baseStart_1696430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696461 : List Nat := [1, 6, 2, 1, 2, 2, 2, 5]
def baseStart_1696461 : Nat := 118140960795 + 1696461 * 2 ^ 59
def prefixEnd_1696461 : Nat := 4983230072969 + 3 ^ 40 * 1696461 * 2
def baseEnd_1696461 : Nat := 129051837719584047738611

theorem tailTrace_1696461 : CollatzResearch.WordTrace tailWord_1696461 prefixEnd_1696461 129051837719584047738611 := by
  unfold tailWord_1696461
  simp only [CollatzResearch.WordTrace]
  refine ⟨61875015907019004317129237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41250010604679336211419491 61875015907019004317129237)
  ·
    refine ⟨2900391370641515827365433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61875015907019004317129237 2900391370641515827365433)
    ·
      refine ⟨2175293527981136870524075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2900391370641515827365433 2175293527981136870524075)
      ·
        refine ⟨3262940291971705305786113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175293527981136870524075 3262940291971705305786113)
        ·
          refine ⟨2447205218978778979339585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3262940291971705305786113 2447205218978778979339585)
          ·
            refine ⟨1835403914234084234504689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2447205218978778979339585 1835403914234084234504689)
            ·
              refine ⟨1376552935675563175878517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835403914234084234504689 1376552935675563175878517)
              ·
                refine ⟨129051837719584047738611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1376552935675563175878517 129051837719584047738611)
                ·
                  rfl

theorem cell21_1696461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 5].length) (baseStart_1696461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696461 prefixEnd_1696461 := by exact prefixLift 1696461
  have htrace : WordTrace (prefixWord ++ tailWord_1696461) baseStart_1696461 baseEnd_1696461 := by
    simpa [prefixWord, tailWord_1696461, baseEnd_1696461] using wordTrace_append hprefix tailTrace_1696461
  have hstable : (prefixWord ++ tailWord_1696461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696461).length < 2 ^ (prefixWord ++ tailWord_1696461).sum := by decide
  have hdescent : baseEnd_1696461 < baseStart_1696461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696610 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1696610 : Nat := 118140960795 + 1696610 * 2 ^ 59
def prefixEnd_1696610 : Nat := 4983230072969 + 3 ^ 40 * 1696610 * 2
def baseEnd_1696610 : Nat := 387189516988760995232195

theorem tailTrace_1696610 : CollatzResearch.WordTrace tailWord_1696610 prefixEnd_1696610 387189516988760995232195 := by
  unfold tailWord_1696610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15470112595869800691075821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41253633588986135176202189 15470112595869800691075821)
  ·
    refine ⟨5801292223451175259153433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15470112595869800691075821 5801292223451175259153433)
    ·
      refine ⟨4350969167588381444365075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5801292223451175259153433 4350969167588381444365075)
      ·
        refine ⟨6526453751382572166547613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350969167588381444365075 6526453751382572166547613)
        ·
          refine ⟨2447420156768464562455355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6526453751382572166547613 2447420156768464562455355)
          ·
            refine ⟨3671130235152696843683033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447420156768464562455355 3671130235152696843683033)
            ·
              refine ⟨2753347676364522632762275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3671130235152696843683033 2753347676364522632762275)
              ·
                refine ⟨4130021514546783949143413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753347676364522632762275 4130021514546783949143413)
                ·
                  refine ⟨387189516988760995232195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4130021514546783949143413 387189516988760995232195)
                  ·
                    rfl

theorem cell21_1696610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1696610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696610 prefixEnd_1696610 := by exact prefixLift 1696610
  have htrace : WordTrace (prefixWord ++ tailWord_1696610) baseStart_1696610 baseEnd_1696610 := by
    simpa [prefixWord, tailWord_1696610, baseEnd_1696610] using wordTrace_append hprefix tailTrace_1696610
  have hstable : (prefixWord ++ tailWord_1696610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696610).length < 2 ^ (prefixWord ++ tailWord_1696610).sum := by decide
  have hdescent : baseEnd_1696610 < baseStart_1696610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696621 : List Nat := [1, 5, 1, 1, 1, 1, 1, 10]
def baseStart_1696621 : Nat := 118140960795 + 1696621 * 2 ^ 59
def prefixEnd_1696621 : Nat := 4983230072969 + 3 ^ 40 * 1696621 * 2
def baseEnd_1696621 : Nat := 129064009112875806849613

theorem tailTrace_1696621 : CollatzResearch.WordTrace tailWord_1696621 prefixEnd_1696621 129064009112875806849613 := by
  unfold tailWord_1696621
  simp only [CollatzResearch.WordTrace]
  refine ⟨61880851586439351642953717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41253901057626234428635811 61880851586439351642953717)
  ·
    refine ⟨5801329836228689216526911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61880851586439351642953717 5801329836228689216526911)
    ·
      refine ⟨8701994754343033824790367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5801329836228689216526911 8701994754343033824790367)
      ·
        refine ⟨13052992131514550737185551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8701994754343033824790367 13052992131514550737185551)
        ·
          refine ⟨19579488197271826105778327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13052992131514550737185551 19579488197271826105778327)
          ·
            refine ⟨29369232295907739158667491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19579488197271826105778327 29369232295907739158667491)
            ·
              refine ⟨44053848443861608738001237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29369232295907739158667491 44053848443861608738001237)
              ·
                refine ⟨129064009112875806849613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44053848443861608738001237 129064009112875806849613)
                ·
                  rfl

theorem cell21_1696621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 10].length) (baseStart_1696621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696621 prefixEnd_1696621 := by exact prefixLift 1696621
  have htrace : WordTrace (prefixWord ++ tailWord_1696621) baseStart_1696621 baseEnd_1696621 := by
    simpa [prefixWord, tailWord_1696621, baseEnd_1696621] using wordTrace_append hprefix tailTrace_1696621
  have hstable : (prefixWord ++ tailWord_1696621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696621).length < 2 ^ (prefixWord ++ tailWord_1696621).sum := by decide
  have hdescent : baseEnd_1696621 < baseStart_1696621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696697 : List Nat := [1, 2, 1, 4, 2, 2, 2, 7]
def baseStart_1696697 : Nat := 118140960795 + 1696697 * 2 ^ 59
def prefixEnd_1696697 : Nat := 4983230072969 + 3 ^ 40 * 1696697 * 2
def baseEnd_1696697 : Nat := 129069790524689392427339

theorem tailTrace_1696697 : CollatzResearch.WordTrace tailWord_1696697 prefixEnd_1696697 129069790524689392427339 := by
  unfold tailWord_1696697
  simp only [CollatzResearch.WordTrace]
  refine ⟨61883623534164016622720345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41255749022776011081813563 61883623534164016622720345)
  ·
    refine ⟨46412717650623012467040259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61883623534164016622720345 46412717650623012467040259)
    ·
      refine ⟨69619076475934518700560389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46412717650623012467040259 69619076475934518700560389)
      ·
        refine ⟨13053576839237722256355073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69619076475934518700560389 13053576839237722256355073)
        ·
          refine ⟨9790182629428291692266305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13053576839237722256355073 9790182629428291692266305)
          ·
            refine ⟨7342636972071218769199729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9790182629428291692266305 7342636972071218769199729)
            ·
              refine ⟨5506977729053414076899797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7342636972071218769199729 5506977729053414076899797)
              ·
                refine ⟨129069790524689392427339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5506977729053414076899797 129069790524689392427339)
                ·
                  rfl

theorem cell21_1696697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 7].length) (baseStart_1696697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696697 prefixEnd_1696697 := by exact prefixLift 1696697
  have htrace : WordTrace (prefixWord ++ tailWord_1696697) baseStart_1696697 baseEnd_1696697 := by
    simpa [prefixWord, tailWord_1696697, baseEnd_1696697] using wordTrace_append hprefix tailTrace_1696697
  have hstable : (prefixWord ++ tailWord_1696697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696697).length < 2 ^ (prefixWord ++ tailWord_1696697).sum := by decide
  have hdescent : baseEnd_1696697 < baseStart_1696697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696776 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_1696776 : Nat := 118140960795 + 1696776 * 2 ^ 59
def prefixEnd_1696776 : Nat := 4983230072969 + 3 ^ 40 * 1696776 * 2
def baseEnd_1696776 : Nat := 387227400450381595465189

theorem tailTrace_1696776 : CollatzResearch.WordTrace tailWord_1696776 prefixEnd_1696776 387227400450381595465189 := by
  unfold tailWord_1696776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30943252450438906557423091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41257669933918542076564121 30943252450438906557423091)
  ·
    refine ⟨46414878675658359836134637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30943252450438906557423091 46414878675658359836134637)
    ·
      refine ⟨17405579503371884938550489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46414878675658359836134637 17405579503371884938550489)
      ·
        refine ⟨13054184627528913703912867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17405579503371884938550489 13054184627528913703912867)
        ·
          refine ⟨19581276941293370555869301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054184627528913703912867 19581276941293370555869301)
          ·
            refine ⟨1835744713246253489612747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19581276941293370555869301 1835744713246253489612747)
            ·
              refine ⟨2753617069869380234419121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835744713246253489612747 2753617069869380234419121)
              ·
                refine ⟨2065212802402035175814341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753617069869380234419121 2065212802402035175814341)
                ·
                  refine ⟨387227400450381595465189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2065212802402035175814341 387227400450381595465189)
                  ·
                    rfl

theorem cell21_1696776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_1696776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696776 prefixEnd_1696776 := by exact prefixLift 1696776
  have htrace : WordTrace (prefixWord ++ tailWord_1696776) baseStart_1696776 baseEnd_1696776 := by
    simpa [prefixWord, tailWord_1696776, baseEnd_1696776] using wordTrace_append hprefix tailTrace_1696776
  have hstable : (prefixWord ++ tailWord_1696776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696776).length < 2 ^ (prefixWord ++ tailWord_1696776).sum := by decide
  have hdescent : baseEnd_1696776 < baseStart_1696776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696807 : List Nat := [1, 1, 7, 1, 1, 1, 4, 5]
def baseStart_1696807 : Nat := 118140960795 + 1696807 * 2 ^ 59
def prefixEnd_1696807 : Nat := 4983230072969 + 3 ^ 40 * 1696807 * 2
def baseEnd_1696807 : Nat := 129078158357577476816153

theorem tailTrace_1696807 : CollatzResearch.WordTrace tailWord_1696807 prefixEnd_1696807 129078158357577476816153 := by
  unfold tailWord_1696807
  simp only [CollatzResearch.WordTrace]
  refine ⟨61887635563765505409224675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41258423709177003606149783 61887635563765505409224675)
  ·
    refine ⟨92831453345648258113837013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61887635563765505409224675 92831453345648258113837013)
    ·
      refine ⟨2175737187788631049543055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 92831453345648258113837013 2175737187788631049543055)
      ·
        refine ⟨3263605781682946574314583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175737187788631049543055 3263605781682946574314583)
        ·
          refine ⟨4895408672524419861471875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263605781682946574314583 4895408672524419861471875)
          ·
            refine ⟨7343113008786629792207813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895408672524419861471875 7343113008786629792207813)
            ·
              refine ⟨1376833689147493086038965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7343113008786629792207813 1376833689147493086038965)
              ·
                refine ⟨129078158357577476816153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1376833689147493086038965 129078158357577476816153)
                ·
                  rfl

theorem cell21_1696807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 5].length) (baseStart_1696807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696807 prefixEnd_1696807 := by exact prefixLift 1696807
  have htrace : WordTrace (prefixWord ++ tailWord_1696807) baseStart_1696807 baseEnd_1696807 := by
    simpa [prefixWord, tailWord_1696807, baseEnd_1696807] using wordTrace_append hprefix tailTrace_1696807
  have hstable : (prefixWord ++ tailWord_1696807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696807).length < 2 ^ (prefixWord ++ tailWord_1696807).sum := by decide
  have hdescent : baseEnd_1696807 < baseStart_1696807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696818 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1696818 : Nat := 118140960795 + 1696818 * 2 ^ 59
def prefixEnd_1696818 : Nat := 4983230072969 + 3 ^ 40 * 1696818 * 2
def baseEnd_1696818 : Nat := 387236985422598855765103

theorem tailTrace_1696818 : CollatzResearch.WordTrace tailWord_1696818 prefixEnd_1696818 387236985422598855765103 := by
  unfold tailWord_1696818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472009191681413571968777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41258691177817102858583405 15472009191681413571968777)
  ·
    refine ⟨11604006893761060178976583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15472009191681413571968777 11604006893761060178976583)
    ·
      refine ⟨17406010340641590268464875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11604006893761060178976583 17406010340641590268464875)
      ·
        refine ⟨26109015510962385402697313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17406010340641590268464875 26109015510962385402697313)
        ·
          refine ⟨19581761633221789052022985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26109015510962385402697313 19581761633221789052022985)
          ·
            refine ⟨14686321224916341789017239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19581761633221789052022985 14686321224916341789017239)
            ·
              refine ⟨22029481837374512683525859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686321224916341789017239 22029481837374512683525859)
              ·
                refine ⟨33044222756061769025288789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22029481837374512683525859 33044222756061769025288789)
                ·
                  refine ⟨387236985422598855765103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33044222756061769025288789 387236985422598855765103)
                  ·
                    rfl

theorem cell21_1696818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1696818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696818 prefixEnd_1696818 := by exact prefixLift 1696818
  have htrace : WordTrace (prefixWord ++ tailWord_1696818) baseStart_1696818 baseEnd_1696818 := by
    simpa [prefixWord, tailWord_1696818, baseEnd_1696818] using wordTrace_append hprefix tailTrace_1696818
  have hstable : (prefixWord ++ tailWord_1696818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696818).length < 2 ^ (prefixWord ++ tailWord_1696818).sum := by decide
  have hdescent : baseEnd_1696818 < baseStart_1696818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696838 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1696838 : Nat := 118140960795 + 1696838 * 2 ^ 59
def prefixEnd_1696838 : Nat := 4983230072969 + 3 ^ 40 * 1696838 * 2
def baseEnd_1696838 : Nat := 387241549695083265431729

theorem tailTrace_1696838 : CollatzResearch.WordTrace tailWord_1696838 prefixEnd_1696838 387241549695083265431729 := by
  unfold tailWord_1696838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1934023944582912428237599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41259177484435465135735445 1934023944582912428237599)
  ·
    refine ⟨2901035916874368642356399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1934023944582912428237599 2901035916874368642356399)
    ·
      refine ⟨4351553875311552963534599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2901035916874368642356399 4351553875311552963534599)
      ·
        refine ⟨6527330812967329445301899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351553875311552963534599 6527330812967329445301899)
        ·
          refine ⟨9790996219450994167952849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527330812967329445301899 9790996219450994167952849)
          ·
            refine ⟨7343247164588245625964637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9790996219450994167952849 7343247164588245625964637)
            ·
              refine ⟨2753717686720592109736739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7343247164588245625964637 2753717686720592109736739)
              ·
                refine ⟨4130576530080888164605109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753717686720592109736739 4130576530080888164605109)
                ·
                  refine ⟨387241549695083265431729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4130576530080888164605109 387241549695083265431729)
                  ·
                    rfl

theorem cell21_1696838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1696838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696838 prefixEnd_1696838 := by exact prefixLift 1696838
  have htrace : WordTrace (prefixWord ++ tailWord_1696838) baseStart_1696838 baseEnd_1696838 := by
    simpa [prefixWord, tailWord_1696838, baseEnd_1696838] using wordTrace_append hprefix tailTrace_1696838
  have hstable : (prefixWord ++ tailWord_1696838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696838).length < 2 ^ (prefixWord ++ tailWord_1696838).sum := by decide
  have hdescent : baseEnd_1696838 < baseStart_1696838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696852 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1696852 : Nat := 118140960795 + 1696852 * 2 ^ 59
def prefixEnd_1696852 : Nat := 4983230072969 + 3 ^ 40 * 1696852 * 2
def baseEnd_1696852 : Nat := 387244744685822352198367

theorem tailTrace_1696852 : CollatzResearch.WordTrace tailWord_1696852 prefixEnd_1696852 387244744685822352198367 := by
  unfold tailWord_1696852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30944638424301239047306405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41259517899068318729741873 30944638424301239047306405)
  ·
    refine ⟨5802119704556482321369951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30944638424301239047306405 5802119704556482321369951)
    ·
      refine ⟨8703179556834723482054927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5802119704556482321369951 8703179556834723482054927)
      ·
        refine ⟨13054769335252085223082391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8703179556834723482054927 13054769335252085223082391)
        ·
          refine ⟨19582154002878127834623587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054769335252085223082391 19582154002878127834623587)
          ·
            refine ⟨29373231004317191751935381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19582154002878127834623587 29373231004317191751935381)
            ·
              refine ⟨1376870203327368363371971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29373231004317191751935381 1376870203327368363371971)
              ·
                refine ⟨2065305304991052545057957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376870203327368363371971 2065305304991052545057957)
                ·
                  refine ⟨387244744685822352198367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2065305304991052545057957 387244744685822352198367)
                  ·
                    rfl

theorem cell21_1696852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1696852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696852 prefixEnd_1696852 := by exact prefixLift 1696852
  have htrace : WordTrace (prefixWord ++ tailWord_1696852) baseStart_1696852 baseEnd_1696852 := by
    simpa [prefixWord, tailWord_1696852, baseEnd_1696852] using wordTrace_append hprefix tailTrace_1696852
  have hstable : (prefixWord ++ tailWord_1696852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696852).length < 2 ^ (prefixWord ++ tailWord_1696852).sum := by decide
  have hdescent : baseEnd_1696852 < baseStart_1696852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696863 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 7]
def baseStart_1696863 : Nat := 118140960795 + 1696863 * 2 ^ 59
def prefixEnd_1696863 : Nat := 4983230072969 + 3 ^ 40 * 1696863 * 2
def baseEnd_1696863 : Nat := 387247255035688777515011

theorem tailTrace_1696863 : CollatzResearch.WordTrace tailWord_1696863 prefixEnd_1696863 387247255035688777515011 := by
  unfold tailWord_1696863
  simp only [CollatzResearch.WordTrace]
  refine ⟨61889678051562626973263243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41259785367708417982175495 61889678051562626973263243)
  ·
    refine ⟨92834517077343940459894865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61889678051562626973263243 92834517077343940459894865)
    ·
      refine ⟨69625887808007955344921149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92834517077343940459894865 69625887808007955344921149)
      ·
        refine ⟨26109707928002983254345431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69625887808007955344921149 26109707928002983254345431)
        ·
          refine ⟨39164561892004474881518147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26109707928002983254345431 39164561892004474881518147)
          ·
            refine ⟨58746842838006712322277221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39164561892004474881518147 58746842838006712322277221)
            ·
              refine ⟨11015033032126258560426979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58746842838006712322277221 11015033032126258560426979)
              ·
                refine ⟨16522549548189387840640469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11015033032126258560426979 16522549548189387840640469)
                ·
                  refine ⟨387247255035688777515011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16522549548189387840640469 387247255035688777515011)
                  ·
                    rfl

theorem cell21_1696863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_1696863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696863 prefixEnd_1696863 := by exact prefixLift 1696863
  have htrace : WordTrace (prefixWord ++ tailWord_1696863) baseStart_1696863 baseEnd_1696863 := by
    simpa [prefixWord, tailWord_1696863, baseEnd_1696863] using wordTrace_append hprefix tailTrace_1696863
  have hstable : (prefixWord ++ tailWord_1696863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696863).length < 2 ^ (prefixWord ++ tailWord_1696863).sum := by decide
  have hdescent : baseEnd_1696863 < baseStart_1696863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696866 : List Nat := [3, 3, 2, 2, 1, 1, 2, 7]
def baseStart_1696866 : Nat := 118140960795 + 1696866 * 2 ^ 59
def prefixEnd_1696866 : Nat := 4983230072969 + 3 ^ 40 * 1696866 * 2
def baseEnd_1696866 : Nat := 129082646558853812988335

theorem tailTrace_1696866 : CollatzResearch.WordTrace tailWord_1696866 prefixEnd_1696866 129082646558853812988335 := by
  unfold tailWord_1696866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472446867637939621405613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41259858313701172323748301 15472446867637939621405613)
  ·
    refine ⟨5802167575364227358027105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15472446867637939621405613 5802167575364227358027105)
    ·
      refine ⟨4351625681523170518520329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5802167575364227358027105 4351625681523170518520329)
      ·
        refine ⟨3263719261142377888890247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4351625681523170518520329 3263719261142377888890247)
        ·
          refine ⟨4895578891713566833335371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3263719261142377888890247 4895578891713566833335371)
          ·
            refine ⟨7343368337570350250003057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895578891713566833335371 7343368337570350250003057)
            ·
              refine ⟨5507526253177762687502293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343368337570350250003057 5507526253177762687502293)
              ·
                refine ⟨129082646558853812988335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5507526253177762687502293 129082646558853812988335)
                ·
                  rfl

theorem cell21_1696866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_1696866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696866 prefixEnd_1696866 := by exact prefixLift 1696866
  have htrace : WordTrace (prefixWord ++ tailWord_1696866) baseStart_1696866 baseEnd_1696866 := by
    simpa [prefixWord, tailWord_1696866, baseEnd_1696866] using wordTrace_append hprefix tailTrace_1696866
  have hstable : (prefixWord ++ tailWord_1696866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696866).length < 2 ^ (prefixWord ++ tailWord_1696866).sum := by decide
  have hdescent : baseEnd_1696866 < baseStart_1696866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1696956 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1696956 : Nat := 118140960795 + 1696956 * 2 ^ 59
def prefixEnd_1696956 : Nat := 4983230072969 + 3 ^ 40 * 1696956 * 2
def baseEnd_1696956 : Nat := 387268478902741282464821

theorem tailTrace_1696956 : CollatzResearch.WordTrace tailWord_1696956 prefixEnd_1696956 387268478902741282464821 := by
  unfold tailWord_1696956
  simp only [CollatzResearch.WordTrace]
  refine ⟨30946535020112851928199361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41262046693483802570932481 30946535020112851928199361)
  ·
    refine ⟨23209901265084638946149521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30946535020112851928199361 23209901265084638946149521)
    ·
      refine ⟨17407425948813479209612141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23209901265084638946149521 17407425948813479209612141)
      ·
        refine ⟨6527784730805054703604553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17407425948813479209612141 6527784730805054703604553)
        ·
          refine ⟨4895838548103791027703415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6527784730805054703604553 4895838548103791027703415)
          ·
            refine ⟨7343757822155686541555123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895838548103791027703415 7343757822155686541555123)
            ·
              refine ⟨11015636733233529812332685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343757822155686541555123 11015636733233529812332685)
              ·
                refine ⟨4130863774962573679624757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11015636733233529812332685 4130863774962573679624757)
                ·
                  refine ⟨387268478902741282464821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4130863774962573679624757 387268478902741282464821)
                  ·
                    rfl

theorem cell21_1696956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1696956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1696956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1696956 prefixEnd_1696956 := by exact prefixLift 1696956
  have htrace : WordTrace (prefixWord ++ tailWord_1696956) baseStart_1696956 baseEnd_1696956 := by
    simpa [prefixWord, tailWord_1696956, baseEnd_1696956] using wordTrace_append hprefix tailTrace_1696956
  have hstable : (prefixWord ++ tailWord_1696956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1696956).length < 2 ^ (prefixWord ++ tailWord_1696956).sum := by decide
  have hdescent : baseEnd_1696956 < baseStart_1696956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1696956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697066 : List Nat := [3, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_1697066 : Nat := 118140960795 + 1697066 * 2 ^ 59
def prefixEnd_1697066 : Nat := 4983230072969 + 3 ^ 40 * 1697066 * 2
def baseEnd_1697066 : Nat := 387293582401405535631263

theorem tailTrace_1697066 : CollatzResearch.WordTrace tailWord_1697066 prefixEnd_1697066 387293582401405535631263 := by
  unfold tailWord_1697066
  simp only [CollatzResearch.WordTrace]
  refine ⟨15474270517456798160725763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41264721379884795095268701 15474270517456798160725763)
  ·
    refine ⟨23211405776185197241088645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15474270517456798160725763 23211405776185197241088645)
    ·
      refine ⟨4352138583034724482704121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23211405776185197241088645 4352138583034724482704121)
      ·
        refine ⟨3264103937276043362028091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4352138583034724482704121 3264103937276043362028091)
        ·
          refine ⟨4896155905914065043042137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3264103937276043362028091 4896155905914065043042137)
          ·
            refine ⟨3672116929435548782281603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4896155905914065043042137 3672116929435548782281603)
            ·
              refine ⟨5508175394153323173422405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3672116929435548782281603 5508175394153323173422405)
              ·
                refine ⟨1032782886403748095016701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5508175394153323173422405 1032782886403748095016701)
                ·
                  refine ⟨387293582401405535631263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032782886403748095016701 387293582401405535631263)
                  ·
                    rfl

theorem cell21_1697066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_1697066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697066 prefixEnd_1697066 := by exact prefixLift 1697066
  have htrace : WordTrace (prefixWord ++ tailWord_1697066) baseStart_1697066 baseEnd_1697066 := by
    simpa [prefixWord, tailWord_1697066, baseEnd_1697066] using wordTrace_append hprefix tailTrace_1697066
  have hstable : (prefixWord ++ tailWord_1697066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697066).length < 2 ^ (prefixWord ++ tailWord_1697066).sum := by decide
  have hdescent : baseEnd_1697066 < baseStart_1697066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697077 : List Nat := [1, 3, 3, 1, 2, 2, 3, 6]
def baseStart_1697077 : Nat := 118140960795 + 1697077 * 2 ^ 59
def prefixEnd_1697077 : Nat := 4983230072969 + 3 ^ 40 * 1697077 * 2
def baseEnd_1697077 : Nat := 129098697583757320315969

theorem tailTrace_1697077 : CollatzResearch.WordTrace tailWord_1697077 prefixEnd_1697077 129098697583757320315969 := by
  unfold tailWord_1697077
  simp only [CollatzResearch.WordTrace]
  refine ⟨61897483272787341521553485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41264988848524894347702323 61897483272787341521553485)
  ·
    refine ⟨23211556227295253070582557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61897483272787341521553485 23211556227295253070582557)
    ·
      refine ⟨8704333585235719901468459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23211556227295253070582557 8704333585235719901468459)
      ·
        refine ⟨13056500377853579852202689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8704333585235719901468459 13056500377853579852202689)
        ·
          refine ⟨9792375283390184889152017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13056500377853579852202689 9792375283390184889152017)
          ·
            refine ⟨7344281462542638666864013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9792375283390184889152017 7344281462542638666864013)
            ·
              refine ⟨2754105548453489500074005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7344281462542638666864013 2754105548453489500074005)
              ·
                refine ⟨129098697583757320315969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2754105548453489500074005 129098697583757320315969)
                ·
                  rfl

theorem cell21_1697077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 6].length) (baseStart_1697077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697077 prefixEnd_1697077 := by exact prefixLift 1697077
  have htrace : WordTrace (prefixWord ++ tailWord_1697077) baseStart_1697077 baseEnd_1697077 := by
    simpa [prefixWord, tailWord_1697077, baseEnd_1697077] using wordTrace_append hprefix tailTrace_1697077
  have hstable : (prefixWord ++ tailWord_1697077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697077).length < 2 ^ (prefixWord ++ tailWord_1697077).sum := by decide
  have hdescent : baseEnd_1697077 < baseStart_1697077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697136 : List Nat := [2, 1, 1, 1, 4, 2, 2, 8]
def baseStart_1697136 : Nat := 118140960795 + 1697136 * 2 ^ 59
def prefixEnd_1697136 : Nat := 4983230072969 + 3 ^ 40 * 1697136 * 2
def baseEnd_1697136 : Nat := 129103185785033656488151

theorem tailTrace_1697136 : CollatzResearch.WordTrace tailWord_1697136 prefixEnd_1697136 129103185785033656488151 := by
  unfold tailWord_1697136
  simp only [CollatzResearch.WordTrace]
  refine ⟨30949817589786797298975631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41266423453049063065300841 30949817589786797298975631)
  ·
    refine ⟨46424726384680195948463447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30949817589786797298975631 46424726384680195948463447)
    ·
      refine ⟨69637089577020293922695171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46424726384680195948463447 69637089577020293922695171)
      ·
        refine ⟨104455634365530440884042757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69637089577020293922695171 104455634365530440884042757)
        ·
          refine ⟨19585431443536957665758017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104455634365530440884042757 19585431443536957665758017)
          ·
            refine ⟨14689073582652718249318513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19585431443536957665758017 14689073582652718249318513)
            ·
              refine ⟨11016805186989538686988885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14689073582652718249318513 11016805186989538686988885)
              ·
                refine ⟨129103185785033656488151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11016805186989538686988885 129103185785033656488151)
                ·
                  rfl

theorem cell21_1697136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_1697136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697136 prefixEnd_1697136 := by exact prefixLift 1697136
  have htrace : WordTrace (prefixWord ++ tailWord_1697136) baseStart_1697136 baseEnd_1697136 := by
    simpa [prefixWord, tailWord_1697136, baseEnd_1697136] using wordTrace_append hprefix tailTrace_1697136
  have hstable : (prefixWord ++ tailWord_1697136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697136).length < 2 ^ (prefixWord ++ tailWord_1697136).sum := by decide
  have hdescent : baseEnd_1697136 < baseStart_1697136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697277 : List Nat := [1, 4, 1, 1, 1, 5, 2, 3, 3]
def baseStart_1697277 : Nat := 118140960795 + 1697277 * 2 ^ 59
def prefixEnd_1697277 : Nat := 4983230072969 + 3 ^ 40 * 1697277 * 2
def baseEnd_1697277 : Nat := 387341735476116057614165

theorem tailTrace_1697277 : CollatzResearch.WordTrace tailWord_1697277 prefixEnd_1697277 387341735476116057614165 := by
  unfold tailWord_1697277
  simp only [CollatzResearch.WordTrace]
  refine ⟨61904777872062775678834085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41269851914708517119222723 61904777872062775678834085)
  ·
    refine ⟨11607145851011770439781391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61904777872062775678834085 11607145851011770439781391)
    ·
      refine ⟨17410718776517655659672087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11607145851011770439781391 17410718776517655659672087)
      ·
        refine ⟨26116078164776483489508131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17410718776517655659672087 26116078164776483489508131)
        ·
          refine ⟨39174117247164725234262197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26116078164776483489508131 39174117247164725234262197)
          ·
            refine ⟨3672573491921692990712081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39174117247164725234262197 3672573491921692990712081)
            ·
              refine ⟨2754430118941269743034061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3672573491921692990712081 2754430118941269743034061)
              ·
                refine ⟨1032911294602976153637773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2754430118941269743034061 1032911294602976153637773)
                ·
                  refine ⟨387341735476116057614165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032911294602976153637773 387341735476116057614165)
                  ·
                    rfl

theorem cell21_1697277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_1697277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697277 prefixEnd_1697277 := by exact prefixLift 1697277
  have htrace : WordTrace (prefixWord ++ tailWord_1697277) baseStart_1697277 baseEnd_1697277 := by
    simpa [prefixWord, tailWord_1697277, baseEnd_1697277] using wordTrace_append hprefix tailTrace_1697277
  have hstable : (prefixWord ++ tailWord_1697277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697277).length < 2 ^ (prefixWord ++ tailWord_1697277).sum := by decide
  have hdescent : baseEnd_1697277 < baseStart_1697277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697367 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 4]
def baseStart_1697367 : Nat := 118140960795 + 1697367 * 2 ^ 59
def prefixEnd_1697367 : Nat := 4983230072969 + 3 ^ 40 * 1697367 * 2
def baseEnd_1697367 : Nat := 387362274702295901113981

theorem tailTrace_1697367 : CollatzResearch.WordTrace tailWord_1697367 prefixEnd_1697367 387362274702295901113981 := by
  unfold tailWord_1697367
  simp only [CollatzResearch.WordTrace]
  refine ⟨61908060441736721049610355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41272040294491147366406903 61908060441736721049610355)
  ·
    refine ⟨92862090662605081574415533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61908060441736721049610355 92862090662605081574415533)
    ·
      refine ⟨34823283998476905590405825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92862090662605081574415533 34823283998476905590405825)
      ·
        refine ⟨26117462998857679192804369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34823283998476905590405825 26117462998857679192804369)
        ·
          refine ⟨19588097249143259394603277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26117462998857679192804369 19588097249143259394603277)
          ·
            refine ⟨7345536468428722272976229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19588097249143259394603277 7345536468428722272976229)
            ·
              refine ⟨1377288087830385426183043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7345536468428722272976229 1377288087830385426183043)
              ·
                refine ⟨2065932131745578139274565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377288087830385426183043 2065932131745578139274565)
                ·
                  refine ⟨387362274702295901113981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2065932131745578139274565 387362274702295901113981)
                  ·
                    rfl

theorem cell21_1697367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 4].length) (baseStart_1697367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697367 prefixEnd_1697367 := by exact prefixLift 1697367
  have htrace : WordTrace (prefixWord ++ tailWord_1697367) baseStart_1697367 baseEnd_1697367 := by
    simpa [prefixWord, tailWord_1697367, baseEnd_1697367] using wordTrace_append hprefix tailTrace_1697367
  have hstable : (prefixWord ++ tailWord_1697367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697367).length < 2 ^ (prefixWord ++ tailWord_1697367).sum := by decide
  have hdescent : baseEnd_1697367 < baseStart_1697367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697471 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 5]
def baseStart_1697471 : Nat := 118140960795 + 1697471 * 2 ^ 59
def prefixEnd_1697471 : Nat := 4983230072969 + 3 ^ 40 * 1697471 * 2
def baseEnd_1697471 : Nat := 387386008919214831380435

theorem tailTrace_1697471 : CollatzResearch.WordTrace tailWord_1697471 prefixEnd_1697471 387386008919214831380435 := by
  unfold tailWord_1697471
  simp only [CollatzResearch.WordTrace]
  refine ⟨61911853633359946811396267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41274569088906631207597511 61911853633359946811396267)
  ·
    refine ⟨92867780450039920217094401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61911853633359946811396267 92867780450039920217094401)
    ·
      refine ⟨69650835337529940162820801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92867780450039920217094401 69650835337529940162820801)
      ·
        refine ⟨52238126503147455122115601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69650835337529940162820801 52238126503147455122115601)
        ·
          refine ⟨39178594877360591341586701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52238126503147455122115601 39178594877360591341586701)
          ·
            refine ⟨14691973079010221753095013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39178594877360591341586701 14691973079010221753095013)
            ·
              refine ⟨2754744952314416578705315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14691973079010221753095013 2754744952314416578705315)
              ·
                refine ⟨4132117428471624868057973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2754744952314416578705315 4132117428471624868057973)
                ·
                  refine ⟨387386008919214831380435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4132117428471624868057973 387386008919214831380435)
                  ·
                    rfl

theorem cell21_1697471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_1697471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697471 prefixEnd_1697471 := by exact prefixLift 1697471
  have htrace : WordTrace (prefixWord ++ tailWord_1697471) baseStart_1697471 baseEnd_1697471 := by
    simpa [prefixWord, tailWord_1697471, baseEnd_1697471] using wordTrace_append hprefix tailTrace_1697471
  have hstable : (prefixWord ++ tailWord_1697471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697471).length < 2 ^ (prefixWord ++ tailWord_1697471).sum := by decide
  have hdescent : baseEnd_1697471 < baseStart_1697471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697564 : List Nat := [2, 2, 3, 1, 1, 2, 2, 5, 3]
def baseStart_1697564 : Nat := 118140960795 + 1697564 * 2 ^ 59
def prefixEnd_1697564 : Nat := 4983230072969 + 3 ^ 40 * 1697564 * 2
def baseEnd_1697564 : Nat := 387407232786267336330245

theorem tailTrace_1697564 : CollatzResearch.WordTrace tailWord_1697564 prefixEnd_1697564 387407232786267336330245 := by
  unfold tailWord_1697564
  simp only [CollatzResearch.WordTrace]
  refine ⟨30957622811011511847265873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41276830414682015796354497 30957622811011511847265873)
  ·
    refine ⟨23218217108258633885449405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30957622811011511847265873 23218217108258633885449405)
    ·
      refine ⟨8706831415596987707043527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23218217108258633885449405 8706831415596987707043527)
      ·
        refine ⟨13060247123395481560565291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8706831415596987707043527 13060247123395481560565291)
        ·
          refine ⟨19590370685093222340847937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13060247123395481560565291 19590370685093222340847937)
          ·
            refine ⟨14692778013819916755635953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19590370685093222340847937 14692778013819916755635953)
            ·
              refine ⟨11019583510364937566726965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14692778013819916755635953 11019583510364937566726965)
              ·
                refine ⟨1033085954096712896880653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11019583510364937566726965 1033085954096712896880653)
                ·
                  refine ⟨387407232786267336330245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033085954096712896880653 387407232786267336330245)
                  ·
                    rfl

theorem cell21_1697564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_1697564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697564 prefixEnd_1697564 := by exact prefixLift 1697564
  have htrace : WordTrace (prefixWord ++ tailWord_1697564) baseStart_1697564 baseEnd_1697564 := by
    simpa [prefixWord, tailWord_1697564, baseEnd_1697564] using wordTrace_append hprefix tailTrace_1697564
  have hstable : (prefixWord ++ tailWord_1697564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697564).length < 2 ^ (prefixWord ++ tailWord_1697564).sum := by decide
  have hdescent : baseEnd_1697564 < baseStart_1697564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697575 : List Nat := [1, 1, 19]
def baseStart_1697575 : Nat := 118140960795 + 1697575 * 2 ^ 59
def prefixEnd_1697575 : Nat := 4983230072969 + 3 ^ 40 * 1697575 * 2
def baseEnd_1697575 : Nat := 531426259445999673041

theorem tailTrace_1697575 : CollatzResearch.WordTrace tailWord_1697575 prefixEnd_1697575 531426259445999673041 := by
  unfold tailWord_1697575
  simp only [CollatzResearch.WordTrace]
  refine ⟨61915646824983172573182179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41277097883322115048788119 61915646824983172573182179)
  ·
    refine ⟨92873470237474758859773269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61915646824983172573182179 92873470237474758859773269)
    ·
      refine ⟨531426259445999673041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 19 92873470237474758859773269 531426259445999673041)
      ·
        rfl

theorem cell21_1697575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 19].length) (baseStart_1697575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697575 prefixEnd_1697575 := by exact prefixLift 1697575
  have htrace : WordTrace (prefixWord ++ tailWord_1697575) baseStart_1697575 baseEnd_1697575 := by
    simpa [prefixWord, tailWord_1697575, baseEnd_1697575] using wordTrace_append hprefix tailTrace_1697575
  have hstable : (prefixWord ++ tailWord_1697575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697575).length < 2 ^ (prefixWord ++ tailWord_1697575).sum := by decide
  have hdescent : baseEnd_1697575 < baseStart_1697575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697592 : List Nat := [2, 1, 2, 1, 3, 3, 3, 6]
def baseStart_1697592 : Nat := 118140960795 + 1697592 * 2 ^ 59
def prefixEnd_1697592 : Nat := 4983230072969 + 3 ^ 40 * 1697592 * 2
def baseEnd_1697592 : Nat := 129137874255915169954507

theorem tailTrace_1697592 : CollatzResearch.WordTrace tailWord_1697592 prefixEnd_1697592 129137874255915169954507 := by
  unfold tailWord_1697592
  simp only [CollatzResearch.WordTrace]
  refine ⟨30958133432960792238275515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41277511243947722984367353 30958133432960792238275515)
  ·
    refine ⟨46437200149441188357413273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30958133432960792238275515 46437200149441188357413273)
    ·
      refine ⟨34827900112080891268059955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46437200149441188357413273 34827900112080891268059955)
      ·
        refine ⟨52241850168121336902089933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34827900112080891268059955 52241850168121336902089933)
        ·
          refine ⟨19590693813045501338283725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52241850168121336902089933 19590693813045501338283725)
          ·
            refine ⟨7346510179892063001856397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19590693813045501338283725 7346510179892063001856397)
            ·
              refine ⟨2754941317459523625696149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7346510179892063001856397 2754941317459523625696149)
              ·
                refine ⟨129137874255915169954507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2754941317459523625696149 129137874255915169954507)
                ·
                  rfl

theorem cell21_1697592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_1697592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697592 prefixEnd_1697592 := by exact prefixLift 1697592
  have htrace : WordTrace (prefixWord ++ tailWord_1697592) baseStart_1697592 baseEnd_1697592 := by
    simpa [prefixWord, tailWord_1697592, baseEnd_1697592] using wordTrace_append hprefix tailTrace_1697592
  have hstable : (prefixWord ++ tailWord_1697592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697592).length < 2 ^ (prefixWord ++ tailWord_1697592).sum := by decide
  have hdescent : baseEnd_1697592 < baseStart_1697592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697640 : List Nat := [2, 1, 4, 2, 1, 1, 1, 6, 3]
def baseStart_1697640 : Nat := 118140960795 + 1697640 * 2 ^ 59
def prefixEnd_1697640 : Nat := 4983230072969 + 3 ^ 40 * 1697640 * 2
def baseEnd_1697640 : Nat := 387424577021708093063423

theorem tailTrace_1697640 : CollatzResearch.WordTrace tailWord_1697640 prefixEnd_1697640 387424577021708093063423 := by
  unfold tailWord_1697640
  simp only [CollatzResearch.WordTrace]
  refine ⟨30959008784873844337149187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41278678379831792449532249 30959008784873844337149187)
  ·
    refine ⟨46438513177310766505723781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30959008784873844337149187 46438513177310766505723781)
    ·
      refine ⟨8707221220745768719823209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46438513177310766505723781 8707221220745768719823209)
      ·
        refine ⟨6530415915559326539867407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8707221220745768719823209 6530415915559326539867407)
        ·
          refine ⟨9795623873338989809801111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6530415915559326539867407 9795623873338989809801111)
          ·
            refine ⟨14693435810008484714701667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9795623873338989809801111 14693435810008484714701667)
            ·
              refine ⟨22040153715012727072052501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14693435810008484714701667 22040153715012727072052501)
              ·
                refine ⟨1033132205391221581502461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22040153715012727072052501 1033132205391221581502461)
                ·
                  refine ⟨387424577021708093063423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033132205391221581502461 387424577021708093063423)
                  ·
                    rfl

theorem cell21_1697640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_1697640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697640 prefixEnd_1697640 := by exact prefixLift 1697640
  have htrace : WordTrace (prefixWord ++ tailWord_1697640) baseStart_1697640 baseEnd_1697640 := by
    simpa [prefixWord, tailWord_1697640, baseEnd_1697640] using wordTrace_append hprefix tailTrace_1697640
  have hstable : (prefixWord ++ tailWord_1697640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697640).length < 2 ^ (prefixWord ++ tailWord_1697640).sum := by decide
  have hdescent : baseEnd_1697640 < baseStart_1697640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697651 : List Nat := [1, 1, 1, 2, 2, 1, 3, 10]
def baseStart_1697651 : Nat := 118140960795 + 1697651 * 2 ^ 59
def prefixEnd_1697651 : Nat := 4983230072969 + 3 ^ 40 * 1697651 * 2
def baseEnd_1697651 : Nat := 129142362457191506126689

theorem tailTrace_1697651 : CollatzResearch.WordTrace tailWord_1697651 prefixEnd_1697651 129142362457191506126689 := by
  unfold tailWord_1697651
  simp only [CollatzResearch.WordTrace]
  refine ⟨61918418772707837552948807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41278945848471891701965871 61918418772707837552948807)
  ·
    refine ⟨92877628159061756329423211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61918418772707837552948807 92877628159061756329423211)
    ·
      refine ⟨139316442238592634494134817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92877628159061756329423211 139316442238592634494134817)
      ·
        refine ⟨104487331678944475870601113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139316442238592634494134817 104487331678944475870601113)
        ·
          refine ⟨78365498759208356902950835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104487331678944475870601113 78365498759208356902950835)
          ·
            refine ⟨117548248138812535354426253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78365498759208356902950835 117548248138812535354426253)
            ·
              refine ⟨44080593052054700757909845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117548248138812535354426253 44080593052054700757909845)
              ·
                refine ⟨129142362457191506126689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44080593052054700757909845 129142362457191506126689)
                ·
                  rfl

theorem cell21_1697651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_1697651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697651 prefixEnd_1697651 := by exact prefixLift 1697651
  have htrace : WordTrace (prefixWord ++ tailWord_1697651) baseStart_1697651 baseEnd_1697651 := by
    simpa [prefixWord, tailWord_1697651, baseEnd_1697651] using wordTrace_append hprefix tailTrace_1697651
  have hstable : (prefixWord ++ tailWord_1697651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697651).length < 2 ^ (prefixWord ++ tailWord_1697651).sum := by decide
  have hdescent : baseEnd_1697651 < baseStart_1697651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697674 : List Nat := [3, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1697674 : Nat := 118140960795 + 1697674 * 2 ^ 59
def prefixEnd_1697674 : Nat := 4983230072969 + 3 ^ 40 * 1697674 * 2
def baseEnd_1697674 : Nat := 387432336284931589496687

theorem tailTrace_1697674 : CollatzResearch.WordTrace tailWord_1697674 prefixEnd_1697674 387432336284931589496687 := by
  unfold tailWord_1697674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15479814412906128120259019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41279505101083008320690717 15479814412906128120259019)
  ·
    refine ⟨23219721619359192180388529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15479814412906128120259019 23219721619359192180388529)
    ·
      refine ⟨17414791214519394135291397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23219721619359192180388529 17414791214519394135291397)
      ·
        refine ⟨3265273352722386400367137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17414791214519394135291397 3265273352722386400367137)
        ·
          refine ⟨2448955014541789800275353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3265273352722386400367137 2448955014541789800275353)
          ·
            refine ⟨1836716260906342350206515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2448955014541789800275353 1836716260906342350206515)
            ·
              refine ⟨2755074391359513525309773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836716260906342350206515 2755074391359513525309773)
              ·
                refine ⟨1033152896759817571991165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2755074391359513525309773 1033152896759817571991165)
                ·
                  refine ⟨387432336284931589496687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033152896759817571991165 387432336284931589496687)
                  ·
                    rfl

theorem cell21_1697674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1697674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697674 prefixEnd_1697674 := by exact prefixLift 1697674
  have htrace : WordTrace (prefixWord ++ tailWord_1697674) baseStart_1697674 baseEnd_1697674 := by
    simpa [prefixWord, tailWord_1697674, baseEnd_1697674] using wordTrace_append hprefix tailTrace_1697674
  have hstable : (prefixWord ++ tailWord_1697674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697674).length < 2 ^ (prefixWord ++ tailWord_1697674).sum := by decide
  have hdescent : baseEnd_1697674 < baseStart_1697674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697727 : List Nat := [1, 1, 2, 2, 2, 1, 3, 9]
def baseStart_1697727 : Nat := 118140960795 + 1697727 * 2 ^ 59
def prefixEnd_1697727 : Nat := 4983230072969 + 3 ^ 40 * 1697727 * 2
def baseEnd_1697727 : Nat := 129148143869005091704415

theorem tailTrace_1697727 : CollatzResearch.WordTrace tailWord_1697727 prefixEnd_1697727 129148143869005091704415 := by
  unfold tailWord_1697727
  simp only [CollatzResearch.WordTrace]
  refine ⟨61921190720432502532715435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41280793813621668355143623 61921190720432502532715435)
  ·
    refine ⟨92881786080648753799073153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61921190720432502532715435 92881786080648753799073153)
    ·
      refine ⟨69661339560486565349304865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92881786080648753799073153 69661339560486565349304865)
      ·
        refine ⟨52246004670364924011978649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69661339560486565349304865 52246004670364924011978649)
        ·
          refine ⟨39184503502773693008983987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52246004670364924011978649 39184503502773693008983987)
          ·
            refine ⟨58776755254160539513475981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39184503502773693008983987 58776755254160539513475981)
            ·
              refine ⟨22041283220310202317553493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58776755254160539513475981 22041283220310202317553493)
              ·
                refine ⟨129148143869005091704415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22041283220310202317553493 129148143869005091704415)
                ·
                  rfl

theorem cell21_1697727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_1697727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697727 prefixEnd_1697727 := by exact prefixLift 1697727
  have htrace : WordTrace (prefixWord ++ tailWord_1697727) baseStart_1697727 baseEnd_1697727 := by
    simpa [prefixWord, tailWord_1697727, baseEnd_1697727] using wordTrace_append hprefix tailTrace_1697727
  have hstable : (prefixWord ++ tailWord_1697727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697727).length < 2 ^ (prefixWord ++ tailWord_1697727).sum := by decide
  have hdescent : baseEnd_1697727 < baseStart_1697727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697750 : List Nat := [5, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1697750 : Nat := 118140960795 + 1697750 * 2 ^ 59
def prefixEnd_1697750 : Nat := 4983230072969 + 3 ^ 40 * 1697750 * 2
def baseEnd_1697750 : Nat := 387449680520372346229865

theorem tailTrace_1697750 : CollatzResearch.WordTrace tailWord_1697750 prefixEnd_1697750 387449680520372346229865 := by
  unfold tailWord_1697750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870126849959323591300169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41281353066232784973868469 3870126849959323591300169)
  ·
    refine ⟨2902595137469492693475127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3870126849959323591300169 2902595137469492693475127)
    ·
      refine ⟨4353892706204239040212691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902595137469492693475127 4353892706204239040212691)
      ·
        refine ⟨6530839059306358560319037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353892706204239040212691 6530839059306358560319037)
        ·
          refine ⟨2449064647239884460119639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6530839059306358560319037 2449064647239884460119639)
          ·
            refine ⟨3673596970859826690179459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449064647239884460119639 3673596970859826690179459)
            ·
              refine ⟨5510395456289740035269189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673596970859826690179459 5510395456289740035269189)
              ·
                refine ⟨1033199148054326256612973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5510395456289740035269189 1033199148054326256612973)
                ·
                  refine ⟨387449680520372346229865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033199148054326256612973 387449680520372346229865)
                  ·
                    rfl

theorem cell21_1697750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1697750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697750 prefixEnd_1697750 := by exact prefixLift 1697750
  have htrace : WordTrace (prefixWord ++ tailWord_1697750) baseStart_1697750 baseEnd_1697750 := by
    simpa [prefixWord, tailWord_1697750, baseEnd_1697750] using wordTrace_append hprefix tailTrace_1697750
  have hstable : (prefixWord ++ tailWord_1697750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697750).length < 2 ^ (prefixWord ++ tailWord_1697750).sum := by decide
  have hdescent : baseEnd_1697750 < baseStart_1697750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697803 : List Nat := [1, 1, 1, 1, 6, 1, 10]
def baseStart_1697803 : Nat := 118140960795 + 1697803 * 2 ^ 59
def prefixEnd_1697803 : Nat := 4983230072969 + 3 ^ 40 * 1697803 * 2
def baseEnd_1697803 : Nat := 43051308426939559094047

theorem tailTrace_1697803 : CollatzResearch.WordTrace tailWord_1697803 prefixEnd_1697803 43051308426939559094047 := by
  unfold tailWord_1697803
  simp only [CollatzResearch.WordTrace]
  refine ⟨61923962668157167512482063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41282641778771445008321375 61923962668157167512482063)
  ·
    refine ⟨92885944002235751268723095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61923962668157167512482063 92885944002235751268723095)
    ·
      refine ⟨139328916003353626903084643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92885944002235751268723095 139328916003353626903084643)
      ·
        refine ⟨208993374005030440354626965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139328916003353626903084643 208993374005030440354626965)
        ·
          refine ⟨9796564406485801891623139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208993374005030440354626965 9796564406485801891623139)
          ·
            refine ⟨14694846609728702837434709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9796564406485801891623139 14694846609728702837434709)
            ·
              refine ⟨43051308426939559094047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14694846609728702837434709 43051308426939559094047)
              ·
                rfl

theorem cell21_1697803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 10].length) (baseStart_1697803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697803 prefixEnd_1697803 := by exact prefixLift 1697803
  have htrace : WordTrace (prefixWord ++ tailWord_1697803) baseStart_1697803 baseEnd_1697803 := by
    simpa [prefixWord, tailWord_1697803, baseEnd_1697803] using wordTrace_append hprefix tailTrace_1697803
  have hstable : (prefixWord ++ tailWord_1697803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697803).length < 2 ^ (prefixWord ++ tailWord_1697803).sum := by decide
  have hdescent : baseEnd_1697803 < baseStart_1697803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697854 : List Nat := [4, 2, 1, 3, 3, 1, 7]
def baseStart_1697854 : Nat := 118140960795 + 1697854 * 2 ^ 59
def prefixEnd_1697854 : Nat := 4983230072969 + 3 ^ 40 * 1697854 * 2
def baseEnd_1697854 : Nat := 43052601637476808499591

theorem tailTrace_1697854 : CollatzResearch.WordTrace tailWord_1697854 prefixEnd_1697854 43052601637476808499591 := by
  unfold tailWord_1697854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7740727848871550402823577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41283881860648268815059077 7740727848871550402823577)
  ·
    refine ⟨5805545886653662802117683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7740727848871550402823577 5805545886653662802117683)
    ·
      refine ⟨8708318829980494203176525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5805545886653662802117683 8708318829980494203176525)
      ·
        refine ⟨3265619561242685326191197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8708318829980494203176525 3265619561242685326191197)
        ·
          refine ⟨1224607335466006997321699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3265619561242685326191197 1224607335466006997321699)
          ·
            refine ⟨1836911003199010495982549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224607335466006997321699 1836911003199010495982549)
            ·
              refine ⟨43052601637476808499591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1836911003199010495982549 43052601637476808499591)
              ·
                rfl

theorem cell21_1697854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 7].length) (baseStart_1697854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697854 prefixEnd_1697854 := by exact prefixLift 1697854
  have htrace : WordTrace (prefixWord ++ tailWord_1697854) baseStart_1697854 baseEnd_1697854 := by
    simpa [prefixWord, tailWord_1697854, baseEnd_1697854] using wordTrace_append hprefix tailTrace_1697854
  have hstable : (prefixWord ++ tailWord_1697854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697854).length < 2 ^ (prefixWord ++ tailWord_1697854).sum := by decide
  have hdescent : baseEnd_1697854 < baseStart_1697854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697865 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 4]
def baseStart_1697865 : Nat := 118140960795 + 1697865 * 2 ^ 59
def prefixEnd_1697865 : Nat := 4983230072969 + 3 ^ 40 * 1697865 * 2
def baseEnd_1697865 : Nat := 387475925087157701812963

theorem tailTrace_1697865 : CollatzResearch.WordTrace tailWord_1697865 prefixEnd_1697865 387475925087157701812963 := by
  unfold tailWord_1697865
  simp only [CollatzResearch.WordTrace]
  refine ⟨61926223993932552101239049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41284149329288368067492699 61926223993932552101239049)
  ·
    refine ⟨46444667995449414075929287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61926223993932552101239049 46444667995449414075929287)
    ·
      refine ⟨69667001993174121113893931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46444667995449414075929287 69667001993174121113893931)
      ·
        refine ⟨104500502989761181670840897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69667001993174121113893931 104500502989761181670840897)
        ·
          refine ⟨78375377242320886253130673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104500502989761181670840897 78375377242320886253130673)
          ·
            refine ⟨58781532931740664689848005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78375377242320886253130673 58781532931740664689848005)
            ·
              refine ⟨11021537424701374629346501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58781532931740664689848005 11021537424701374629346501)
              ·
                refine ⟨2066538267131507743002469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11021537424701374629346501 2066538267131507743002469)
                ·
                  refine ⟨387475925087157701812963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066538267131507743002469 387475925087157701812963)
                  ·
                    rfl

theorem cell21_1697865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_1697865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697865 prefixEnd_1697865 := by exact prefixLift 1697865
  have htrace : WordTrace (prefixWord ++ tailWord_1697865) baseStart_1697865 baseEnd_1697865 := by
    simpa [prefixWord, tailWord_1697865, baseEnd_1697865] using wordTrace_append hprefix tailTrace_1697865
  have hstable : (prefixWord ++ tailWord_1697865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697865).length < 2 ^ (prefixWord ++ tailWord_1697865).sum := by decide
  have hdescent : baseEnd_1697865 < baseStart_1697865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697879 : List Nat := [1, 1, 3, 2, 2, 1, 3, 8]
def baseStart_1697879 : Nat := 118140960795 + 1697879 * 2 ^ 59
def prefixEnd_1697879 : Nat := 4983230072969 + 3 ^ 40 * 1697879 * 2
def baseEnd_1697879 : Nat := 129159706692632262859867

theorem tailTrace_1697879 : CollatzResearch.WordTrace tailWord_1697879 prefixEnd_1697879 129159706692632262859867 := by
  unfold tailWord_1697879
  simp only [CollatzResearch.WordTrace]
  refine ⟨61926734615881832492248691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41284489743921221661499127 61926734615881832492248691)
  ·
    refine ⟨92890101923822748738373037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61926734615881832492248691 92890101923822748738373037)
    ·
      refine ⟨34833788221433530776889889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92890101923822748738373037 34833788221433530776889889)
      ·
        refine ⟨26125341166075148082667417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34833788221433530776889889 26125341166075148082667417)
        ·
          refine ⟨19594005874556361062000563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26125341166075148082667417 19594005874556361062000563)
          ·
            refine ⟨29391008811834541593000845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19594005874556361062000563 29391008811834541593000845)
            ·
              refine ⟨11021628304437953097375317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29391008811834541593000845 11021628304437953097375317)
              ·
                refine ⟨129159706692632262859867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11021628304437953097375317 129159706692632262859867)
                ·
                  rfl

theorem cell21_1697879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_1697879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697879 prefixEnd_1697879 := by exact prefixLift 1697879
  have htrace : WordTrace (prefixWord ++ tailWord_1697879) baseStart_1697879 baseEnd_1697879 := by
    simpa [prefixWord, tailWord_1697879, baseEnd_1697879] using wordTrace_append hprefix tailTrace_1697879
  have hstable : (prefixWord ++ tailWord_1697879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697879).length < 2 ^ (prefixWord ++ tailWord_1697879).sum := by decide
  have hdescent : baseEnd_1697879 < baseStart_1697879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1697941 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 4]
def baseStart_1697941 : Nat := 118140960795 + 1697941 * 2 ^ 59
def prefixEnd_1697941 : Nat := 4983230072969 + 3 ^ 40 * 1697941 * 2
def baseEnd_1697941 : Nat := 387493269322598458546141

theorem tailTrace_1697941 : CollatzResearch.WordTrace tailWord_1697941 prefixEnd_1697941 387493269322598458546141 := by
  unfold tailWord_1697941
  simp only [CollatzResearch.WordTrace]
  refine ⟨61928995941657217081005677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41285997294438144720670451 61928995941657217081005677)
  ·
    refine ⟨23223373478121456405377129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61928995941657217081005677 23223373478121456405377129)
    ·
      refine ⟨17417530108591092304032847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23223373478121456405377129 17417530108591092304032847)
      ·
        refine ⟨26126295162886638456049271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17417530108591092304032847 26126295162886638456049271)
        ·
          refine ⟨39189442744329957684073907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26126295162886638456049271 39189442744329957684073907)
          ·
            refine ⟨58784164116494936526110861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39189442744329957684073907 58784164116494936526110861)
            ·
              refine ⟨22044061543685601197291573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58784164116494936526110861 22044061543685601197291573)
              ·
                refine ⟨2066630769720525112246085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22044061543685601197291573 2066630769720525112246085)
                ·
                  refine ⟨387493269322598458546141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066630769720525112246085 387493269322598458546141)
                  ·
                    rfl

theorem cell21_1697941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_1697941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1697941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1697941 prefixEnd_1697941 := by exact prefixLift 1697941
  have htrace : WordTrace (prefixWord ++ tailWord_1697941) baseStart_1697941 baseEnd_1697941 := by
    simpa [prefixWord, tailWord_1697941, baseEnd_1697941] using wordTrace_append hprefix tailTrace_1697941
  have hstable : (prefixWord ++ tailWord_1697941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1697941).length < 2 ^ (prefixWord ++ tailWord_1697941).sum := by decide
  have hdescent : baseEnd_1697941 < baseStart_1697941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1697941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698006 : List Nat := [5, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1698006 : Nat := 118140960795 + 1698006 * 2 ^ 59
def prefixEnd_1698006 : Nat := 4983230072969 + 3 ^ 40 * 1698006 * 2
def baseEnd_1698006 : Nat := 129169367736057596654225

theorem tailTrace_1698006 : CollatzResearch.WordTrace tailWord_1698006 prefixEnd_1698006 129169367736057596654225 := by
  unfold tailWord_1698006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870710417901358323882617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41287577790947822121414581 3870710417901358323882617)
  ·
    refine ⟨2903032813426018742911963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3870710417901358323882617 2903032813426018742911963)
    ·
      refine ⟨4354549220139028114367945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903032813426018742911963 4354549220139028114367945)
      ·
        refine ⟨3265911915104271085775959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4354549220139028114367945 3265911915104271085775959)
        ·
          refine ⟨4898867872656406628663939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3265911915104271085775959 4898867872656406628663939)
          ·
            refine ⟨7348301808984609942995909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898867872656406628663939 7348301808984609942995909)
            ·
              refine ⟨1377806589184614364311733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7348301808984609942995909 1377806589184614364311733)
              ·
                refine ⟨129169367736057596654225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1377806589184614364311733 129169367736057596654225)
                ·
                  rfl

theorem cell21_1698006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1698006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698006 prefixEnd_1698006 := by exact prefixLift 1698006
  have htrace : WordTrace (prefixWord ++ tailWord_1698006) baseStart_1698006 baseEnd_1698006 := by
    simpa [prefixWord, tailWord_1698006, baseEnd_1698006] using wordTrace_append hprefix tailTrace_1698006
  have hstable : (prefixWord ++ tailWord_1698006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698006).length < 2 ^ (prefixWord ++ tailWord_1698006).sum := by decide
  have hdescent : baseEnd_1698006 < baseStart_1698006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698031 : List Nat := [1, 1, 2, 1, 6, 1, 9]
def baseStart_1698031 : Nat := 118140960795 + 1698031 * 2 ^ 59
def prefixEnd_1698031 : Nat := 4983230072969 + 3 ^ 40 * 1698031 * 2
def baseEnd_1698031 : Nat := 43057089838753144671773

theorem tailTrace_1698031 : CollatzResearch.WordTrace tailWord_1698031 prefixEnd_1698031 43057089838753144671773 := by
  unfold tailWord_1698031
  simp only [CollatzResearch.WordTrace]
  refine ⟨61932278511331162451781947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41288185674220774967854631 61932278511331162451781947)
  ·
    refine ⟨92898417766996743677672921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61932278511331162451781947 92898417766996743677672921)
    ·
      refine ⟨69673813325247557758254691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92898417766996743677672921 69673813325247557758254691)
      ·
        refine ⟨104510719987871336637382037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69673813325247557758254691 104510719987871336637382037)
        ·
          refine ⟨4898939999431468904877283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104510719987871336637382037 4898939999431468904877283)
          ·
            refine ⟨7348409999147203357315925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4898939999431468904877283 7348409999147203357315925)
            ·
              refine ⟨43057089838753144671773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7348409999147203357315925 43057089838753144671773)
              ·
                rfl

theorem cell21_1698031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 9].length) (baseStart_1698031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698031 prefixEnd_1698031 := by exact prefixLift 1698031
  have htrace : WordTrace (prefixWord ++ tailWord_1698031) baseStart_1698031 baseEnd_1698031 := by
    simpa [prefixWord, tailWord_1698031, baseEnd_1698031] using wordTrace_append hprefix tailTrace_1698031
  have hstable : (prefixWord ++ tailWord_1698031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698031).length < 2 ^ (prefixWord ++ tailWord_1698031).sum := by decide
  have hdescent : baseEnd_1698031 < baseStart_1698031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698062 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1698062 : Nat := 118140960795 + 1698062 * 2 ^ 59
def prefixEnd_1698062 : Nat := 4983230072969 + 3 ^ 40 * 1698062 * 2
def baseEnd_1698062 : Nat := 387520883171129137029227

theorem tailTrace_1698062 : CollatzResearch.WordTrace tailWord_1698062 prefixEnd_1698062 387520883171129137029227 := by
  unfold tailWord_1698062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7741676146777356843270055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41288939449479236497440293 7741676146777356843270055)
  ·
    refine ⟨11612514220166035264905083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7741676146777356843270055 11612514220166035264905083)
    ·
      refine ⟨17418771330249052897357625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11612514220166035264905083 17418771330249052897357625)
      ·
        refine ⟨13064078497686789673018219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17418771330249052897357625 13064078497686789673018219)
        ·
          refine ⟨19596117746530184509527329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13064078497686789673018219 19596117746530184509527329)
          ·
            refine ⟨14697088309897638382145497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19596117746530184509527329 14697088309897638382145497)
            ·
              refine ⟨11022816232423228786609123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14697088309897638382145497 11022816232423228786609123)
              ·
                refine ⟨16534224348634843179913685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11022816232423228786609123 16534224348634843179913685)
                ·
                  refine ⟨387520883171129137029227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16534224348634843179913685 387520883171129137029227)
                  ·
                    rfl

theorem cell21_1698062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1698062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698062 prefixEnd_1698062 := by exact prefixLift 1698062
  have htrace : WordTrace (prefixWord ++ tailWord_1698062) baseStart_1698062 baseEnd_1698062 := by
    simpa [prefixWord, tailWord_1698062, baseEnd_1698062] using wordTrace_append hprefix tailTrace_1698062
  have hstable : (prefixWord ++ tailWord_1698062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698062).length < 2 ^ (prefixWord ++ tailWord_1698062).sum := by decide
  have hdescent : baseEnd_1698062 < baseStart_1698062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698110 : List Nat := [4, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1698110 : Nat := 118140960795 + 1698110 * 2 ^ 59
def prefixEnd_1698110 : Nat := 4983230072969 + 3 ^ 40 * 1698110 * 2
def baseEnd_1698110 : Nat := 387531837425091720229129

theorem tailTrace_1698110 : CollatzResearch.WordTrace tailWord_1698110 prefixEnd_1698110 387531837425091720229129 := by
  unfold tailWord_1698110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7741894984755619867988473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41290106585363305962605189 7741894984755619867988473)
  ·
    refine ⟨5806421238566714900991355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7741894984755619867988473 5806421238566714900991355)
    ·
      refine ⟨8709631857850072351487033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5806421238566714900991355 8709631857850072351487033)
      ·
        refine ⟨6532223893387554263615275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8709631857850072351487033 6532223893387554263615275)
        ·
          refine ⟨9798335840081331395422913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532223893387554263615275 9798335840081331395422913)
          ·
            refine ⟨7348751880060998546567185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9798335840081331395422913 7348751880060998546567185)
            ·
              refine ⟨5511563910045748909925389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7348751880060998546567185 5511563910045748909925389)
              ·
                refine ⟨2066836466267155841222021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5511563910045748909925389 2066836466267155841222021)
                ·
                  refine ⟨387531837425091720229129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2066836466267155841222021 387531837425091720229129)
                  ·
                    rfl

theorem cell21_1698110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1698110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698110 prefixEnd_1698110 := by exact prefixLift 1698110
  have htrace : WordTrace (prefixWord ++ tailWord_1698110) baseStart_1698110 baseEnd_1698110 := by
    simpa [prefixWord, tailWord_1698110, baseEnd_1698110] using wordTrace_append hprefix tailTrace_1698110
  have hstable : (prefixWord ++ tailWord_1698110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698110).length < 2 ^ (prefixWord ++ tailWord_1698110).sum := by decide
  have hdescent : baseEnd_1698110 < baseStart_1698110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698124 : List Nat := [2, 2, 1, 3, 2, 1, 5, 5]
def baseStart_1698124 : Nat := 118140960795 + 1698124 * 2 ^ 59
def prefixEnd_1698124 : Nat := 4983230072969 + 3 ^ 40 * 1698124 * 2
def baseEnd_1698124 : Nat := 129178344138610268998589

theorem tailTrace_1698124 : CollatzResearch.WordTrace tailWord_1698124 prefixEnd_1698124 129178344138610268998589 := by
  unfold tailWord_1698124
  simp only [CollatzResearch.WordTrace]
  refine ⟨30967835249997119667458713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41290446999996159556611617 30967835249997119667458713)
  ·
    refine ⟨23225876437497839750594035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30967835249997119667458713 23225876437497839750594035)
    ·
      refine ⟨34838814656246759625891053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23225876437497839750594035 34838814656246759625891053)
      ·
        refine ⟨13064555496092534859709145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34838814656246759625891053 13064555496092534859709145)
        ·
          refine ⟨9798416622069401144781859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13064555496092534859709145 9798416622069401144781859)
          ·
            refine ⟨14697624933104101717172789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9798416622069401144781859 14697624933104101717172789)
            ·
              refine ⟨1377902337478509535984949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14697624933104101717172789 1377902337478509535984949)
              ·
                refine ⟨129178344138610268998589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1377902337478509535984949 129178344138610268998589)
                ·
                  rfl

theorem cell21_1698124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_1698124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698124 prefixEnd_1698124 := by exact prefixLift 1698124
  have htrace : WordTrace (prefixWord ++ tailWord_1698124) baseStart_1698124 baseEnd_1698124 := by
    simpa [prefixWord, tailWord_1698124, baseEnd_1698124] using wordTrace_append hprefix tailTrace_1698124
  have hstable : (prefixWord ++ tailWord_1698124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698124).length < 2 ^ (prefixWord ++ tailWord_1698124).sum := by decide
  have hdescent : baseEnd_1698124 < baseStart_1698124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698183 : List Nat := [1, 1, 4, 2, 2, 1, 3, 7]
def baseStart_1698183 : Nat := 118140960795 + 1698183 * 2 ^ 59
def prefixEnd_1698183 : Nat := 4983230072969 + 3 ^ 40 * 1698183 * 2
def baseEnd_1698183 : Nat := 129182832339886605170771

theorem tailTrace_1698183 : CollatzResearch.WordTrace tailWord_1698183 prefixEnd_1698183 129182832339886605170771 := by
  unfold tailWord_1698183
  simp only [CollatzResearch.WordTrace]
  refine ⟨61937822406780492411315203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41291881604520328274210135 61937822406780492411315203)
  ·
    refine ⟨92906733610170738616972805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61937822406780492411315203 92906733610170738616972805)
    ·
      refine ⟨17420012551907013490682401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92906733610170738616972805 17420012551907013490682401)
      ·
        refine ⟨13065009413930260118011801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17420012551907013490682401 13065009413930260118011801)
        ·
          refine ⟨9798757060447695088508851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13065009413930260118011801 9798757060447695088508851)
          ·
            refine ⟨14698135590671542632763277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9798757060447695088508851 14698135590671542632763277)
            ·
              refine ⟨5511800846501828487286229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14698135590671542632763277 5511800846501828487286229)
              ·
                refine ⟨129182832339886605170771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5511800846501828487286229 129182832339886605170771)
                ·
                  rfl

theorem cell21_1698183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_1698183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698183 prefixEnd_1698183 := by exact prefixLift 1698183
  have htrace : WordTrace (prefixWord ++ tailWord_1698183) baseStart_1698183 baseEnd_1698183 := by
    simpa [prefixWord, tailWord_1698183, baseEnd_1698183] using wordTrace_append hprefix tailTrace_1698183
  have hstable : (prefixWord ++ tailWord_1698183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698183).length < 2 ^ (prefixWord ++ tailWord_1698183).sum := by decide
  have hdescent : baseEnd_1698183 < baseStart_1698183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698200 : List Nat := [2, 1, 2, 5, 1, 3, 7]
def baseStart_1698200 : Nat := 118140960795 + 1698200 * 2 ^ 59
def prefixEnd_1698200 : Nat := 4983230072969 + 3 ^ 40 * 1698200 * 2
def baseEnd_1698200 : Nat := 43061375183474618192105

theorem tailTrace_1698200 : CollatzResearch.WordTrace tailWord_1698200 prefixEnd_1698200 43061375183474618192105 := by
  unfold tailWord_1698200
  simp only [CollatzResearch.WordTrace]
  refine ⟨30969221223859452157342027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41292294965145936209789369 30969221223859452157342027)
  ·
    refine ⟨46453831835789178236013041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30969221223859452157342027 46453831835789178236013041)
    ·
      refine ⟨34840373876841883677009781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46453831835789178236013041 34840373876841883677009781)
      ·
        refine ⟨3266285050953926594719667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34840373876841883677009781 3266285050953926594719667)
        ·
          refine ⟨4899427576430889892079501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266285050953926594719667 4899427576430889892079501)
          ·
            refine ⟨1837285341161583709529813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4899427576430889892079501 1837285341161583709529813)
            ·
              refine ⟨43061375183474618192105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1837285341161583709529813 43061375183474618192105)
              ·
                rfl

theorem cell21_1698200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 7].length) (baseStart_1698200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698200 prefixEnd_1698200 := by exact prefixLift 1698200
  have htrace : WordTrace (prefixWord ++ tailWord_1698200) baseStart_1698200 baseEnd_1698200 := by
    simpa [prefixWord, tailWord_1698200, baseEnd_1698200] using wordTrace_append hprefix tailTrace_1698200
  have hstable : (prefixWord ++ tailWord_1698200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698200).length < 2 ^ (prefixWord ++ tailWord_1698200).sum := by decide
  have hdescent : baseEnd_1698200 < baseStart_1698200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698206 : List Nat := [4, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1698206 : Nat := 118140960795 + 1698206 * 2 ^ 59
def prefixEnd_1698206 : Nat := 4983230072969 + 3 ^ 40 * 1698206 * 2
def baseEnd_1698206 : Nat := 387553745933016886628933

theorem tailTrace_1698206 : CollatzResearch.WordTrace tailWord_1698206 prefixEnd_1698206 387553745933016886628933 := by
  unfold tailWord_1698206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7742332660712145917425309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41292440857131444892934981 7742332660712145917425309)
  ·
    refine ⟨2903374747767054719034491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7742332660712145917425309 2903374747767054719034491)
    ·
      refine ⟨4355062121650582078551737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903374747767054719034491 4355062121650582078551737)
      ·
        refine ⟨3266296591237936558913803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4355062121650582078551737 3266296591237936558913803)
        ·
          refine ⟨4899444886856904838370705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266296591237936558913803 4899444886856904838370705)
          ·
            refine ⟨3674583665142678628778029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899444886856904838370705 3674583665142678628778029)
            ·
              refine ⟨1377968874428504485791761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3674583665142678628778029 1377968874428504485791761)
              ·
                refine ⟨1033476655821378364343821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377968874428504485791761 1033476655821378364343821)
                ·
                  refine ⟨387553745933016886628933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033476655821378364343821 387553745933016886628933)
                  ·
                    rfl

theorem cell21_1698206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1698206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698206 prefixEnd_1698206 := by exact prefixLift 1698206
  have htrace : WordTrace (prefixWord ++ tailWord_1698206) baseStart_1698206 baseEnd_1698206 := by
    simpa [prefixWord, tailWord_1698206, baseEnd_1698206] using wordTrace_append hprefix tailTrace_1698206
  have hstable : (prefixWord ++ tailWord_1698206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698206).length < 2 ^ (prefixWord ++ tailWord_1698206).sum := by decide
  have hdescent : baseEnd_1698206 < baseStart_1698206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698307 : List Nat := [1, 1, 1, 3, 2, 1, 6, 3, 3]
def baseStart_1698307 : Nat := 118140960795 + 1698307 * 2 ^ 59
def prefixEnd_1698307 : Nat := 4983230072969 + 3 ^ 40 * 1698307 * 2
def baseEnd_1698307 : Nat := 387576795509063155445393

theorem tailTrace_1698307 : CollatzResearch.WordTrace tailWord_1698307 prefixEnd_1698307 387576795509063155445393 := by
  unfold tailWord_1698307
  simp only [CollatzResearch.WordTrace]
  refine ⟨61942345058331261588829175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41294896705554174392552783 61942345058331261588829175)
  ·
    refine ⟨92913517587496892383243763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61942345058331261588829175 92913517587496892383243763)
    ·
      refine ⟨139370276381245338574865645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92913517587496892383243763 139370276381245338574865645)
      ·
        refine ⟨52263853642967001965574617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139370276381245338574865645 52263853642967001965574617)
        ·
          refine ⟨39197890232225251474180963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52263853642967001965574617 39197890232225251474180963)
          ·
            refine ⟨58796835348337877211271445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39197890232225251474180963 58796835348337877211271445)
            ·
              refine ⟨2756101656953337994278349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58796835348337877211271445 2756101656953337994278349)
              ·
                refine ⟨1033538121357501747854381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2756101656953337994278349 1033538121357501747854381)
                ·
                  refine ⟨387576795509063155445393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033538121357501747854381 387576795509063155445393)
                  ·
                    rfl

theorem cell21_1698307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 3].length) (baseStart_1698307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698307 prefixEnd_1698307 := by exact prefixLift 1698307
  have htrace : WordTrace (prefixWord ++ tailWord_1698307) baseStart_1698307 baseEnd_1698307 := by
    simpa [prefixWord, tailWord_1698307, baseEnd_1698307] using wordTrace_append hprefix tailTrace_1698307
  have hstable : (prefixWord ++ tailWord_1698307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698307).length < 2 ^ (prefixWord ++ tailWord_1698307).sum := by decide
  have hdescent : baseEnd_1698307 < baseStart_1698307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698310 : List Nat := [6, 2, 1, 1, 1, 2, 8]
def baseStart_1698310 : Nat := 118140960795 + 1698310 * 2 ^ 59
def prefixEnd_1698310 : Nat := 4983230072969 + 3 ^ 40 * 1698310 * 2
def baseEnd_1698310 : Nat := 43064164461103979655043

theorem tailTrace_1698310 : CollatzResearch.WordTrace tailWord_1698310 prefixEnd_1698310 43064164461103979655043 := by
  unfold tailWord_1698310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935701702416262284412137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41294969651546928734125589 1935701702416262284412137)
  ·
    refine ⟨1451776276812196713309103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1935701702416262284412137 1451776276812196713309103)
    ·
      refine ⟨2177664415218295069963655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451776276812196713309103 2177664415218295069963655)
      ·
        refine ⟨3266496622827442604945483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177664415218295069963655 3266496622827442604945483)
        ·
          refine ⟨4899744934241163907418225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266496622827442604945483 4899744934241163907418225)
          ·
            refine ⟨3674808700680872930563669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899744934241163907418225 3674808700680872930563669)
            ·
              refine ⟨43064164461103979655043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3674808700680872930563669 43064164461103979655043)
              ·
                rfl

theorem cell21_1698310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 8].length) (baseStart_1698310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698310 prefixEnd_1698310 := by exact prefixLift 1698310
  have htrace : WordTrace (prefixWord ++ tailWord_1698310) baseStart_1698310 baseEnd_1698310 := by
    simpa [prefixWord, tailWord_1698310, baseEnd_1698310] using wordTrace_append hprefix tailTrace_1698310
  have hstable : (prefixWord ++ tailWord_1698310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698310).length < 2 ^ (prefixWord ++ tailWord_1698310).sum := by decide
  have hdescent : baseEnd_1698310 < baseStart_1698310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698324 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1698324 : Nat := 118140960795 + 1698324 * 2 ^ 59
def prefixEnd_1698324 : Nat := 4983230072969 + 3 ^ 40 * 1698324 * 2
def baseEnd_1698324 : Nat := 387580675140674903662025

theorem tailTrace_1698324 : CollatzResearch.WordTrace tailWord_1698324 prefixEnd_1698324 387580675140674903662025 := by
  unfold tailWord_1698324
  simp only [CollatzResearch.WordTrace]
  refine ⟨30971482549634836746099013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41295310066179782328132017 30971482549634836746099013)
  ·
    refine ⟨5807152978056531889893565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30971482549634836746099013 5807152978056531889893565)
    ·
      refine ⟨2177682366771199458710087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5807152978056531889893565 2177682366771199458710087)
      ·
        refine ⟨3266523550156799188065131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177682366771199458710087 3266523550156799188065131)
        ·
          refine ⟨4899785325235198782097697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3266523550156799188065131 4899785325235198782097697)
          ·
            refine ⟨3674838993926399086573273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4899785325235198782097697 3674838993926399086573273)
            ·
              refine ⟨2756129245444799314929955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3674838993926399086573273 2756129245444799314929955)
              ·
                refine ⟨4134193868167198972394933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2756129245444799314929955 4134193868167198972394933)
                ·
                  refine ⟨387580675140674903662025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4134193868167198972394933 387580675140674903662025)
                  ·
                    rfl

theorem cell21_1698324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1698324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698324 prefixEnd_1698324 := by exact prefixLift 1698324
  have htrace : WordTrace (prefixWord ++ tailWord_1698324) baseStart_1698324 baseEnd_1698324 := by
    simpa [prefixWord, tailWord_1698324, baseEnd_1698324] using wordTrace_append hprefix tailTrace_1698324
  have hstable : (prefixWord ++ tailWord_1698324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698324).length < 2 ^ (prefixWord ++ tailWord_1698324).sum := by decide
  have hdescent : baseEnd_1698324 < baseStart_1698324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698380 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1698380 : Nat := 118140960795 + 1698380 * 2 ^ 59
def prefixEnd_1698380 : Nat := 4983230072969 + 3 ^ 40 * 1698380 * 2
def baseEnd_1698380 : Nat := 387593455103631250728577

theorem tailTrace_1698380 : CollatzResearch.WordTrace tailWord_1698380 prefixEnd_1698380 387593455103631250728577 := by
  unfold tailWord_1698380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30972503793533397528118297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41296671724711196704157729 30972503793533397528118297)
  ·
    refine ⟨23229377845150048146088723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30972503793533397528118297 23229377845150048146088723)
    ·
      refine ⟨34844066767725072219133085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23229377845150048146088723 34844066767725072219133085)
      ·
        refine ⟨13066525037896902082174907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34844066767725072219133085 13066525037896902082174907)
        ·
          refine ⟨19599787556845353123262361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13066525037896902082174907 19599787556845353123262361)
          ·
            refine ⟨14699840667634014842446771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19599787556845353123262361 14699840667634014842446771)
            ·
              refine ⟨22049761001451022263670157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14699840667634014842446771 22049761001451022263670157)
              ·
                refine ⟨8268660375544133348876309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22049761001451022263670157 8268660375544133348876309)
                ·
                  refine ⟨387593455103631250728577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8268660375544133348876309 387593455103631250728577)
                  ·
                    rfl

theorem cell21_1698380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1698380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698380 prefixEnd_1698380 := by exact prefixLift 1698380
  have htrace : WordTrace (prefixWord ++ tailWord_1698380) baseStart_1698380 baseEnd_1698380 := by
    simpa [prefixWord, tailWord_1698380, baseEnd_1698380] using wordTrace_append hprefix tailTrace_1698380
  have hstable : (prefixWord ++ tailWord_1698380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698380).length < 2 ^ (prefixWord ++ tailWord_1698380).sum := by decide
  have hdescent : baseEnd_1698380 < baseStart_1698380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698487 : List Nat := [1, 1, 3, 1, 6, 1, 8]
def baseStart_1698487 : Nat := 118140960795 + 1698487 * 2 ^ 59
def prefixEnd_1698487 : Nat := 4983230072969 + 3 ^ 40 * 1698487 * 2
def baseEnd_1698487 : Nat := 43068652662380315827225

theorem tailTrace_1698487 : CollatzResearch.WordTrace tailWord_1698487 prefixEnd_1698487 43068652662380315827225 := by
  unfold tailWord_1698487
  simp only [CollatzResearch.WordTrace]
  refine ⟨61948910197679152330381715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41299273465119434886921143 61948910197679152330381715)
  ·
    refine ⟨92923365296518728495572573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61948910197679152330381715 92923365296518728495572573)
    ·
      refine ⟨34846261986194523185839715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92923365296518728495572573 34846261986194523185839715)
      ·
        refine ⟨52269392979291784778759573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34846261986194523185839715 52269392979291784778759573)
        ·
          refine ⟨2450127795904302411504355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52269392979291784778759573 2450127795904302411504355)
          ·
            refine ⟨3675191693856453617256533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450127795904302411504355 3675191693856453617256533)
            ·
              refine ⟨43068652662380315827225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3675191693856453617256533 43068652662380315827225)
              ·
                rfl

theorem cell21_1698487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 8].length) (baseStart_1698487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698487 prefixEnd_1698487 := by exact prefixLift 1698487
  have htrace : WordTrace (prefixWord ++ tailWord_1698487) baseStart_1698487 baseEnd_1698487 := by
    simpa [prefixWord, tailWord_1698487, baseEnd_1698487] using wordTrace_append hprefix tailTrace_1698487
  have hstable : (prefixWord ++ tailWord_1698487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698487).length < 2 ^ (prefixWord ++ tailWord_1698487).sum := by decide
  have hdescent : baseEnd_1698487 < baseStart_1698487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698532 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1698532 : Nat := 118140960795 + 1698532 * 2 ^ 59
def prefixEnd_1698532 : Nat := 4983230072969 + 3 ^ 40 * 1698532 * 2
def baseEnd_1698532 : Nat := 387628143574512764194933

theorem tailTrace_1698532 : CollatzResearch.WordTrace tailWord_1698532 prefixEnd_1698532 387628143574512764194933 := by
  unfold tailWord_1698532
  simp only [CollatzResearch.WordTrace]
  refine ⟨30975275741258062507884925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41300367655010750010513233 30975275741258062507884925)
  ·
    refine ⟨11615728402971773440456847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30975275741258062507884925 11615728402971773440456847)
    ·
      refine ⟨17423592604457660160685271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11615728402971773440456847 17423592604457660160685271)
      ·
        refine ⟨26135388906686490241027907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17423592604457660160685271 26135388906686490241027907)
        ·
          refine ⟨39203083360029735361541861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26135388906686490241027907 39203083360029735361541861)
          ·
            refine ⟨7350578130005575380289099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39203083360029735361541861 7350578130005575380289099)
            ·
              refine ⟨11025867195008363070433649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7350578130005575380289099 11025867195008363070433649)
              ·
                refine ⟨8269400396256272302825237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11025867195008363070433649 8269400396256272302825237)
                ·
                  refine ⟨387628143574512764194933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8269400396256272302825237 387628143574512764194933)
                  ·
                    rfl

theorem cell21_1698532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1698532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698532 prefixEnd_1698532 := by exact prefixLift 1698532
  have htrace : WordTrace (prefixWord ++ tailWord_1698532) baseStart_1698532 baseEnd_1698532 := by
    simpa [prefixWord, tailWord_1698532, baseEnd_1698532] using wordTrace_append hprefix tailTrace_1698532
  have hstable : (prefixWord ++ tailWord_1698532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698532).length < 2 ^ (prefixWord ++ tailWord_1698532).sum := by decide
  have hdescent : baseEnd_1698532 < baseStart_1698532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698577 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 5]
def baseStart_1698577 : Nat := 118140960795 + 1698577 * 2 ^ 59
def prefixEnd_1698577 : Nat := 4983230072969 + 3 ^ 40 * 1698577 * 2
def baseEnd_1698577 : Nat := 387638413187602685944841

theorem tailTrace_1698577 : CollatzResearch.WordTrace tailWord_1698577 prefixEnd_1698577 387638413187602685944841 := by
  unfold tailWord_1698577
  simp only [CollatzResearch.WordTrace]
  refine ⟨61952192767353097701157985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41301461844902065134105323 61952192767353097701157985)
  ·
    refine ⟨46464144575514823275868489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61952192767353097701157985 46464144575514823275868489)
    ·
      refine ⟨34848108431636117456901367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46464144575514823275868489 34848108431636117456901367)
      ·
        refine ⟨52272162647454176185352051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34848108431636117456901367 52272162647454176185352051)
        ·
          refine ⟨78408243971181264278028077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52272162647454176185352051 78408243971181264278028077)
          ·
            refine ⟨29403091489192974104260529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78408243971181264278028077 29403091489192974104260529)
            ·
              refine ⟨22052318616894730578195397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29403091489192974104260529 22052318616894730578195397)
              ·
                refine ⟨4134809740667761983411637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22052318616894730578195397 4134809740667761983411637)
                ·
                  refine ⟨387638413187602685944841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4134809740667761983411637 387638413187602685944841)
                  ·
                    rfl

theorem cell21_1698577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_1698577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698577 prefixEnd_1698577 := by exact prefixLift 1698577
  have htrace : WordTrace (prefixWord ++ tailWord_1698577) baseStart_1698577 baseEnd_1698577 := by
    simpa [prefixWord, tailWord_1698577, baseEnd_1698577] using wordTrace_append hprefix tailTrace_1698577
  have hstable : (prefixWord ++ tailWord_1698577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698577).length < 2 ^ (prefixWord ++ tailWord_1698577).sum := by decide
  have hdescent : baseEnd_1698577 < baseStart_1698577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698611 : List Nat := [1, 1, 1, 2, 6, 2, 1, 4, 3]
def baseStart_1698611 : Nat := 118140960795 + 1698611 * 2 ^ 59
def prefixEnd_1698611 : Nat := 4983230072969 + 3 ^ 40 * 1698611 * 2
def baseEnd_1698611 : Nat := 387646172450826182378105

theorem tailTrace_1698611 : CollatzResearch.WordTrace tailWord_1698611 prefixEnd_1698611 387646172450826182378105 := by
  unfold tailWord_1698611
  simp only [CollatzResearch.WordTrace]
  refine ⟨61953432849229921507895687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41302288566153281005263791 61953432849229921507895687)
  ·
    refine ⟨92930149273844882261843531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61953432849229921507895687 92930149273844882261843531)
    ·
      refine ⟨139395223910767323392765297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92930149273844882261843531 139395223910767323392765297)
      ·
        refine ⟨104546417933075492544573973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139395223910767323392765297 104546417933075492544573973)
        ·
          refine ⟨4900613340612913713026905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104546417933075492544573973 4900613340612913713026905)
          ·
            refine ⟨3675460005459685284770179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4900613340612913713026905 3675460005459685284770179)
            ·
              refine ⟨5513190008189527927155269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675460005459685284770179 5513190008189527927155269)
              ·
                refine ⟨1033723126535536486341613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5513190008189527927155269 1033723126535536486341613)
                ·
                  refine ⟨387646172450826182378105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033723126535536486341613 387646172450826182378105)
                  ·
                    rfl

theorem cell21_1698611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 3].length) (baseStart_1698611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698611 prefixEnd_1698611 := by exact prefixLift 1698611
  have htrace : WordTrace (prefixWord ++ tailWord_1698611) baseStart_1698611 baseEnd_1698611 := by
    simpa [prefixWord, tailWord_1698611, baseEnd_1698611] using wordTrace_append hprefix tailTrace_1698611
  have hstable : (prefixWord ++ tailWord_1698611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698611).length < 2 ^ (prefixWord ++ tailWord_1698611).sum := by decide
  have hdescent : baseEnd_1698611 < baseStart_1698611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698614 : List Nat := [5, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1698614 : Nat := 118140960795 + 1698614 * 2 ^ 59
def prefixEnd_1698614 : Nat := 4983230072969 + 3 ^ 40 * 1698614 * 2
def baseEnd_1698614 : Nat := 129215619030566281276033

theorem tailTrace_1698614 : CollatzResearch.WordTrace tailWord_1698614 prefixEnd_1698614 129215619030566281276033 := by
  unfold tailWord_1698614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872096391763690813765931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41302361512146035346836597 3872096391763690813765931)
  ·
    refine ⟨5808144587645536220648897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872096391763690813765931 5808144587645536220648897)
    ·
      refine ⟨4356108440734152165486673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5808144587645536220648897 4356108440734152165486673)
      ·
        refine ⟨3267081330550614124115005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4356108440734152165486673 3267081330550614124115005)
        ·
          refine ⟨1225155498956480296543127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3267081330550614124115005 1225155498956480296543127)
          ·
            refine ⟨1837733248434720444814691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225155498956480296543127 1837733248434720444814691)
            ·
              refine ⟨2756599872652080667222037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1837733248434720444814691 2756599872652080667222037)
              ·
                refine ⟨129215619030566281276033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2756599872652080667222037 129215619030566281276033)
                ·
                  rfl

theorem cell21_1698614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1698614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698614 prefixEnd_1698614 := by exact prefixLift 1698614
  have htrace : WordTrace (prefixWord ++ tailWord_1698614) baseStart_1698614 baseEnd_1698614 := by
    simpa [prefixWord, tailWord_1698614, baseEnd_1698614] using wordTrace_append hprefix tailTrace_1698614
  have hstable : (prefixWord ++ tailWord_1698614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698614).length < 2 ^ (prefixWord ++ tailWord_1698614).sum := by decide
  have hdescent : baseEnd_1698614 < baseStart_1698614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698628 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_1698628 : Nat := 118140960795 + 1698628 * 2 ^ 59
def prefixEnd_1698628 : Nat := 4983230072969 + 3 ^ 40 * 1698628 * 2
def baseEnd_1698628 : Nat := 387650052082437930594737

theorem tailTrace_1698628 : CollatzResearch.WordTrace tailWord_1698628 prefixEnd_1698628 387650052082437930594737 := by
  unfold tailWord_1698628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30977026445084166705632269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41302701926778888940843025 30977026445084166705632269)
  ·
    refine ⟨11616384916906562514612101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30977026445084166705632269 11616384916906562514612101)
    ·
      refine ⟨2178072171919980471489769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11616384916906562514612101 2178072171919980471489769)
      ·
        refine ⟨1633554128939985353617327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2178072171919980471489769 1633554128939985353617327)
        ·
          refine ⟨2450331193409978030425991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633554128939985353617327 2450331193409978030425991)
          ·
            refine ⟨3675496790114967045638987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450331193409978030425991 3675496790114967045638987)
            ·
              refine ⟨5513245185172450568458481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3675496790114967045638987 5513245185172450568458481)
              ·
                refine ⟨4134933888879337926343861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5513245185172450568458481 4134933888879337926343861)
                ·
                  refine ⟨387650052082437930594737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4134933888879337926343861 387650052082437930594737)
                  ·
                    rfl

theorem cell21_1698628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_1698628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698628 prefixEnd_1698628 := by exact prefixLift 1698628
  have htrace : WordTrace (prefixWord ++ tailWord_1698628) baseStart_1698628 baseEnd_1698628 := by
    simpa [prefixWord, tailWord_1698628, baseEnd_1698628] using wordTrace_append hprefix tailTrace_1698628
  have hstable : (prefixWord ++ tailWord_1698628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698628).length < 2 ^ (prefixWord ++ tailWord_1698628).sum := by decide
  have hdescent : baseEnd_1698628 < baseStart_1698628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698684 : List Nat := [2, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_1698684 : Nat := 118140960795 + 1698684 * 2 ^ 59
def prefixEnd_1698684 : Nat := 4983230072969 + 3 ^ 40 * 1698684 * 2
def baseEnd_1698684 : Nat := 387662832045394277661289

theorem tailTrace_1698684 : CollatzResearch.WordTrace tailWord_1698684 prefixEnd_1698684 387662832045394277661289 := by
  unfold tailWord_1698684
  simp only [CollatzResearch.WordTrace]
  refine ⟨30978047688982727487651553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41304063585310303316868737 30978047688982727487651553)
  ·
    refine ⟨23233535766737045615738665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30978047688982727487651553 23233535766737045615738665)
    ·
      refine ⟨17425151825052784211803999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23233535766737045615738665 17425151825052784211803999)
      ·
        refine ⟨26137727737579176317705999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17425151825052784211803999 26137727737579176317705999)
        ·
          refine ⟨39206591606368764476558999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26137727737579176317705999 39206591606368764476558999)
          ·
            refine ⟨58809887409553146714838499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39206591606368764476558999 58809887409553146714838499)
            ·
              refine ⟨88214831114329720072257749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58809887409553146714838499 88214831114329720072257749)
              ·
                refine ⟨2067535104242102814193541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88214831114329720072257749 2067535104242102814193541)
                ·
                  refine ⟨387662832045394277661289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067535104242102814193541 387662832045394277661289)
                  ·
                    rfl

theorem cell21_1698684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1698684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698684 prefixEnd_1698684 := by exact prefixLift 1698684
  have htrace : WordTrace (prefixWord ++ tailWord_1698684) baseStart_1698684 baseEnd_1698684 := by
    simpa [prefixWord, tailWord_1698684, baseEnd_1698684] using wordTrace_append hprefix tailTrace_1698684
  have hstable : (prefixWord ++ tailWord_1698684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698684).length < 2 ^ (prefixWord ++ tailWord_1698684).sum := by decide
  have hdescent : baseEnd_1698684 < baseStart_1698684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698777 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 4]
def baseStart_1698777 : Nat := 118140960795 + 1698777 * 2 ^ 59
def prefixEnd_1698777 : Nat := 4983230072969 + 3 ^ 40 * 1698777 * 2
def baseEnd_1698777 : Nat := 387684055912446782611099

theorem tailTrace_1698777 : CollatzResearch.WordTrace tailWord_1698777 prefixEnd_1698777 387684055912446782611099 := by
  unfold tailWord_1698777
  simp only [CollatzResearch.WordTrace]
  refine ⟨61959487366628531858438585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41306324911085687905625723 61959487366628531858438585)
  ·
    refine ⟨46469615524971398893828939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61959487366628531858438585 46469615524971398893828939)
    ·
      refine ⟨69704423287457098340743409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46469615524971398893828939 69704423287457098340743409)
      ·
        refine ⟨52278317465592823755557557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69704423287457098340743409 52278317465592823755557557)
        ·
          refine ⟨4901092262399327227083521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52278317465592823755557557 4901092262399327227083521)
          ·
            refine ⟨3675819196799495420312641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4901092262399327227083521 3675819196799495420312641)
            ·
              refine ⟨2756864397599621565234481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3675819196799495420312641 2756864397599621565234481)
              ·
                refine ⟨2067648298199716173925861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2756864397599621565234481 2067648298199716173925861)
                ·
                  refine ⟨387684055912446782611099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067648298199716173925861 387684055912446782611099)
                  ·
                    rfl

theorem cell21_1698777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_1698777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698777 prefixEnd_1698777 := by exact prefixLift 1698777
  have htrace : WordTrace (prefixWord ++ tailWord_1698777) baseStart_1698777 baseEnd_1698777 := by
    simpa [prefixWord, tailWord_1698777, baseEnd_1698777] using wordTrace_append hprefix tailTrace_1698777
  have hstable : (prefixWord ++ tailWord_1698777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698777).length < 2 ^ (prefixWord ++ tailWord_1698777).sum := by decide
  have hdescent : baseEnd_1698777 < baseStart_1698777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698791 : List Nat := [1, 1, 5, 2, 2, 1, 3, 6]
def baseStart_1698791 : Nat := 118140960795 + 1698791 * 2 ^ 59
def prefixEnd_1698791 : Nat := 4983230072969 + 3 ^ 40 * 1698791 * 2
def baseEnd_1698791 : Nat := 129229083634395289792579

theorem tailTrace_1698791 : CollatzResearch.WordTrace tailWord_1698791 prefixEnd_1698791 129229083634395289792579 := by
  unfold tailWord_1698791
  simp only [CollatzResearch.WordTrace]
  refine ⟨61959997988577812249448227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41306665325718541499632151 61959997988577812249448227)
  ·
    refine ⟨92939996982866718374172341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61959997988577812249448227 92939996982866718374172341)
    ·
      refine ⟨8713124717143754847578657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92939996982866718374172341 8713124717143754847578657)
      ·
        refine ⟨6534843537857816135683993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8713124717143754847578657 6534843537857816135683993)
        ·
          refine ⟨4901132653393362101762995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6534843537857816135683993 4901132653393362101762995)
          ·
            refine ⟨7351698980090043152644493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901132653393362101762995 7351698980090043152644493)
            ·
              refine ⟨2756887117533766182241685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7351698980090043152644493 2756887117533766182241685)
              ·
                refine ⟨129229083634395289792579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2756887117533766182241685 129229083634395289792579)
                ·
                  rfl

theorem cell21_1698791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 6].length) (baseStart_1698791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698791 prefixEnd_1698791 := by exact prefixLift 1698791
  have htrace : WordTrace (prefixWord ++ tailWord_1698791) baseStart_1698791 baseEnd_1698791 := by
    simpa [prefixWord, tailWord_1698791, baseEnd_1698791] using wordTrace_append hprefix tailTrace_1698791
  have hstable : (prefixWord ++ tailWord_1698791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698791).length < 2 ^ (prefixWord ++ tailWord_1698791).sum := by decide
  have hdescent : baseEnd_1698791 < baseStart_1698791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698839 : List Nat := [1, 1, 3, 5, 1, 1, 2, 4, 3]
def baseStart_1698839 : Nat := 118140960795 + 1698839 * 2 ^ 59
def prefixEnd_1698839 : Nat := 4983230072969 + 3 ^ 40 * 1698839 * 2
def baseEnd_1698839 : Nat := 387698205157148452577639

theorem tailTrace_1698839 : CollatzResearch.WordTrace tailWord_1698839 prefixEnd_1698839 387698205157148452577639 := by
  unfold tailWord_1698839
  simp only [CollatzResearch.WordTrace]
  refine ⟨61961748692403916447195571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41307832461602610964797047 61961748692403916447195571)
  ·
    refine ⟨92942623038605874670793357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61961748692403916447195571 92942623038605874670793357)
    ·
      refine ⟨34853483639477203001547509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92942623038605874670793357 34853483639477203001547509)
      ·
        refine ⟨3267514091200987781395079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34853483639477203001547509 3267514091200987781395079)
        ·
          refine ⟨4901271136801481672092619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3267514091200987781395079 4901271136801481672092619)
          ·
            refine ⟨7351906705202222508138929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901271136801481672092619 7351906705202222508138929)
            ·
              refine ⟨5513930028901666881104197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7351906705202222508138929 5513930028901666881104197)
              ·
                refine ⟨1033861880419062540207037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5513930028901666881104197 1033861880419062540207037)
                ·
                  refine ⟨387698205157148452577639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033861880419062540207037 387698205157148452577639)
                  ·
                    rfl

theorem cell21_1698839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 3].length) (baseStart_1698839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698839 prefixEnd_1698839 := by exact prefixLift 1698839
  have htrace : WordTrace (prefixWord ++ tailWord_1698839) baseStart_1698839 baseEnd_1698839 := by
    simpa [prefixWord, tailWord_1698839, baseEnd_1698839] using wordTrace_append hprefix tailTrace_1698839
  have hstable : (prefixWord ++ tailWord_1698839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698839).length < 2 ^ (prefixWord ++ tailWord_1698839).sum := by decide
  have hdescent : baseEnd_1698839 < baseStart_1698839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698853 : List Nat := [1, 3, 1, 2, 2, 2, 5, 1, 4]
def baseStart_1698853 : Nat := 118140960795 + 1698853 * 2 ^ 59
def prefixEnd_1698853 : Nat := 4983230072969 + 3 ^ 40 * 1698853 * 2
def baseEnd_1698853 : Nat := 387701400147887539344277

theorem tailTrace_1698853 : CollatzResearch.WordTrace tailWord_1698853 prefixEnd_1698853 387701400147887539344277 := by
  unfold tailWord_1698853
  simp only [CollatzResearch.WordTrace]
  refine ⟨61962259314353196838205213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41308172876235464558803475 61962259314353196838205213)
  ·
    refine ⟨23235847242882448814326955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61962259314353196838205213 23235847242882448814326955)
    ·
      refine ⟨34853770864323673221490433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23235847242882448814326955 34853770864323673221490433)
      ·
        refine ⟨26140328148242754916117825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34853770864323673221490433 26140328148242754916117825)
        ·
          refine ⟨19605246111182066187088369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26140328148242754916117825 19605246111182066187088369)
          ·
            refine ⟨14703934583386549640316277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19605246111182066187088369 14703934583386549640316277)
            ·
              refine ⟨1378493867192489028779651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14703934583386549640316277 1378493867192489028779651)
              ·
                refine ⟨2067740800788733543169477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378493867192489028779651 2067740800788733543169477)
                ·
                  refine ⟨387701400147887539344277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067740800788733543169477 387701400147887539344277)
                  ·
                    rfl

theorem cell21_1698853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_1698853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698853 prefixEnd_1698853 := by exact prefixLift 1698853
  have htrace : WordTrace (prefixWord ++ tailWord_1698853) baseStart_1698853 baseEnd_1698853 := by
    simpa [prefixWord, tailWord_1698853, baseEnd_1698853] using wordTrace_append hprefix tailTrace_1698853
  have hstable : (prefixWord ++ tailWord_1698853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698853).length < 2 ^ (prefixWord ++ tailWord_1698853).sum := by decide
  have hdescent : baseEnd_1698853 < baseStart_1698853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698898 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1698898 : Nat := 118140960795 + 1698898 * 2 ^ 59
def prefixEnd_1698898 : Nat := 4983230072969 + 3 ^ 40 * 1698898 * 2
def baseEnd_1698898 : Nat := 387711669760977461094185

theorem tailTrace_1698898 : CollatzResearch.WordTrace tailWord_1698898 prefixEnd_1698898 387711669760977461094185 := by
  unfold tailWord_1698898
  simp only [CollatzResearch.WordTrace]
  refine ⟨15490975149797542380898337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41309267066126779682395565 15490975149797542380898337)
  ·
    refine ⟨11618231362348156785673753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15490975149797542380898337 11618231362348156785673753)
    ·
      refine ⟨8713673521761117589255315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11618231362348156785673753 8713673521761117589255315)
      ·
        refine ⟨13070510282641676383882973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8713673521761117589255315 13070510282641676383882973)
        ·
          refine ⟨4901441355990628643956115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13070510282641676383882973 4901441355990628643956115)
          ·
            refine ⟨7352162033985942965934173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901441355990628643956115 7352162033985942965934173)
            ·
              refine ⟨2757060762744728612225315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7352162033985942965934173 2757060762744728612225315)
              ·
                refine ⟨4135591144117092918337973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757060762744728612225315 4135591144117092918337973)
                ·
                  refine ⟨387711669760977461094185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4135591144117092918337973 387711669760977461094185)
                  ·
                    rfl

theorem cell21_1698898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1698898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698898 prefixEnd_1698898 := by exact prefixLift 1698898
  have htrace : WordTrace (prefixWord ++ tailWord_1698898) baseStart_1698898 baseEnd_1698898 := by
    simpa [prefixWord, tailWord_1698898, baseEnd_1698898] using wordTrace_append hprefix tailTrace_1698898
  have hstable : (prefixWord ++ tailWord_1698898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698898).length < 2 ^ (prefixWord ++ tailWord_1698898).sum := by decide
  have hdescent : baseEnd_1698898 < baseStart_1698898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698912 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_1698912 : Nat := 118140960795 + 1698912 * 2 ^ 59
def prefixEnd_1698912 : Nat := 4983230072969 + 3 ^ 40 * 1698912 * 2
def baseEnd_1698912 : Nat := 387714864751716547860823

theorem tailTrace_1698912 : CollatzResearch.WordTrace tailWord_1698912 prefixEnd_1698912 387714864751716547860823 := by
  unfold tailWord_1698912
  simp only [CollatzResearch.WordTrace]
  refine ⟨30982205610569724957301495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41309607480759633276401993 30982205610569724957301495)
  ·
    refine ⟨46473308415854587435952243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30982205610569724957301495 46473308415854587435952243)
    ·
      refine ⟨69709962623781881153928365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46473308415854587435952243 69709962623781881153928365)
      ·
        refine ⟨26141235983918205432723137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69709962623781881153928365 26141235983918205432723137)
        ·
          refine ⟨19605926987938654074542353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26141235983918205432723137 19605926987938654074542353)
          ·
            refine ⟨14704445240953990555906765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19605926987938654074542353 14704445240953990555906765)
            ·
              refine ⟨5514166965357746458465037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14704445240953990555906765 5514166965357746458465037)
              ·
                refine ⟨2067812612009154921924389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5514166965357746458465037 2067812612009154921924389)
                ·
                  refine ⟨387714864751716547860823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067812612009154921924389 387714864751716547860823)
                  ·
                    rfl

theorem cell21_1698912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_1698912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698912 prefixEnd_1698912 := by exact prefixLift 1698912
  have htrace : WordTrace (prefixWord ++ tailWord_1698912) baseStart_1698912 baseEnd_1698912 := by
    simpa [prefixWord, tailWord_1698912, baseEnd_1698912] using wordTrace_append hprefix tailTrace_1698912
  have hstable : (prefixWord ++ tailWord_1698912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698912).length < 2 ^ (prefixWord ++ tailWord_1698912).sum := by decide
  have hdescent : baseEnd_1698912 < baseStart_1698912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698949 : List Nat := [1, 3, 1, 1, 7, 1, 2, 2, 3]
def baseStart_1698949 : Nat := 118140960795 + 1698949 * 2 ^ 59
def prefixEnd_1698949 : Nat := 4983230072969 + 3 ^ 40 * 1698949 * 2
def baseEnd_1698949 : Nat := 387723308655812705744081

theorem tailTrace_1698949 : CollatzResearch.WordTrace tailWord_1698949 prefixEnd_1698949 387723308655812705744081 := by
  unfold tailWord_1698949
  simp only [CollatzResearch.WordTrace]
  refine ⟨61965760722005405233699901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41310507148003603489133267 61965760722005405233699901)
  ·
    refine ⟨23237160270752026962637463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61965760722005405233699901 23237160270752026962637463)
    ·
      refine ⟨34855740406128040443956195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23237160270752026962637463 34855740406128040443956195)
      ·
        refine ⟨52283610609192060665934293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34855740406128040443956195 52283610609192060665934293)
        ·
          refine ⟨1225397123652938921857835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52283610609192060665934293 1225397123652938921857835)
          ·
            refine ⟨1838095685479408382786753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225397123652938921857835 1838095685479408382786753)
            ·
              refine ⟨1378571764109556287090065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838095685479408382786753 1378571764109556287090065)
              ·
                refine ⟨1033928823082167215317549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1378571764109556287090065 1033928823082167215317549)
                ·
                  refine ⟨387723308655812705744081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033928823082167215317549 387723308655812705744081)
                  ·
                    rfl

theorem cell21_1698949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_1698949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698949 prefixEnd_1698949 := by exact prefixLift 1698949
  have htrace : WordTrace (prefixWord ++ tailWord_1698949) baseStart_1698949 baseEnd_1698949 := by
    simpa [prefixWord, tailWord_1698949, baseEnd_1698949] using wordTrace_append hprefix tailTrace_1698949
  have hstable : (prefixWord ++ tailWord_1698949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698949).length < 2 ^ (prefixWord ++ tailWord_1698949).sum := by decide
  have hdescent : baseEnd_1698949 < baseStart_1698949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1698974 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1698974 : Nat := 118140960795 + 1698974 * 2 ^ 59
def prefixEnd_1698974 : Nat := 4983230072969 + 3 ^ 40 * 1698974 * 2
def baseEnd_1698974 : Nat := 387729013996418217827363

theorem tailTrace_1698974 : CollatzResearch.WordTrace tailWord_1698974 prefixEnd_1698974 387729013996418217827363 := by
  unfold tailWord_1698974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745834068364354312919997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41311115031276556335573317 7745834068364354312919997)
  ·
    refine ⟨2904687775636632867344999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7745834068364354312919997 2904687775636632867344999)
    ·
      refine ⟨4357031663454949301017499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2904687775636632867344999 4357031663454949301017499)
      ·
        refine ⟨6535547495182423951526249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4357031663454949301017499 6535547495182423951526249)
        ·
          refine ⟨4901660621386817963644687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6535547495182423951526249 4901660621386817963644687)
          ·
            refine ⟨7352490932080226945467031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4901660621386817963644687 7352490932080226945467031)
            ·
              refine ⟨11028736398120340418200547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7352490932080226945467031 11028736398120340418200547)
              ·
                refine ⟨16543104597180510627300821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11028736398120340418200547 16543104597180510627300821)
                ·
                  refine ⟨387729013996418217827363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16543104597180510627300821 387729013996418217827363)
                  ·
                    rfl

theorem cell21_1698974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1698974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1698974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1698974 prefixEnd_1698974 := by exact prefixLift 1698974
  have htrace : WordTrace (prefixWord ++ tailWord_1698974) baseStart_1698974 baseEnd_1698974 := by
    simpa [prefixWord, tailWord_1698974, baseEnd_1698974] using wordTrace_append hprefix tailTrace_1698974
  have hstable : (prefixWord ++ tailWord_1698974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1698974).length < 2 ^ (prefixWord ++ tailWord_1698974).sum := by decide
  have hdescent : baseEnd_1698974 < baseStart_1698974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1698974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699022 : List Nat := [4, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_1699022 : Nat := 118140960795 + 1699022 * 2 ^ 59
def prefixEnd_1699022 : Nat := 4983230072969 + 3 ^ 40 * 1699022 * 2
def baseEnd_1699022 : Nat := 387739968250380801027265

theorem tailTrace_1699022 : CollatzResearch.WordTrace tailWord_1699022 prefixEnd_1699022 387739968250380801027265 := by
  unfold tailWord_1699022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7746052906342617337638415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41312282167160625800738213 7746052906342617337638415)
  ·
    refine ⟨11619079359513926006457623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7746052906342617337638415 11619079359513926006457623)
    ·
      refine ⟨17428619039270889009686435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11619079359513926006457623 17428619039270889009686435)
      ·
        refine ⟨26142928558906333514529653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17428619039270889009686435 26142928558906333514529653)
        ·
          refine ⟨2450899552397468766987155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26142928558906333514529653 2450899552397468766987155)
          ·
            refine ⟨3676349328596203150480733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450899552397468766987155 3676349328596203150480733)
            ·
              refine ⟨1378630998223576181430275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3676349328596203150480733 1378630998223576181430275)
              ·
                refine ⟨2067946497335364272145413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1378630998223576181430275 2067946497335364272145413)
                ·
                  refine ⟨387739968250380801027265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2067946497335364272145413 387739968250380801027265)
                  ·
                    rfl

theorem cell21_1699022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_1699022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699022 prefixEnd_1699022 := by exact prefixLift 1699022
  have htrace : WordTrace (prefixWord ++ tailWord_1699022) baseStart_1699022 baseEnd_1699022 := by
    simpa [prefixWord, tailWord_1699022, baseEnd_1699022] using wordTrace_append hprefix tailTrace_1699022
  have hstable : (prefixWord ++ tailWord_1699022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699022).length < 2 ^ (prefixWord ++ tailWord_1699022).sum := by decide
  have hdescent : baseEnd_1699022 < baseStart_1699022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699289 : List Nat := [1, 2, 1, 2, 4, 11]
def baseStart_1699289 : Nat := 118140960795 + 1699289 * 2 ^ 59
def prefixEnd_1699289 : Nat := 4983230072969 + 3 ^ 40 * 1699289 * 2
def baseEnd_1699289 : Nat := 14362996344001765558397

theorem tailTrace_1699289 : CollatzResearch.WordTrace tailWord_1699289 prefixEnd_1699289 14362996344001765558397 := by
  unfold tailWord_1699289
  simp only [CollatzResearch.WordTrace]
  refine ⟨61978161540773643301076921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41318774360515762200717947 61978161540773643301076921)
  ·
    refine ⟨46483621155580232475807691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61978161540773643301076921 46483621155580232475807691)
    ·
      refine ⟨69725431733370348713711537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46483621155580232475807691 69725431733370348713711537)
      ·
        refine ⟨52294073800027761535283653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69725431733370348713711537 52294073800027761535283653)
        ·
          refine ⟨9805138837505205287865685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52294073800027761535283653 9805138837505205287865685)
          ·
            refine ⟨14362996344001765558397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9805138837505205287865685 14362996344001765558397)
            ·
              rfl

theorem cell21_1699289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 11].length) (baseStart_1699289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699289 prefixEnd_1699289 := by exact prefixLift 1699289
  have htrace : WordTrace (prefixWord ++ tailWord_1699289) baseStart_1699289 baseEnd_1699289 := by
    simpa [prefixWord, tailWord_1699289, baseEnd_1699289] using wordTrace_append hprefix tailTrace_1699289
  have hstable : (prefixWord ++ tailWord_1699289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699289).length < 2 ^ (prefixWord ++ tailWord_1699289).sum := by decide
  have hdescent : baseEnd_1699289 < baseStart_1699289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699320 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_1699320 : Nat := 118140960795 + 1699320 * 2 ^ 59
def prefixEnd_1699320 : Nat := 4983230072969 + 3 ^ 40 * 1699320 * 2
def baseEnd_1699320 : Nat := 387807975910398505059989

theorem tailTrace_1699320 : CollatzResearch.WordTrace tailWord_1699320 prefixEnd_1699320 387807975910398505059989 := by
  unfold tailWord_1699320
  simp only [CollatzResearch.WordTrace]
  refine ⟨30989646101830667797727707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41319528135774223730303609 30989646101830667797727707)
  ·
    refine ⟨46484469152746001696591561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30989646101830667797727707 46484469152746001696591561)
    ·
      refine ⟨34863351864559501272443671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46484469152746001696591561 34863351864559501272443671)
      ·
        refine ⟨52295027796839251908665507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34863351864559501272443671 52295027796839251908665507)
        ·
          refine ⟨78442541695258877862998261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52295027796839251908665507 78442541695258877862998261)
          ·
            refine ⟨7353988283930519799656087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78442541695258877862998261 7353988283930519799656087)
            ·
              refine ⟨11030982425895779699484131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7353988283930519799656087 11030982425895779699484131)
              ·
                refine ⟨16546473638843669549226197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11030982425895779699484131 16546473638843669549226197)
                ·
                  refine ⟨387807975910398505059989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16546473638843669549226197 387807975910398505059989)
                  ·
                    rfl

theorem cell21_1699320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_1699320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699320 prefixEnd_1699320 := by exact prefixLift 1699320
  have htrace : WordTrace (prefixWord ++ tailWord_1699320) baseStart_1699320 baseEnd_1699320 := by
    simpa [prefixWord, tailWord_1699320, baseEnd_1699320] using wordTrace_append hprefix tailTrace_1699320
  have hstable : (prefixWord ++ tailWord_1699320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699320).length < 2 ^ (prefixWord ++ tailWord_1699320).sum := by decide
  have hdescent : baseEnd_1699320 < baseStart_1699320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699365 : List Nat := [1, 3, 1, 2, 2, 1, 1, 10]
def baseStart_1699365 : Nat := 118140960795 + 1699365 * 2 ^ 59
def prefixEnd_1699365 : Nat := 4983230072969 + 3 ^ 40 * 1699365 * 2
def baseEnd_1699365 : Nat := 129272748507829475603299

theorem tailTrace_1699365 : CollatzResearch.WordTrace tailWord_1699365 prefixEnd_1699365 129272748507829475603299 := by
  unfold tailWord_1699365
  simp only [CollatzResearch.WordTrace]
  refine ⟨61980933488498308280843549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41320622325665538853895699 61980933488498308280843549)
  ·
    refine ⟨23242850058186865605316331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61980933488498308280843549 23242850058186865605316331)
    ·
      refine ⟨34864275087280298407974497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23242850058186865605316331 34864275087280298407974497)
      ·
        refine ⟨26148206315460223805980873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34864275087280298407974497 26148206315460223805980873)
        ·
          refine ⟨19611154736595167854485655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26148206315460223805980873 19611154736595167854485655)
          ·
            refine ⟨29416732104892751781728483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19611154736595167854485655 29416732104892751781728483)
            ·
              refine ⟨44125098157339127672592725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29416732104892751781728483 44125098157339127672592725)
              ·
                refine ⟨129272748507829475603299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44125098157339127672592725 129272748507829475603299)
                ·
                  rfl

theorem cell21_1699365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 10].length) (baseStart_1699365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699365 prefixEnd_1699365 := by exact prefixLift 1699365
  have htrace : WordTrace (prefixWord ++ tailWord_1699365) baseStart_1699365 baseEnd_1699365 := by
    simpa [prefixWord, tailWord_1699365, baseEnd_1699365] using wordTrace_append hprefix tailTrace_1699365
  have hstable : (prefixWord ++ tailWord_1699365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699365).length < 2 ^ (prefixWord ++ tailWord_1699365).sum := by decide
  have hdescent : baseEnd_1699365 < baseStart_1699365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699388 : List Nat := [2, 2, 2, 2, 5, 1, 1, 3, 3]
def baseStart_1699388 : Nat := 118140960795 + 1699388 * 2 ^ 59
def prefixEnd_1699388 : Nat := 4983230072969 + 3 ^ 40 * 1699388 * 2
def baseEnd_1699388 : Nat := 387823494436845497926517

theorem tailTrace_1699388 : CollatzResearch.WordTrace tailWord_1699388 prefixEnd_1699388 387823494436845497926517 := by
  unfold tailWord_1699388
  simp only [CollatzResearch.WordTrace]
  refine ⟨30990886183707491604465409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41321181578276655472620545 30990886183707491604465409)
  ·
    refine ⟨23243164637780618703349057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30990886183707491604465409 23243164637780618703349057)
    ·
      refine ⟨17432373478335464027511793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23243164637780618703349057 17432373478335464027511793)
      ·
        refine ⟨13074280108751598020633845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17432373478335464027511793 13074280108751598020633845)
        ·
          refine ⟨1225713760195462314434423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13074280108751598020633845 1225713760195462314434423)
          ·
            refine ⟨1838570640293193471651635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225713760195462314434423 1838570640293193471651635)
            ·
              refine ⟨2757855960439790207477453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838570640293193471651635 2757855960439790207477453)
              ·
                refine ⟨1034195985164921327804045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2757855960439790207477453 1034195985164921327804045)
                ·
                  refine ⟨387823494436845497926517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034195985164921327804045 387823494436845497926517)
                  ·
                    rfl

theorem cell21_1699388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_1699388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699388 prefixEnd_1699388 := by exact prefixLift 1699388
  have htrace : WordTrace (prefixWord ++ tailWord_1699388) baseStart_1699388 baseEnd_1699388 := by
    simpa [prefixWord, tailWord_1699388, baseEnd_1699388] using wordTrace_append hprefix tailTrace_1699388
  have hstable : (prefixWord ++ tailWord_1699388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699388).length < 2 ^ (prefixWord ++ tailWord_1699388).sum := by decide
  have hdescent : baseEnd_1699388 < baseStart_1699388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699399 : List Nat := [1, 1, 4, 1, 6, 1, 7]
def baseStart_1699399 : Nat := 118140960795 + 1699399 * 2 ^ 59
def prefixEnd_1699399 : Nat := 4983230072969 + 3 ^ 40 * 1699399 * 2
def baseEnd_1699399 : Nat := 43091778309634658138129

theorem tailTrace_1699399 : CollatzResearch.WordTrace tailWord_1699399 prefixEnd_1699399 43091778309634658138129 := by
  unfold tailWord_1699399
  simp only [CollatzResearch.WordTrace]
  refine ⟨61982173570375132087581251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41321449046916754725054167 61982173570375132087581251)
  ·
    refine ⟨92973260355562698131371877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61982173570375132087581251 92973260355562698131371877)
    ·
      refine ⟨17432486316668005899632227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92973260355562698131371877 17432486316668005899632227)
      ·
        refine ⟨26148729475002008849448341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17432486316668005899632227 26148729475002008849448341)
        ·
          refine ⟨1225721694140719164817891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26148729475002008849448341 1225721694140719164817891)
          ·
            refine ⟨1838582541211078747226837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225721694140719164817891 1838582541211078747226837)
            ·
              refine ⟨43091778309634658138129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1838582541211078747226837 43091778309634658138129)
              ·
                rfl

theorem cell21_1699399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 7].length) (baseStart_1699399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699399 prefixEnd_1699399 := by exact prefixLift 1699399
  have htrace : WordTrace (prefixWord ++ tailWord_1699399) baseStart_1699399 baseEnd_1699399 := by
    simpa [prefixWord, tailWord_1699399, baseEnd_1699399] using wordTrace_append hprefix tailTrace_1699399
  have hstable : (prefixWord ++ tailWord_1699399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699399).length < 2 ^ (prefixWord ++ tailWord_1699399).sum := by decide
  have hdescent : baseEnd_1699399 < baseStart_1699399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699489 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 5]
def baseStart_1699489 : Nat := 118140960795 + 1699489 * 2 ^ 59
def prefixEnd_1699489 : Nat := 4983230072969 + 3 ^ 40 * 1699489 * 2
def baseEnd_1699489 : Nat := 387846544012891766742977

theorem tailTrace_1699489 : CollatzResearch.WordTrace tailWord_1699489 prefixEnd_1699489 387846544012891766742977 := by
  unfold tailWord_1699489
  simp only [CollatzResearch.WordTrace]
  refine ⟨61985456140049077458357521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41323637426699384972238347 61985456140049077458357521)
  ·
    refine ⟨46489092105036808093768141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61985456140049077458357521 46489092105036808093768141)
    ·
      refine ⟨17433409539388803035163053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46489092105036808093768141 17433409539388803035163053)
      ·
        refine ⟨6537528577270801138186145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17433409539388803035163053 6537528577270801138186145)
        ·
          refine ⟨4903146432953100853639609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6537528577270801138186145 4903146432953100853639609)
          ·
            refine ⟨3677359824714825640229707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4903146432953100853639609 3677359824714825640229707)
            ·
              refine ⟨5516039737072238460344561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3677359824714825640229707 5516039737072238460344561)
              ·
                refine ⟨4137029802804178845258421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5516039737072238460344561 4137029802804178845258421)
                ·
                  refine ⟨387846544012891766742977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4137029802804178845258421 387846544012891766742977)
                  ·
                    rfl

theorem cell21_1699489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_1699489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699489 prefixEnd_1699489 := by exact prefixLift 1699489
  have htrace : WordTrace (prefixWord ++ tailWord_1699489) baseStart_1699489 baseEnd_1699489 := by
    simpa [prefixWord, tailWord_1699489, baseEnd_1699489] using wordTrace_append hprefix tailTrace_1699489
  have hstable : (prefixWord ++ tailWord_1699489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699489).length < 2 ^ (prefixWord ++ tailWord_1699489).sum := by decide
  have hdescent : baseEnd_1699489 < baseStart_1699489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699517 : List Nat := [1, 4, 1, 2, 1, 2, 10]
def baseStart_1699517 : Nat := 118140960795 + 1699517 * 2 ^ 59
def prefixEnd_1699517 : Nat := 4983230072969 + 3 ^ 40 * 1699517 * 2
def baseEnd_1699517 : Nat := 43094770443818882252917

theorem tailTrace_1699517 : CollatzResearch.WordTrace tailWord_1699517 prefixEnd_1699517 43094770443818882252917 := by
  unfold tailWord_1699517
  simp only [CollatzResearch.WordTrace]
  refine ⟨61986477383947638240376805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41324318255965092160251203 61986477383947638240376805)
  ·
    refine ⟨11622464509490182170070651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61986477383947638240376805 11622464509490182170070651)
    ·
      refine ⟨17433696764235273255105977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11622464509490182170070651 17433696764235273255105977)
      ·
        refine ⟨13075272573176454941329483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17433696764235273255105977 13075272573176454941329483)
        ·
          refine ⟨19612908859764682411994225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075272573176454941329483 19612908859764682411994225)
          ·
            refine ⟨14709681644823511808995669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19612908859764682411994225 14709681644823511808995669)
            ·
              refine ⟨43094770443818882252917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14709681644823511808995669 43094770443818882252917)
              ·
                rfl

theorem cell21_1699517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 10].length) (baseStart_1699517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699517 prefixEnd_1699517 := by exact prefixLift 1699517
  have htrace : WordTrace (prefixWord ++ tailWord_1699517) baseStart_1699517 baseEnd_1699517 := by
    simpa [prefixWord, tailWord_1699517, baseEnd_1699517] using wordTrace_append hprefix tailTrace_1699517
  have hstable : (prefixWord ++ tailWord_1699517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699517).length < 2 ^ (prefixWord ++ tailWord_1699517).sum := by decide
  have hdescent : baseEnd_1699517 < baseStart_1699517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699596 : List Nat := [2, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_1699596 : Nat := 118140960795 + 1699596 * 2 ^ 59
def prefixEnd_1699596 : Nat := 4983230072969 + 3 ^ 40 * 1699596 * 2
def baseEnd_1699596 : Nat := 387870962870683358459425

theorem tailTrace_1699596 : CollatzResearch.WordTrace tailWord_1699596 prefixEnd_1699596 387870962870683358459425 := by
  unfold tailWord_1699596
  simp only [CollatzResearch.WordTrace]
  refine ⟨30994679375330717366251321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41326239167107623155001761 30994679375330717366251321)
  ·
    refine ⟨23246009531498038024688491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30994679375330717366251321 23246009531498038024688491)
    ·
      refine ⟨34869014297247057037032737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23246009531498038024688491 34869014297247057037032737)
      ·
        refine ⟨26151760722935292777774553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34869014297247057037032737 26151760722935292777774553)
        ·
          refine ⟨19613820542201469583330915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26151760722935292777774553 19613820542201469583330915)
          ·
            refine ⟨29420730813302204374996373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19613820542201469583330915 29420730813302204374996373)
            ·
              refine ⟨1379096756873540830077955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29420730813302204374996373 1379096756873540830077955)
              ·
                refine ⟨2068645135310311245116933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379096756873540830077955 2068645135310311245116933)
                ·
                  refine ⟨387870962870683358459425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2068645135310311245116933 387870962870683358459425)
                  ·
                    rfl

theorem cell21_1699596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_1699596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699596 prefixEnd_1699596 := by exact prefixLift 1699596
  have htrace : WordTrace (prefixWord ++ tailWord_1699596) baseStart_1699596 baseEnd_1699596 := by
    simpa [prefixWord, tailWord_1699596, baseEnd_1699596] using wordTrace_append hprefix tailTrace_1699596
  have hstable : (prefixWord ++ tailWord_1699596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699596).length < 2 ^ (prefixWord ++ tailWord_1699596).sum := by decide
  have hdescent : baseEnd_1699596 < baseStart_1699596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699655 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 4]
def baseStart_1699655 : Nat := 118140960795 + 1699655 * 2 ^ 59
def prefixEnd_1699655 : Nat := 4983230072969 + 3 ^ 40 * 1699655 * 2
def baseEnd_1699655 : Nat := 387884427474512366975971

theorem tailTrace_1699655 : CollatzResearch.WordTrace tailWord_1699655 prefixEnd_1699655 387884427474512366975971 := by
  unfold tailWord_1699655
  simp only [CollatzResearch.WordTrace]
  refine ⟨61991510657447687808900419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41327673771631791872600279 61991510657447687808900419)
  ·
    refine ⟨92987265986171531713350629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61991510657447687808900419 92987265986171531713350629)
    ·
      refine ⟨17435112372407162196253243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92987265986171531713350629 17435112372407162196253243)
      ·
        refine ⟨26152668558610743294379865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17435112372407162196253243 26152668558610743294379865)
        ·
          refine ⟨19614501418958057470784899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26152668558610743294379865 19614501418958057470784899)
          ·
            refine ⟨29421752128437086206177349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19614501418958057470784899 29421752128437086206177349)
            ·
              refine ⟨5516578524081953663658253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29421752128437086206177349 5516578524081953663658253)
              ·
                refine ⟨2068716946530732623871845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5516578524081953663658253 2068716946530732623871845)
                ·
                  refine ⟨387884427474512366975971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2068716946530732623871845 387884427474512366975971)
                  ·
                    rfl

theorem cell21_1699655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_1699655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699655 prefixEnd_1699655 := by exact prefixLift 1699655
  have htrace : WordTrace (prefixWord ++ tailWord_1699655) baseStart_1699655 baseEnd_1699655 := by
    simpa [prefixWord, tailWord_1699655, baseEnd_1699655] using wordTrace_append hprefix tailTrace_1699655
  have hstable : (prefixWord ++ tailWord_1699655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699655).length < 2 ^ (prefixWord ++ tailWord_1699655).sum := by decide
  have hdescent : baseEnd_1699655 < baseStart_1699655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699720 : List Nat := [2, 1, 3, 3, 4, 1, 2, 5]
def baseStart_1699720 : Nat := 118140960795 + 1699720 * 2 ^ 59
def prefixEnd_1699720 : Nat := 4983230072969 + 3 ^ 40 * 1699720 * 2
def baseEnd_1699720 : Nat := 129299753786695566130835

theorem tailTrace_1699720 : CollatzResearch.WordTrace tailWord_1699720 prefixEnd_1699720 129299753786695566130835 := by
  unfold tailWord_1699720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30996940701106101955008307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41329254268141469273344409 30996940701106101955008307)
  ·
    refine ⟨46495411051659152932512461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30996940701106101955008307 46495411051659152932512461)
    ·
      refine ⟨17435779144372182349692173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46495411051659152932512461 17435779144372182349692173)
      ·
        refine ⟨6538417179139568381134565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17435779144372182349692173 6538417179139568381134565)
        ·
          refine ⟨1225953221088669071462731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6538417179139568381134565 1225953221088669071462731)
          ·
            refine ⟨1838929831633003607194097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225953221088669071462731 1838929831633003607194097)
            ·
              refine ⟨1379197373724752705395573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838929831633003607194097 1379197373724752705395573)
              ·
                refine ⟨129299753786695566130835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1379197373724752705395573 129299753786695566130835)
                ·
                  rfl

theorem cell21_1699720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_1699720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699720 prefixEnd_1699720 := by exact prefixLift 1699720
  have htrace : WordTrace (prefixWord ++ tailWord_1699720) baseStart_1699720 baseEnd_1699720 := by
    simpa [prefixWord, tailWord_1699720, baseEnd_1699720] using wordTrace_append hprefix tailTrace_1699720
  have hstable : (prefixWord ++ tailWord_1699720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699720).length < 2 ^ (prefixWord ++ tailWord_1699720).sum := by decide
  have hdescent : baseEnd_1699720 < baseStart_1699720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699751 : List Nat := [1, 1, 6, 1, 2, 2, 3, 2, 3]
def baseStart_1699751 : Nat := 118140960795 + 1699751 * 2 ^ 59
def prefixEnd_1699751 : Nat := 4983230072969 + 3 ^ 40 * 1699751 * 2
def baseEnd_1699751 : Nat := 387906335982437533375775

theorem tailTrace_1699751 : CollatzResearch.WordTrace tailWord_1699751 prefixEnd_1699751 387906335982437533375775 := by
  unfold tailWord_1699751
  simp only [CollatzResearch.WordTrace]
  refine ⟨61995012065099896204395107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41330008043399930802930071 61995012065099896204395107)
  ·
    refine ⟨92992518097649844306592661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61995012065099896204395107 92992518097649844306592661)
    ·
      refine ⟨4359024285827336451871531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92992518097649844306592661 4359024285827336451871531)
      ·
        refine ⟨6538536428741004677807297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359024285827336451871531 6538536428741004677807297)
        ·
          refine ⟨4903902321555753508355473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538536428741004677807297 4903902321555753508355473)
          ·
            refine ⟨3677926741166815131266605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4903902321555753508355473 3677926741166815131266605)
            ·
              refine ⟨1379222527937555674224977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3677926741166815131266605 1379222527937555674224977)
              ·
                refine ⟨1034416895953166755668733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379222527937555674224977 1034416895953166755668733)
                ·
                  refine ⟨387906335982437533375775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034416895953166755668733 387906335982437533375775)
                  ·
                    rfl

theorem cell21_1699751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 3].length) (baseStart_1699751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699751 prefixEnd_1699751 := by exact prefixLift 1699751
  have htrace : WordTrace (prefixWord ++ tailWord_1699751) baseStart_1699751 baseEnd_1699751 := by
    simpa [prefixWord, tailWord_1699751, baseEnd_1699751] using wordTrace_append hprefix tailTrace_1699751
  have hstable : (prefixWord ++ tailWord_1699751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699751).length < 2 ^ (prefixWord ++ tailWord_1699751).sum := by decide
  have hdescent : baseEnd_1699751 < baseStart_1699751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699765 : List Nat := [1, 3, 3, 2, 1, 4, 2, 1, 4]
def baseStart_1699765 : Nat := 118140960795 + 1699765 * 2 ^ 59
def prefixEnd_1699765 : Nat := 4983230072969 + 3 ^ 40 * 1699765 * 2
def baseEnd_1699765 : Nat := 387909530973176620142413

theorem tailTrace_1699765 : CollatzResearch.WordTrace tailWord_1699765 prefixEnd_1699765 387909530973176620142413 := by
  unfold tailWord_1699765
  simp only [CollatzResearch.WordTrace]
  refine ⟨61995522687049176595404749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41330348458032784396936499 61995522687049176595404749)
  ·
    refine ⟨23248321007643441223276781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61995522687049176595404749 23248321007643441223276781)
    ·
      refine ⟨8718120377866290458728793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23248321007643441223276781 8718120377866290458728793)
      ·
        refine ⟨6538590283399717844046595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8718120377866290458728793 6538590283399717844046595)
        ·
          refine ⟨9807885425099576766069893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6538590283399717844046595 9807885425099576766069893)
          ·
            refine ⟨1838978517206170643638105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9807885425099576766069893 1838978517206170643638105)
            ·
              refine ⟨1379233887904627982728579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1838978517206170643638105 1379233887904627982728579)
              ·
                refine ⟨2068850831856941974092869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379233887904627982728579 2068850831856941974092869)
                ·
                  refine ⟨387909530973176620142413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2068850831856941974092869 387909530973176620142413)
                  ·
                    rfl

theorem cell21_1699765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_1699765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699765 prefixEnd_1699765 := by exact prefixLift 1699765
  have htrace : WordTrace (prefixWord ++ tailWord_1699765) baseStart_1699765 baseEnd_1699765 := by
    simpa [prefixWord, tailWord_1699765, baseEnd_1699765] using wordTrace_append hprefix tailTrace_1699765
  have hstable : (prefixWord ++ tailWord_1699765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699765).length < 2 ^ (prefixWord ++ tailWord_1699765).sum := by decide
  have hdescent : baseEnd_1699765 < baseStart_1699765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699807 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 4]
def baseStart_1699807 : Nat := 118140960795 + 1699807 * 2 ^ 59
def prefixEnd_1699807 : Nat := 4983230072969 + 3 ^ 40 * 1699807 * 2
def baseEnd_1699807 : Nat := 387919115945393880442327

theorem tailTrace_1699807 : CollatzResearch.WordTrace tailWord_1699807 prefixEnd_1699807 387919115945393880442327 := by
  unfold tailWord_1699807
  simp only [CollatzResearch.WordTrace]
  refine ⟨61997054552897017768433675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41331369701931345178955783 61997054552897017768433675)
  ·
    refine ⟨92995581829345526652650513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61997054552897017768433675 92995581829345526652650513)
    ·
      refine ⟨69746686372009144989487885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92995581829345526652650513 69746686372009144989487885)
      ·
        refine ⟨26155007389503429371057957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69746686372009144989487885 26155007389503429371057957)
        ·
          refine ⟨4904063885531893007073367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26155007389503429371057957 4904063885531893007073367)
          ·
            refine ⟨7356095828297839510610051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904063885531893007073367 7356095828297839510610051)
            ·
              refine ⟨11034143742446759265915077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356095828297839510610051 11034143742446759265915077)
              ·
                refine ⟨2068901951708767362359077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11034143742446759265915077 2068901951708767362359077)
                ·
                  refine ⟨387919115945393880442327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2068901951708767362359077 387919115945393880442327)
                  ·
                    rfl

theorem cell21_1699807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_1699807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699807 prefixEnd_1699807 := by exact prefixLift 1699807
  have htrace : WordTrace (prefixWord ++ tailWord_1699807) baseStart_1699807 baseEnd_1699807 := by
    simpa [prefixWord, tailWord_1699807, baseEnd_1699807] using wordTrace_append hprefix tailTrace_1699807
  have hstable : (prefixWord ++ tailWord_1699807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699807).length < 2 ^ (prefixWord ++ tailWord_1699807).sum := by decide
  have hdescent : baseEnd_1699807 < baseStart_1699807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699835 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 7]
def baseStart_1699835 : Nat := 118140960795 + 1699835 * 2 ^ 59
def prefixEnd_1699835 : Nat := 4983230072969 + 3 ^ 40 * 1699835 * 2
def baseEnd_1699835 : Nat := 387925505926872053975603

theorem tailTrace_1699835 : CollatzResearch.WordTrace tailWord_1699835 prefixEnd_1699835 387925505926872053975603 := by
  unfold tailWord_1699835
  simp only [CollatzResearch.WordTrace]
  refine ⟨61998075796795578550452959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41332050531197052366968639 61998075796795578550452959)
  ·
    refine ⟨92997113695193367825679439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61998075796795578550452959 92997113695193367825679439)
    ·
      refine ⟨139495670542790051738519159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92997113695193367825679439 139495670542790051738519159)
      ·
        refine ⟨209243505814185077607778739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139495670542790051738519159 209243505814185077607778739)
        ·
          refine ⟨313865258721277616411668109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209243505814185077607778739 313865258721277616411668109)
          ·
            refine ⟨117699472020479106154375541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 313865258721277616411668109 117699472020479106154375541)
            ·
              refine ⟨11034325501919916201972707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117699472020479106154375541 11034325501919916201972707)
              ·
                refine ⟨16551488252879874302959061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11034325501919916201972707 16551488252879874302959061)
                ·
                  refine ⟨387925505926872053975603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16551488252879874302959061 387925505926872053975603)
                  ·
                    rfl

theorem cell21_1699835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_1699835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699835 prefixEnd_1699835 := by exact prefixLift 1699835
  have htrace : WordTrace (prefixWord ++ tailWord_1699835) baseStart_1699835 baseEnd_1699835 := by
    simpa [prefixWord, tailWord_1699835, baseEnd_1699835] using wordTrace_append hprefix tailTrace_1699835
  have hstable : (prefixWord ++ tailWord_1699835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699835).length < 2 ^ (prefixWord ++ tailWord_1699835).sum := by decide
  have hdescent : baseEnd_1699835 < baseStart_1699835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699869 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1699869 : Nat := 118140960795 + 1699869 * 2 ^ 59
def prefixEnd_1699869 : Nat := 4983230072969 + 3 ^ 40 * 1699869 * 2
def baseEnd_1699869 : Nat := 387933265190095550408867

theorem tailTrace_1699869 : CollatzResearch.WordTrace tailWord_1699869 prefixEnd_1699869 387933265190095550408867 := by
  unfold tailWord_1699869
  simp only [CollatzResearch.WordTrace]
  refine ⟨61999315878672402357190661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41332877252448268238127107 61999315878672402357190661)
  ·
    refine ⟨11624871727251075441973249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61999315878672402357190661 11624871727251075441973249)
    ·
      refine ⟨8718653795438306581479937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11624871727251075441973249 8718653795438306581479937)
      ·
        refine ⟨6538990346578729936109953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8718653795438306581479937 6538990346578729936109953)
        ·
          refine ⟨4904242759934047452082465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538990346578729936109953 4904242759934047452082465)
          ·
            refine ⟨3678182069950535589061849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4904242759934047452082465 3678182069950535589061849)
            ·
              refine ⟨2758636552462901691796387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678182069950535589061849 2758636552462901691796387)
              ·
                refine ⟨4137954828694352537694581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758636552462901691796387 4137954828694352537694581)
                ·
                  refine ⟨387933265190095550408867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4137954828694352537694581 387933265190095550408867)
                  ·
                    rfl

theorem cell21_1699869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1699869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699869 prefixEnd_1699869 := by exact prefixLift 1699869
  have htrace : WordTrace (prefixWord ++ tailWord_1699869) baseStart_1699869 baseEnd_1699869 := by
    simpa [prefixWord, tailWord_1699869, baseEnd_1699869] using wordTrace_append hprefix tailTrace_1699869
  have hstable : (prefixWord ++ tailWord_1699869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699869).length < 2 ^ (prefixWord ++ tailWord_1699869).sum := by decide
  have hdescent : baseEnd_1699869 < baseStart_1699869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699928 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_1699928 : Nat := 118140960795 + 1699928 * 2 ^ 59
def prefixEnd_1699928 : Nat := 4983230072969 + 3 ^ 40 * 1699928 * 2
def baseEnd_1699928 : Nat := 387946729793924558925413

theorem tailTrace_1699928 : CollatzResearch.WordTrace tailWord_1699928 prefixEnd_1699928 387946729793924558925413 := by
  unfold tailWord_1699928
  simp only [CollatzResearch.WordTrace]
  refine ⟨31000733892729327716794219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41334311856972436955725625 31000733892729327716794219)
  ·
    refine ⟨46501100839093991575191329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31000733892729327716794219 46501100839093991575191329)
    ·
      refine ⟨34875825629320493681393497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46501100839093991575191329 34875825629320493681393497)
      ·
        refine ⟨26156869221990370261045123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34875825629320493681393497 26156869221990370261045123)
        ·
          refine ⟨39235303832985555391567685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26156869221990370261045123 39235303832985555391567685)
          ·
            refine ⟨7356619468684791635918941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39235303832985555391567685 7356619468684791635918941)
            ·
              refine ⟨2758732300756796863469603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7356619468684791635918941 2758732300756796863469603)
              ·
                refine ⟨4138098451135195295204405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758732300756796863469603 4138098451135195295204405)
                ·
                  refine ⟨387946729793924558925413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4138098451135195295204405 387946729793924558925413)
                  ·
                    rfl

theorem cell21_1699928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_1699928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699928 prefixEnd_1699928 := by exact prefixLift 1699928
  have htrace : WordTrace (prefixWord ++ tailWord_1699928) baseStart_1699928 baseEnd_1699928 := by
    simpa [prefixWord, tailWord_1699928, baseEnd_1699928] using wordTrace_append hprefix tailTrace_1699928
  have hstable : (prefixWord ++ tailWord_1699928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699928).length < 2 ^ (prefixWord ++ tailWord_1699928).sum := by decide
  have hdescent : baseEnd_1699928 < baseStart_1699928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699934 : List Nat := [4, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1699934 : Nat := 118140960795 + 1699934 * 2 ^ 59
def prefixEnd_1699934 : Nat := 4983230072969 + 3 ^ 40 * 1699934 * 2
def baseEnd_1699934 : Nat := 387948099075669881825401

theorem tailTrace_1699934 : CollatzResearch.WordTrace tailWord_1699934 prefixEnd_1699934 387948099075669881825401 := by
  unfold tailWord_1699934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7750210827929614807288357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41334457748957945638871237 7750210827929614807288357)
  ·
    refine ⟨1453164530236802776366567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7750210827929614807288357 1453164530236802776366567)
    ·
      refine ⟨2179746795355204164549851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1453164530236802776366567 2179746795355204164549851)
      ·
        refine ⟨3269620193032806246824777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2179746795355204164549851 3269620193032806246824777)
        ·
          refine ⟨2452215144774604685118583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269620193032806246824777 2452215144774604685118583)
          ·
            refine ⟨3678322717161907027677875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452215144774604685118583 3678322717161907027677875)
            ·
              refine ⟨5517484075742860541516813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678322717161907027677875 5517484075742860541516813)
              ·
                refine ⟨2069056528403572703068805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5517484075742860541516813 2069056528403572703068805)
                ·
                  refine ⟨387948099075669881825401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069056528403572703068805 387948099075669881825401)
                  ·
                    rfl

theorem cell21_1699934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1699934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699934 prefixEnd_1699934 := by exact prefixLift 1699934
  have htrace : WordTrace (prefixWord ++ tailWord_1699934) baseStart_1699934 baseEnd_1699934 := by
    simpa [prefixWord, tailWord_1699934, baseEnd_1699934] using wordTrace_append hprefix tailTrace_1699934
  have hstable : (prefixWord ++ tailWord_1699934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699934).length < 2 ^ (prefixWord ++ tailWord_1699934).sum := by decide
  have hdescent : baseEnd_1699934 < baseStart_1699934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699976 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_1699976 : Nat := 118140960795 + 1699976 * 2 ^ 59
def prefixEnd_1699976 : Nat := 4983230072969 + 3 ^ 40 * 1699976 * 2
def baseEnd_1699976 : Nat := 387957684047887142125315

theorem tailTrace_1699976 : CollatzResearch.WordTrace tailWord_1699976 prefixEnd_1699976 387957684047887142125315 := by
  unfold tailWord_1699976
  simp only [CollatzResearch.WordTrace]
  refine ⟨31001609244642379815667891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41335478992856506420890521 31001609244642379815667891)
  ·
    refine ⟨46502413866963569723501837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31001609244642379815667891 46502413866963569723501837)
    ·
      refine ⟨17438405200111338646313189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46502413866963569723501837 17438405200111338646313189)
      ·
        refine ⟨3269700975020875996183723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17438405200111338646313189 3269700975020875996183723)
        ·
          refine ⟨4904551462531313994275585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3269700975020875996183723 4904551462531313994275585)
          ·
            refine ⟨3678413596898485495706689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4904551462531313994275585 3678413596898485495706689)
            ·
              refine ⟨2758810197673864121780017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678413596898485495706689 2758810197673864121780017)
              ·
                refine ⟨2069107648255398091335013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758810197673864121780017 2069107648255398091335013)
                ·
                  refine ⟨387957684047887142125315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069107648255398091335013 387957684047887142125315)
                  ·
                    rfl

theorem cell21_1699976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_1699976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699976 prefixEnd_1699976 := by exact prefixLift 1699976
  have htrace : WordTrace (prefixWord ++ tailWord_1699976) baseStart_1699976 baseEnd_1699976 := by
    simpa [prefixWord, tailWord_1699976, baseEnd_1699976] using wordTrace_append hprefix tailTrace_1699976
  have hstable : (prefixWord ++ tailWord_1699976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699976).length < 2 ^ (prefixWord ++ tailWord_1699976).sum := by decide
  have hdescent : baseEnd_1699976 < baseStart_1699976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1699987 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 5]
def baseStart_1699987 : Nat := 118140960795 + 1699987 * 2 ^ 59
def prefixEnd_1699987 : Nat := 4983230072969 + 3 ^ 40 * 1699987 * 2
def baseEnd_1699987 : Nat := 387960194397753567441959

theorem tailTrace_1699987 : CollatzResearch.WordTrace tailWord_1699987 prefixEnd_1699987 387960194397753567441959 := by
  unfold tailWord_1699987
  simp only [CollatzResearch.WordTrace]
  refine ⟨62003619692244908509986215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41335746461496605673324143 62003619692244908509986215)
  ·
    refine ⟨93005429538367362764979323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62003619692244908509986215 93005429538367362764979323)
    ·
      refine ⟨139508144307551044147468985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93005429538367362764979323 139508144307551044147468985)
      ·
        refine ⟨104631108230663283110601739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139508144307551044147468985 104631108230663283110601739)
        ·
          refine ⟨156946662345994924665902609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104631108230663283110601739 156946662345994924665902609)
          ·
            refine ⟨117709996759496193499426957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156946662345994924665902609 117709996759496193499426957)
            ·
              refine ⟨44141248784811072562285109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117709996759496193499426957 44141248784811072562285109)
              ·
                refine ⟨4138242073576038052714229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44141248784811072562285109 4138242073576038052714229)
                ·
                  refine ⟨387960194397753567441959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4138242073576038052714229 387960194397753567441959)
                  ·
                    rfl

theorem cell21_1699987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_1699987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1699987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1699987 prefixEnd_1699987 := by exact prefixLift 1699987
  have htrace : WordTrace (prefixWord ++ tailWord_1699987) baseStart_1699987 baseEnd_1699987 := by
    simpa [prefixWord, tailWord_1699987, baseEnd_1699987] using wordTrace_append hprefix tailTrace_1699987
  have hstable : (prefixWord ++ tailWord_1699987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1699987).length < 2 ^ (prefixWord ++ tailWord_1699987).sum := by decide
  have hdescent : baseEnd_1699987 < baseStart_1699987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1699987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700007 : List Nat := [1, 1, 6, 2, 2, 1, 3, 5]
def baseStart_1700007 : Nat := 118140960795 + 1700007 * 2 ^ 59
def prefixEnd_1700007 : Nat := 4983230072969 + 3 ^ 40 * 1700007 * 2
def baseEnd_1700007 : Nat := 129321586223412659036195

theorem tailTrace_1700007 : CollatzResearch.WordTrace tailWord_1700007 prefixEnd_1700007 129321586223412659036195 := by
  unfold tailWord_1700007
  simp only [CollatzResearch.WordTrace]
  refine ⟨62004349152172451925714275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41336232768114967950476183 62004349152172451925714275)
  ·
    refine ⟨93006523728258677888571413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62004349152172451925714275 93006523728258677888571413)
    ·
      refine ⟨4359680799762125526026785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93006523728258677888571413 4359680799762125526026785)
      ·
        refine ⟨3269760599821594144520089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4359680799762125526026785 3269760599821594144520089)
        ·
          refine ⟨2452320449866195608390067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3269760599821594144520089 2452320449866195608390067)
          ·
            refine ⟨3678480674799293412585101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452320449866195608390067 3678480674799293412585101)
            ·
              refine ⟨1379430253049735029719413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3678480674799293412585101 1379430253049735029719413)
              ·
                refine ⟨129321586223412659036195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1379430253049735029719413 129321586223412659036195)
                ·
                  rfl

theorem cell21_1700007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 5].length) (baseStart_1700007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700007 prefixEnd_1700007 := by exact prefixLift 1700007
  have htrace : WordTrace (prefixWord ++ tailWord_1700007) baseStart_1700007 baseEnd_1700007 := by
    simpa [prefixWord, tailWord_1700007, baseEnd_1700007] using wordTrace_append hprefix tailTrace_1700007
  have hstable : (prefixWord ++ tailWord_1700007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700007).length < 2 ^ (prefixWord ++ tailWord_1700007).sum := by decide
  have hdescent : baseEnd_1700007 < baseStart_1700007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700018 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1700018 : Nat := 118140960795 + 1700018 * 2 ^ 59
def prefixEnd_1700018 : Nat := 4983230072969 + 3 ^ 40 * 1700018 * 2
def baseEnd_1700018 : Nat := 387967269020104402425229

theorem tailTrace_1700018 : CollatzResearch.WordTrace tailWord_1700018 prefixEnd_1700018 387967269020104402425229 := by
  unfold tailWord_1700018
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501187588783150201091177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41336500236755067202909805 15501187588783150201091177)
  ·
    refine ⟨11625890691587362650818383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15501187588783150201091177 11625890691587362650818383)
    ·
      refine ⟨17438836037381043976227575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11625890691587362650818383 17438836037381043976227575)
      ·
        refine ⟨26158254056071565964341363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17438836037381043976227575 26158254056071565964341363)
        ·
          refine ⟨39237381084107348946512045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26158254056071565964341363 39237381084107348946512045)
          ·
            refine ⟨14714017906540255854942017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39237381084107348946512045 14714017906540255854942017)
            ·
              refine ⟨11035513429905191891206513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14714017906540255854942017 11035513429905191891206513)
              ·
                refine ⟨8276635072428893918404885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11035513429905191891206513 8276635072428893918404885)
                ·
                  refine ⟨387967269020104402425229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8276635072428893918404885 387967269020104402425229)
                  ·
                    rfl

theorem cell21_1700018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1700018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700018 prefixEnd_1700018 := by exact prefixLift 1700018
  have htrace : WordTrace (prefixWord ++ tailWord_1700018) baseStart_1700018 baseEnd_1700018 := by
    simpa [prefixWord, tailWord_1700018, baseEnd_1700018] using wordTrace_append hprefix tailTrace_1700018
  have hstable : (prefixWord ++ tailWord_1700018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700018).length < 2 ^ (prefixWord ++ tailWord_1700018).sum := by decide
  have hdescent : baseEnd_1700018 < baseStart_1700018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700142 : List Nat := [4, 1, 3, 3, 1, 9]
def baseStart_1700142 : Nat := 118140960795 + 1700142 * 2 ^ 59
def prefixEnd_1700142 : Nat := 4983230072969 + 3 ^ 40 * 1700142 * 2
def baseEnd_1700142 : Nat := 14370206204055842309567

theorem tailTrace_1700142 : CollatzResearch.WordTrace tailWord_1700142 prefixEnd_1700142 14370206204055842309567 := by
  unfold tailWord_1700142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751159125835421247734835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41339515337788913321252453 7751159125835421247734835)
  ·
    refine ⟨11626738688753131871602253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7751159125835421247734835 11626738688753131871602253)
    ·
      refine ⟨4360027008282424451850845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11626738688753131871602253 4360027008282424451850845)
      ·
        refine ⟨1635010128105909169444067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4360027008282424451850845 1635010128105909169444067)
        ·
          refine ⟨2452515192158863754166101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635010128105909169444067 2452515192158863754166101)
          ·
            refine ⟨14370206204055842309567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2452515192158863754166101 14370206204055842309567)
            ·
              rfl

theorem cell21_1700142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 9].length) (baseStart_1700142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700142 prefixEnd_1700142 := by exact prefixLift 1700142
  have htrace : WordTrace (prefixWord ++ tailWord_1700142) baseStart_1700142 baseEnd_1700142 := by
    simpa [prefixWord, tailWord_1700142, baseEnd_1700142] using wordTrace_append hprefix tailTrace_1700142
  have hstable : (prefixWord ++ tailWord_1700142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700142).length < 2 ^ (prefixWord ++ tailWord_1700142).sum := by decide
  have hdescent : baseEnd_1700142 < baseStart_1700142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700204 : List Nat := [2, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_1700204 : Nat := 118140960795 + 1700204 * 2 ^ 59
def prefixEnd_1700204 : Nat := 4983230072969 + 3 ^ 40 * 1700204 * 2
def baseEnd_1700204 : Nat := 388009716754209412324849

theorem tailTrace_1700204 : CollatzResearch.WordTrace tailWord_1700204 prefixEnd_1700204 388009716754209412324849 := by
  unfold tailWord_1700204
  simp only [CollatzResearch.WordTrace]
  refine ⟨31005767166229377285317833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41341022888305836380423777 31005767166229377285317833)
  ·
    refine ⟨23254325374672032963988375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31005767166229377285317833 23254325374672032963988375)
    ·
      refine ⟨34881488062008049445982563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23254325374672032963988375 34881488062008049445982563)
      ·
        refine ⟨52322232093012074168973845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34881488062008049445982563 52322232093012074168973845)
        ·
          refine ⟨2452604629359940976670649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52322232093012074168973845 2452604629359940976670649)
          ·
            refine ⟨1839453472019955732502987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2452604629359940976670649 1839453472019955732502987)
            ·
              refine ⟨2759180208029933598754481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839453472019955732502987 2759180208029933598754481)
              ·
                refine ⟨2069385156022450199065861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759180208029933598754481 2069385156022450199065861)
                ·
                  refine ⟨388009716754209412324849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069385156022450199065861 388009716754209412324849)
                  ·
                    rfl

theorem cell21_1700204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_1700204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700204 prefixEnd_1700204 := by exact prefixLift 1700204
  have htrace : WordTrace (prefixWord ++ tailWord_1700204) baseStart_1700204 baseEnd_1700204 := by
    simpa [prefixWord, tailWord_1700204, baseEnd_1700204] using wordTrace_append hprefix tailTrace_1700204
  have hstable : (prefixWord ++ tailWord_1700204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700204).length < 2 ^ (prefixWord ++ tailWord_1700204).sum := by decide
  have hdescent : baseEnd_1700204 < baseStart_1700204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700260 : List Nat := [2, 3, 1, 2, 1, 1, 11]
def baseStart_1700260 : Nat := 118140960795 + 1700260 * 2 ^ 59
def prefixEnd_1700260 : Nat := 4983230072969 + 3 ^ 40 * 1700260 * 2
def baseEnd_1700260 : Nat := 43113610746351751043489

theorem tailTrace_1700260 : CollatzResearch.WordTrace tailWord_1700260 prefixEnd_1700260 43113610746351751043489 := by
  unfold tailWord_1700260
  simp only [CollatzResearch.WordTrace]
  refine ⟨31006788410127938067337117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41342384546837250756449489 31006788410127938067337117)
  ·
    refine ⟨11627545653797976775251419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31006788410127938067337117 11627545653797976775251419)
    ·
      refine ⟨17441318480696965162877129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11627545653797976775251419 17441318480696965162877129)
      ·
        refine ⟨13080988860522723872157847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17441318480696965162877129 13080988860522723872157847)
        ·
          refine ⟨19621483290784085808236771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13080988860522723872157847 19621483290784085808236771)
          ·
            refine ⟨29432224936176128712355157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19621483290784085808236771 29432224936176128712355157)
            ·
              refine ⟨43113610746351751043489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29432224936176128712355157 43113610746351751043489)
              ·
                rfl

theorem cell21_1700260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 11].length) (baseStart_1700260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700260 prefixEnd_1700260 := by exact prefixLift 1700260
  have htrace : WordTrace (prefixWord ++ tailWord_1700260) baseStart_1700260 baseEnd_1700260 := by
    simpa [prefixWord, tailWord_1700260, baseEnd_1700260] using wordTrace_append hprefix tailTrace_1700260
  have hstable : (prefixWord ++ tailWord_1700260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700260).length < 2 ^ (prefixWord ++ tailWord_1700260).sum := by decide
  have hdescent : baseEnd_1700260 < baseStart_1700260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700305 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 8]
def baseStart_1700305 : Nat := 118140960795 + 1700305 * 2 ^ 59
def prefixEnd_1700305 : Nat := 4983230072969 + 3 ^ 40 * 1700305 * 2
def baseEnd_1700305 : Nat := 388032766330255681141309

theorem tailTrace_1700305 : CollatzResearch.WordTrace tailWord_1700305 prefixEnd_1700305 388032766330255681141309 := by
  unfold tailWord_1700305
  simp only [CollatzResearch.WordTrace]
  refine ⟨62015218105092848820062369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41343478736728565880041579 62015218105092848820062369)
  ·
    refine ⟨46511413578819636615046777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62015218105092848820062369 46511413578819636615046777)
    ·
      refine ⟨34883560184114727461285083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46511413578819636615046777 34883560184114727461285083)
      ·
        refine ⟨52325340276172091191927625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34883560184114727461285083 52325340276172091191927625)
        ·
          refine ⟨39244005207129068393945719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52325340276172091191927625 39244005207129068393945719)
          ·
            refine ⟨58866007810693602590918579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39244005207129068393945719 58866007810693602590918579)
            ·
              refine ⟨88299011716040403886377869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58866007810693602590918579 88299011716040403886377869)
              ·
                refine ⟨33112129393515151457391701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88299011716040403886377869 33112129393515151457391701)
                ·
                  refine ⟨388032766330255681141309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33112129393515151457391701 388032766330255681141309)
                  ·
                    rfl

theorem cell21_1700305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_1700305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700305 prefixEnd_1700305 := by exact prefixLift 1700305
  have htrace : WordTrace (prefixWord ++ tailWord_1700305) baseStart_1700305 baseEnd_1700305 := by
    simpa [prefixWord, tailWord_1700305, baseEnd_1700305] using wordTrace_append hprefix tailTrace_1700305
  have hstable : (prefixWord ++ tailWord_1700305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700305).length < 2 ^ (prefixWord ++ tailWord_1700305).sum := by decide
  have hdescent : baseEnd_1700305 < baseStart_1700305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700404 : List Nat := [2, 5, 1, 3, 1, 2, 2, 5]
def baseStart_1700404 : Nat := 118140960795 + 1700404 * 2 ^ 59
def prefixEnd_1700404 : Nat := 4983230072969 + 3 ^ 40 * 1700404 * 2
def baseEnd_1700404 : Nat := 129351786493017836330369

theorem tailTrace_1700404 : CollatzResearch.WordTrace tailWord_1700404 prefixEnd_1700404 129351786493017836330369 := by
  unfold tailWord_1700404
  simp only [CollatzResearch.WordTrace]
  refine ⟨31009414465867094363958133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41345885954489459151944177 31009414465867094363958133)
  ·
    refine ⟨2907132606175040096621075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31009414465867094363958133 2907132606175040096621075)
    ·
      refine ⟨4360698909262560144931613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907132606175040096621075 4360698909262560144931613)
      ·
        refine ⟨1635262090973460054349355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4360698909262560144931613 1635262090973460054349355)
        ·
          refine ⟨2452893136460190081524033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635262090973460054349355 2452893136460190081524033)
          ·
            refine ⟨1839669852345142561143025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2452893136460190081524033 1839669852345142561143025)
            ·
              refine ⟨1379752389258856920857269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1839669852345142561143025 1379752389258856920857269)
              ·
                refine ⟨129351786493017836330369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1379752389258856920857269 129351786493017836330369)
                ·
                  rfl

theorem cell21_1700404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_1700404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700404 prefixEnd_1700404 := by exact prefixLift 1700404
  have htrace : WordTrace (prefixWord ++ tailWord_1700404) baseStart_1700404 baseEnd_1700404 := by
    simpa [prefixWord, tailWord_1700404, baseEnd_1700404] using wordTrace_append hprefix tailTrace_1700404
  have hstable : (prefixWord ++ tailWord_1700404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700404).length < 2 ^ (prefixWord ++ tailWord_1700404).sum := by decide
  have hdescent : baseEnd_1700404 < baseStart_1700404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700429 : List Nat := [1, 6, 1, 1, 2, 1, 9]
def baseStart_1700429 : Nat := 118140960795 + 1700429 * 2 ^ 59
def prefixEnd_1700429 : Nat := 4983230072969 + 3 ^ 40 * 1700429 * 2
def baseEnd_1700429 : Nat := 43117896091073224563821

theorem tailTrace_1700429 : CollatzResearch.WordTrace tailWord_1700429 prefixEnd_1700429 43117896091073224563821 := by
  unfold tailWord_1700429
  simp only [CollatzResearch.WordTrace]
  refine ⟨62019740756643617997576341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41346493837762411998384227 62019740756643617997576341)
  ·
    refine ⟨2907175347967669593636391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62019740756643617997576341 2907175347967669593636391)
    ·
      refine ⟨4360763021951504390454587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907175347967669593636391 4360763021951504390454587)
      ·
        refine ⟨6541144532927256585681881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360763021951504390454587 6541144532927256585681881)
        ·
          refine ⟨4905858399695442439261411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6541144532927256585681881 4905858399695442439261411)
          ·
            refine ⟨7358787599543163658892117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4905858399695442439261411 7358787599543163658892117)
            ·
              refine ⟨43117896091073224563821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7358787599543163658892117 43117896091073224563821)
              ·
                rfl

theorem cell21_1700429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 9].length) (baseStart_1700429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700429 prefixEnd_1700429 := by exact prefixLift 1700429
  have htrace : WordTrace (prefixWord ++ tailWord_1700429) baseStart_1700429 baseEnd_1700429 := by
    simpa [prefixWord, tailWord_1700429, baseEnd_1700429] using wordTrace_append hprefix tailTrace_1700429
  have hstable : (prefixWord ++ tailWord_1700429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700429).length < 2 ^ (prefixWord ++ tailWord_1700429).sum := by decide
  have hdescent : baseEnd_1700429 < baseStart_1700429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700567 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 4]
def baseStart_1700567 : Nat := 118140960795 + 1700567 * 2 ^ 59
def prefixEnd_1700567 : Nat := 4983230072969 + 3 ^ 40 * 1700567 * 2
def baseEnd_1700567 : Nat := 388092558299801447774107

theorem tailTrace_1700567 : CollatzResearch.WordTrace tailWord_1700567 prefixEnd_1700567 388092558299801447774107 := by
  unfold tailWord_1700567
  simp only [CollatzResearch.WordTrace]
  refine ⟨62024774030143667566099955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41349849353429111710733303 62024774030143667566099955)
  ·
    refine ⟨93037161045215501349149933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62024774030143667566099955 93037161045215501349149933)
    ·
      refine ⟨34888935391955813005931225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93037161045215501349149933 34888935391955813005931225)
      ·
        refine ⟨26166701543966859754448419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34888935391955813005931225 26166701543966859754448419)
        ·
          refine ⟨39250052315950289631672629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26166701543966859754448419 39250052315950289631672629)
          ·
            refine ⟨3679692404620339652969309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39250052315950289631672629 3679692404620339652969309)
            ·
              refine ⟨1379884651732627369863491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3679692404620339652969309 1379884651732627369863491)
              ·
                refine ⟨2069826977598941054795237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1379884651732627369863491 2069826977598941054795237)
                ·
                  refine ⟨388092558299801447774107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069826977598941054795237 388092558299801447774107)
                  ·
                    rfl

theorem cell21_1700567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 4].length) (baseStart_1700567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700567 prefixEnd_1700567 := by exact prefixLift 1700567
  have htrace : WordTrace (prefixWord ++ tailWord_1700567) baseStart_1700567 baseEnd_1700567 := by
    simpa [prefixWord, tailWord_1700567, baseEnd_1700567] using wordTrace_append hprefix tailTrace_1700567
  have hstable : (prefixWord ++ tailWord_1700567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700567).length < 2 ^ (prefixWord ++ tailWord_1700567).sum := by decide
  have hdescent : baseEnd_1700567 < baseStart_1700567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700581 : List Nat := [1, 3, 1, 4, 1, 2, 4, 5]
def baseStart_1700581 : Nat := 118140960795 + 1700581 * 2 ^ 59
def prefixEnd_1700581 : Nat := 4983230072969 + 3 ^ 40 * 1700581 * 2
def baseEnd_1700581 : Nat := 129365251096846844846915

theorem tailTrace_1700581 : CollatzResearch.WordTrace tailWord_1700581 prefixEnd_1700581 129365251096846844846915 := by
  unfold tailWord_1700581
  simp only [CollatzResearch.WordTrace]
  refine ⟨62025284652092947957109597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41350189768061965304739731 62025284652092947957109597)
  ·
    refine ⟨23259481744534855483916099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62025284652092947957109597 23259481744534855483916099)
    ·
      refine ⟨34889222616802283225874149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23259481744534855483916099 34889222616802283225874149)
      ·
        refine ⟨6541729240650428104851403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34889222616802283225874149 6541729240650428104851403)
        ·
          refine ⟨9812593860975642157277105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541729240650428104851403 9812593860975642157277105)
          ·
            refine ⟨7359445395731731617957829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9812593860975642157277105 7359445395731731617957829)
            ·
              refine ⟨1379896011699699678367093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7359445395731731617957829 1379896011699699678367093)
              ·
                refine ⟨129365251096846844846915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1379896011699699678367093 129365251096846844846915)
                ·
                  rfl

theorem cell21_1700581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 5].length) (baseStart_1700581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700581 prefixEnd_1700581 := by exact prefixLift 1700581
  have htrace : WordTrace (prefixWord ++ tailWord_1700581) baseStart_1700581 baseEnd_1700581 := by
    simpa [prefixWord, tailWord_1700581, baseEnd_1700581] using wordTrace_append hprefix tailTrace_1700581
  have hstable : (prefixWord ++ tailWord_1700581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700581).length < 2 ^ (prefixWord ++ tailWord_1700581).sum := by decide
  have hdescent : baseEnd_1700581 < baseStart_1700581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700640 : List Nat := [2, 1, 1, 5, 1, 2, 2, 7]
def baseStart_1700640 : Nat := 118140960795 + 1700640 * 2 ^ 59
def prefixEnd_1700640 : Nat := 4983230072969 + 3 ^ 40 * 1700640 * 2
def baseEnd_1700640 : Nat := 129369739298123181019097

theorem tailTrace_1700640 : CollatzResearch.WordTrace tailWord_1700640 prefixEnd_1700640 129369739298123181019097 := by
  unfold tailWord_1700640
  simp only [CollatzResearch.WordTrace]
  refine ⟨31013718279439600516753687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41351624372586134022338249 31013718279439600516753687)
  ·
    refine ⟨46520577419159400775130531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31013718279439600516753687 46520577419159400775130531)
    ·
      refine ⟨69780866128739101162695797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46520577419159400775130531 69780866128739101162695797)
      ·
        refine ⟨6541956199569290734002731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69780866128739101162695797 6541956199569290734002731)
        ·
          refine ⟨9812934299353936101004097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541956199569290734002731 9812934299353936101004097)
          ·
            refine ⟨7359700724515452075753073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9812934299353936101004097 7359700724515452075753073)
            ·
              refine ⟨5519775543386589056814805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7359700724515452075753073 5519775543386589056814805)
              ·
                refine ⟨129369739298123181019097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5519775543386589056814805 129369739298123181019097)
                ·
                  rfl

theorem cell21_1700640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_1700640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700640 prefixEnd_1700640 := by exact prefixLift 1700640
  have htrace : WordTrace (prefixWord ++ tailWord_1700640) baseStart_1700640 baseEnd_1700640 := by
    simpa [prefixWord, tailWord_1700640, baseEnd_1700640] using wordTrace_append hprefix tailTrace_1700640
  have hstable : (prefixWord ++ tailWord_1700640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700640).length < 2 ^ (prefixWord ++ tailWord_1700640).sum := by decide
  have hdescent : baseEnd_1700640 < baseStart_1700640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700660 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1700660 : Nat := 118140960795 + 1700660 * 2 ^ 59
def prefixEnd_1700660 : Nat := 4983230072969 + 3 ^ 40 * 1700660 * 2
def baseEnd_1700660 : Nat := 388113782166853952723917

theorem tailTrace_1700660 : CollatzResearch.WordTrace tailWord_1700660 prefixEnd_1700660 388113782166853952723917 := by
  unfold tailWord_1700660
  simp only [CollatzResearch.WordTrace]
  refine ⟨31014083009403372224617717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41352110679204496299490289 31014083009403372224617717)
  ·
    refine ⟨2907570282131566146057911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31014083009403372224617717 2907570282131566146057911)
    ·
      refine ⟨4361355423197349219086867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907570282131566146057911 4361355423197349219086867)
      ·
        refine ⟨6542033134796023828630301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361355423197349219086867 6542033134796023828630301)
        ·
          refine ⟨2453262425548508935736363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6542033134796023828630301 2453262425548508935736363)
          ·
            refine ⟨3679893638322763403604545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453262425548508935736363 3679893638322763403604545)
            ·
              refine ⟨2759920228742072552703409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3679893638322763403604545 2759920228742072552703409)
              ·
                refine ⟨2069940171556554414527557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759920228742072552703409 2069940171556554414527557)
                ·
                  refine ⟨388113782166853952723917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2069940171556554414527557 388113782166853952723917)
                  ·
                    rfl

theorem cell21_1700660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1700660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700660 prefixEnd_1700660 := by exact prefixLift 1700660
  have htrace : WordTrace (prefixWord ++ tailWord_1700660) baseStart_1700660 baseEnd_1700660 := by
    simpa [prefixWord, tailWord_1700660, baseEnd_1700660] using wordTrace_append hprefix tailTrace_1700660
  have hstable : (prefixWord ++ tailWord_1700660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700660).length < 2 ^ (prefixWord ++ tailWord_1700660).sum := by decide
  have hdescent : baseEnd_1700660 < baseStart_1700660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700792 : List Nat := [2, 1, 2, 1, 2, 5, 2, 6]
def baseStart_1700792 : Nat := 118140960795 + 1700792 * 2 ^ 59
def prefixEnd_1700792 : Nat := 4983230072969 + 3 ^ 40 * 1700792 * 2
def baseEnd_1700792 : Nat := 129381302121750352174549

theorem tailTrace_1700792 : CollatzResearch.WordTrace tailWord_1700792 prefixEnd_1700792 129381302121750352174549 := by
  unfold tailWord_1700792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31016490227164265496520315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41355320302885687328693753 31016490227164265496520315)
  ·
    refine ⟨46524735340746398244780473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31016490227164265496520315 46524735340746398244780473)
    ·
      refine ⟨34893551505559798683585355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46524735340746398244780473 34893551505559798683585355)
      ·
        refine ⟨52340327258339698025378033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34893551505559798683585355 52340327258339698025378033)
        ·
          refine ⟨39255245443754773519033525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52340327258339698025378033 39255245443754773519033525)
          ·
            refine ⟨3680179260352010017409393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39255245443754773519033525 3680179260352010017409393)
            ·
              refine ⟨2760134445264007513057045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680179260352010017409393 2760134445264007513057045)
              ·
                refine ⟨129381302121750352174549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2760134445264007513057045 129381302121750352174549)
                ·
                  rfl

theorem cell21_1700792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_1700792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700792 prefixEnd_1700792 := by exact prefixLift 1700792
  have htrace : WordTrace (prefixWord ++ tailWord_1700792) baseStart_1700792 baseEnd_1700792 := by
    simpa [prefixWord, tailWord_1700792, baseEnd_1700792] using wordTrace_append hprefix tailTrace_1700792
  have hstable : (prefixWord ++ tailWord_1700792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700792).length < 2 ^ (prefixWord ++ tailWord_1700792).sum := by decide
  have hdescent : baseEnd_1700792 < baseStart_1700792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700899 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 5]
def baseStart_1700899 : Nat := 118140960795 + 1700899 * 2 ^ 59
def prefixEnd_1700899 : Nat := 4983230072969 + 3 ^ 40 * 1700899 * 2
def baseEnd_1700899 : Nat := 388168325223042648240095

theorem tailTrace_1700899 : CollatzResearch.WordTrace tailWord_1700899 prefixEnd_1700899 388168325223042648240095 := by
  unfold tailWord_1700899
  simp only [CollatzResearch.WordTrace]
  refine ⟨62036883064940888267185751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41357922043293925511457167 62036883064940888267185751)
  ·
    refine ⟨93055324597411332400778627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62036883064940888267185751 93055324597411332400778627)
    ·
      refine ⟨139582986896116998601167941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93055324597411332400778627 139582986896116998601167941)
      ·
        refine ⟨26171810043021937237718989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139582986896116998601167941 26171810043021937237718989)
        ·
          refine ⟨9814428766133226464144621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26171810043021937237718989 9814428766133226464144621)
          ·
            refine ⟨3680410787299959924054233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9814428766133226464144621 3680410787299959924054233)
            ·
              refine ⟨2760308090474969943040675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680410787299959924054233 2760308090474969943040675)
              ·
                refine ⟨4140462135712454914561013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760308090474969943040675 4140462135712454914561013)
                ·
                  refine ⟨388168325223042648240095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4140462135712454914561013 388168325223042648240095)
                  ·
                    rfl

theorem cell21_1700899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_1700899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700899 prefixEnd_1700899 := by exact prefixLift 1700899
  have htrace : WordTrace (prefixWord ++ tailWord_1700899) baseStart_1700899 baseEnd_1700899 := by
    simpa [prefixWord, tailWord_1700899, baseEnd_1700899] using wordTrace_append hprefix tailTrace_1700899
  have hstable : (prefixWord ++ tailWord_1700899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700899).length < 2 ^ (prefixWord ++ tailWord_1700899).sum := by decide
  have hdescent : baseEnd_1700899 < baseStart_1700899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700916 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1700916 : Nat := 118140960795 + 1700916 * 2 ^ 59
def prefixEnd_1700916 : Nat := 4983230072969 + 3 ^ 40 * 1700916 * 2
def baseEnd_1700916 : Nat := 388172204854654396456727

theorem tailTrace_1700916 : CollatzResearch.WordTrace tailWord_1700916 prefixEnd_1700916 388172204854654396456727 := by
  unfold tailWord_1700916
  simp only [CollatzResearch.WordTrace]
  refine ⟨31018751552939650085277301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41358335403919533447036401 31018751552939650085277301)
  ·
    refine ⟨2908007958088092195494747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31018751552939650085277301 2908007958088092195494747)
    ·
      refine ⟨4362011937132138293242121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908007958088092195494747 4362011937132138293242121)
      ·
        refine ⟨3271508952849103719931591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4362011937132138293242121 3271508952849103719931591)
        ·
          refine ⟨4907263429273655579897387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271508952849103719931591 4907263429273655579897387)
          ·
            refine ⟨7360895143910483369846081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907263429273655579897387 7360895143910483369846081)
            ·
              refine ⟨5520671357932862527384561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360895143910483369846081 5520671357932862527384561)
              ·
                refine ⟨4140503518449646895538421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520671357932862527384561 4140503518449646895538421)
                ·
                  refine ⟨388172204854654396456727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4140503518449646895538421 388172204854654396456727)
                  ·
                    rfl

theorem cell21_1700916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1700916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700916 prefixEnd_1700916 := by exact prefixLift 1700916
  have htrace : WordTrace (prefixWord ++ tailWord_1700916) baseStart_1700916 baseEnd_1700916 := by
    simpa [prefixWord, tailWord_1700916, baseEnd_1700916] using wordTrace_append hprefix tailTrace_1700916
  have hstable : (prefixWord ++ tailWord_1700916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700916).length < 2 ^ (prefixWord ++ tailWord_1700916).sum := by decide
  have hdescent : baseEnd_1700916 < baseStart_1700916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1700950 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1700950 : Nat := 118140960795 + 1700950 * 2 ^ 59
def prefixEnd_1700950 : Nat := 4983230072969 + 3 ^ 40 * 1700950 * 2
def baseEnd_1700950 : Nat := 388179964117877892889991

theorem tailTrace_1700950 : CollatzResearch.WordTrace tailWord_1700950 prefixEnd_1700950 388179964117877892889991 := by
  unfold tailWord_1700950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3877421449234757748580769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41359162125170749318194869 3877421449234757748580769)
  ·
    refine ⟨2908066086926068311435577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3877421449234757748580769 2908066086926068311435577)
    ·
      refine ⟨2181049565194551233576683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2908066086926068311435577 2181049565194551233576683)
      ·
        refine ⟨3271574347791826850365025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181049565194551233576683 3271574347791826850365025)
        ·
          refine ⟨2453680760843870137773769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3271574347791826850365025 2453680760843870137773769)
          ·
            refine ⟨1840260570632902603330327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2453680760843870137773769 1840260570632902603330327)
            ·
              refine ⟨2760390855949353904995491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840260570632902603330327 2760390855949353904995491)
              ·
                refine ⟨4140586283924030857493237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760390855949353904995491 4140586283924030857493237)
                ·
                  refine ⟨388179964117877892889991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4140586283924030857493237 388179964117877892889991)
                  ·
                    rfl

theorem cell21_1700950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1700950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1700950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1700950 prefixEnd_1700950 := by exact prefixLift 1700950
  have htrace : WordTrace (prefixWord ++ tailWord_1700950) baseStart_1700950 baseEnd_1700950 := by
    simpa [prefixWord, tailWord_1700950, baseEnd_1700950] using wordTrace_append hprefix tailTrace_1700950
  have hstable : (prefixWord ++ tailWord_1700950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1700950).length < 2 ^ (prefixWord ++ tailWord_1700950).sum := by decide
  have hdescent : baseEnd_1700950 < baseStart_1700950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1700950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701006 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1701006 : Nat := 118140960795 + 1701006 * 2 ^ 59
def prefixEnd_1701006 : Nat := 4983230072969 + 3 ^ 40 * 1701006 * 2
def baseEnd_1701006 : Nat := 388192744080834239956543

theorem tailTrace_1701006 : CollatzResearch.WordTrace tailWord_1701006 prefixEnd_1701006 388192744080834239956543 := by
  unfold tailWord_1701006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755098209444155692666359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41360523783702163694220581 7755098209444155692666359)
  ·
    refine ⟨11632647314166233538999539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7755098209444155692666359 11632647314166233538999539)
    ·
      refine ⟨17448970971249350308499309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11632647314166233538999539 17448970971249350308499309)
      ·
        refine ⟨6543364114218506365687241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17448970971249350308499309 6543364114218506365687241)
        ·
          refine ⟨4907523085663879774265431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6543364114218506365687241 4907523085663879774265431)
          ·
            refine ⟨7361284628495819661398147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907523085663879774265431 7361284628495819661398147)
            ·
              refine ⟨11041926942743729492097221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361284628495819661398147 11041926942743729492097221)
              ·
                refine ⟨2070361301764449279768229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11041926942743729492097221 2070361301764449279768229)
                ·
                  refine ⟨388192744080834239956543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2070361301764449279768229 388192744080834239956543)
                  ·
                    rfl

theorem cell21_1701006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1701006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701006 prefixEnd_1701006 := by exact prefixLift 1701006
  have htrace : WordTrace (prefixWord ++ tailWord_1701006) baseStart_1701006 baseEnd_1701006 := by
    simpa [prefixWord, tailWord_1701006, baseEnd_1701006] using wordTrace_append hprefix tailTrace_1701006
  have hstable : (prefixWord ++ tailWord_1701006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701006).length < 2 ^ (prefixWord ++ tailWord_1701006).sum := by decide
  have hdescent : baseEnd_1701006 < baseStart_1701006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701020 : List Nat := [2, 2, 3, 2, 1, 2, 3, 6]
def baseStart_1701020 : Nat := 118140960795 + 1701020 * 2 ^ 59
def prefixEnd_1701020 : Nat := 4983230072969 + 3 ^ 40 * 1701020 * 2
def baseEnd_1701020 : Nat := 129398646357191108907727

theorem tailTrace_1701020 : CollatzResearch.WordTrace tailWord_1701020 prefixEnd_1701020 129398646357191108907727 := by
  unfold tailWord_1701020
  simp only [CollatzResearch.WordTrace]
  refine ⟨31020648148751262966170257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41360864198335017288227009 31020648148751262966170257)
  ·
    refine ⟨23265486111563447224627693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31020648148751262966170257 23265486111563447224627693)
    ·
      refine ⟨8724557291836292709235385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23265486111563447224627693 8724557291836292709235385)
      ·
        refine ⟨6543417968877219531926539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8724557291836292709235385 6543417968877219531926539)
        ·
          refine ⟨9815126953315829297889809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543417968877219531926539 9815126953315829297889809)
          ·
            refine ⟨7361345214986871973417357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9815126953315829297889809 7361345214986871973417357)
            ·
              refine ⟨2760504455620076990031509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7361345214986871973417357 2760504455620076990031509)
              ·
                refine ⟨129398646357191108907727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2760504455620076990031509 129398646357191108907727)
                ·
                  rfl

theorem cell21_1701020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_1701020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701020 prefixEnd_1701020 := by exact prefixLift 1701020
  have htrace : WordTrace (prefixWord ++ tailWord_1701020) baseStart_1701020 baseEnd_1701020 := by
    simpa [prefixWord, tailWord_1701020, baseEnd_1701020] using wordTrace_append hprefix tailTrace_1701020
  have hstable : (prefixWord ++ tailWord_1701020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701020).length < 2 ^ (prefixWord ++ tailWord_1701020).sum := by decide
  have hdescent : baseEnd_1701020 < baseStart_1701020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701155 : List Nat := [1, 1, 1, 4, 2, 3, 2, 7]
def baseStart_1701155 : Nat := 118140960795 + 1701155 * 2 ^ 59
def prefixEnd_1701155 : Nat := 4983230072969 + 3 ^ 40 * 1701155 * 2
def baseEnd_1701155 : Nat := 129408915970281030657635

theorem tailTrace_1701155 : CollatzResearch.WordTrace tailWord_1701155 prefixEnd_1701155 129408915970281030657635 := by
  unfold tailWord_1701155
  simp only [CollatzResearch.WordTrace]
  refine ⟨62046220152013443988504919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41364146768008962659003279 62046220152013443988504919)
  ·
    refine ⟨93069330228020165982757379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62046220152013443988504919 93069330228020165982757379)
    ·
      refine ⟨139603995342030248974136069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93069330228020165982757379 139603995342030248974136069)
      ·
        refine ⟨26175749126630671682650513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139603995342030248974136069 26175749126630671682650513)
        ·
          refine ⟨19631811844973003761987885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26175749126630671682650513 19631811844973003761987885)
          ·
            refine ⟨7361929441864876410745457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19631811844973003761987885 7361929441864876410745457)
            ·
              refine ⟨5521447081398657308059093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7361929441864876410745457 5521447081398657308059093)
              ·
                refine ⟨129408915970281030657635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5521447081398657308059093 129408915970281030657635)
                ·
                  rfl

theorem cell21_1701155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_1701155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701155 prefixEnd_1701155 := by exact prefixLift 1701155
  have htrace : WordTrace (prefixWord ++ tailWord_1701155) baseStart_1701155 baseEnd_1701155 := by
    simpa [prefixWord, tailWord_1701155, baseEnd_1701155] using wordTrace_append hprefix tailTrace_1701155
  have hstable : (prefixWord ++ tailWord_1701155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701155).length < 2 ^ (prefixWord ++ tailWord_1701155).sum := by decide
  have hdescent : baseEnd_1701155 < baseStart_1701155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701220 : List Nat := [2, 3, 1, 1, 3, 3, 2, 3, 3]
def baseStart_1701220 : Nat := 118140960795 + 1701220 * 2 ^ 59
def prefixEnd_1701220 : Nat := 4983230072969 + 3 ^ 40 * 1701220 * 2
def baseEnd_1701220 : Nat := 388241581796417423389439

theorem tailTrace_1701220 : CollatzResearch.WordTrace tailWord_1701220 prefixEnd_1701220 388241581796417423389439 := by
  unfold tailWord_1701220
  simp only [CollatzResearch.WordTrace]
  refine ⟨31024295448388980044810557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41365727264518640059747409 31024295448388980044810557)
  ·
    refine ⟨11634110793145867516803959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31024295448388980044810557 11634110793145867516803959)
    ·
      refine ⟨17451166189718801275205939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11634110793145867516803959 17451166189718801275205939)
      ·
        refine ⟨26176749284578201912808909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17451166189718801275205939 26176749284578201912808909)
        ·
          refine ⟨9816280981716825717303341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26176749284578201912808909 9816280981716825717303341)
          ·
            refine ⟨3681105368143809643988753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9816280981716825717303341 3681105368143809643988753)
            ·
              refine ⟨2760829026107857232991565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3681105368143809643988753 2760829026107857232991565)
              ·
                refine ⟨1035310884790446462371837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2760829026107857232991565 1035310884790446462371837)
                ·
                  refine ⟨388241581796417423389439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035310884790446462371837 388241581796417423389439)
                  ·
                    rfl

theorem cell21_1701220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_1701220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701220 prefixEnd_1701220 := by exact prefixLift 1701220
  have htrace : WordTrace (prefixWord ++ tailWord_1701220) baseStart_1701220 baseEnd_1701220 := by
    simpa [prefixWord, tailWord_1701220, baseEnd_1701220] using wordTrace_append hprefix tailTrace_1701220
  have hstable : (prefixWord ++ tailWord_1701220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701220).length < 2 ^ (prefixWord ++ tailWord_1701220).sum := by decide
  have hdescent : baseEnd_1701220 < baseStart_1701220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701321 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 7]
def baseStart_1701321 : Nat := 118140960795 + 1701321 * 2 ^ 59
def prefixEnd_1701321 : Nat := 4983230072969 + 3 ^ 40 * 1701321 * 2
def baseEnd_1701321 : Nat := 388264631372463692205899

theorem tailTrace_1701321 : CollatzResearch.WordTrace tailWord_1701321 prefixEnd_1701321 388264631372463692205899 := by
  unfold tailWord_1701321
  simp only [CollatzResearch.WordTrace]
  refine ⟨62052274669412054339047817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41368183112941369559365211 62052274669412054339047817)
  ·
    refine ⟨46539206002059040754285863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62052274669412054339047817 46539206002059040754285863)
    ·
      refine ⟨69808809003088561131428795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46539206002059040754285863 69808809003088561131428795)
      ·
        refine ⟨104713213504632841697143193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69808809003088561131428795 104713213504632841697143193)
        ·
          refine ⟨78534910128474631272857395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104713213504632841697143193 78534910128474631272857395)
          ·
            refine ⟨117802365192711946909286093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78534910128474631272857395 117802365192711946909286093)
            ·
              refine ⟨44175886947266980090982285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117802365192711946909286093 44175886947266980090982285)
              ·
                refine ⟨16565957605225117534118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44175886947266980090982285 16565957605225117534118357)
                ·
                  refine ⟨388264631372463692205899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16565957605225117534118357 388264631372463692205899)
                  ·
                    rfl

theorem cell21_1701321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_1701321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701321 prefixEnd_1701321 := by exact prefixLift 1701321
  have htrace : WordTrace (prefixWord ++ tailWord_1701321) baseStart_1701321 baseEnd_1701321 := by
    simpa [prefixWord, tailWord_1701321, baseEnd_1701321] using wordTrace_append hprefix tailTrace_1701321
  have hstable : (prefixWord ++ tailWord_1701321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701321).length < 2 ^ (prefixWord ++ tailWord_1701321).sum := by decide
  have hdescent : baseEnd_1701321 < baseStart_1701321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701406 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1701406 : Nat := 118140960795 + 1701406 * 2 ^ 59
def prefixEnd_1701406 : Nat := 4983230072969 + 3 ^ 40 * 1701406 * 2
def baseEnd_1701406 : Nat := 388284029530522433289059

theorem tailTrace_1701406 : CollatzResearch.WordTrace tailWord_1701406 prefixEnd_1701406 388284029530522433289059 := by
  unfold tailWord_1701406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756921859263014231986509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41370249916069409237261381 7756921859263014231986509)
  ·
    refine ⟨2908845697223630336994941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7756921859263014231986509 2908845697223630336994941)
    ·
      refine ⟨1090817136458861376373103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2908845697223630336994941 1090817136458861376373103)
      ·
        refine ⟨1636225704688292064559655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090817136458861376373103 1636225704688292064559655)
        ·
          refine ⟨2454338557032438096839483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636225704688292064559655 2454338557032438096839483)
          ·
            refine ⟨3681507835548657145259225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454338557032438096839483 3681507835548657145259225)
            ·
              refine ⟨2761130876661492858944419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3681507835548657145259225 2761130876661492858944419)
              ·
                refine ⟨4141696314992239288416629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761130876661492858944419 4141696314992239288416629)
                ·
                  refine ⟨388284029530522433289059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4141696314992239288416629 388284029530522433289059)
                  ·
                    rfl

theorem cell21_1701406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1701406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701406 prefixEnd_1701406 := by exact prefixLift 1701406
  have htrace : WordTrace (prefixWord ++ tailWord_1701406) baseStart_1701406 baseEnd_1701406 := by
    simpa [prefixWord, tailWord_1701406, baseEnd_1701406] using wordTrace_append hprefix tailTrace_1701406
  have hstable : (prefixWord ++ tailWord_1701406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701406).length < 2 ^ (prefixWord ++ tailWord_1701406).sum := by decide
  have hdescent : baseEnd_1701406 < baseStart_1701406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701611 : List Nat := [1, 1, 1, 1, 2, 4, 6, 5]
def baseStart_1701611 : Nat := 118140960795 + 1701611 * 2 ^ 59
def prefixEnd_1701611 : Nat := 4983230072969 + 3 ^ 40 * 1701611 * 2
def baseEnd_1701611 : Nat := 129443604441162544123991

theorem tailTrace_1701611 : CollatzResearch.WordTrace tailWord_1701611 prefixEnd_1701611 129443604441162544123991 := by
  unfold tailWord_1701611
  simp only [CollatzResearch.WordTrace]
  refine ⟨62062851838361433867104687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41375234558907622578069791 62062851838361433867104687)
  ·
    refine ⟨93094277757542150800657031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62062851838361433867104687 93094277757542150800657031)
    ·
      refine ⟨139641416636313226200985547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93094277757542150800657031 139641416636313226200985547)
      ·
        refine ⟨209462124954469839301478321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139641416636313226200985547 209462124954469839301478321)
        ·
          refine ⟨157096593715852379476108741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209462124954469839301478321 157096593715852379476108741)
          ·
            refine ⟨29455611321722321151770389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157096593715852379476108741 29455611321722321151770389)
            ·
              refine ⟨1380731780705733803989237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29455611321722321151770389 1380731780705733803989237)
              ·
                refine ⟨129443604441162544123991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1380731780705733803989237 129443604441162544123991)
                ·
                  rfl

theorem cell21_1701611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 5].length) (baseStart_1701611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701611 prefixEnd_1701611 := by exact prefixLift 1701611
  have htrace : WordTrace (prefixWord ++ tailWord_1701611) baseStart_1701611 baseEnd_1701611 := by
    simpa [prefixWord, tailWord_1701611, baseEnd_1701611] using wordTrace_append hprefix tailTrace_1701611
  have hstable : (prefixWord ++ tailWord_1701611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701611).length < 2 ^ (prefixWord ++ tailWord_1701611).sum := by decide
  have hdescent : baseEnd_1701611 < baseStart_1701611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701642 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1701642 : Nat := 118140960795 + 1701642 * 2 ^ 59
def prefixEnd_1701642 : Nat := 4983230072969 + 3 ^ 40 * 1701642 * 2
def baseEnd_1701642 : Nat := 388337887945838467355243

theorem tailTrace_1701642 : CollatzResearch.WordTrace tailWord_1701642 prefixEnd_1701642 388337887945838467355243 := by
  unfold tailWord_1701642
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515995625312281540370795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41375988334166084107655453 15515995625312281540370795)
  ·
    refine ⟨23273993437968422310556193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15515995625312281540370795 23273993437968422310556193)
    ·
      refine ⟨17455495078476316732917145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23273993437968422310556193 17455495078476316732917145)
      ·
        refine ⟨13091621308857237549687859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17455495078476316732917145 13091621308857237549687859)
        ·
          refine ⟨19637431963285856324531789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13091621308857237549687859 19637431963285856324531789)
          ·
            refine ⟨7364036986232196121699421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19637431963285856324531789 7364036986232196121699421)
            ·
              refine ⟨2761513869837073545637283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7364036986232196121699421 2761513869837073545637283)
              ·
                refine ⟨4142270804755610318455925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761513869837073545637283 4142270804755610318455925)
                ·
                  refine ⟨388337887945838467355243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4142270804755610318455925 388337887945838467355243)
                  ·
                    rfl

theorem cell21_1701642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1701642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701642 prefixEnd_1701642 := by exact prefixLift 1701642
  have htrace : WordTrace (prefixWord ++ tailWord_1701642) baseStart_1701642 baseEnd_1701642 := by
    simpa [prefixWord, tailWord_1701642, baseEnd_1701642] using wordTrace_append hprefix tailTrace_1701642
  have hstable : (prefixWord ++ tailWord_1701642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701642).length < 2 ^ (prefixWord ++ tailWord_1701642).sum := by decide
  have hdescent : baseEnd_1701642 < baseStart_1701642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701693 : List Nat := [1, 4, 1, 4, 1, 3, 2, 2, 3]
def baseStart_1701693 : Nat := 118140960795 + 1701693 * 2 ^ 59
def prefixEnd_1701693 : Nat := 4983230072969 + 3 ^ 40 * 1701693 * 2
def baseEnd_1701693 : Nat := 388349526840673712005139

theorem tailTrace_1701693 : CollatzResearch.WordTrace tailWord_1701693 prefixEnd_1701693 388349526840673712005139 := by
  unfold tailWord_1701693
  simp only [CollatzResearch.WordTrace]
  refine ⟨62065842624064361871589733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41377228416042907914393155 62065842624064361871589733)
  ·
    refine ⟨11637345492012067850923075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62065842624064361871589733 11637345492012067850923075)
    ·
      refine ⟨17456018238018101776384613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11637345492012067850923075 17456018238018101776384613)
      ·
        refine ⟨3273003419628394083072115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17456018238018101776384613 3273003419628394083072115)
        ·
          refine ⟨4909505129442591124608173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273003419628394083072115 4909505129442591124608173)
          ·
            refine ⟨1841064423540971671728065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4909505129442591124608173 1841064423540971671728065)
            ·
              refine ⟨1380798317655728753796049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841064423540971671728065 1380798317655728753796049)
              ·
                refine ⟨1035598738241796565347037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380798317655728753796049 1035598738241796565347037)
                ·
                  refine ⟨388349526840673712005139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035598738241796565347037 388349526840673712005139)
                  ·
                    rfl

theorem cell21_1701693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_1701693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701693 prefixEnd_1701693 := by exact prefixLift 1701693
  have htrace : WordTrace (prefixWord ++ tailWord_1701693) baseStart_1701693 baseEnd_1701693 := by
    simpa [prefixWord, tailWord_1701693, baseEnd_1701693] using wordTrace_append hprefix tailTrace_1701693
  have hstable : (prefixWord ++ tailWord_1701693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701693).length < 2 ^ (prefixWord ++ tailWord_1701693).sum := by decide
  have hdescent : baseEnd_1701693 < baseStart_1701693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701701 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1701701 : Nat := 118140960795 + 1701701 * 2 ^ 59
def prefixEnd_1701701 : Nat := 4983230072969 + 3 ^ 40 * 1701701 * 2
def baseEnd_1701701 : Nat := 388351352549667475871789

theorem tailTrace_1701701 : CollatzResearch.WordTrace tailWord_1701701 prefixEnd_1701701 388351352549667475871789 := by
  unfold tailWord_1701701
  simp only [CollatzResearch.WordTrace]
  refine ⟨62066134408035379237880957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41377422938690252825253971 62066134408035379237880957)
  ·
    refine ⟨23274800403013267214205359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62066134408035379237880957 23274800403013267214205359)
    ·
      refine ⟨34912200604519900821308039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23274800403013267214205359 34912200604519900821308039)
      ·
        refine ⟨52368300906779851231962059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34912200604519900821308039 52368300906779851231962059)
        ·
          refine ⟨78552451360169776847943089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52368300906779851231962059 78552451360169776847943089)
          ·
            refine ⟨58914338520127332635957317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78552451360169776847943089 58914338520127332635957317)
            ·
              refine ⟨11046438472523874869241997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58914338520127332635957317 11046438472523874869241997)
              ·
                refine ⟨4142414427196453075965749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11046438472523874869241997 4142414427196453075965749)
                ·
                  refine ⟨388351352549667475871789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4142414427196453075965749 388351352549667475871789)
                  ·
                    rfl

theorem cell21_1701701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1701701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701701 prefixEnd_1701701 := by exact prefixLift 1701701
  have htrace : WordTrace (prefixWord ++ tailWord_1701701) baseStart_1701701 baseEnd_1701701 := by
    simpa [prefixWord, tailWord_1701701, baseEnd_1701701] using wordTrace_append hprefix tailTrace_1701701
  have hstable : (prefixWord ++ tailWord_1701701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701701).length < 2 ^ (prefixWord ++ tailWord_1701701).sum := by decide
  have hdescent : baseEnd_1701701 < baseStart_1701701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701715 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 10]
def baseStart_1701715 : Nat := 118140960795 + 1701715 * 2 ^ 59
def prefixEnd_1701715 : Nat := 4983230072969 + 3 ^ 40 * 1701715 * 2
def baseEnd_1701715 : Nat := 388354547540406562638427

theorem tailTrace_1701715 : CollatzResearch.WordTrace tailWord_1701715 prefixEnd_1701715 388354547540406562638427 := by
  unfold tailWord_1701715
  simp only [CollatzResearch.WordTrace]
  refine ⟨62066645029984659628890599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41377763353323106419260399 62066645029984659628890599)
  ·
    refine ⟨93099967544976989443335899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62066645029984659628890599 93099967544976989443335899)
    ·
      refine ⟨139649951317465484165003849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93099967544976989443335899 139649951317465484165003849)
      ·
        refine ⟨104737463488099113123752887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139649951317465484165003849 104737463488099113123752887)
        ·
          refine ⟨157106195232148669685629331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104737463488099113123752887 157106195232148669685629331)
          ·
            refine ⟨235659292848223004528443997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157106195232148669685629331 235659292848223004528443997)
            ·
              refine ⟨88372234818083626698166499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235659292848223004528443997 88372234818083626698166499)
              ·
                refine ⟨132558352227125440047249749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88372234818083626698166499 132558352227125440047249749)
                ·
                  refine ⟨388354547540406562638427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132558352227125440047249749 388354547540406562638427)
                  ·
                    rfl

theorem cell21_1701715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_1701715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701715 prefixEnd_1701715 := by exact prefixLift 1701715
  have htrace : WordTrace (prefixWord ++ tailWord_1701715) baseStart_1701715 baseEnd_1701715 := by
    simpa [prefixWord, tailWord_1701715, baseEnd_1701715] using wordTrace_append hprefix tailTrace_1701715
  have hstable : (prefixWord ++ tailWord_1701715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701715).length < 2 ^ (prefixWord ++ tailWord_1701715).sum := by decide
  have hdescent : baseEnd_1701715 < baseStart_1701715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701735 : List Nat := [1, 1, 5, 1, 2, 1, 4, 3, 3]
def baseStart_1701735 : Nat := 118140960795 + 1701735 * 2 ^ 59
def prefixEnd_1701735 : Nat := 4983230072969 + 3 ^ 40 * 1701735 * 2
def baseEnd_1701735 : Nat := 388359111812890972305053

theorem tailTrace_1701735 : CollatzResearch.WordTrace tailWord_1701735 prefixEnd_1701735 388359111812890972305053 := by
  unfold tailWord_1701735
  simp only [CollatzResearch.WordTrace]
  refine ⟨62067374489912203044618659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41378249659941468696412439 62067374489912203044618659)
  ·
    refine ⟨93101061734868304566927989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62067374489912203044618659 93101061734868304566927989)
    ·
      refine ⟨8728224537643903553149499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93101061734868304566927989 8728224537643903553149499)
      ·
        refine ⟨13092336806465855329724249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8728224537643903553149499 13092336806465855329724249)
        ·
          refine ⟨9819252604849391497293187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13092336806465855329724249 9819252604849391497293187)
          ·
            refine ⟨14728878907274087245939781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9819252604849391497293187 14728878907274087245939781)
            ·
              refine ⟨2761664795113891358613709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14728878907274087245939781 2761664795113891358613709)
              ·
                refine ⟨1035624298167709259480141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2761664795113891358613709 1035624298167709259480141)
                ·
                  refine ⟨388359111812890972305053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035624298167709259480141 388359111812890972305053)
                  ·
                    rfl

theorem cell21_1701735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 3].length) (baseStart_1701735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701735 prefixEnd_1701735 := by exact prefixLift 1701735
  have htrace : WordTrace (prefixWord ++ tailWord_1701735) baseStart_1701735 baseEnd_1701735 := by
    simpa [prefixWord, tailWord_1701735, baseEnd_1701735] using wordTrace_append hprefix tailTrace_1701735
  have hstable : (prefixWord ++ tailWord_1701735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701735).length < 2 ^ (prefixWord ++ tailWord_1701735).sum := by decide
  have hdescent : baseEnd_1701735 < baseStart_1701735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701777 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 5]
def baseStart_1701777 : Nat := 118140960795 + 1701777 * 2 ^ 59
def prefixEnd_1701777 : Nat := 4983230072969 + 3 ^ 40 * 1701777 * 2
def baseEnd_1701777 : Nat := 388368696785108232604967

theorem tailTrace_1701777 : CollatzResearch.WordTrace tailWord_1701777 prefixEnd_1701777 388368696785108232604967 := by
  unfold tailWord_1701777
  simp only [CollatzResearch.WordTrace]
  refine ⟨62068906355760044217647585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41379270903840029478431723 62068906355760044217647585)
  ·
    refine ⟨46551679766820033163235689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62068906355760044217647585 46551679766820033163235689)
    ·
      refine ⟨34913759825115024872426767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46551679766820033163235689 34913759825115024872426767)
      ·
        refine ⟨52370639737672537308640151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34913759825115024872426767 52370639737672537308640151)
        ·
          refine ⟨78555959606508805962960227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52370639737672537308640151 78555959606508805962960227)
          ·
            refine ⟨117833939409763208944440341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78555959606508805962960227 117833939409763208944440341)
            ·
              refine ⟨5523465909832650419270641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117833939409763208944440341 5523465909832650419270641)
              ·
                refine ⟨4142599432374487814452981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523465909832650419270641 4142599432374487814452981)
                ·
                  refine ⟨388368696785108232604967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4142599432374487814452981 388368696785108232604967)
                  ·
                    rfl

theorem cell21_1701777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_1701777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701777 prefixEnd_1701777 := by exact prefixLift 1701777
  have htrace : WordTrace (prefixWord ++ tailWord_1701777) baseStart_1701777 baseEnd_1701777 := by
    simpa [prefixWord, tailWord_1701777, baseEnd_1701777] using wordTrace_append hprefix tailTrace_1701777
  have hstable : (prefixWord ++ tailWord_1701777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701777).length < 2 ^ (prefixWord ++ tailWord_1701777).sum := by decide
  have hdescent : baseEnd_1701777 < baseStart_1701777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701780 : List Nat := [2, 4, 2, 1, 1, 2, 4, 5]
def baseStart_1701780 : Nat := 118140960795 + 1701780 * 2 ^ 59
def prefixEnd_1701780 : Nat := 4983230072969 + 3 ^ 40 * 1701780 * 2
def baseEnd_1701780 : Nat := 129456460475326964684987

theorem tailTrace_1701780 : CollatzResearch.WordTrace tailWord_1701780 prefixEnd_1701780 129456460475326964684987 := by
  unfold tailWord_1701780
  simp only [CollatzResearch.WordTrace]
  refine ⟨31034507887374587865003397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41379343849832783820004529 31034507887374587865003397)
  ·
    refine ⟨5818970228882735224688137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31034507887374587865003397 5818970228882735224688137)
    ·
      refine ⟨4364227671662051418516103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5818970228882735224688137 4364227671662051418516103)
      ·
        refine ⟨6546341507493077127774155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364227671662051418516103 6546341507493077127774155)
        ·
          refine ⟨9819512261239615691661233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6546341507493077127774155 9819512261239615691661233)
          ·
            refine ⟨7364634195929711768745925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9819512261239615691661233 7364634195929711768745925)
            ·
              refine ⟨1380868911736820956639861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7364634195929711768745925 1380868911736820956639861)
              ·
                refine ⟨129456460475326964684987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1380868911736820956639861 129456460475326964684987)
                ·
                  rfl

theorem cell21_1701780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_1701780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701780 prefixEnd_1701780 := by exact prefixLift 1701780
  have htrace : WordTrace (prefixWord ++ tailWord_1701780) baseStart_1701780 baseEnd_1701780 := by
    simpa [prefixWord, tailWord_1701780, baseEnd_1701780] using wordTrace_append hprefix tailTrace_1701780
  have hstable : (prefixWord ++ tailWord_1701780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701780).length < 2 ^ (prefixWord ++ tailWord_1701780).sum := by decide
  have hdescent : baseEnd_1701780 < baseStart_1701780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701811 : List Nat := [1, 1, 1, 2, 3, 1, 7, 2, 3]
def baseStart_1701811 : Nat := 118140960795 + 1701811 * 2 ^ 59
def prefixEnd_1701811 : Nat := 4983230072969 + 3 ^ 40 * 1701811 * 2
def baseEnd_1701811 : Nat := 388376456048331729038231

theorem tailTrace_1701811 : CollatzResearch.WordTrace tailWord_1701811 prefixEnd_1701811 388376456048331729038231 := by
  unfold tailWord_1701811
  simp only [CollatzResearch.WordTrace]
  refine ⟨62070146437636868024385287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41380097625091245349590191 62070146437636868024385287)
  ·
    refine ⟨93105219656455302036577931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62070146437636868024385287 93105219656455302036577931)
    ·
      refine ⟨139657829484682953054866897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93105219656455302036577931 139657829484682953054866897)
      ·
        refine ⟨104743372113512214791150173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139657829484682953054866897 104743372113512214791150173)
        ·
          refine ⟨39278764542567080546681315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104743372113512214791150173 39278764542567080546681315)
          ·
            refine ⟨58918146813850620820021973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39278764542567080546681315 58918146813850620820021973)
            ·
              refine ⟨1380894065949623925469265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58918146813850620820021973 1380894065949623925469265)
              ·
                refine ⟨1035670549462217944101949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1380894065949623925469265 1035670549462217944101949)
                ·
                  refine ⟨388376456048331729038231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035670549462217944101949 388376456048331729038231)
                  ·
                    rfl

theorem cell21_1701811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 3].length) (baseStart_1701811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701811 prefixEnd_1701811 := by exact prefixLift 1701811
  have htrace : WordTrace (prefixWord ++ tailWord_1701811) baseStart_1701811 baseEnd_1701811 := by
    simpa [prefixWord, tailWord_1701811, baseEnd_1701811] using wordTrace_append hprefix tailTrace_1701811
  have hstable : (prefixWord ++ tailWord_1701811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701811).length < 2 ^ (prefixWord ++ tailWord_1701811).sum := by decide
  have hdescent : baseEnd_1701811 < baseStart_1701811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701867 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 6]
def baseStart_1701867 : Nat := 118140960795 + 1701867 * 2 ^ 59
def prefixEnd_1701867 : Nat := 4983230072969 + 3 ^ 40 * 1701867 * 2
def baseEnd_1701867 : Nat := 388389236011288076104783

theorem tailTrace_1701867 : CollatzResearch.WordTrace tailWord_1701867 prefixEnd_1701867 388389236011288076104783 := by
  unfold tailWord_1701867
  simp only [CollatzResearch.WordTrace]
  refine ⟨62072188925433989588423855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41381459283622659725615903 62072188925433989588423855)
  ·
    refine ⟨93108283388150984382635783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62072188925433989588423855 93108283388150984382635783)
    ·
      refine ⟨139662425082226476573953675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93108283388150984382635783 139662425082226476573953675)
      ·
        refine ⟨209493637623339714860930513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139662425082226476573953675 209493637623339714860930513)
        ·
          refine ⟨157120228217504786145697885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209493637623339714860930513 157120228217504786145697885)
          ·
            refine ⟨58920085581564294804636707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157120228217504786145697885 58920085581564294804636707)
            ·
              refine ⟨88380128372346442206955061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58920085581564294804636707 88380128372346442206955061)
              ·
                refine ⟨8285637034907478956902037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88380128372346442206955061 8285637034907478956902037)
                ·
                  refine ⟨388389236011288076104783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8285637034907478956902037 388389236011288076104783)
                  ·
                    rfl

theorem cell21_1701867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_1701867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701867 prefixEnd_1701867 := by exact prefixLift 1701867
  have htrace : WordTrace (prefixWord ++ tailWord_1701867) baseStart_1701867 baseEnd_1701867 := by
    simpa [prefixWord, tailWord_1701867, baseEnd_1701867] using wordTrace_append hprefix tailTrace_1701867
  have hstable : (prefixWord ++ tailWord_1701867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701867).length < 2 ^ (prefixWord ++ tailWord_1701867).sum := by decide
  have hdescent : baseEnd_1701867 < baseStart_1701867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701884 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_1701884 : Nat := 118140960795 + 1701884 * 2 ^ 59
def prefixEnd_1701884 : Nat := 4983230072969 + 3 ^ 40 * 1701884 * 2
def baseEnd_1701884 : Nat := 388393115642899824321415

theorem tailTrace_1701884 : CollatzResearch.WordTrace tailWord_1701884 prefixEnd_1701884 388393115642899824321415 := by
  unfold tailWord_1701884
  simp only [CollatzResearch.WordTrace]
  refine ⟨31036404483186200745896353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41381872644248267661195137 31036404483186200745896353)
  ·
    refine ⟨23277303362389650559422265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31036404483186200745896353 23277303362389650559422265)
    ·
      refine ⟨17457977521792237919566699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23277303362389650559422265 17457977521792237919566699)
      ·
        refine ⟨26186966282688356879350049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17457977521792237919566699 26186966282688356879350049)
        ·
          refine ⟨19640224712016267659512537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26186966282688356879350049 19640224712016267659512537)
          ·
            refine ⟨14730168534012200744634403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19640224712016267659512537 14730168534012200744634403)
            ·
              refine ⟨22095252801018301116951605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14730168534012200744634403 22095252801018301116951605)
              ·
                refine ⟨2071429950095465729714213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22095252801018301116951605 2071429950095465729714213)
                ·
                  refine ⟨388393115642899824321415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071429950095465729714213 388393115642899824321415)
                  ·
                    rfl

theorem cell21_1701884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_1701884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701884 prefixEnd_1701884 := by exact prefixLift 1701884
  have htrace : WordTrace (prefixWord ++ tailWord_1701884) baseStart_1701884 baseEnd_1701884 := by
    simpa [prefixWord, tailWord_1701884, baseEnd_1701884] using wordTrace_append hprefix tailTrace_1701884
  have hstable : (prefixWord ++ tailWord_1701884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701884).length < 2 ^ (prefixWord ++ tailWord_1701884).sum := by decide
  have hdescent : baseEnd_1701884 < baseStart_1701884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1701980 : List Nat := [2, 2, 4, 1, 1, 3, 3, 2, 3]
def baseStart_1701980 : Nat := 118140960795 + 1701980 * 2 ^ 59
def prefixEnd_1701980 : Nat := 4983230072969 + 3 ^ 40 * 1701980 * 2
def baseEnd_1701980 : Nat := 388415024150824990721219

theorem tailTrace_1701980 : CollatzResearch.WordTrace tailWord_1701980 prefixEnd_1701980 388415024150824990721219 := by
  unfold tailWord_1701980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31038155187012304943643697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41384206916016406591524929 31038155187012304943643697)
  ·
    refine ⟨23278616390259228707732773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31038155187012304943643697 23278616390259228707732773)
    ·
      refine ⟨4364740573173605382699895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23278616390259228707732773 4364740573173605382699895)
      ·
        refine ⟨6547110859760408074049843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364740573173605382699895 6547110859760408074049843)
        ·
          refine ⟨9820666289640612111074765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547110859760408074049843 9820666289640612111074765)
          ·
            refine ⟨3682749858615229541653037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9820666289640612111074765 3682749858615229541653037)
            ·
              refine ⟨1381031196980711078119889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3682749858615229541653037 1381031196980711078119889)
              ·
                refine ⟨1035773397735533308589917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1381031196980711078119889 1035773397735533308589917)
                ·
                  refine ⟨388415024150824990721219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035773397735533308589917 388415024150824990721219)
                  ·
                    rfl

theorem cell21_1701980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_1701980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1701980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1701980 prefixEnd_1701980 := by exact prefixLift 1701980
  have htrace : WordTrace (prefixWord ++ tailWord_1701980) baseStart_1701980 baseEnd_1701980 := by
    simpa [prefixWord, tailWord_1701980, baseEnd_1701980] using wordTrace_append hprefix tailTrace_1701980
  have hstable : (prefixWord ++ tailWord_1701980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1701980).length < 2 ^ (prefixWord ++ tailWord_1701980).sum := by decide
  have hdescent : baseEnd_1701980 < baseStart_1701980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1701980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702039 : List Nat := [1, 1, 3, 3, 4, 1, 1, 4, 3]
def baseStart_1702039 : Nat := 118140960795 + 1702039 * 2 ^ 59
def prefixEnd_1702039 : Nat := 4983230072969 + 3 ^ 40 * 1702039 * 2
def baseEnd_1702039 : Nat := 388428488754653999237765

theorem tailTrace_1702039 : CollatzResearch.WordTrace tailWord_1702039 prefixEnd_1702039 388428488754653999237765 := by
  unfold tailWord_1702039
  simp only [CollatzResearch.WordTrace]
  refine ⟨62078462280810862963685171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41385641520540575309123447 62078462280810862963685171)
  ·
    refine ⟨93117693421216294445527757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62078462280810862963685171 93117693421216294445527757)
    ·
      refine ⟨34919135032956110417072909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93117693421216294445527757 34919135032956110417072909)
      ·
        refine ⟨13094675637358541406402341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34919135032956110417072909 13094675637358541406402341)
        ·
          refine ⟨2455251682004726513700439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13094675637358541406402341 2455251682004726513700439)
          ·
            refine ⟨3682877523007089770550659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455251682004726513700439 3682877523007089770550659)
            ·
              refine ⟨5524316284510634655825989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682877523007089770550659 5524316284510634655825989)
              ·
                refine ⟨1035809303345743997967373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5524316284510634655825989 1035809303345743997967373)
                ·
                  refine ⟨388428488754653999237765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1035809303345743997967373 388428488754653999237765)
                  ·
                    rfl

theorem cell21_1702039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 3].length) (baseStart_1702039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702039 prefixEnd_1702039 := by exact prefixLift 1702039
  have htrace : WordTrace (prefixWord ++ tailWord_1702039) baseStart_1702039 baseEnd_1702039 := by
    simpa [prefixWord, tailWord_1702039, baseEnd_1702039] using wordTrace_append hprefix tailTrace_1702039
  have hstable : (prefixWord ++ tailWord_1702039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702039).length < 2 ^ (prefixWord ++ tailWord_1702039).sum := by decide
  have hdescent : baseEnd_1702039 < baseStart_1702039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702095 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 6]
def baseStart_1702095 : Nat := 118140960795 + 1702095 * 2 ^ 59
def prefixEnd_1702095 : Nat := 4983230072969 + 3 ^ 40 * 1702095 * 2
def baseEnd_1702095 : Nat := 388441268717610346304317

theorem tailTrace_1702095 : CollatzResearch.WordTrace tailWord_1702095 prefixEnd_1702095 388441268717610346304317 := by
  unfold tailWord_1702095
  simp only [CollatzResearch.WordTrace]
  refine ⟨62080504768607984527723739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41387003179071989685149159 62080504768607984527723739)
  ·
    refine ⟨93120757152911976791585609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62080504768607984527723739 93120757152911976791585609)
    ·
      refine ⟨69840567864683982593689207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93120757152911976791585609 69840567864683982593689207)
      ·
        refine ⟨104760851797025973890533811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69840567864683982593689207 104760851797025973890533811)
        ·
          refine ⟨157141277695538960835800717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104760851797025973890533811 157141277695538960835800717)
          ·
            refine ⟨58927979135827110313425269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157141277695538960835800717 58927979135827110313425269)
            ·
              refine ⟨5524498043983791591883619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58927979135827110313425269 5524498043983791591883619)
              ·
                refine ⟨8286747065975687387825429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524498043983791591883619 8286747065975687387825429)
                ·
                  refine ⟨388441268717610346304317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8286747065975687387825429 388441268717610346304317)
                  ·
                    rfl

theorem cell21_1702095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_1702095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702095 prefixEnd_1702095 := by exact prefixLift 1702095
  have htrace : WordTrace (prefixWord ++ tailWord_1702095) baseStart_1702095 baseEnd_1702095 := by
    simpa [prefixWord, tailWord_1702095, baseEnd_1702095] using wordTrace_append hprefix tailTrace_1702095
  have hstable : (prefixWord ++ tailWord_1702095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702095).length < 2 ^ (prefixWord ++ tailWord_1702095).sum := by decide
  have hdescent : baseEnd_1702095 < baseStart_1702095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702098 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1702098 : Nat := 118140960795 + 1702098 * 2 ^ 59
def prefixEnd_1702098 : Nat := 4983230072969 + 3 ^ 40 * 1702098 * 2
def baseEnd_1702098 : Nat := 388441953358483007754311

theorem tailTrace_1702098 : CollatzResearch.WordTrace tailWord_1702098 prefixEnd_1702098 388441953358483007754311 := by
  unfold tailWord_1702098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15520153546899279010020737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41387076125064744026721965 15520153546899279010020737)
  ·
    refine ⟨11640115160174459257515553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15520153546899279010020737 11640115160174459257515553)
    ·
      refine ⟨8730086370130844443136665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11640115160174459257515553 8730086370130844443136665)
      ·
        refine ⟨6547564777598133332352499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8730086370130844443136665 6547564777598133332352499)
        ·
          refine ⟨9821347166397199998528749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6547564777598133332352499 9821347166397199998528749)
          ·
            refine ⟨3683005187398949999448281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9821347166397199998528749 3683005187398949999448281)
            ·
              refine ⟨2762253890549212499586211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3683005187398949999448281 2762253890549212499586211)
              ·
                refine ⟨4143380835823818749379317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762253890549212499586211 4143380835823818749379317)
                ·
                  refine ⟨388441953358483007754311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4143380835823818749379317 388441953358483007754311)
                  ·
                    rfl

theorem cell21_1702098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1702098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702098 prefixEnd_1702098 := by exact prefixLift 1702098
  have htrace : WordTrace (prefixWord ++ tailWord_1702098) baseStart_1702098 baseEnd_1702098 := by
    simpa [prefixWord, tailWord_1702098, baseEnd_1702098] using wordTrace_append hprefix tailTrace_1702098
  have hstable : (prefixWord ++ tailWord_1702098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702098).length < 2 ^ (prefixWord ++ tailWord_1702098).sum := by decide
  have hdescent : baseEnd_1702098 < baseStart_1702098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702281 : List Nat := [1, 2, 1, 1, 6, 2, 3, 1, 4]
def baseStart_1702281 : Nat := 118140960795 + 1702281 * 2 ^ 59
def prefixEnd_1702281 : Nat := 4983230072969 + 3 ^ 40 * 1702281 * 2
def baseEnd_1702281 : Nat := 388483716451715356203937

theorem tailTrace_1702281 : CollatzResearch.WordTrace tailWord_1702281 prefixEnd_1702281 388483716451715356203937 := by
  unfold tailWord_1702281
  simp only [CollatzResearch.WordTrace]
  refine ⟨62087288745934138293994697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41391525830622758862663131 62087288745934138293994697)
  ·
    refine ⟨46565466559450603720496023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62087288745934138293994697 46565466559450603720496023)
    ·
      refine ⟨69848199839175905580744035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46565466559450603720496023 69848199839175905580744035)
      ·
        refine ⟨104772299758763858371116053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69848199839175905580744035 104772299758763858371116053)
        ·
          refine ⟨4911201551192055861146065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104772299758763858371116053 4911201551192055861146065)
          ·
            refine ⟨3683401163394041895859549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4911201551192055861146065 3683401163394041895859549)
            ·
              refine ⟨1381275436272765710947331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3683401163394041895859549 1381275436272765710947331)
              ·
                refine ⟨2071913154409148566420997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381275436272765710947331 2071913154409148566420997)
                ·
                  refine ⟨388483716451715356203937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2071913154409148566420997 388483716451715356203937)
                  ·
                    rfl

theorem cell21_1702281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_1702281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702281 prefixEnd_1702281 := by exact prefixLift 1702281
  have htrace : WordTrace (prefixWord ++ tailWord_1702281) baseStart_1702281 baseEnd_1702281 := by
    simpa [prefixWord, tailWord_1702281, baseEnd_1702281] using wordTrace_append hprefix tailTrace_1702281
  have hstable : (prefixWord ++ tailWord_1702281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702281).length < 2 ^ (prefixWord ++ tailWord_1702281).sum := by decide
  have hdescent : baseEnd_1702281 < baseStart_1702281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702399 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 4]
def baseStart_1702399 : Nat := 118140960795 + 1702399 * 2 ^ 59
def prefixEnd_1702399 : Nat := 4983230072969 + 3 ^ 40 * 1702399 * 2
def baseEnd_1702399 : Nat := 388510645659373373237029

theorem tailTrace_1702399 : CollatzResearch.WordTrace tailWord_1702399 prefixEnd_1702399 388510645659373373237029 := by
  unfold tailWord_1702399
  simp only [CollatzResearch.WordTrace]
  refine ⟨62091592559506644446790251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41394395039671096297860167 62091592559506644446790251)
  ·
    refine ⟨93137388839259966670185377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62091592559506644446790251 93137388839259966670185377)
    ·
      refine ⟨69853041629444975002639033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93137388839259966670185377 69853041629444975002639033)
      ·
        refine ⟨52389781222083731251979275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69853041629444975002639033 52389781222083731251979275)
        ·
          refine ⟨78584671833125596877968913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52389781222083731251979275 78584671833125596877968913)
          ·
            refine ⟨58938503874844197658476685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78584671833125596877968913 58938503874844197658476685)
            ·
              refine ⟨22101938953066574121928757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58938503874844197658476685 22101938953066574121928757)
              ·
                refine ⟨2072056776849991323930821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22101938953066574121928757 2072056776849991323930821)
                ·
                  refine ⟨388510645659373373237029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072056776849991323930821 388510645659373373237029)
                  ·
                    rfl

theorem cell21_1702399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_1702399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702399 prefixEnd_1702399 := by exact prefixLift 1702399
  have htrace : WordTrace (prefixWord ++ tailWord_1702399) baseStart_1702399 baseEnd_1702399 := by
    simpa [prefixWord, tailWord_1702399, baseEnd_1702399] using wordTrace_append hprefix tailTrace_1702399
  have hstable : (prefixWord ++ tailWord_1702399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702399).length < 2 ^ (prefixWord ++ tailWord_1702399).sum := by decide
  have hdescent : baseEnd_1702399 < baseStart_1702399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702461 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1702461 : Nat := 118140960795 + 1702461 * 2 ^ 59
def prefixEnd_1702461 : Nat := 4983230072969 + 3 ^ 40 * 1702461 * 2
def baseEnd_1702461 : Nat := 388524794904075043203569

theorem tailTrace_1702461 : CollatzResearch.WordTrace tailWord_1702461 prefixEnd_1702461 388524794904075043203569 := by
  unfold tailWord_1702461
  simp only [CollatzResearch.WordTrace]
  refine ⟨62093853885282029035547237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41395902590188019357031491 62093853885282029035547237)
  ·
    refine ⟨11642597603490380444165107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62093853885282029035547237 11642597603490380444165107)
    ·
      refine ⟨17463896405235570666247661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11642597603490380444165107 17463896405235570666247661)
      ·
        refine ⟨6548961151963338999842873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17463896405235570666247661 6548961151963338999842873)
        ·
          refine ⟨4911720863972504249882155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6548961151963338999842873 4911720863972504249882155)
          ·
            refine ⟨7367581295958756374823233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911720863972504249882155 7367581295958756374823233)
            ·
              refine ⟨5525685971969067281117425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367581295958756374823233 5525685971969067281117425)
              ·
                refine ⟨4144264478976800460838069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5525685971969067281117425 4144264478976800460838069)
                ·
                  refine ⟨388524794904075043203569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4144264478976800460838069 388524794904075043203569)
                  ·
                    rfl

theorem cell21_1702461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1702461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702461 prefixEnd_1702461 := by exact prefixLift 1702461
  have htrace : WordTrace (prefixWord ++ tailWord_1702461) baseStart_1702461 baseEnd_1702461 := by
    simpa [prefixWord, tailWord_1702461, baseEnd_1702461] using wordTrace_append hprefix tailTrace_1702461
  have hstable : (prefixWord ++ tailWord_1702461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702461).length < 2 ^ (prefixWord ++ tailWord_1702461).sum := by decide
  have hdescent : baseEnd_1702461 < baseStart_1702461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702478 : List Nat := [4, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_1702478 : Nat := 118140960795 + 1702478 * 2 ^ 59
def prefixEnd_1702478 : Nat := 4983230072969 + 3 ^ 40 * 1702478 * 2
def baseEnd_1702478 : Nat := 388528674535686791420201

theorem tailTrace_1702478 : CollatzResearch.WordTrace tailWord_1702478 prefixEnd_1702478 388528674535686791420201 := by
  unfold tailWord_1702478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761809240777555117364511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41396315950813627292610725 7761809240777555117364511)
  ·
    refine ⟨11642713861166332676046767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7761809240777555117364511 11642713861166332676046767)
    ·
      refine ⟨17464070791749499014070151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11642713861166332676046767 17464070791749499014070151)
      ·
        refine ⟨26196106187624248521105227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17464070791749499014070151 26196106187624248521105227)
        ·
          refine ⟨39294159281436372781657841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26196106187624248521105227 39294159281436372781657841)
          ·
            refine ⟨29470619461077279586243381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39294159281436372781657841 29470619461077279586243381)
            ·
              refine ⟨2762870574475994961210317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29470619461077279586243381 2762870574475994961210317)
              ·
                refine ⟨1036076465428498110453869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2762870574475994961210317 1036076465428498110453869)
                ·
                  refine ⟨388528674535686791420201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036076465428498110453869 388528674535686791420201)
                  ·
                    rfl

theorem cell21_1702478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_1702478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702478 prefixEnd_1702478 := by exact prefixLift 1702478
  have htrace : WordTrace (prefixWord ++ tailWord_1702478) baseStart_1702478 baseEnd_1702478 := by
    simpa [prefixWord, tailWord_1702478, baseEnd_1702478] using wordTrace_append hprefix tailTrace_1702478
  have hstable : (prefixWord ++ tailWord_1702478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702478).length < 2 ^ (prefixWord ++ tailWord_1702478).sum := by decide
  have hdescent : baseEnd_1702478 < baseStart_1702478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702506 : List Nat := [3, 1, 3, 2, 1, 1, 4, 6]
def baseStart_1702506 : Nat := 118140960795 + 1702506 * 2 ^ 59
def prefixEnd_1702506 : Nat := 4983230072969 + 3 ^ 40 * 1702506 * 2
def baseEnd_1702506 : Nat := 129511688172388321651159

theorem tailTrace_1702506 : CollatzResearch.WordTrace tailWord_1702506 prefixEnd_1702506 129511688172388321651159 := by
  unfold tailWord_1702506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15523873792529750430233843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41396996780079334480623581 15523873792529750430233843)
  ·
    refine ⟨23285810688794625645350765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15523873792529750430233843 23285810688794625645350765)
    ·
      refine ⟨8732179008297984617006537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23285810688794625645350765 8732179008297984617006537)
      ·
        refine ⟨6549134256223488462754903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8732179008297984617006537 6549134256223488462754903)
        ·
          refine ⟨9823701384335232694132355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549134256223488462754903 9823701384335232694132355)
          ·
            refine ⟨14735552076502849041198533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823701384335232694132355 14735552076502849041198533)
            ·
              refine ⟨2762916014344284195224725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14735552076502849041198533 2762916014344284195224725)
              ·
                refine ⟨129511688172388321651159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2762916014344284195224725 129511688172388321651159)
                ·
                  rfl

theorem cell21_1702506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_1702506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702506 prefixEnd_1702506 := by exact prefixLift 1702506
  have htrace : WordTrace (prefixWord ++ tailWord_1702506) baseStart_1702506 baseEnd_1702506 := by
    simpa [prefixWord, tailWord_1702506, baseEnd_1702506] using wordTrace_append hprefix tailTrace_1702506
  have hstable : (prefixWord ++ tailWord_1702506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702506).length < 2 ^ (prefixWord ++ tailWord_1702506).sum := by decide
  have hdescent : baseEnd_1702506 < baseStart_1702506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702509 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1702509 : Nat := 118140960795 + 1702509 * 2 ^ 59
def prefixEnd_1702509 : Nat := 4983230072969 + 3 ^ 40 * 1702509 * 2
def baseEnd_1702509 : Nat := 388535749158037626403471

theorem tailTrace_1702509 : CollatzResearch.WordTrace tailWord_1702509 prefixEnd_1702509 388535749158037626403471 := by
  unfold tailWord_1702509
  simp only [CollatzResearch.WordTrace]
  refine ⟨62095604589108133233294581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41397069726072088822196387 62095604589108133233294581)
  ·
    refine ⟨5821462930228887490621367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62095604589108133233294581 5821462930228887490621367)
    ·
      refine ⟨8732194395343331235932051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821462930228887490621367 8732194395343331235932051)
      ·
        refine ⟨13098291593014996853898077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8732194395343331235932051 13098291593014996853898077)
        ·
          refine ⟨4911859347380623820211779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13098291593014996853898077 4911859347380623820211779)
          ·
            refine ⟨7367789021070935730317669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911859347380623820211779 7367789021070935730317669)
            ·
              refine ⟨1381460441450800449434563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7367789021070935730317669 1381460441450800449434563)
              ·
                refine ⟨2072190662176200674151845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381460441450800449434563 2072190662176200674151845)
                ·
                  refine ⟨388535749158037626403471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072190662176200674151845 388535749158037626403471)
                  ·
                    rfl

theorem cell21_1702509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1702509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702509 prefixEnd_1702509 := by exact prefixLift 1702509
  have htrace : WordTrace (prefixWord ++ tailWord_1702509) baseStart_1702509 baseEnd_1702509 := by
    simpa [prefixWord, tailWord_1702509, baseEnd_1702509] using wordTrace_append hprefix tailTrace_1702509
  have hstable : (prefixWord ++ tailWord_1702509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702509).length < 2 ^ (prefixWord ++ tailWord_1702509).sum := by decide
  have hdescent : baseEnd_1702509 < baseStart_1702509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702537 : List Nat := [1, 2, 1, 1, 4, 1, 1, 7, 3]
def baseStart_1702537 : Nat := 118140960795 + 1702537 * 2 ^ 59
def prefixEnd_1702537 : Nat := 4983230072969 + 3 ^ 40 * 1702537 * 2
def baseEnd_1702537 : Nat := 388542139139515799936747

theorem tailTrace_1702537 : CollatzResearch.WordTrace tailWord_1702537 prefixEnd_1702537 388542139139515799936747 := by
  unfold tailWord_1702537
  simp only [CollatzResearch.WordTrace]
  refine ⟨62096625833006694015313865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41397750555337796010209243 62096625833006694015313865)
  ·
    refine ⟨46572469374755020511485399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62096625833006694015313865 46572469374755020511485399)
    ·
      refine ⟨69858704062132530767228099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46572469374755020511485399 69858704062132530767228099)
      ·
        refine ⟨104788056093198796150842149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69858704062132530767228099 104788056093198796150842149)
        ·
          refine ⟨19647760517474774278282903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104788056093198796150842149 19647760517474774278282903)
          ·
            refine ⟨29471640776212161417424355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19647760517474774278282903 29471640776212161417424355)
            ·
              refine ⟨44207461164318242126136533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29471640776212161417424355 44207461164318242126136533)
              ·
                refine ⟨1036112371038708799831325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44207461164318242126136533 1036112371038708799831325)
                ·
                  refine ⟨388542139139515799936747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036112371038708799831325 388542139139515799936747)
                  ·
                    rfl

theorem cell21_1702537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_1702537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702537 prefixEnd_1702537 := by exact prefixLift 1702537
  have htrace : WordTrace (prefixWord ++ tailWord_1702537) baseStart_1702537 baseEnd_1702537 := by
    simpa [prefixWord, tailWord_1702537, baseEnd_1702537] using wordTrace_append hprefix tailTrace_1702537
  have hstable : (prefixWord ++ tailWord_1702537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702537).length < 2 ^ (prefixWord ++ tailWord_1702537).sum := by decide
  have hdescent : baseEnd_1702537 < baseStart_1702537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702641 : List Nat := [1, 2, 2, 2, 2, 2, 3, 7]
def baseStart_1702641 : Nat := 118140960795 + 1702641 * 2 ^ 59
def prefixEnd_1702641 : Nat := 4983230072969 + 3 ^ 40 * 1702641 * 2
def baseEnd_1702641 : Nat := 129521957785478243401067

theorem tailTrace_1702641 : CollatzResearch.WordTrace tailWord_1702641 prefixEnd_1702641 129521957785478243401067 := by
  unfold tailWord_1702641
  simp only [CollatzResearch.WordTrace]
  refine ⟨62100419024629919777099777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41400279349753279851399851 62100419024629919777099777)
  ·
    refine ⟨46575314268472439832824833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62100419024629919777099777 46575314268472439832824833)
    ·
      refine ⟨34931485701354329874618625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46575314268472439832824833 34931485701354329874618625)
      ·
        refine ⟨26198614276015747405963969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34931485701354329874618625 26198614276015747405963969)
        ·
          refine ⟨19648960707011810554472977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26198614276015747405963969 19648960707011810554472977)
          ·
            refine ⟨14736720530258857915854733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19648960707011810554472977 14736720530258857915854733)
            ·
              refine ⟨5526270198847071718445525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14736720530258857915854733 5526270198847071718445525)
              ·
                refine ⟨129521957785478243401067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5526270198847071718445525 129521957785478243401067)
                ·
                  rfl

theorem cell21_1702641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 7].length) (baseStart_1702641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702641 prefixEnd_1702641 := by exact prefixLift 1702641
  have htrace : WordTrace (prefixWord ++ tailWord_1702641) baseStart_1702641 baseEnd_1702641 := by
    simpa [prefixWord, tailWord_1702641, baseEnd_1702641] using wordTrace_append hprefix tailTrace_1702641
  have hstable : (prefixWord ++ tailWord_1702641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702641).length < 2 ^ (prefixWord ++ tailWord_1702641).sum := by decide
  have hdescent : baseEnd_1702641 < baseStart_1702641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702658 : List Nat := [3, 4, 1, 1, 1, 2, 9]
def baseStart_1702658 : Nat := 118140960795 + 1702658 * 2 ^ 59
def prefixEnd_1702658 : Nat := 4983230072969 + 3 ^ 40 * 1702658 * 2
def baseEnd_1702658 : Nat := 43174416998671830935537

theorem tailTrace_1702658 : CollatzResearch.WordTrace tailWord_1702658 prefixEnd_1702658 43174416998671830935537 := by
  unfold tailWord_1702658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15525259766392082920117157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41400692710378887786979085 15525259766392082920117157)
  ·
    refine ⟨2910986206198515547521967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15525259766392082920117157 2910986206198515547521967)
    ·
      refine ⟨4366479309297773321282951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2910986206198515547521967 4366479309297773321282951)
      ·
        refine ⟨6549718963946659981924427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4366479309297773321282951 6549718963946659981924427)
        ·
          refine ⟨9824578445919989972886641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549718963946659981924427 9824578445919989972886641)
          ·
            refine ⟨7368433834439992479664981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9824578445919989972886641 7368433834439992479664981)
            ·
              refine ⟨43174416998671830935537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7368433834439992479664981 43174416998671830935537)
              ·
                rfl

theorem cell21_1702658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 9].length) (baseStart_1702658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702658 prefixEnd_1702658 := by exact prefixLift 1702658
  have htrace : WordTrace (prefixWord ++ tailWord_1702658) baseStart_1702658 baseEnd_1702658 := by
    simpa [prefixWord, tailWord_1702658, baseEnd_1702658] using wordTrace_append hprefix tailTrace_1702658
  have hstable : (prefixWord ++ tailWord_1702658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702658).length < 2 ^ (prefixWord ++ tailWord_1702658).sum := by decide
  have hdescent : baseEnd_1702658 < baseStart_1702658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702717 : List Nat := [1, 4, 1, 4, 11]
def baseStart_1702717 : Nat := 118140960795 + 1702717 * 2 ^ 59
def prefixEnd_1702717 : Nat := 4983230072969 + 3 ^ 40 * 1702717 * 2
def baseEnd_1702717 : Nat := 4797323673973771443659

theorem tailTrace_1702717 : CollatzResearch.WordTrace tailWord_1702717 prefixEnd_1702717 4797323673973771443659 := by
  unfold tailWord_1702717
  simp only [CollatzResearch.WordTrace]
  refine ⟨62103190972354584756866405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41402127314903056504577603 62103190972354584756866405)
  ·
    refine ⟨11644348307316484641912451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62103190972354584756866405 11644348307316484641912451)
    ·
      refine ⟨17466522460974726962868677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11644348307316484641912451 17466522460974726962868677)
      ·
        refine ⟨3274972961432761305537877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17466522460974726962868677 3274972961432761305537877)
        ·
          refine ⟨4797323673973771443659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3274972961432761305537877 4797323673973771443659)
          ·
            rfl

theorem cell21_1702717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 11].length) (baseStart_1702717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702717 prefixEnd_1702717 := by exact prefixLift 1702717
  have htrace : WordTrace (prefixWord ++ tailWord_1702717) baseStart_1702717 baseEnd_1702717 := by
    simpa [prefixWord, tailWord_1702717, baseEnd_1702717] using wordTrace_append hprefix tailTrace_1702717
  have hstable : (prefixWord ++ tailWord_1702717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702717).length < 2 ^ (prefixWord ++ tailWord_1702717).sum := by decide
  have hdescent : baseEnd_1702717 < baseStart_1702717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702731 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 11]
def baseStart_1702731 : Nat := 118140960795 + 1702731 * 2 ^ 59
def prefixEnd_1702731 : Nat := 4983230072969 + 3 ^ 40 * 1702731 * 2
def baseEnd_1702731 : Nat := 388586412582614573703017

theorem tailTrace_1702731 : CollatzResearch.WordTrace tailWord_1702731 prefixEnd_1702731 388586412582614573703017 := by
  unfold tailWord_1702731
  simp only [CollatzResearch.WordTrace]
  refine ⟨62103701594303865147876047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41402467729535910098584031 62103701594303865147876047)
  ·
    refine ⟨93155552391455797721814071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62103701594303865147876047 93155552391455797721814071)
    ·
      refine ⟨139733328587183696582721107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93155552391455797721814071 139733328587183696582721107)
      ·
        refine ⟨209599992880775544874081661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139733328587183696582721107 209599992880775544874081661)
        ·
          refine ⟨78599997330290829327780623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209599992880775544874081661 78599997330290829327780623)
          ·
            refine ⟨117899995995436243991670935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78599997330290829327780623 117899995995436243991670935)
            ·
              refine ⟨176849993993154365987506403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117899995995436243991670935 176849993993154365987506403)
              ·
                refine ⟨265274990989731548981259605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176849993993154365987506403 265274990989731548981259605)
                ·
                  refine ⟨388586412582614573703017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 265274990989731548981259605 388586412582614573703017)
                  ·
                    rfl

theorem cell21_1702731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_1702731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702731 prefixEnd_1702731 := by exact prefixLift 1702731
  have htrace : WordTrace (prefixWord ++ tailWord_1702731) baseStart_1702731 baseEnd_1702731 := by
    simpa [prefixWord, tailWord_1702731, baseEnd_1702731] using wordTrace_append hprefix tailTrace_1702731
  have hstable : (prefixWord ++ tailWord_1702731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702731).length < 2 ^ (prefixWord ++ tailWord_1702731).sum := by decide
  have hdescent : baseEnd_1702731 < baseStart_1702731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702779 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 4]
def baseStart_1702779 : Nat := 118140960795 + 1702779 * 2 ^ 59
def prefixEnd_1702779 : Nat := 4983230072969 + 3 ^ 40 * 1702779 * 2
def baseEnd_1702779 : Nat := 388597366836577156902919

theorem tailTrace_1702779 : CollatzResearch.WordTrace tailWord_1702779 prefixEnd_1702779 388597366836577156902919 := by
  unfold tailWord_1702779
  simp only [CollatzResearch.WordTrace]
  refine ⟨62105452298129969345623391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41403634865419979563748927 62105452298129969345623391)
  ·
    refine ⟨93158178447194954018435087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62105452298129969345623391 93158178447194954018435087)
    ·
      refine ⟨139737267670792431027652631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93158178447194954018435087 139737267670792431027652631)
      ·
        refine ⟨209605901506188646541478947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139737267670792431027652631 209605901506188646541478947)
        ·
          refine ⟨314408852259282969812218421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209605901506188646541478947 314408852259282969812218421)
          ·
            refine ⟨29475829899307778419895477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 314408852259282969812218421 29475829899307778419895477)
            ·
              refine ⟨2763359053060104226865201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29475829899307778419895477 2763359053060104226865201)
              ·
                refine ⟨2072519289795078170148901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763359053060104226865201 2072519289795078170148901)
                ·
                  refine ⟨388597366836577156902919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072519289795078170148901 388597366836577156902919)
                  ·
                    rfl

theorem cell21_1702779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_1702779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702779 prefixEnd_1702779 := by exact prefixLift 1702779
  have htrace : WordTrace (prefixWord ++ tailWord_1702779) baseStart_1702779 baseEnd_1702779 := by
    simpa [prefixWord, tailWord_1702779, baseEnd_1702779] using wordTrace_append hprefix tailTrace_1702779
  have hstable : (prefixWord ++ tailWord_1702779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702779).length < 2 ^ (prefixWord ++ tailWord_1702779).sum := by decide
  have hdescent : baseEnd_1702779 < baseStart_1702779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702810 : List Nat := [3, 1, 1, 4, 3, 1, 1, 7]
def baseStart_1702810 : Nat := 118140960795 + 1702810 * 2 ^ 59
def prefixEnd_1702810 : Nat := 4983230072969 + 3 ^ 40 * 1702810 * 2
def baseEnd_1702810 : Nat := 129534813819642663962063

theorem tailTrace_1702810 : CollatzResearch.WordTrace tailWord_1702810 prefixEnd_1702810 129534813819642663962063 := by
  unfold tailWord_1702810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15526645740254415410000471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41404388640678441093334589 15526645740254415410000471)
  ·
    refine ⟨23289968610381623115000707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15526645740254415410000471 23289968610381623115000707)
    ·
      refine ⟨34934952915572434672501061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23289968610381623115000707 34934952915572434672501061)
      ·
        refine ⟨6550303671669831501093949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34934952915572434672501061 6550303671669831501093949)
        ·
          refine ⟨2456363876876186812910231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6550303671669831501093949 2456363876876186812910231)
          ·
            refine ⟨3684545815314280219365347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456363876876186812910231 3684545815314280219365347)
            ·
              refine ⟨5526818722971420329048021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684545815314280219365347 5526818722971420329048021)
              ·
                refine ⟨129534813819642663962063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5526818722971420329048021 129534813819642663962063)
                ·
                  rfl

theorem cell21_1702810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_1702810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702810 prefixEnd_1702810 := by exact prefixLift 1702810
  have htrace : WordTrace (prefixWord ++ tailWord_1702810) baseStart_1702810 baseEnd_1702810 := by
    simpa [prefixWord, tailWord_1702810, baseEnd_1702810] using wordTrace_append hprefix tailTrace_1702810
  have hstable : (prefixWord ++ tailWord_1702810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702810).length < 2 ^ (prefixWord ++ tailWord_1702810).sum := by decide
  have hdescent : baseEnd_1702810 < baseStart_1702810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702841 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 5]
def baseStart_1702841 : Nat := 118140960795 + 1702841 * 2 ^ 59
def prefixEnd_1702841 : Nat := 4983230072969 + 3 ^ 40 * 1702841 * 2
def baseEnd_1702841 : Nat := 388611516081278826869459

theorem tailTrace_1702841 : CollatzResearch.WordTrace tailWord_1702841 prefixEnd_1702841 388611516081278826869459 := by
  unfold tailWord_1702841
  simp only [CollatzResearch.WordTrace]
  refine ⟨62107713623905353934380377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41405142415936902622920251 62107713623905353934380377)
  ·
    refine ⟨46580785217929015450785283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62107713623905353934380377 46580785217929015450785283)
    ·
      refine ⟨69871177826893523176177925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46580785217929015450785283 69871177826893523176177925)
      ·
        refine ⟨13100845842542535595533361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69871177826893523176177925 13100845842542535595533361)
        ·
          refine ⟨9825634381906901696650021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13100845842542535595533361 9825634381906901696650021)
          ·
            refine ⟨1842306446607544068121879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9825634381906901696650021 1842306446607544068121879)
            ·
              refine ⟨2763459669911316102182819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842306446607544068121879 2763459669911316102182819)
              ·
                refine ⟨4145189504866974153274229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763459669911316102182819 4145189504866974153274229)
                ·
                  refine ⟨388611516081278826869459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4145189504866974153274229 388611516081278826869459)
                  ·
                    rfl

theorem cell21_1702841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_1702841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702841 prefixEnd_1702841 := by exact prefixLift 1702841
  have htrace : WordTrace (prefixWord ++ tailWord_1702841) baseStart_1702841 baseEnd_1702841 := by
    simpa [prefixWord, tailWord_1702841, baseEnd_1702841] using wordTrace_append hprefix tailTrace_1702841
  have hstable : (prefixWord ++ tailWord_1702841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702841).length < 2 ^ (prefixWord ++ tailWord_1702841).sum := by decide
  have hdescent : baseEnd_1702841 < baseStart_1702841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702945 : List Nat := [1, 2, 3, 2, 3, 2, 8]
def baseStart_1702945 : Nat := 118140960795 + 1702945 * 2 ^ 59
def prefixEnd_1702945 : Nat := 4983230072969 + 3 ^ 40 * 1702945 * 2
def baseEnd_1702945 : Nat := 43181694477577528570657

theorem tailTrace_1702945 : CollatzResearch.WordTrace tailWord_1702945 prefixEnd_1702945 43181694477577528570657 := by
  unfold tailWord_1702945
  simp only [CollatzResearch.WordTrace]
  refine ⟨62111506815528579696166289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41407671210352386464110859 62111506815528579696166289)
  ·
    refine ⟨46583630111646434772124717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62111506815528579696166289 46583630111646434772124717)
    ·
      refine ⟨17468861291867413039546769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46583630111646434772124717 17468861291867413039546769)
      ·
        refine ⟨13101645968900559779660077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17468861291867413039546769 13101645968900559779660077)
        ·
          refine ⟨4913117238337709917372529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13101645968900559779660077 4913117238337709917372529)
          ·
            refine ⟨3684837928753282438029397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4913117238337709917372529 3684837928753282438029397)
            ·
              refine ⟨43181694477577528570657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3684837928753282438029397 43181694477577528570657)
              ·
                rfl

theorem cell21_1702945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 8].length) (baseStart_1702945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702945 prefixEnd_1702945 := by exact prefixLift 1702945
  have htrace : WordTrace (prefixWord ++ tailWord_1702945) baseStart_1702945 baseEnd_1702945 := by
    simpa [prefixWord, tailWord_1702945, baseEnd_1702945] using wordTrace_append hprefix tailTrace_1702945
  have hstable : (prefixWord ++ tailWord_1702945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702945).length < 2 ^ (prefixWord ++ tailWord_1702945).sum := by decide
  have hdescent : baseEnd_1702945 < baseStart_1702945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702948 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_1702948 : Nat := 118140960795 + 1702948 * 2 ^ 59
def prefixEnd_1702948 : Nat := 4983230072969 + 3 ^ 40 * 1702948 * 2
def baseEnd_1702948 : Nat := 388635934939070418585907

theorem tailTrace_1702948 : CollatzResearch.WordTrace tailWord_1702948 prefixEnd_1702948 388635934939070418585907 := by
  unfold tailWord_1702948
  simp only [CollatzResearch.WordTrace]
  refine ⟨31055808117258855604262749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41407744156345140805683665 31055808117258855604262749)
  ·
    refine ⟨11645928043972070851598531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31055808117258855604262749 11645928043972070851598531)
    ·
      refine ⟨17468892065958106277397797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11645928043972070851598531 17468892065958106277397797)
      ·
        refine ⟨3275417262367144927012087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17468892065958106277397797 3275417262367144927012087)
        ·
          refine ⟨4913125893550717390518131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275417262367144927012087 4913125893550717390518131)
          ·
            refine ⟨7369688840326076085777197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913125893550717390518131 7369688840326076085777197)
            ·
              refine ⟨2763633315122278532166449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7369688840326076085777197 2763633315122278532166449)
              ·
                refine ⟨2072724986341708899124837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763633315122278532166449 2072724986341708899124837)
                ·
                  refine ⟨388635934939070418585907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072724986341708899124837 388635934939070418585907)
                  ·
                    rfl

theorem cell21_1702948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_1702948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702948 prefixEnd_1702948 := by exact prefixLift 1702948
  have htrace : WordTrace (prefixWord ++ tailWord_1702948) baseStart_1702948 baseEnd_1702948 := by
    simpa [prefixWord, tailWord_1702948, baseEnd_1702948] using wordTrace_append hprefix tailTrace_1702948
  have hstable : (prefixWord ++ tailWord_1702948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702948).length < 2 ^ (prefixWord ++ tailWord_1702948).sum := by decide
  have hdescent : baseEnd_1702948 < baseStart_1702948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702990 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1702990 : Nat := 118140960795 + 1702990 * 2 ^ 59
def prefixEnd_1702990 : Nat := 4983230072969 + 3 ^ 40 * 1702990 * 2
def baseEnd_1702990 : Nat := 388645519911287678885821

theorem tailTrace_1702990 : CollatzResearch.WordTrace tailWord_1702990 prefixEnd_1702990 388645519911287678885821 := by
  unfold tailWord_1702990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764143512545694047694303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41408765400243701587702949 7764143512545694047694303)
  ·
    refine ⟨11646215268818541071541455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7764143512545694047694303 11646215268818541071541455)
    ·
      refine ⟨17469322903227811607312183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11646215268818541071541455 17469322903227811607312183)
      ·
        refine ⟨26203984354841717410968275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17469322903227811607312183 26203984354841717410968275)
        ·
          refine ⟨39305976532262576116452413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26203984354841717410968275 39305976532262576116452413)
          ·
            refine ⟨14739741199598466043669655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39305976532262576116452413 14739741199598466043669655)
            ·
              refine ⟨22109611799397699065504483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14739741199598466043669655 22109611799397699065504483)
              ·
                refine ⟨33164417699096548598256725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22109611799397699065504483 33164417699096548598256725)
                ·
                  refine ⟨388645519911287678885821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33164417699096548598256725 388645519911287678885821)
                  ·
                    rfl

theorem cell21_1702990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1702990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702990 prefixEnd_1702990 := by exact prefixLift 1702990
  have htrace : WordTrace (prefixWord ++ tailWord_1702990) baseStart_1702990 baseEnd_1702990 := by
    simpa [prefixWord, tailWord_1702990, baseEnd_1702990] using wordTrace_append hprefix tailTrace_1702990
  have hstable : (prefixWord ++ tailWord_1702990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702990).length < 2 ^ (prefixWord ++ tailWord_1702990).sum := by decide
  have hdescent : baseEnd_1702990 < baseStart_1702990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1702993 : List Nat := [1, 2, 2, 1, 3, 1, 5, 3, 3]
def baseStart_1702993 : Nat := 118140960795 + 1702993 * 2 ^ 59
def prefixEnd_1702993 : Nat := 4983230072969 + 3 ^ 40 * 1702993 * 2
def baseEnd_1702993 : Nat := 388646204552160340335815

theorem tailTrace_1702993 : CollatzResearch.WordTrace tailWord_1702993 prefixEnd_1702993 388646204552160340335815 := by
  unfold tailWord_1702993
  simp only [CollatzResearch.WordTrace]
  refine ⟨62113257519354683893913633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41408838346236455929275755 62113257519354683893913633)
  ·
    refine ⟨46584943139516012920435225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62113257519354683893913633 46584943139516012920435225)
    ·
      refine ⟨34938707354637009690326419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46584943139516012920435225 34938707354637009690326419)
      ·
        refine ⟨52408061031955514535489629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34938707354637009690326419 52408061031955514535489629)
        ·
          refine ⟨19653022886983317950808611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52408061031955514535489629 19653022886983317950808611)
          ·
            refine ⟨29479534330474976926212917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19653022886983317950808611 29479534330474976926212917)
            ·
              refine ⟨2763706343482029086832461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29479534330474976926212917 2763706343482029086832461)
              ·
                refine ⟨1036389878805760907562173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2763706343482029086832461 1036389878805760907562173)
                ·
                  refine ⟨388646204552160340335815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036389878805760907562173 388646204552160340335815)
                  ·
                    rfl

theorem cell21_1702993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_1702993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1702993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1702993 prefixEnd_1702993 := by exact prefixLift 1702993
  have htrace : WordTrace (prefixWord ++ tailWord_1702993) baseStart_1702993 baseEnd_1702993 := by
    simpa [prefixWord, tailWord_1702993, baseEnd_1702993] using wordTrace_append hprefix tailTrace_1702993
  have hstable : (prefixWord ++ tailWord_1702993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1702993).length < 2 ^ (prefixWord ++ tailWord_1702993).sum := by decide
  have hdescent : baseEnd_1702993 < baseStart_1702993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1702993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703010 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1703010 : Nat := 118140960795 + 1703010 * 2 ^ 59
def prefixEnd_1703010 : Nat := 4983230072969 + 3 ^ 40 * 1703010 * 2
def baseEnd_1703010 : Nat := 388650084183772088552447

theorem tailTrace_1703010 : CollatzResearch.WordTrace tailWord_1703010 prefixEnd_1703010 388650084183772088552447 := by
  unfold tailWord_1703010
  simp only [CollatzResearch.WordTrace]
  refine ⟨15528469390073273949320621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41409251706862063864854989 15528469390073273949320621)
  ·
    refine ⟨5823176021277477730995233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15528469390073273949320621 5823176021277477730995233)
    ·
      refine ⟨4367382015958108298246425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5823176021277477730995233 4367382015958108298246425)
      ·
        refine ⟨3275536511968581223684819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4367382015958108298246425 3275536511968581223684819)
        ·
          refine ⟨4913304767952871835527229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275536511968581223684819 4913304767952871835527229)
          ·
            refine ⟨1842489287982326938322711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4913304767952871835527229 1842489287982326938322711)
            ·
              refine ⟨2763733931973490407484067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842489287982326938322711 2763733931973490407484067)
              ·
                refine ⟨4145600897960235611226101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763733931973490407484067 4145600897960235611226101)
                ·
                  refine ⟨388650084183772088552447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4145600897960235611226101 388650084183772088552447)
                  ·
                    rfl

theorem cell21_1703010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1703010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703010 prefixEnd_1703010 := by exact prefixLift 1703010
  have htrace : WordTrace (prefixWord ++ tailWord_1703010) baseStart_1703010 baseEnd_1703010 := by
    simpa [prefixWord, tailWord_1703010, baseEnd_1703010] using wordTrace_append hprefix tailTrace_1703010
  have hstable : (prefixWord ++ tailWord_1703010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703010).length < 2 ^ (prefixWord ++ tailWord_1703010).sum := by decide
  have hdescent : baseEnd_1703010 < baseStart_1703010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703021 : List Nat := [1, 5, 1, 1, 2, 2, 1, 8]
def baseStart_1703021 : Nat := 118140960795 + 1703021 * 2 ^ 59
def prefixEnd_1703021 : Nat := 4983230072969 + 3 ^ 40 * 1703021 * 2
def baseEnd_1703021 : Nat := 129550864844546171289697

theorem tailTrace_1703021 : CollatzResearch.WordTrace tailWord_1703021 prefixEnd_1703021 129550864844546171289697 := by
  unfold tailWord_1703021
  simp only [CollatzResearch.WordTrace]
  refine ⟨62114278763253244675932917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41409519175502163117288611 62114278763253244675932917)
  ·
    refine ⟨5823213634054991688368711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62114278763253244675932917 5823213634054991688368711)
    ·
      refine ⟨8734820451082487532553067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823213634054991688368711 8734820451082487532553067)
      ·
        refine ⟨13102230676623731298829601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8734820451082487532553067 13102230676623731298829601)
        ·
          refine ⟨9826673007467798474122201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13102230676623731298829601 9826673007467798474122201)
          ·
            refine ⟨7370004755600848855591651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9826673007467798474122201 7370004755600848855591651)
            ·
              refine ⟨11055007133401273283387477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7370004755600848855591651 11055007133401273283387477)
              ·
                refine ⟨129550864844546171289697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11055007133401273283387477 129550864844546171289697)
                ·
                  rfl

theorem cell21_1703021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 8].length) (baseStart_1703021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703021 prefixEnd_1703021 := by exact prefixLift 1703021
  have htrace : WordTrace (prefixWord ++ tailWord_1703021) baseStart_1703021 baseEnd_1703021 := by
    simpa [prefixWord, tailWord_1703021, baseEnd_1703021] using wordTrace_append hprefix tailTrace_1703021
  have hstable : (prefixWord ++ tailWord_1703021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703021).length < 2 ^ (prefixWord ++ tailWord_1703021).sum := by decide
  have hdescent : baseEnd_1703021 < baseStart_1703021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703035 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 5]
def baseStart_1703035 : Nat := 118140960795 + 1703035 * 2 ^ 59
def prefixEnd_1703035 : Nat := 4983230072969 + 3 ^ 40 * 1703035 * 2
def baseEnd_1703035 : Nat := 388655789524377600635729

theorem tailTrace_1703035 : CollatzResearch.WordTrace tailWord_1703035 prefixEnd_1703035 388655789524377600635729 := by
  unfold tailWord_1703035
  simp only [CollatzResearch.WordTrace]
  refine ⟨62114789385202525066942559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41409859590135016711295039 62114789385202525066942559)
  ·
    refine ⟨93172184077803787600413839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62114789385202525066942559 93172184077803787600413839)
    ·
      refine ⟨139758276116705681400620759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93172184077803787600413839 139758276116705681400620759)
      ·
        refine ⟨209637414175058522100931139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139758276116705681400620759 209637414175058522100931139)
        ·
          refine ⟨314456121262587783151396709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209637414175058522100931139 314456121262587783151396709)
          ·
            refine ⟨58960522736735209340886883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314456121262587783151396709 58960522736735209340886883)
            ·
              refine ⟨88440784105102814011330325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58960522736735209340886883 88440784105102814011330325)
              ·
                refine ⟨4145661754926694406781109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88440784105102814011330325 4145661754926694406781109)
                ·
                  refine ⟨388655789524377600635729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4145661754926694406781109 388655789524377600635729)
                  ·
                    rfl

theorem cell21_1703035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_1703035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703035 prefixEnd_1703035 := by exact prefixLift 1703035
  have htrace : WordTrace (prefixWord ++ tailWord_1703035) baseStart_1703035 baseEnd_1703035 := by
    simpa [prefixWord, tailWord_1703035, baseEnd_1703035] using wordTrace_append hprefix tailTrace_1703035
  have hstable : (prefixWord ++ tailWord_1703035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703035).length < 2 ^ (prefixWord ++ tailWord_1703035).sum := by decide
  have hdescent : baseEnd_1703035 < baseStart_1703035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703069 : List Nat := [1, 4, 2, 1, 1, 2, 3, 4, 3]
def baseStart_1703069 : Nat := 118140960795 + 1703069 * 2 ^ 59
def prefixEnd_1703069 : Nat := 4983230072969 + 3 ^ 40 * 1703069 * 2
def baseEnd_1703069 : Nat := 388663548787601097068993

theorem tailTrace_1703069 : CollatzResearch.WordTrace tailWord_1703069 prefixEnd_1703069 388663548787601097068993 := by
  unfold tailWord_1703069
  simp only [CollatzResearch.WordTrace]
  refine ⟨62116029467079348873680261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41410686311386232582453507 62116029467079348873680261)
  ·
    refine ⟨11646755525077377913815049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62116029467079348873680261 11646755525077377913815049)
    ·
      refine ⟨8735066643808033435361287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11646755525077377913815049 8735066643808033435361287)
      ·
        refine ⟨13102599965712050153041931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735066643808033435361287 13102599965712050153041931)
        ·
          refine ⟨19653899948568075229562897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13102599965712050153041931 19653899948568075229562897)
          ·
            refine ⟨14740424961426056422172173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19653899948568075229562897 14740424961426056422172173)
            ·
              refine ⟨5527659360534771158314565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14740424961426056422172173 5527659360534771158314565)
              ·
                refine ⟨1036436130100269592183981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5527659360534771158314565 1036436130100269592183981)
                ·
                  refine ⟨388663548787601097068993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036436130100269592183981 388663548787601097068993)
                  ·
                    rfl

theorem cell21_1703069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_1703069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703069 prefixEnd_1703069 := by exact prefixLift 1703069
  have htrace : WordTrace (prefixWord ++ tailWord_1703069) baseStart_1703069 baseEnd_1703069 := by
    simpa [prefixWord, tailWord_1703069, baseEnd_1703069] using wordTrace_append hprefix tailTrace_1703069
  have hstable : (prefixWord ++ tailWord_1703069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703069).length < 2 ^ (prefixWord ++ tailWord_1703069).sum := by decide
  have hdescent : baseEnd_1703069 < baseStart_1703069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703117 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1703117 : Nat := 118140960795 + 1703117 * 2 ^ 59
def prefixEnd_1703117 : Nat := 4983230072969 + 3 ^ 40 * 1703117 * 2
def baseEnd_1703117 : Nat := 388674503041563680268895

theorem tailTrace_1703117 : CollatzResearch.WordTrace tailWord_1703117 prefixEnd_1703117 388674503041563680268895 := by
  unfold tailWord_1703117
  simp only [CollatzResearch.WordTrace]
  refine ⟨62117780170905453071427605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41411853447270302047618403 62117780170905453071427605)
  ·
    refine ⟨2911770945511193112723169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62117780170905453071427605 2911770945511193112723169)
    ·
      refine ⟨2183828209133394834542377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2911770945511193112723169 2183828209133394834542377)
      ·
        refine ⟨1637871156850046125906783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2183828209133394834542377 1637871156850046125906783)
        ·
          refine ⟨2456806735275069188860175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637871156850046125906783 2456806735275069188860175)
          ·
            refine ⟨3685210102912603783290263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456806735275069188860175 3685210102912603783290263)
            ·
              refine ⟨5527815154368905674935395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685210102912603783290263 5527815154368905674935395)
              ·
                refine ⟨8291722731553358512403093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527815154368905674935395 8291722731553358512403093)
                ·
                  refine ⟨388674503041563680268895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8291722731553358512403093 388674503041563680268895)
                  ·
                    rfl

theorem cell21_1703117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1703117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703117 prefixEnd_1703117 := by exact prefixLift 1703117
  have htrace : WordTrace (prefixWord ++ tailWord_1703117) baseStart_1703117 baseEnd_1703117 := by
    simpa [prefixWord, tailWord_1703117, baseEnd_1703117] using wordTrace_append hprefix tailTrace_1703117
  have hstable : (prefixWord ++ tailWord_1703117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703117).length < 2 ^ (prefixWord ++ tailWord_1703117).sum := by decide
  have hdescent : baseEnd_1703117 < baseStart_1703117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703266 : List Nat := [3, 3, 2, 1, 1, 1, 5, 5]
def baseStart_1703266 : Nat := 118140960795 + 1703266 * 2 ^ 59
def prefixEnd_1703266 : Nat := 4983230072969 + 3 ^ 40 * 1703266 * 2
def baseEnd_1703266 : Nat := 129569502290524177428419

theorem tailTrace_1703266 : CollatzResearch.WordTrace tailWord_1703266 prefixEnd_1703266 129569502290524177428419 := by
  unfold tailWord_1703266
  simp only [CollatzResearch.WordTrace]
  refine ⟨15530803661841412879650413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41415476431577101012401101 15530803661841412879650413)
  ·
    refine ⟨5824051373190529829868905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15530803661841412879650413 5824051373190529829868905)
    ·
      refine ⟨4368038529892897372401679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5824051373190529829868905 4368038529892897372401679)
      ·
        refine ⟨6552057794839346058602519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4368038529892897372401679 6552057794839346058602519)
        ·
          refine ⟨9828086692259019087903779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552057794839346058602519 9828086692259019087903779)
          ·
            refine ⟨14742130038388528631855669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9828086692259019087903779 14742130038388528631855669)
            ·
              refine ⟨1382074691098924559236469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14742130038388528631855669 1382074691098924559236469)
              ·
                refine ⟨129569502290524177428419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1382074691098924559236469 129569502290524177428419)
                ·
                  rfl

theorem cell21_1703266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_1703266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703266 prefixEnd_1703266 := by exact prefixLift 1703266
  have htrace : WordTrace (prefixWord ++ tailWord_1703266) baseStart_1703266 baseEnd_1703266 := by
    simpa [prefixWord, tailWord_1703266, baseEnd_1703266] using wordTrace_append hprefix tailTrace_1703266
  have hstable : (prefixWord ++ tailWord_1703266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703266).length < 2 ^ (prefixWord ++ tailWord_1703266).sum := by decide
  have hdescent : baseEnd_1703266 < baseStart_1703266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703297 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 5]
def baseStart_1703297 : Nat := 118140960795 + 1703297 * 2 ^ 59
def prefixEnd_1703297 : Nat := 4983230072969 + 3 ^ 40 * 1703297 * 2
def baseEnd_1703297 : Nat := 388715581493923367268527

theorem tailTrace_1703297 : CollatzResearch.WordTrace tailWord_1703297 prefixEnd_1703297 388715581493923367268527 := by
  unfold tailWord_1703297
  simp only [CollatzResearch.WordTrace]
  refine ⟨62124345310253343812980145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41416230206835562541986763 62124345310253343812980145)
  ·
    refine ⟨46593258982690007859735109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62124345310253343812980145 46593258982690007859735109)
    ·
      refine ⟨8736236059254376473700333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46593258982690007859735109 8736236059254376473700333)
      ·
        refine ⟨3276088522220391177637625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8736236059254376473700333 3276088522220391177637625)
        ·
          refine ⟨2457066391665293383228219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3276088522220391177637625 2457066391665293383228219)
          ·
            refine ⟨3685599587497940074842329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457066391665293383228219 3685599587497940074842329)
            ·
              refine ⟨2764199690623455056131747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685599587497940074842329 2764199690623455056131747)
              ·
                refine ⟨4146299535935182584197621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764199690623455056131747 4146299535935182584197621)
                ·
                  refine ⟨388715581493923367268527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4146299535935182584197621 388715581493923367268527)
                  ·
                    rfl

theorem cell21_1703297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_1703297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703297 prefixEnd_1703297 := by exact prefixLift 1703297
  have htrace : WordTrace (prefixWord ++ tailWord_1703297) baseStart_1703297 baseEnd_1703297 := by
    simpa [prefixWord, tailWord_1703297, baseEnd_1703297] using wordTrace_append hprefix tailTrace_1703297
  have hstable : (prefixWord ++ tailWord_1703297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703297).length < 2 ^ (prefixWord ++ tailWord_1703297).sum := by decide
  have hdescent : baseEnd_1703297 < baseStart_1703297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703308 : List Nat := [2, 2, 1, 2, 1, 3, 2, 8]
def baseStart_1703308 : Nat := 118140960795 + 1703308 * 2 ^ 59
def prefixEnd_1703308 : Nat := 4983230072969 + 3 ^ 40 * 1703308 * 2
def baseEnd_1703308 : Nat := 129572697281263264195057

theorem tailTrace_1703308 : CollatzResearch.WordTrace tailWord_1703308 prefixEnd_1703308 129572697281263264195057 := by
  unfold tailWord_1703308
  simp only [CollatzResearch.WordTrace]
  refine ⟨31062373256606746345815289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41416497675475661794420385 31062373256606746345815289)
  ·
    refine ⟨23296779942455059759361467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31062373256606746345815289 23296779942455059759361467)
    ·
      refine ⟨34945169913682589639042201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23296779942455059759361467 34945169913682589639042201)
      ·
        refine ⟨26208877435261942229281651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34945169913682589639042201 26208877435261942229281651)
        ·
          refine ⟨39313316152892913343922477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26208877435261942229281651 39313316152892913343922477)
          ·
            refine ⟨14742493557334842503970929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39313316152892913343922477 14742493557334842503970929)
            ·
              refine ⟨11056870168001131877978197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14742493557334842503970929 11056870168001131877978197)
              ·
                refine ⟨129572697281263264195057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11056870168001131877978197 129572697281263264195057)
                ·
                  rfl

theorem cell21_1703308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_1703308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703308 prefixEnd_1703308 := by exact prefixLift 1703308
  have htrace : WordTrace (prefixWord ++ tailWord_1703308) baseStart_1703308 baseEnd_1703308 := by
    simpa [prefixWord, tailWord_1703308, baseEnd_1703308] using wordTrace_append hprefix tailTrace_1703308
  have hstable : (prefixWord ++ tailWord_1703308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703308).length < 2 ^ (prefixWord ++ tailWord_1703308).sum := by decide
  have hdescent : baseEnd_1703308 < baseStart_1703308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703325 : List Nat := [1, 4, 2, 1, 3, 2, 1, 7]
def baseStart_1703325 : Nat := 118140960795 + 1703325 * 2 ^ 59
def prefixEnd_1703325 : Nat := 4983230072969 + 3 ^ 40 * 1703325 * 2
def baseEnd_1703325 : Nat := 129573990491800513600601

theorem tailTrace_1703325 : CollatzResearch.WordTrace tailWord_1703325 prefixEnd_1703325 129573990491800513600601 := by
  unfold tailWord_1703325
  simp only [CollatzResearch.WordTrace]
  refine ⟨62125366554151904594999429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41416911036101269729999619 62125366554151904594999429)
  ·
    refine ⟨11648506228903482111562393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62125366554151904594999429 11648506228903482111562393)
    ·
      refine ⟨8736379671677611583671795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11648506228903482111562393 8736379671677611583671795)
      ·
        refine ⟨13104569507516417375507693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8736379671677611583671795 13104569507516417375507693)
        ·
          refine ⟨4914213565318656515815385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13104569507516417375507693 4914213565318656515815385)
          ·
            refine ⟨3685660173988992386861539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4914213565318656515815385 3685660173988992386861539)
            ·
              refine ⟨5528490260983488580292309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685660173988992386861539 5528490260983488580292309)
              ·
                refine ⟨129573990491800513600601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5528490260983488580292309 129573990491800513600601)
                ·
                  rfl

theorem cell21_1703325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 7].length) (baseStart_1703325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703325 prefixEnd_1703325 := by exact prefixLift 1703325
  have htrace : WordTrace (prefixWord ++ tailWord_1703325) baseStart_1703325 baseEnd_1703325 := by
    simpa [prefixWord, tailWord_1703325, baseEnd_1703325] using wordTrace_append hprefix tailTrace_1703325
  have hstable : (prefixWord ++ tailWord_1703325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703325).length < 2 ^ (prefixWord ++ tailWord_1703325).sum := by decide
  have hdescent : baseEnd_1703325 < baseStart_1703325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703384 : List Nat := [2, 1, 2, 2, 2, 1, 4, 7]
def baseStart_1703384 : Nat := 118140960795 + 1703384 * 2 ^ 59
def prefixEnd_1703384 : Nat := 4983230072969 + 3 ^ 40 * 1703384 * 2
def baseEnd_1703384 : Nat := 129578478693076849772783

theorem tailTrace_1703384 : CollatzResearch.WordTrace tailWord_1703384 prefixEnd_1703384 129578478693076849772783 := by
  unfold tailWord_1703384
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063759230469078835698603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41418345640625438447598137 31063759230469078835698603)
  ·
    refine ⟨46595638845703618253547905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31063759230469078835698603 46595638845703618253547905)
    ·
      refine ⟨34946729134277713690160929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46595638845703618253547905 34946729134277713690160929)
      ·
        refine ⟨26210046850708285267620697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34946729134277713690160929 26210046850708285267620697)
        ·
          refine ⟨19657535138031213950715523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26210046850708285267620697 19657535138031213950715523)
          ·
            refine ⟨29486302707046820926073285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19657535138031213950715523 29486302707046820926073285)
            ·
              refine ⟨5528681757571278923638741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29486302707046820926073285 5528681757571278923638741)
              ·
                refine ⟨129578478693076849772783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5528681757571278923638741 129578478693076849772783)
                ·
                  rfl

theorem cell21_1703384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_1703384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703384 prefixEnd_1703384 := by exact prefixLift 1703384
  have htrace : WordTrace (prefixWord ++ tailWord_1703384) baseStart_1703384 baseEnd_1703384 := by
    simpa [prefixWord, tailWord_1703384, baseEnd_1703384] using wordTrace_append hprefix tailTrace_1703384
  have hstable : (prefixWord ++ tailWord_1703384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703384).length < 2 ^ (prefixWord ++ tailWord_1703384).sum := by decide
  have hdescent : baseEnd_1703384 < baseStart_1703384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703429 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1703429 : Nat := 118140960795 + 1703429 * 2 ^ 59
def prefixEnd_1703429 : Nat := 4983230072969 + 3 ^ 40 * 1703429 * 2
def baseEnd_1703429 : Nat := 388745705692320471068257

theorem tailTrace_1703429 : CollatzResearch.WordTrace tailWord_1703429 prefixEnd_1703429 388745705692320471068257 := by
  unfold tailWord_1703429
  simp only [CollatzResearch.WordTrace]
  refine ⟨62129159745775130356785341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41419439830516753571190227 62129159745775130356785341)
  ·
    refine ⟨23298434904665673883794503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62129159745775130356785341 23298434904665673883794503)
    ·
      refine ⟨34947652356998510825691755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23298434904665673883794503 34947652356998510825691755)
      ·
        refine ⟨52421478535497766238537633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34947652356998510825691755 52421478535497766238537633)
        ·
          refine ⟨39316108901623324678903225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52421478535497766238537633 39316108901623324678903225)
          ·
            refine ⟨29487081676217493509177419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39316108901623324678903225 29487081676217493509177419)
            ·
              refine ⟨44230622514326240263766129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29487081676217493509177419 44230622514326240263766129)
              ·
                refine ⟨33172966885744680197824597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44230622514326240263766129 33172966885744680197824597)
                ·
                  refine ⟨388745705692320471068257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33172966885744680197824597 388745705692320471068257)
                  ·
                    rfl

theorem cell21_1703429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1703429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703429 prefixEnd_1703429 := by exact prefixLift 1703429
  have htrace : WordTrace (prefixWord ++ tailWord_1703429) baseStart_1703429 baseEnd_1703429 := by
    simpa [prefixWord, tailWord_1703429, baseEnd_1703429] using wordTrace_append hprefix tailTrace_1703429
  have hstable : (prefixWord ++ tailWord_1703429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703429).length < 2 ^ (prefixWord ++ tailWord_1703429).sum := by decide
  have hdescent : baseEnd_1703429 < baseStart_1703429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703505 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 8]
def baseStart_1703505 : Nat := 118140960795 + 1703505 * 2 ^ 59
def prefixEnd_1703505 : Nat := 4983230072969 + 3 ^ 40 * 1703505 * 2
def baseEnd_1703505 : Nat := 388763049927761227801435

theorem tailTrace_1703505 : CollatzResearch.WordTrace tailWord_1703505 prefixEnd_1703505 388763049927761227801435 := by
  unfold tailWord_1703505
  simp only [CollatzResearch.WordTrace]
  refine ⟨62131931693499795336551969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41421287795666530224367979 62131931693499795336551969)
  ·
    refine ⟨46598948770124846502413977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62131931693499795336551969 46598948770124846502413977)
    ·
      refine ⟨34949211577593634876810483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46598948770124846502413977 34949211577593634876810483)
      ·
        refine ⟨52423817366390452315215725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34949211577593634876810483 52423817366390452315215725)
        ·
          refine ⟨19658931512396419618205897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52423817366390452315215725 19658931512396419618205897)
          ·
            refine ⟨14744198634297314713654423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19658931512396419618205897 14744198634297314713654423)
            ·
              refine ⟨22116297951445972070481635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14744198634297314713654423 22116297951445972070481635)
              ·
                refine ⟨33174446927168958105722453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22116297951445972070481635 33174446927168958105722453)
                ·
                  refine ⟨388763049927761227801435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33174446927168958105722453 388763049927761227801435)
                  ·
                    rfl

theorem cell21_1703505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_1703505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703505 prefixEnd_1703505 := by exact prefixLift 1703505
  have htrace : WordTrace (prefixWord ++ tailWord_1703505) baseStart_1703505 baseEnd_1703505 := by
    simpa [prefixWord, tailWord_1703505, baseEnd_1703505] using wordTrace_append hprefix tailTrace_1703505
  have hstable : (prefixWord ++ tailWord_1703505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703505).length < 2 ^ (prefixWord ++ tailWord_1703505).sum := by decide
  have hdescent : baseEnd_1703505 < baseStart_1703505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703536 : List Nat := [2, 1, 1, 1, 6, 1, 1, 8]
def baseStart_1703536 : Nat := 118140960795 + 1703536 * 2 ^ 59
def prefixEnd_1703536 : Nat := 4983230072969 + 3 ^ 40 * 1703536 * 2
def baseEnd_1703536 : Nat := 129590041516704020928235

theorem tailTrace_1703536 : CollatzResearch.WordTrace tailWord_1703536 prefixEnd_1703536 129590041516704020928235 := by
  unfold tailWord_1703536
  simp only [CollatzResearch.WordTrace]
  refine ⟨31066531178193743815465231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41422041570924991753953641 31066531178193743815465231)
  ·
    refine ⟨46599796767290615723197847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31066531178193743815465231 46599796767290615723197847)
    ·
      refine ⟨69899695150935923584796771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46599796767290615723197847 69899695150935923584796771)
      ·
        refine ⟨104849542726403885377195157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69899695150935923584796771 104849542726403885377195157)
        ·
          refine ⟨4914822315300182127056023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104849542726403885377195157 4914822315300182127056023)
          ·
            refine ⟨7372233472950273190584035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914822315300182127056023 7372233472950273190584035)
            ·
              refine ⟨11058350209425409785876053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372233472950273190584035 11058350209425409785876053)
              ·
                refine ⟨129590041516704020928235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11058350209425409785876053 129590041516704020928235)
                ·
                  rfl

theorem cell21_1703536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_1703536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703536 prefixEnd_1703536 := by exact prefixLift 1703536
  have htrace : WordTrace (prefixWord ++ tailWord_1703536) baseStart_1703536 baseEnd_1703536 := by
    simpa [prefixWord, tailWord_1703536, baseEnd_1703536] using wordTrace_append hprefix tailTrace_1703536
  have hstable : (prefixWord ++ tailWord_1703536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703536).length < 2 ^ (prefixWord ++ tailWord_1703536).sum := by decide
  have hdescent : baseEnd_1703536 < baseStart_1703536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703686 : List Nat := [6, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1703686 : Nat := 118140960795 + 1703686 * 2 ^ 59
def prefixEnd_1703686 : Nat := 4983230072969 + 3 ^ 40 * 1703686 * 2
def baseEnd_1703686 : Nat := 388804356593745135284399

theorem tailTrace_1703686 : CollatzResearch.WordTrace tailWord_1703686 prefixEnd_1703686 388804356593745135284399 := by
  unfold tailWord_1703686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941829165807626976527841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41425688870562708832593941 1941829165807626976527841)
  ·
    refine ⟨1456371874355720232395881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1941829165807626976527841 1456371874355720232395881)
    ·
      refine ⟨1092278905766790174296911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1456371874355720232395881 1092278905766790174296911)
      ·
        refine ⟨1638418358650185261445367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092278905766790174296911 1638418358650185261445367)
        ·
          refine ⟨2457627537975277892168051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638418358650185261445367 2457627537975277892168051)
          ·
            refine ⟨3686441306962916838252077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457627537975277892168051 3686441306962916838252077)
            ·
              refine ⟨1382415490111093814344529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3686441306962916838252077 1382415490111093814344529)
              ·
                refine ⟨1036811617583320360758397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382415490111093814344529 1036811617583320360758397)
                ·
                  refine ⟨388804356593745135284399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036811617583320360758397 388804356593745135284399)
                  ·
                    rfl

theorem cell21_1703686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1703686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703686 prefixEnd_1703686 := by exact prefixLift 1703686
  have htrace : WordTrace (prefixWord ++ tailWord_1703686) baseStart_1703686 baseEnd_1703686 := by
    simpa [prefixWord, tailWord_1703686, baseEnd_1703686] using wordTrace_append hprefix tailTrace_1703686
  have hstable : (prefixWord ++ tailWord_1703686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703686).length < 2 ^ (prefixWord ++ tailWord_1703686).sum := by decide
  have hdescent : baseEnd_1703686 < baseStart_1703686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703747 : List Nat := [1, 1, 1, 3, 1, 14]
def baseStart_1703747 : Nat := 118140960795 + 1703747 * 2 ^ 59
def prefixEnd_1703747 : Nat := 4983230072969 + 3 ^ 40 * 1703747 * 2
def baseEnd_1703747 : Nat := 14400676949067503139541

theorem tailTrace_1703747 : CollatzResearch.WordTrace tailWord_1703747 prefixEnd_1703747 14400676949067503139541 := by
  unfold tailWord_1703747
  simp only [CollatzResearch.WordTrace]
  refine ⟨62140758158623070666861495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41427172105748713777907663 62140758158623070666861495)
  ·
    refine ⟨93211137237934606000292243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62140758158623070666861495 93211137237934606000292243)
    ·
      refine ⟨139816705856901909000438365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93211137237934606000292243 139816705856901909000438365)
      ·
        refine ⟨52431264696338215875164387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139816705856901909000438365 52431264696338215875164387)
        ·
          refine ⟨78646897044507323812746581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52431264696338215875164387 78646897044507323812746581)
          ·
            refine ⟨14400676949067503139541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 78646897044507323812746581 14400676949067503139541)
            ·
              rfl

theorem cell21_1703747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 14].length) (baseStart_1703747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703747 prefixEnd_1703747 := by exact prefixLift 1703747
  have htrace : WordTrace (prefixWord ++ tailWord_1703747) baseStart_1703747 baseEnd_1703747 := by
    simpa [prefixWord, tailWord_1703747, baseEnd_1703747] using wordTrace_append hprefix tailTrace_1703747
  have hstable : (prefixWord ++ tailWord_1703747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703747).length < 2 ^ (prefixWord ++ tailWord_1703747).sum := by decide
  have hdescent : baseEnd_1703747 < baseStart_1703747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703812 : List Nat := [2, 3, 2, 1, 1, 1, 4, 4, 3]
def baseStart_1703812 : Nat := 118140960795 + 1703812 * 2 ^ 59
def prefixEnd_1703812 : Nat := 4983230072969 + 3 ^ 40 * 1703812 * 2
def baseEnd_1703812 : Nat := 388833111510396916184141

theorem tailTrace_1703812 : CollatzResearch.WordTrace tailWord_1703812 prefixEnd_1703812 388833111510396916184141 := by
  unfold tailWord_1703812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31071564451693793383988845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41428752602258391178651793 31071564451693793383988845)
  ·
    refine ⟨11651836669385172518995817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31071564451693793383988845 11651836669385172518995817)
    ·
      refine ⟨8738877502038879389246863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11651836669385172518995817 8738877502038879389246863)
      ·
        refine ⟨13108316253058319083870295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8738877502038879389246863 13108316253058319083870295)
        ·
          refine ⟨19662474379587478625805443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13108316253058319083870295 19662474379587478625805443)
          ·
            refine ⟨29493711569381217938708165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19662474379587478625805443 29493711569381217938708165)
            ·
              refine ⟨5530070919258978363507781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29493711569381217938708165 5530070919258978363507781)
              ·
                refine ⟨1036888297361058443157709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5530070919258978363507781 1036888297361058443157709)
                ·
                  refine ⟨388833111510396916184141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036888297361058443157709 388833111510396916184141)
                  ·
                    rfl

theorem cell21_1703812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_1703812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703812 prefixEnd_1703812 := by exact prefixLift 1703812
  have htrace : WordTrace (prefixWord ++ tailWord_1703812) baseStart_1703812 baseEnd_1703812 := by
    simpa [prefixWord, tailWord_1703812, baseEnd_1703812] using wordTrace_append hprefix tailTrace_1703812
  have hstable : (prefixWord ++ tailWord_1703812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703812).length < 2 ^ (prefixWord ++ tailWord_1703812).sum := by decide
  have hdescent : baseEnd_1703812 < baseStart_1703812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703964 : List Nat := [2, 2, 3, 1, 3, 1, 1, 5, 3]
def baseStart_1703964 : Nat := 118140960795 + 1703964 * 2 ^ 59
def prefixEnd_1703964 : Nat := 4983230072969 + 3 ^ 40 * 1703964 * 2
def baseEnd_1703964 : Nat := 388867799981278429650497

theorem tailTrace_1703964 : CollatzResearch.WordTrace tailWord_1703964 prefixEnd_1703964 388867799981278429650497 := by
  unfold tailWord_1703964
  simp only [CollatzResearch.WordTrace]
  refine ⟨31074336399418458363755473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41432448532557944485007297 31074336399418458363755473)
  ·
    refine ⟨23305752299563843772816605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31074336399418458363755473 23305752299563843772816605)
    ·
      refine ⟨8739657112336441414806227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23305752299563843772816605 8739657112336441414806227)
      ·
        refine ⟨13109485668504662122209341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8739657112336441414806227 13109485668504662122209341)
        ·
          refine ⟨4916057125689248295828503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13109485668504662122209341 4916057125689248295828503)
          ·
            refine ⟨7374085688533872443742755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916057125689248295828503 7374085688533872443742755)
            ·
              refine ⟨11061128532800808665614133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374085688533872443742755 11061128532800808665614133)
              ·
                refine ⟨1036980799950075812401325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11061128532800808665614133 1036980799950075812401325)
                ·
                  refine ⟨388867799981278429650497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036980799950075812401325 388867799981278429650497)
                  ·
                    rfl

theorem cell21_1703964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_1703964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703964 prefixEnd_1703964 := by exact prefixLift 1703964
  have htrace : WordTrace (prefixWord ++ tailWord_1703964) baseStart_1703964 baseEnd_1703964 := by
    simpa [prefixWord, tailWord_1703964, baseEnd_1703964] using wordTrace_append hprefix tailTrace_1703964
  have hstable : (prefixWord ++ tailWord_1703964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703964).length < 2 ^ (prefixWord ++ tailWord_1703964).sum := by decide
  have hdescent : baseEnd_1703964 < baseStart_1703964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703978 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_1703978 : Nat := 118140960795 + 1703978 * 2 ^ 59
def prefixEnd_1703978 : Nat := 4983230072969 + 3 ^ 40 * 1703978 * 2
def baseEnd_1703978 : Nat := 388870994972017516417135

theorem tailTrace_1703978 : CollatzResearch.WordTrace tailWord_1703978 prefixEnd_1703978 388870994972017516417135 := by
  unfold tailWord_1703978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15537295855196549279630147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41432788947190798079013725 15537295855196549279630147)
  ·
    refine ⟨23305943782794823919445221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15537295855196549279630147 23305943782794823919445221)
    ·
      refine ⟨4369864459274029484895979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23305943782794823919445221 4369864459274029484895979)
      ·
        refine ⟨6554796688911044227343969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369864459274029484895979 6554796688911044227343969)
        ·
          refine ⟨4916097516683283170507977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6554796688911044227343969 4916097516683283170507977)
          ·
            refine ⟨3687073137512462377880983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4916097516683283170507977 3687073137512462377880983)
            ·
              refine ⟨5530609706268693566821475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687073137512462377880983 5530609706268693566821475)
              ·
                refine ⟨8295914559403040350232213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530609706268693566821475 8295914559403040350232213)
                ·
                  refine ⟨388870994972017516417135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8295914559403040350232213 388870994972017516417135)
                  ·
                    rfl

theorem cell21_1703978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_1703978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1703978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1703978 prefixEnd_1703978 := by exact prefixLift 1703978
  have htrace : WordTrace (prefixWord ++ tailWord_1703978) baseStart_1703978 baseEnd_1703978 := by
    simpa [prefixWord, tailWord_1703978, baseEnd_1703978] using wordTrace_append hprefix tailTrace_1703978
  have hstable : (prefixWord ++ tailWord_1703978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703978).length < 2 ^ (prefixWord ++ tailWord_1703978).sum := by decide
  have hdescent : baseEnd_1703978 < baseStart_1703978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704037 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 6]
def baseStart_1704037 : Nat := 118140960795 + 1704037 * 2 ^ 59
def prefixEnd_1704037 : Nat := 4983230072969 + 3 ^ 40 * 1704037 * 2
def baseEnd_1704037 : Nat := 388884459575846524933681

theorem tailTrace_1704037 : CollatzResearch.WordTrace tailWord_1704037 prefixEnd_1704037 388884459575846524933681 := by
  unfold tailWord_1704037
  simp only [CollatzResearch.WordTrace]
  refine ⟨62151335327572450194918365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41434223551714966796612243 62151335327572450194918365)
  ·
    refine ⟨23306750747839668823094387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62151335327572450194918365 23306750747839668823094387)
    ·
      refine ⟨34960126121759503234641581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23306750747839668823094387 34960126121759503234641581)
      ·
        refine ⟨13110047295659813712990593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34960126121759503234641581 13110047295659813712990593)
        ·
          refine ⟨9832535471744860284742945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13110047295659813712990593 9832535471744860284742945)
          ·
            refine ⟨7374401603808645213557209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9832535471744860284742945 7374401603808645213557209)
            ·
              refine ⟨5530801202856483910167907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7374401603808645213557209 5530801202856483910167907)
              ·
                refine ⟨8296201804284725865251861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530801202856483910167907 8296201804284725865251861)
                ·
                  refine ⟨388884459575846524933681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8296201804284725865251861 388884459575846524933681)
                  ·
                    rfl

theorem cell21_1704037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_1704037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704037 prefixEnd_1704037 := by exact prefixLift 1704037
  have htrace : WordTrace (prefixWord ++ tailWord_1704037) baseStart_1704037 baseEnd_1704037 := by
    simpa [prefixWord, tailWord_1704037, baseEnd_1704037] using wordTrace_append hprefix tailTrace_1704037
  have hstable : (prefixWord ++ tailWord_1704037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704037).length < 2 ^ (prefixWord ++ tailWord_1704037).sum := by decide
  have hdescent : baseEnd_1704037 < baseStart_1704037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704223 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 4]
def baseStart_1704223 : Nat := 118140960795 + 1704223 * 2 ^ 59
def prefixEnd_1704223 : Nat := 4983230072969 + 3 ^ 40 * 1704223 * 2
def baseEnd_1704223 : Nat := 388926907309951534833301

theorem tailTrace_1704223 : CollatzResearch.WordTrace tailWord_1704223 prefixEnd_1704223 388926907309951534833301 := by
  unfold tailWord_1704223
  simp only [CollatzResearch.WordTrace]
  refine ⟨62158119304898603961189323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41438746203265735974126215 62158119304898603961189323)
  ·
    refine ⟨93237178957347905941783985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62158119304898603961189323 93237178957347905941783985)
    ·
      refine ⟨69927884218010929456337989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93237178957347905941783985 69927884218010929456337989)
      ·
        refine ⟨13111478290877049273063373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69927884218010929456337989 13111478290877049273063373)
        ·
          refine ⟨4916804359078893477398765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13111478290877049273063373 4916804359078893477398765)
          ·
            refine ⟨1843801634654585054024537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4916804359078893477398765 1843801634654585054024537)
            ·
              refine ⟨1382851225990938790518403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843801634654585054024537 1382851225990938790518403)
              ·
                refine ⟨2074276838986408185777605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382851225990938790518403 2074276838986408185777605)
                ·
                  refine ⟨388926907309951534833301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2074276838986408185777605 388926907309951534833301)
                  ·
                    rfl

theorem cell21_1704223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 4].length) (baseStart_1704223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704223 prefixEnd_1704223 := by exact prefixLift 1704223
  have htrace : WordTrace (prefixWord ++ tailWord_1704223) baseStart_1704223 baseEnd_1704223 := by
    simpa [prefixWord, tailWord_1704223, baseEnd_1704223] using wordTrace_append hprefix tailTrace_1704223
  have hstable : (prefixWord ++ tailWord_1704223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704223).length < 2 ^ (prefixWord ++ tailWord_1704223).sum := by decide
  have hdescent : baseEnd_1704223 < baseStart_1704223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704248 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_1704248 : Nat := 118140960795 + 1704248 * 2 ^ 59
def prefixEnd_1704248 : Nat := 4983230072969 + 3 ^ 40 * 1704248 * 2
def baseEnd_1704248 : Nat := 388932612650557046916583

theorem tailTrace_1704248 : CollatzResearch.WordTrace tailWord_1704248 prefixEnd_1704248 388932612650557046916583 := by
  unfold tailWord_1704248
  simp only [CollatzResearch.WordTrace]
  refine ⟨31079515564904016615424699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41439354086538688820566265 31079515564904016615424699)
  ·
    refine ⟨46619273347356024923137049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31079515564904016615424699 46619273347356024923137049)
    ·
      refine ⟨34964455010517018692352787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46619273347356024923137049 34964455010517018692352787)
      ·
        refine ⟨52446682515775528038529181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34964455010517018692352787 52446682515775528038529181)
        ·
          refine ⟨19667505943415823014448443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52446682515775528038529181 19667505943415823014448443)
          ·
            refine ⟨29501258915123734521672665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19667505943415823014448443 29501258915123734521672665)
            ·
              refine ⟨22125944186342800891254499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29501258915123734521672665 22125944186342800891254499)
              ·
                refine ⟨33188916279514201336881749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22125944186342800891254499 33188916279514201336881749)
                ·
                  refine ⟨388932612650557046916583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33188916279514201336881749 388932612650557046916583)
                  ·
                    rfl

theorem cell21_1704248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_1704248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704248 prefixEnd_1704248 := by exact prefixLift 1704248
  have htrace : WordTrace (prefixWord ++ tailWord_1704248) baseStart_1704248 baseEnd_1704248 := by
    simpa [prefixWord, tailWord_1704248, baseEnd_1704248] using wordTrace_append hprefix tailTrace_1704248
  have hstable : (prefixWord ++ tailWord_1704248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704248).length < 2 ^ (prefixWord ++ tailWord_1704248).sum := by decide
  have hdescent : baseEnd_1704248 < baseStart_1704248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704327 : List Nat := [1, 1, 4, 2, 2, 1, 1, 6, 3]
def baseStart_1704327 : Nat := 118140960795 + 1704327 * 2 ^ 59
def prefixEnd_1704327 : Nat := 4983230072969 + 3 ^ 40 * 1704327 * 2
def baseEnd_1704327 : Nat := 388950641526870465099755

theorem tailTrace_1704327 : CollatzResearch.WordTrace tailWord_1704327 prefixEnd_1704327 388950641526870465099755 := by
  unfold tailWord_1704327
  simp only [CollatzResearch.WordTrace]
  refine ⟨62161912496521829722975235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41441274997681219815316823 62161912496521829722975235)
  ·
    refine ⟨93242868744782744584462853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62161912496521829722975235 93242868744782744584462853)
    ·
      refine ⟨17483037889646764609586785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93242868744782744584462853 17483037889646764609586785)
      ·
        refine ⟨13112278417235073457190089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17483037889646764609586785 13112278417235073457190089)
        ·
          refine ⟨9834208812926305092892567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13112278417235073457190089 9834208812926305092892567)
          ·
            refine ⟨14751313219389457639338851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9834208812926305092892567 14751313219389457639338851)
            ·
              refine ⟨22126969829084186459008277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14751313219389457639338851 22126969829084186459008277)
              ·
                refine ⟨1037201710738321240266013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22126969829084186459008277 1037201710738321240266013)
                ·
                  refine ⟨388950641526870465099755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037201710738321240266013 388950641526870465099755)
                  ·
                    rfl

theorem cell21_1704327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 3].length) (baseStart_1704327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704327 prefixEnd_1704327 := by exact prefixLift 1704327
  have htrace : WordTrace (prefixWord ++ tailWord_1704327) baseStart_1704327 baseEnd_1704327 := by
    simpa [prefixWord, tailWord_1704327, baseEnd_1704327] using wordTrace_append hprefix tailTrace_1704327
  have hstable : (prefixWord ++ tailWord_1704327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704327).length < 2 ^ (prefixWord ++ tailWord_1704327).sum := by decide
  have hdescent : baseEnd_1704327 < baseStart_1704327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704355 : List Nat := [1, 1, 1, 4, 1, 5, 1, 7]
def baseStart_1704355 : Nat := 118140960795 + 1704355 * 2 ^ 59
def prefixEnd_1704355 : Nat := 4983230072969 + 3 ^ 40 * 1704355 * 2
def baseEnd_1704355 : Nat := 129652343836116212877677

theorem tailTrace_1704355 : CollatzResearch.WordTrace tailWord_1704355 prefixEnd_1704355 129652343836116212877677 := by
  unfold tailWord_1704355
  simp only [CollatzResearch.WordTrace]
  refine ⟨62162933740420390504994519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41441955826946927003329679 62162933740420390504994519)
  ·
    refine ⟨93244400610630585757491779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62162933740420390504994519 93244400610630585757491779)
    ·
      refine ⟨139866600915945878636237669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93244400610630585757491779 139866600915945878636237669)
      ·
        refine ⟨26224987671739852244294563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139866600915945878636237669 26224987671739852244294563)
        ·
          refine ⟨39337481507609778366441845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26224987671739852244294563 39337481507609778366441845)
          ·
            refine ⟨3687888891338416721853923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39337481507609778366441845 3687888891338416721853923)
            ·
              refine ⟨5531833337007625082780885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687888891338416721853923 5531833337007625082780885)
              ·
                refine ⟨129652343836116212877677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5531833337007625082780885 129652343836116212877677)
                ·
                  rfl

theorem cell21_1704355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 7].length) (baseStart_1704355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704355 prefixEnd_1704355 := by exact prefixLift 1704355
  have htrace : WordTrace (prefixWord ++ tailWord_1704355) baseStart_1704355 baseEnd_1704355 := by
    simpa [prefixWord, tailWord_1704355, baseEnd_1704355] using wordTrace_append hprefix tailTrace_1704355
  have hstable : (prefixWord ++ tailWord_1704355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704355).length < 2 ^ (prefixWord ++ tailWord_1704355).sum := by decide
  have hdescent : baseEnd_1704355 < baseStart_1704355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704437 : List Nat := [1, 3, 5, 1, 2, 1, 1, 4, 3]
def baseStart_1704437 : Nat := 118140960795 + 1704437 * 2 ^ 59
def prefixEnd_1704437 : Nat := 4983230072969 + 3 ^ 40 * 1704437 * 2
def baseEnd_1704437 : Nat := 388975745025534718266197

theorem tailTrace_1704437 : CollatzResearch.WordTrace tailWord_1704437 prefixEnd_1704437 388975745025534718266197 := by
  unfold tailWord_1704437
  simp only [CollatzResearch.WordTrace]
  refine ⟨62165924526123318509479565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41443949684082212339653043 62165924526123318509479565)
  ·
    refine ⟨23312221697296244441054837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62165924526123318509479565 23312221697296244441054837)
    ·
      refine ⟨2185520784121522916348891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23312221697296244441054837 2185520784121522916348891)
      ·
        refine ⟨3278281176182284374523337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185520784121522916348891 3278281176182284374523337)
        ·
          refine ⟨2458710882136713280892503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3278281176182284374523337 2458710882136713280892503)
          ·
            refine ⟨3688066323205069921338755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458710882136713280892503 3688066323205069921338755)
            ·
              refine ⟨5532099484807604882008133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688066323205069921338755 5532099484807604882008133)
              ·
                refine ⟨1037268653401425915376525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5532099484807604882008133 1037268653401425915376525)
                ·
                  refine ⟨388975745025534718266197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037268653401425915376525 388975745025534718266197)
                  ·
                    rfl

theorem cell21_1704437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_1704437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704437 prefixEnd_1704437 := by exact prefixLift 1704437
  have htrace : WordTrace (prefixWord ++ tailWord_1704437) baseStart_1704437 baseEnd_1704437 := by
    simpa [prefixWord, tailWord_1704437, baseEnd_1704437] using wordTrace_append hprefix tailTrace_1704437
  have hstable : (prefixWord ++ tailWord_1704437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704437).length < 2 ^ (prefixWord ++ tailWord_1704437).sum := by decide
  have hdescent : baseEnd_1704437 < baseStart_1704437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704462 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1704462 : Nat := 118140960795 + 1704462 * 2 ^ 59
def prefixEnd_1704462 : Nat := 4983230072969 + 3 ^ 40 * 1704462 * 2
def baseEnd_1704462 : Nat := 388981450366140230349479

theorem tailTrace_1704462 : CollatzResearch.WordTrace tailWord_1704462 prefixEnd_1704462 388981450366140230349479 := by
  unfold tailWord_1704462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770854543879093472392455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41444557567355165186093093 7770854543879093472392455)
  ·
    refine ⟨11656281815818640208588683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7770854543879093472392455 11656281815818640208588683)
    ·
      refine ⟨17484422723727960312883025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11656281815818640208588683 17484422723727960312883025)
      ·
        refine ⟨13113317042795970234662269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17484422723727960312883025 13113317042795970234662269)
        ·
          refine ⟨4917493891048488837998351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13113317042795970234662269 4917493891048488837998351)
          ·
            refine ⟨7376240836572733256997527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4917493891048488837998351 7376240836572733256997527)
            ·
              refine ⟨11064361254859099885496291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7376240836572733256997527 11064361254859099885496291)
              ·
                refine ⟨16596541882288649828244437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11064361254859099885496291 16596541882288649828244437)
                ·
                  refine ⟨388981450366140230349479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16596541882288649828244437 388981450366140230349479)
                  ·
                    rfl

theorem cell21_1704462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1704462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704462 prefixEnd_1704462 := by exact prefixLift 1704462
  have htrace : WordTrace (prefixWord ++ tailWord_1704462) baseStart_1704462 baseEnd_1704462 := by
    simpa [prefixWord, tailWord_1704462, baseEnd_1704462] using wordTrace_append hprefix tailTrace_1704462
  have hstable : (prefixWord ++ tailWord_1704462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704462).length < 2 ^ (prefixWord ++ tailWord_1704462).sum := by decide
  have hdescent : baseEnd_1704462 < baseStart_1704462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704516 : List Nat := [2, 3, 5, 1, 2, 1, 2, 5]
def baseStart_1704516 : Nat := 118140960795 + 1704516 * 2 ^ 59
def prefixEnd_1704516 : Nat := 4983230072969 + 3 ^ 40 * 1704516 * 2
def baseEnd_1704516 : Nat := 129664591300616045483123

theorem tailTrace_1704516 : CollatzResearch.WordTrace tailWord_1704516 prefixEnd_1704516 129664591300616045483123 := by
  unfold tailWord_1704516
  simp only [CollatzResearch.WordTrace]
  refine ⟨31084402946418557500802701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41445870595224743334403601 31084402946418557500802701)
  ·
    refine ⟨11656651104906959062801013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31084402946418557500802701 11656651104906959062801013)
    ·
      refine ⟨1092811041085027412137595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11656651104906959062801013 1092811041085027412137595)
      ·
        refine ⟨1639216561627541118206393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092811041085027412137595 1639216561627541118206393)
        ·
          refine ⟨1229412421220655838654795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1639216561627541118206393 1229412421220655838654795)
          ·
            refine ⟨1844118631830983757982193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229412421220655838654795 1844118631830983757982193)
            ·
              refine ⟨1383088973873237818486645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844118631830983757982193 1383088973873237818486645)
              ·
                refine ⟨129664591300616045483123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1383088973873237818486645 129664591300616045483123)
                ·
                  rfl

theorem cell21_1704516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_1704516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704516 prefixEnd_1704516 := by exact prefixLift 1704516
  have htrace : WordTrace (prefixWord ++ tailWord_1704516) baseStart_1704516 baseEnd_1704516 := by
    simpa [prefixWord, tailWord_1704516, baseEnd_1704516] using wordTrace_append hprefix tailTrace_1704516
  have hstable : (prefixWord ++ tailWord_1704516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704516).length < 2 ^ (prefixWord ++ tailWord_1704516).sum := by decide
  have hdescent : baseEnd_1704516 < baseStart_1704516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704569 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 4]
def baseStart_1704569 : Nat := 118140960795 + 1704569 * 2 ^ 59
def prefixEnd_1704569 : Nat := 4983230072969 + 3 ^ 40 * 1704569 * 2
def baseEnd_1704569 : Nat := 389005869223931822065927

theorem tailTrace_1704569 : CollatzResearch.WordTrace tailWord_1704569 prefixEnd_1704569 389005869223931822065927 := by
  unfold tailWord_1704569
  simp only [CollatzResearch.WordTrace]
  refine ⟨62170738961645105053284761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41447159307763403368856507 62170738961645105053284761)
  ·
    refine ⟨46628054221233828789963571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62170738961645105053284761 46628054221233828789963571)
    ·
      refine ⟨69942081331850743184945357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46628054221233828789963571 69942081331850743184945357)
      ·
        refine ⟨26228280499444028694354509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69942081331850743184945357 26228280499444028694354509)
        ·
          refine ⟨9835605187291510760382941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26228280499444028694354509 9835605187291510760382941)
          ·
            refine ⟨3688351945234316535143603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9835605187291510760382941 3688351945234316535143603)
            ·
              refine ⟨5532527917851474802715405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688351945234316535143603 5532527917851474802715405)
              ·
                refine ⟨2074697969194303051018277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5532527917851474802715405 2074697969194303051018277)
                ·
                  refine ⟨389005869223931822065927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2074697969194303051018277 389005869223931822065927)
                  ·
                    rfl

theorem cell21_1704569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_1704569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704569 prefixEnd_1704569 := by exact prefixLift 1704569
  have htrace : WordTrace (prefixWord ++ tailWord_1704569) baseStart_1704569 baseEnd_1704569 := by
    simpa [prefixWord, tailWord_1704569, baseEnd_1704569] using wordTrace_append hprefix tailTrace_1704569
  have hstable : (prefixWord ++ tailWord_1704569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704569).length < 2 ^ (prefixWord ++ tailWord_1704569).sum := by decide
  have hdescent : baseEnd_1704569 < baseStart_1704569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704690 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1704690 : Nat := 118140960795 + 1704690 * 2 ^ 59
def prefixEnd_1704690 : Nat := 4983230072969 + 3 ^ 40 * 1704690 * 2
def baseEnd_1704690 : Nat := 389033483072462500549013

theorem tailTrace_1704690 : CollatzResearch.WordTrace tailWord_1704690 prefixEnd_1704690 389033483072462500549013 := by
  unfold tailWord_1704690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15543788048551685679609881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41450101462804495145626349 15543788048551685679609881)
  ·
    refine ⟨11657841036413764259707411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15543788048551685679609881 11657841036413764259707411)
    ·
      refine ⟨17486761554620646389561117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11657841036413764259707411 17486761554620646389561117)
      ·
        refine ⟨6557535582982742396085419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17486761554620646389561117 6557535582982742396085419)
        ·
          refine ⟨9836303374474113594128129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6557535582982742396085419 9836303374474113594128129)
          ·
            refine ⟨7377227530855585195596097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9836303374474113594128129 7377227530855585195596097)
            ·
              refine ⟨5532920648141688896697073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377227530855585195596097 5532920648141688896697073)
              ·
                refine ⟨4149690486106266672522805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532920648141688896697073 4149690486106266672522805)
                ·
                  refine ⟨389033483072462500549013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4149690486106266672522805 389033483072462500549013)
                  ·
                    rfl

theorem cell21_1704690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1704690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704690 prefixEnd_1704690 := by exact prefixLift 1704690
  have htrace : WordTrace (prefixWord ++ tailWord_1704690) baseStart_1704690 baseEnd_1704690 := by
    simpa [prefixWord, tailWord_1704690, baseEnd_1704690] using wordTrace_append hprefix tailTrace_1704690
  have hstable : (prefixWord ++ tailWord_1704690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704690).length < 2 ^ (prefixWord ++ tailWord_1704690).sum := by decide
  have hdescent : baseEnd_1704690 < baseStart_1704690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704735 : List Nat := [1, 1, 2, 4, 2, 3, 2, 6]
def baseStart_1704735 : Nat := 118140960795 + 1704735 * 2 ^ 59
def prefixEnd_1704735 : Nat := 4983230072969 + 3 ^ 40 * 1704735 * 2
def baseEnd_1704735 : Nat := 129681250895184140766307

theorem tailTrace_1704735 : CollatzResearch.WordTrace tailWord_1704735 prefixEnd_1704735 129681250895184140766307 := by
  unfold tailWord_1704735
  simp only [CollatzResearch.WordTrace]
  refine ⟨62176793479043715403827659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41451195652695810269218439 62176793479043715403827659)
  ·
    refine ⟨93265190218565573105741489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62176793479043715403827659 93265190218565573105741489)
    ·
      refine ⟨69948892663924179829306117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93265190218565573105741489 69948892663924179829306117)
      ·
        refine ⟨13115417374485783717994897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69948892663924179829306117 13115417374485783717994897)
        ·
          refine ⟨9836563030864337788496173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13115417374485783717994897 9836563030864337788496173)
          ·
            refine ⟨3688711136574126670686065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9836563030864337788496173 3688711136574126670686065)
            ·
              refine ⟨2766533352430595003014549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3688711136574126670686065 2766533352430595003014549)
              ·
                refine ⟨129681250895184140766307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2766533352430595003014549 129681250895184140766307)
                ·
                  rfl

theorem cell21_1704735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 6].length) (baseStart_1704735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704735 prefixEnd_1704735 := by exact prefixLift 1704735
  have htrace : WordTrace (prefixWord ++ tailWord_1704735) baseStart_1704735 baseEnd_1704735 := by
    simpa [prefixWord, tailWord_1704735, baseEnd_1704735] using wordTrace_append hprefix tailTrace_1704735
  have hstable : (prefixWord ++ tailWord_1704735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704735).length < 2 ^ (prefixWord ++ tailWord_1704735).sum := by decide
  have hdescent : baseEnd_1704735 < baseStart_1704735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704738 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1704738 : Nat := 118140960795 + 1704738 * 2 ^ 59
def prefixEnd_1704738 : Nat := 4983230072969 + 3 ^ 40 * 1704738 * 2
def baseEnd_1704738 : Nat := 389044437326425083748915

theorem tailTrace_1704738 : CollatzResearch.WordTrace tailWord_1704738 prefixEnd_1704738 389044437326425083748915 := by
  unfold tailWord_1704738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544225724508211729046717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41451268598688564610791245 15544225724508211729046717)
  ·
    refine ⟨5829084646690579398392519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15544225724508211729046717 5829084646690579398392519)
    ·
      refine ⟨8743626970035869097588779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5829084646690579398392519 8743626970035869097588779)
      ·
        refine ⟨13115440455053803646383169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8743626970035869097588779 13115440455053803646383169)
        ·
          refine ⟨9836580341290352734787377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13115440455053803646383169 9836580341290352734787377)
          ·
            refine ⟨7377435255967764551090533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9836580341290352734787377 7377435255967764551090533)
            ·
              refine ⟨1383269110493955853329475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7377435255967764551090533 1383269110493955853329475)
              ·
                refine ⟨2074903665740933779994213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383269110493955853329475 2074903665740933779994213)
                ·
                  refine ⟨389044437326425083748915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2074903665740933779994213 389044437326425083748915)
                  ·
                    rfl

theorem cell21_1704738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1704738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704738 prefixEnd_1704738 := by exact prefixLift 1704738
  have htrace : WordTrace (prefixWord ++ tailWord_1704738) baseStart_1704738 baseEnd_1704738 := by
    simpa [prefixWord, tailWord_1704738, baseEnd_1704738] using wordTrace_append hprefix tailTrace_1704738
  have hstable : (prefixWord ++ tailWord_1704738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704738).length < 2 ^ (prefixWord ++ tailWord_1704738).sum := by decide
  have hdescent : baseEnd_1704738 < baseStart_1704738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704842 : List Nat := [3, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_1704842 : Nat := 118140960795 + 1704842 * 2 ^ 59
def prefixEnd_1704842 : Nat := 4983230072969 + 3 ^ 40 * 1704842 * 2
def baseEnd_1704842 : Nat := 389068171543344014015369

theorem tailTrace_1704842 : CollatzResearch.WordTrace tailWord_1704842 prefixEnd_1704842 389068171543344014015369 := by
  unfold tailWord_1704842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545174022414018169493195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41453797393104048451981853 15545174022414018169493195)
  ·
    refine ⟨23317761033621027254239793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15545174022414018169493195 23317761033621027254239793)
    ·
      refine ⟨17488320775215770440679845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23317761033621027254239793 17488320775215770440679845)
      ·
        refine ⟨3279060145352956957627471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17488320775215770440679845 3279060145352956957627471)
        ·
          refine ⟨4918590218029435436441207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279060145352956957627471 4918590218029435436441207)
          ·
            refine ⟨7377885327044153154661811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918590218029435436441207 7377885327044153154661811)
            ·
              refine ⟨11066827990566229731992717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377885327044153154661811 11066827990566229731992717)
              ·
                refine ⟨4150060496462336149497269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11066827990566229731992717 4150060496462336149497269)
                ·
                  refine ⟨389068171543344014015369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4150060496462336149497269 389068171543344014015369)
                  ·
                    rfl

theorem cell21_1704842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_1704842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1704842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1704842 prefixEnd_1704842 := by exact prefixLift 1704842
  have htrace : WordTrace (prefixWord ++ tailWord_1704842) baseStart_1704842 baseEnd_1704842 := by
    simpa [prefixWord, tailWord_1704842, baseEnd_1704842] using wordTrace_append hprefix tailTrace_1704842
  have hstable : (prefixWord ++ tailWord_1704842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704842).length < 2 ^ (prefixWord ++ tailWord_1704842).sum := by decide
  have hdescent : baseEnd_1704842 < baseStart_1704842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705070 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1705070 : Nat := 118140960795 + 1705070 * 2 ^ 59
def prefixEnd_1705070 : Nat := 4983230072969 + 3 ^ 40 * 1705070 * 2
def baseEnd_1705070 : Nat := 389120204249666284214903

theorem tailTrace_1705070 : CollatzResearch.WordTrace tailWord_1705070 prefixEnd_1705070 389120204249666284214903 := by
  unfold tailWord_1705070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773626491603758452159083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41459341288553378411515109 7773626491603758452159083)
  ·
    refine ⟨11660439737405637678238625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7773626491603758452159083 11660439737405637678238625)
    ·
      refine ⟨8745329803054228258678969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11660439737405637678238625 8745329803054228258678969)
      ·
        refine ⟨6558997352290671194009227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8745329803054228258678969 6558997352290671194009227)
        ·
          refine ⟨9838496028436006791013841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6558997352290671194009227 9838496028436006791013841)
          ·
            refine ⟨7378872021327005093260381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9838496028436006791013841 7378872021327005093260381)
            ·
              refine ⟨2767077007997626909972643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7378872021327005093260381 2767077007997626909972643)
              ·
                refine ⟨4150615511996440364958965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767077007997626909972643 4150615511996440364958965)
                ·
                  refine ⟨389120204249666284214903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4150615511996440364958965 389120204249666284214903)
                  ·
                    rfl

theorem cell21_1705070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1705070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705070 prefixEnd_1705070 := by exact prefixLift 1705070
  have htrace : WordTrace (prefixWord ++ tailWord_1705070) baseStart_1705070 baseEnd_1705070 := by
    simpa [prefixWord, tailWord_1705070, baseEnd_1705070] using wordTrace_append hprefix tailTrace_1705070
  have hstable : (prefixWord ++ tailWord_1705070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705070).length < 2 ^ (prefixWord ++ tailWord_1705070).sum := by decide
  have hdescent : baseEnd_1705070 < baseStart_1705070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705084 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_1705084 : Nat := 118140960795 + 1705084 * 2 ^ 59
def prefixEnd_1705084 : Nat := 4983230072969 + 3 ^ 40 * 1705084 * 2
def baseEnd_1705084 : Nat := 389123399240405370981541

theorem tailTrace_1705084 : CollatzResearch.WordTrace tailWord_1705084 prefixEnd_1705084 389123399240405370981541 := by
  unfold tailWord_1705084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31094761277389674004141153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41459681703186232005521537 31094761277389674004141153)
  ·
    refine ⟨23321070958042255503105865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31094761277389674004141153 23321070958042255503105865)
    ·
      refine ⟨17490803218531691627329399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23321070958042255503105865 17490803218531691627329399)
      ·
        refine ⟨26236204827797537440994099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17490803218531691627329399 26236204827797537440994099)
        ·
          refine ⟨39354307241696306161491149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26236204827797537440994099 39354307241696306161491149)
          ·
            refine ⟨14757865215636114810559181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39354307241696306161491149 14757865215636114810559181)
            ·
              refine ⟨5534199455863543053959693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14757865215636114810559181 5534199455863543053959693)
              ·
                refine ⟨2075324795948828645234885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5534199455863543053959693 2075324795948828645234885)
                ·
                  refine ⟨389123399240405370981541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075324795948828645234885 389123399240405370981541)
                  ·
                    rfl

theorem cell21_1705084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_1705084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705084 prefixEnd_1705084 := by exact prefixLift 1705084
  have htrace : WordTrace (prefixWord ++ tailWord_1705084) baseStart_1705084 baseEnd_1705084 := by
    simpa [prefixWord, tailWord_1705084, baseEnd_1705084] using wordTrace_append hprefix tailTrace_1705084
  have hstable : (prefixWord ++ tailWord_1705084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705084).length < 2 ^ (prefixWord ++ tailWord_1705084).sum := by decide
  have hdescent : baseEnd_1705084 < baseStart_1705084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705098 : List Nat := [3, 1, 2, 3, 1, 1, 1, 9]
def baseStart_1705098 : Nat := 118140960795 + 1705098 * 2 ^ 59
def prefixEnd_1705098 : Nat := 4983230072969 + 3 ^ 40 * 1705098 * 2
def baseEnd_1705098 : Nat := 129708864743714819249393

theorem tailTrace_1705098 : CollatzResearch.WordTrace tailWord_1705098 prefixEnd_1705098 129708864743714819249393 := by
  unfold tailWord_1705098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15547508294182157099822987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41460022117819085599527965 15547508294182157099822987)
  ·
    refine ⟨23321262441273235649734481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15547508294182157099822987 23321262441273235649734481)
    ·
      refine ⟨17490946830954926737300861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23321262441273235649734481 17490946830954926737300861)
      ·
        refine ⟨6559105061608097526487823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17490946830954926737300861 6559105061608097526487823)
        ·
          refine ⟨9838657592412146289731735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559105061608097526487823 9838657592412146289731735)
          ·
            refine ⟨14757986388618219434597603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838657592412146289731735 14757986388618219434597603)
            ·
              refine ⟨22136979582927329151896405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14757986388618219434597603 22136979582927329151896405)
              ·
                refine ⟨129708864743714819249393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22136979582927329151896405 129708864743714819249393)
                ·
                  rfl

theorem cell21_1705098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_1705098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705098 prefixEnd_1705098 := by exact prefixLift 1705098
  have htrace : WordTrace (prefixWord ++ tailWord_1705098) baseStart_1705098 baseEnd_1705098 := by
    simpa [prefixWord, tailWord_1705098, baseEnd_1705098] using wordTrace_append hprefix tailTrace_1705098
  have hstable : (prefixWord ++ tailWord_1705098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705098).length < 2 ^ (prefixWord ++ tailWord_1705098).sum := by decide
  have hdescent : baseEnd_1705098 < baseStart_1705098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705118 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1705118 : Nat := 118140960795 + 1705118 * 2 ^ 59
def prefixEnd_1705118 : Nat := 4983230072969 + 3 ^ 40 * 1705118 * 2
def baseEnd_1705118 : Nat := 389131158503628867414805

theorem tailTrace_1705118 : CollatzResearch.WordTrace tailWord_1705118 prefixEnd_1705118 389131158503628867414805 := by
  unfold tailWord_1705118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773845329582021476877501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41460508424437447876680005 7773845329582021476877501)
  ·
    refine ⟨2915191998593258053829063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7773845329582021476877501 2915191998593258053829063)
    ·
      refine ⟨4372787997889887080743595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915191998593258053829063 4372787997889887080743595)
      ·
        refine ⟨6559181996834830621115393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372787997889887080743595 6559181996834830621115393)
        ·
          refine ⟨4919386497626122965836545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6559181996834830621115393 4919386497626122965836545)
          ·
            refine ⟨3689539873219592224377409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919386497626122965836545 3689539873219592224377409)
            ·
              refine ⟨2767154904914694168283057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689539873219592224377409 2767154904914694168283057)
              ·
                refine ⟨2075366178686020626212293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767154904914694168283057 2075366178686020626212293)
                ·
                  refine ⟨389131158503628867414805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075366178686020626212293 389131158503628867414805)
                  ·
                    rfl

theorem cell21_1705118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1705118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705118 prefixEnd_1705118 := by exact prefixLift 1705118
  have htrace : WordTrace (prefixWord ++ tailWord_1705118) baseStart_1705118 baseEnd_1705118 := by
    simpa [prefixWord, tailWord_1705118, baseEnd_1705118] using wordTrace_append hprefix tailTrace_1705118
  have hstable : (prefixWord ++ tailWord_1705118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705118).length < 2 ^ (prefixWord ++ tailWord_1705118).sum := by decide
  have hdescent : baseEnd_1705118 < baseStart_1705118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705219 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 6]
def baseStart_1705219 : Nat := 118140960795 + 1705219 * 2 ^ 59
def prefixEnd_1705219 : Nat := 4983230072969 + 3 ^ 40 * 1705219 * 2
def baseEnd_1705219 : Nat := 389154208079675136231265

theorem tailTrace_1705219 : CollatzResearch.WordTrace tailWord_1705219 prefixEnd_1705219 389154208079675136231265 := by
  unfold tailWord_1705219
  simp only [CollatzResearch.WordTrace]
  refine ⟨62194446409290266064446711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41462964272860177376297807 62194446409290266064446711)
  ·
    refine ⟨93291669613935399096670067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62194446409290266064446711 93291669613935399096670067)
    ·
      refine ⟨139937504420903098645005101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93291669613935399096670067 139937504420903098645005101)
      ·
        refine ⟨52476564157838661991876913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139937504420903098645005101 52476564157838661991876913)
        ·
          refine ⟨39357423118378996493907685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52476564157838661991876913 39357423118378996493907685)
          ·
            refine ⟨7379516834696061842607691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39357423118378996493907685 7379516834696061842607691)
            ·
              refine ⟨11069275252044092763911537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379516834696061842607691 11069275252044092763911537)
              ·
                refine ⟨8301956439033069572933653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11069275252044092763911537 8301956439033069572933653)
                ·
                  refine ⟨389154208079675136231265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8301956439033069572933653 389154208079675136231265)
                  ·
                    rfl

theorem cell21_1705219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_1705219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705219 prefixEnd_1705219 := by exact prefixLift 1705219
  have htrace : WordTrace (prefixWord ++ tailWord_1705219) baseStart_1705219 baseEnd_1705219 := by
    simpa [prefixWord, tailWord_1705219, baseEnd_1705219] using wordTrace_append hprefix tailTrace_1705219
  have hstable : (prefixWord ++ tailWord_1705219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705219).length < 2 ^ (prefixWord ++ tailWord_1705219).sum := by decide
  have hdescent : baseEnd_1705219 < baseStart_1705219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705239 : List Nat := [1, 1, 3, 4, 1, 1, 5, 2, 3]
def baseStart_1705239 : Nat := 118140960795 + 1705239 * 2 ^ 59
def prefixEnd_1705239 : Nat := 4983230072969 + 3 ^ 40 * 1705239 * 2
def baseEnd_1705239 : Nat := 389158772352159545897891

theorem tailTrace_1705239 : CollatzResearch.WordTrace tailWord_1705239 prefixEnd_1705239 389158772352159545897891 := by
  unfold tailWord_1705239
  simp only [CollatzResearch.WordTrace]
  refine ⟨62195175869217809480174771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41463450579478539653449847 62195175869217809480174771)
  ·
    refine ⟨93292763803826714220262157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62195175869217809480174771 93292763803826714220262157)
    ·
      refine ⟨34984786426435017832598309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93292763803826714220262157 34984786426435017832598309)
      ·
        refine ⟨6559647454956565843612183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34984786426435017832598309 6559647454956565843612183)
        ·
          refine ⟨9839471182434848765418275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559647454956565843612183 9839471182434848765418275)
          ·
            refine ⟨14759206773652273148127413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9839471182434848765418275 14759206773652273148127413)
            ·
              refine ⟨1383675635029900607636945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14759206773652273148127413 1383675635029900607636945)
              ·
                refine ⟨1037756726272425455727709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383675635029900607636945 1037756726272425455727709)
                ·
                  refine ⟨389158772352159545897891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037756726272425455727709 389158772352159545897891)
                  ·
                    rfl

theorem cell21_1705239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 3].length) (baseStart_1705239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705239 prefixEnd_1705239 := by exact prefixLift 1705239
  have htrace : WordTrace (prefixWord ++ tailWord_1705239) baseStart_1705239 baseEnd_1705239 := by
    simpa [prefixWord, tailWord_1705239, baseEnd_1705239] using wordTrace_append hprefix tailTrace_1705239
  have hstable : (prefixWord ++ tailWord_1705239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705239).length < 2 ^ (prefixWord ++ tailWord_1705239).sum := by decide
  have hdescent : baseEnd_1705239 < baseStart_1705239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705253 : List Nat := [1, 3, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1705253 : Nat := 118140960795 + 1705253 * 2 ^ 59
def prefixEnd_1705253 : Nat := 4983230072969 + 3 ^ 40 * 1705253 * 2
def baseEnd_1705253 : Nat := 389161967342898632664529

theorem tailTrace_1705253 : CollatzResearch.WordTrace tailWord_1705253 prefixEnd_1705253 389161967342898632664529 := by
  unfold tailWord_1705253
  simp only [CollatzResearch.WordTrace]
  refine ⟨62195686491167089871184413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41463790994111393247456275 62195686491167089871184413)
  ·
    refine ⟨23323382434187658701694155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62195686491167089871184413 23323382434187658701694155)
    ·
      refine ⟨34985073651281488052541233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23323382434187658701694155 34985073651281488052541233)
      ·
        refine ⟨26238805238461116039405925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34985073651281488052541233 26238805238461116039405925)
        ·
          refine ⟨4919775982211459257388611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26238805238461116039405925 4919775982211459257388611)
          ·
            refine ⟨7379663973317188886082917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919775982211459257388611 7379663973317188886082917)
            ·
              refine ⟨1383686994996972916140547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7379663973317188886082917 1383686994996972916140547)
              ·
                refine ⟨2075530492495459374210821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383686994996972916140547 2075530492495459374210821)
                ·
                  refine ⟨389161967342898632664529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075530492495459374210821 389161967342898632664529)
                  ·
                    rfl

theorem cell21_1705253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1705253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705253 prefixEnd_1705253 := by exact prefixLift 1705253
  have htrace : WordTrace (prefixWord ++ tailWord_1705253) baseStart_1705253 baseEnd_1705253 := by
    simpa [prefixWord, tailWord_1705253, baseEnd_1705253] using wordTrace_append hprefix tailTrace_1705253
  have hstable : (prefixWord ++ tailWord_1705253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705253).length < 2 ^ (prefixWord ++ tailWord_1705253).sum := by decide
  have hdescent : baseEnd_1705253 < baseStart_1705253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705264 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_1705264 : Nat := 118140960795 + 1705264 * 2 ^ 59
def prefixEnd_1705264 : Nat := 4983230072969 + 3 ^ 40 * 1705264 * 2
def baseEnd_1705264 : Nat := 389164477692765057981173

theorem tailTrace_1705264 : CollatzResearch.WordTrace tailWord_1705264 prefixEnd_1705264 389164477692765057981173 := by
  unfold tailWord_1705264
  simp only [CollatzResearch.WordTrace]
  refine ⟨31098043847063619374917423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41464058462751492499889897 31098043847063619374917423)
  ·
    refine ⟨46647065770595429062376135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31098043847063619374917423 46647065770595429062376135)
    ·
      refine ⟨69970598655893143593564203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46647065770595429062376135 69970598655893143593564203)
      ·
        refine ⟨104955897983839715390346305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69970598655893143593564203 104955897983839715390346305)
        ·
          refine ⟨78716923487879786542759729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104955897983839715390346305 78716923487879786542759729)
          ·
            refine ⟨59037692615909839907069797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78716923487879786542759729 59037692615909839907069797)
            ·
              refine ⟨11069567365483094982575587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59037692615909839907069797 11069567365483094982575587)
              ·
                refine ⟨16604351048224642473863381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11069567365483094982575587 16604351048224642473863381)
                ·
                  refine ⟨389164477692765057981173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16604351048224642473863381 389164477692765057981173)
                  ·
                    rfl

theorem cell21_1705264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_1705264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705264 prefixEnd_1705264 := by exact prefixLift 1705264
  have htrace : WordTrace (prefixWord ++ tailWord_1705264) baseStart_1705264 baseEnd_1705264 := by
    simpa [prefixWord, tailWord_1705264, baseEnd_1705264] using wordTrace_append hprefix tailTrace_1705264
  have hstable : (prefixWord ++ tailWord_1705264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705264).length < 2 ^ (prefixWord ++ tailWord_1705264).sum := by decide
  have hdescent : baseEnd_1705264 < baseStart_1705264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705312 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_1705312 : Nat := 118140960795 + 1705312 * 2 ^ 59
def prefixEnd_1705312 : Nat := 4983230072969 + 3 ^ 40 * 1705312 * 2
def baseEnd_1705312 : Nat := 389175431946727641181075

theorem tailTrace_1705312 : CollatzResearch.WordTrace tailWord_1705312 prefixEnd_1705312 389175431946727641181075 := by
  unfold tailWord_1705312
  simp only [CollatzResearch.WordTrace]
  refine ⟨31098919198976671473791095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41465225598635561965054793 31098919198976671473791095)
  ·
    refine ⟨46648378798465007210686643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31098919198976671473791095 46648378798465007210686643)
    ·
      refine ⟨69972568197697510816029965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46648378798465007210686643 69972568197697510816029965)
      ·
        refine ⟨26239713074136566556011237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69972568197697510816029965 26239713074136566556011237)
        ·
          refine ⟨4919946201400606229252107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26239713074136566556011237 4919946201400606229252107)
          ·
            refine ⟨7379919302100909343878161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919946201400606229252107 7379919302100909343878161)
            ·
              refine ⟨5534939476575682007908621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7379919302100909343878161 5534939476575682007908621)
              ·
                refine ⟨2075602303715880752965733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5534939476575682007908621 2075602303715880752965733)
                ·
                  refine ⟨389175431946727641181075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075602303715880752965733 389175431946727641181075)
                  ·
                    rfl

theorem cell21_1705312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_1705312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705312 prefixEnd_1705312 := by exact prefixLift 1705312
  have htrace : WordTrace (prefixWord ++ tailWord_1705312) baseStart_1705312 baseEnd_1705312 := by
    simpa [prefixWord, tailWord_1705312, baseEnd_1705312] using wordTrace_append hprefix tailTrace_1705312
  have hstable : (prefixWord ++ tailWord_1705312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705312).length < 2 ^ (prefixWord ++ tailWord_1705312).sum := by decide
  have hdescent : baseEnd_1705312 < baseStart_1705312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705340 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_1705340 : Nat := 118140960795 + 1705340 * 2 ^ 59
def prefixEnd_1705340 : Nat := 4983230072969 + 3 ^ 40 * 1705340 * 2
def baseEnd_1705340 : Nat := 389181821928205814714351

theorem tailTrace_1705340 : CollatzResearch.WordTrace tailWord_1705340 prefixEnd_1705340 389181821928205814714351 := by
  unfold tailWord_1705340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31099429820925951864800737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41465906427901269153067649 31099429820925951864800737)
  ·
    refine ⟨23324572365694463898600553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31099429820925951864800737 23324572365694463898600553)
    ·
      refine ⟨17493429274270847923950415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23324572365694463898600553 17493429274270847923950415)
      ·
        refine ⟨26240143911406271885925623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17493429274270847923950415 26240143911406271885925623)
        ·
          refine ⟨39360215867109407828888435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26240143911406271885925623 39360215867109407828888435)
          ·
            refine ⟨59040323800664111743332653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39360215867109407828888435 59040323800664111743332653)
            ·
              refine ⟨22140121425249041903749745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59040323800664111743332653 22140121425249041903749745)
              ·
                refine ⟨16605091068936781427812309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22140121425249041903749745 16605091068936781427812309)
                ·
                  refine ⟨389181821928205814714351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16605091068936781427812309 389181821928205814714351)
                  ·
                    rfl

theorem cell21_1705340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_1705340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705340 prefixEnd_1705340 := by exact prefixLift 1705340
  have htrace : WordTrace (prefixWord ++ tailWord_1705340) baseStart_1705340 baseEnd_1705340 := by
    simpa [prefixWord, tailWord_1705340, baseEnd_1705340] using wordTrace_append hprefix tailTrace_1705340
  have hstable : (prefixWord ++ tailWord_1705340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705340).length < 2 ^ (prefixWord ++ tailWord_1705340).sum := by decide
  have hdescent : baseEnd_1705340 < baseStart_1705340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705346 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1705346 : Nat := 118140960795 + 1705346 * 2 ^ 59
def prefixEnd_1705346 : Nat := 4983230072969 + 3 ^ 40 * 1705346 * 2
def baseEnd_1705346 : Nat := 389183191209951137614339

theorem tailTrace_1705346 : CollatzResearch.WordTrace tailWord_1705346 prefixEnd_1705346 389183191209951137614339 := by
  unfold tailWord_1705346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15549769619957541688579973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41466052319886777836213261 15549769619957541688579973)
  ·
    refine ⟨2915581803742039066608745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15549769619957541688579973 2915581803742039066608745)
    ·
      refine ⟨2186686352806529299956559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2915581803742039066608745 2186686352806529299956559)
      ·
        refine ⟨3280029529209793949934839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186686352806529299956559 3280029529209793949934839)
        ·
          refine ⟨4920044293814690924902259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280029529209793949934839 4920044293814690924902259)
          ·
            refine ⟨7380066440722036387353389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920044293814690924902259 7380066440722036387353389)
            ·
              refine ⟨2767524915270763645257521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7380066440722036387353389 2767524915270763645257521)
              ·
                refine ⟨2075643686453072733943141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767524915270763645257521 2075643686453072733943141)
                ·
                  refine ⟨389183191209951137614339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075643686453072733943141 389183191209951137614339)
                  ·
                    rfl

theorem cell21_1705346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1705346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705346 prefixEnd_1705346 := by exact prefixLift 1705346
  have htrace : WordTrace (prefixWord ++ tailWord_1705346) baseStart_1705346 baseEnd_1705346 := by
    simpa [prefixWord, tailWord_1705346, baseEnd_1705346] using wordTrace_append hprefix tailTrace_1705346
  have hstable : (prefixWord ++ tailWord_1705346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705346).length < 2 ^ (prefixWord ++ tailWord_1705346).sum := by decide
  have hdescent : baseEnd_1705346 < baseStart_1705346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705464 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_1705464 : Nat := 118140960795 + 1705464 * 2 ^ 59
def prefixEnd_1705464 : Nat := 4983230072969 + 3 ^ 40 * 1705464 * 2
def baseEnd_1705464 : Nat := 389210120417609154647431

theorem tailTrace_1705464 : CollatzResearch.WordTrace tailWord_1705464 prefixEnd_1705464 389210120417609154647431 := by
  unfold tailWord_1705464
  simp only [CollatzResearch.WordTrace]
  refine ⟨31101691146701336453557723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41468921528935115271410297 31101691146701336453557723)
  ·
    refine ⟨46652536720052004680336585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31101691146701336453557723 46652536720052004680336585)
    ·
      refine ⟨34989402540039003510252439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46652536720052004680336585 34989402540039003510252439)
      ·
        refine ⟨52484103810058505265378659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34989402540039003510252439 52484103810058505265378659)
        ·
          refine ⟨78726155715087757898067989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52484103810058505265378659 78726155715087757898067989)
          ·
            refine ⟨3690288549144738651471937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78726155715087757898067989 3690288549144738651471937)
            ·
              refine ⟨2767716411858553988603953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3690288549144738651471937 2767716411858553988603953)
              ·
                refine ⟨2075787308893915491452965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767716411858553988603953 2075787308893915491452965)
                ·
                  refine ⟨389210120417609154647431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075787308893915491452965 389210120417609154647431)
                  ·
                    rfl

theorem cell21_1705464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_1705464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705464 prefixEnd_1705464 := by exact prefixLift 1705464
  have htrace : WordTrace (prefixWord ++ tailWord_1705464) baseStart_1705464 baseEnd_1705464 := by
    simpa [prefixWord, tailWord_1705464, baseEnd_1705464] using wordTrace_append hprefix tailTrace_1705464
  have hstable : (prefixWord ++ tailWord_1705464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705464).length < 2 ^ (prefixWord ++ tailWord_1705464).sum := by decide
  have hdescent : baseEnd_1705464 < baseStart_1705464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705523 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 6]
def baseStart_1705523 : Nat := 118140960795 + 1705523 * 2 ^ 59
def prefixEnd_1705523 : Nat := 4983230072969 + 3 ^ 40 * 1705523 * 2
def baseEnd_1705523 : Nat := 389223585021438163163977

theorem tailTrace_1705523 : CollatzResearch.WordTrace tailWord_1705523 prefixEnd_1705523 389223585021438163163977 := by
  unfold tailWord_1705523
  simp only [CollatzResearch.WordTrace]
  refine ⟨62205534200188925983513223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41470356133459283989008815 62205534200188925983513223)
  ·
    refine ⟨93308301300283388975269835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62205534200188925983513223 93308301300283388975269835)
    ·
      refine ⟨139962451950425083462904753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93308301300283388975269835 139962451950425083462904753)
      ·
        refine ⟨104971838962818812597178565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139962451950425083462904753 104971838962818812597178565)
        ·
          refine ⟨19682219805528527361970981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104971838962818812597178565 19682219805528527361970981)
          ·
            refine ⟨3690416213536598880369559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19682219805528527361970981 3690416213536598880369559)
            ·
              refine ⟨5535624320304898320554339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690416213536598880369559 5535624320304898320554339)
              ·
                refine ⟨8303436480457347480831509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535624320304898320554339 8303436480457347480831509)
                ·
                  refine ⟨389223585021438163163977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8303436480457347480831509 389223585021438163163977)
                  ·
                    rfl

theorem cell21_1705523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_1705523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705523 prefixEnd_1705523 := by exact prefixLift 1705523
  have htrace : WordTrace (prefixWord ++ tailWord_1705523) baseStart_1705523 baseEnd_1705523 := by
    simpa [prefixWord, tailWord_1705523, baseEnd_1705523] using wordTrace_append hprefix tailTrace_1705523
  have hstable : (prefixWord ++ tailWord_1705523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705523).length < 2 ^ (prefixWord ++ tailWord_1705523).sum := by decide
  have hdescent : baseEnd_1705523 < baseStart_1705523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705554 : List Nat := [3, 2, 2, 1, 2, 3, 1, 7]
def baseStart_1705554 : Nat := 118140960795 + 1705554 * 2 ^ 59
def prefixEnd_1705554 : Nat := 4983230072969 + 3 ^ 40 * 1705554 * 2
def baseEnd_1705554 : Nat := 129743553214596332715749

theorem tailTrace_1705554 : CollatzResearch.WordTrace tailWord_1705554 prefixEnd_1705554 129743553214596332715749 := by
  unfold tailWord_1705554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15551666215769154569472929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41471109908717745518594477 15551666215769154569472929)
  ·
    refine ⟨11663749661826865927104697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15551666215769154569472929 11663749661826865927104697)
    ·
      refine ⟨8747812246370149445328523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11663749661826865927104697 8747812246370149445328523)
      ·
        refine ⟨13121718369555224167992785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8747812246370149445328523 13121718369555224167992785)
        ·
          refine ⟨9841288777166418125994589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13121718369555224167992785 9841288777166418125994589)
          ·
            refine ⟨3690483291437406797247971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9841288777166418125994589 3690483291437406797247971)
            ·
              refine ⟨5535724937156110195871957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690483291437406797247971 5535724937156110195871957)
              ·
                refine ⟨129743553214596332715749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5535724937156110195871957 129743553214596332715749)
                ·
                  rfl

theorem cell21_1705554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_1705554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705554 prefixEnd_1705554 := by exact prefixLift 1705554
  have htrace : WordTrace (prefixWord ++ tailWord_1705554) baseStart_1705554 baseEnd_1705554 := by
    simpa [prefixWord, tailWord_1705554, baseEnd_1705554] using wordTrace_append hprefix tailTrace_1705554
  have hstable : (prefixWord ++ tailWord_1705554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705554).length < 2 ^ (prefixWord ++ tailWord_1705554).sum := by decide
  have hdescent : baseEnd_1705554 < baseStart_1705554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705585 : List Nat := [1, 2, 2, 2, 1, 1, 1, 8, 3]
def baseStart_1705585 : Nat := 118140960795 + 1705585 * 2 ^ 59
def prefixEnd_1705585 : Nat := 4983230072969 + 3 ^ 40 * 1705585 * 2
def baseEnd_1705585 : Nat := 389237734266139833130517

theorem tailTrace_1705585 : CollatzResearch.WordTrace tailWord_1705585 prefixEnd_1705585 389237734266139833130517 := by
  unfold tailWord_1705585
  simp only [CollatzResearch.WordTrace]
  refine ⟨62207795525964310572270209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41471863683976207048180139 62207795525964310572270209)
  ·
    refine ⟨46655846644473232929202657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62207795525964310572270209 46655846644473232929202657)
    ·
      refine ⟨34991884983354924696901993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46655846644473232929202657 34991884983354924696901993)
      ·
        refine ⟨26243913737516193522676495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34991884983354924696901993 26243913737516193522676495)
        ·
          refine ⟨39365870606274290284014743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26243913737516193522676495 39365870606274290284014743)
          ·
            refine ⟨59048805909411435426022115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39365870606274290284014743 59048805909411435426022115)
            ·
              refine ⟨88573208864117153139033173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59048805909411435426022115 88573208864117153139033173)
              ·
                refine ⟨1037967291376372888348045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 88573208864117153139033173 1037967291376372888348045)
                ·
                  refine ⟨389237734266139833130517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037967291376372888348045 389237734266139833130517)
                  ·
                    rfl

theorem cell21_1705585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_1705585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705585 prefixEnd_1705585 := by exact prefixLift 1705585
  have htrace : WordTrace (prefixWord ++ tailWord_1705585) baseStart_1705585 baseEnd_1705585 := by
    simpa [prefixWord, tailWord_1705585, baseEnd_1705585] using wordTrace_append hprefix tailTrace_1705585
  have hstable : (prefixWord ++ tailWord_1705585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705585).length < 2 ^ (prefixWord ++ tailWord_1705585).sum := by decide
  have hdescent : baseEnd_1705585 < baseStart_1705585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705630 : List Nat := [4, 3, 1, 1, 1, 11]
def baseStart_1705630 : Nat := 118140960795 + 1705630 * 2 ^ 59
def prefixEnd_1705630 : Nat := 4983230072969 + 3 ^ 40 * 1705630 * 2
def baseEnd_1705630 : Nat := 14416592736267768699275

theorem tailTrace_1705630 : CollatzResearch.WordTrace tailWord_1705630 prefixEnd_1705630 14416592736267768699275 := by
  unfold tailWord_1705630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776179601350160407207293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41472957873867522171772229 7776179601350160407207293)
  ·
    refine ⟨2916067350506310152702735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7776179601350160407207293 2916067350506310152702735)
    ·
      refine ⟨4374101025759465229054103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2916067350506310152702735 4374101025759465229054103)
      ·
        refine ⟨6561151538639197843581155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374101025759465229054103 6561151538639197843581155)
        ·
          refine ⟨9841727307958796765371733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561151538639197843581155 9841727307958796765371733)
          ·
            refine ⟨14416592736267768699275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9841727307958796765371733 14416592736267768699275)
            ·
              rfl

theorem cell21_1705630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 11].length) (baseStart_1705630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705630 prefixEnd_1705630 := by exact prefixLift 1705630
  have htrace : WordTrace (prefixWord ++ tailWord_1705630) baseStart_1705630 baseEnd_1705630 := by
    simpa [prefixWord, tailWord_1705630, baseEnd_1705630] using wordTrace_append hprefix tailTrace_1705630
  have hstable : (prefixWord ++ tailWord_1705630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705630).length < 2 ^ (prefixWord ++ tailWord_1705630).sum := by decide
  have hdescent : baseEnd_1705630 < baseStart_1705630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705678 : List Nat := [4, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1705678 : Nat := 118140960795 + 1705678 * 2 ^ 59
def prefixEnd_1705678 : Nat := 4983230072969 + 3 ^ 40 * 1705678 * 2
def baseEnd_1705678 : Nat := 389258958133192338080327

theorem tailTrace_1705678 : CollatzResearch.WordTrace tailWord_1705678 prefixEnd_1705678 389258958133192338080327 := by
  unfold tailWord_1705678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776398439328423431925711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41474125009751591636937125 7776398439328423431925711)
  ·
    refine ⟨11664597658992635147888567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7776398439328423431925711 11664597658992635147888567)
    ·
      refine ⟨17496896488488952721832851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664597658992635147888567 17496896488488952721832851)
      ·
        refine ⟨26245344732733429082749277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17496896488488952721832851 26245344732733429082749277)
        ·
          refine ⟨9842004274775035906030979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26245344732733429082749277 9842004274775035906030979)
          ·
            refine ⟨14763006412162553859046469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9842004274775035906030979 14763006412162553859046469)
            ·
              refine ⟨2768063702280478848571213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14763006412162553859046469 2768063702280478848571213)
              ·
                refine ⟨1038023888355179568214205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2768063702280478848571213 1038023888355179568214205)
                ·
                  refine ⟨389258958133192338080327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038023888355179568214205 389258958133192338080327)
                  ·
                    rfl

theorem cell21_1705678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1705678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705678 prefixEnd_1705678 := by exact prefixLift 1705678
  have htrace : WordTrace (prefixWord ++ tailWord_1705678) baseStart_1705678 baseEnd_1705678 := by
    simpa [prefixWord, tailWord_1705678, baseEnd_1705678] using wordTrace_append hprefix tailTrace_1705678
  have hstable : (prefixWord ++ tailWord_1705678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705678).length < 2 ^ (prefixWord ++ tailWord_1705678).sum := by decide
  have hdescent : baseEnd_1705678 < baseStart_1705678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705689 : List Nat := [1, 2, 1, 2, 3, 4, 8]
def baseStart_1705689 : Nat := 118140960795 + 1705689 * 2 ^ 59
def prefixEnd_1705689 : Nat := 4983230072969 + 3 ^ 40 * 1705689 * 2
def baseEnd_1705689 : Nat := 43251274275895418155219

theorem tailTrace_1705689 : CollatzResearch.WordTrace tailWord_1705689 prefixEnd_1705689 43251274275895418155219 := by
  unfold tailWord_1705689
  simp only [CollatzResearch.WordTrace]
  refine ⟨62211588717587536334056121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41474392478391690889370747 62211588717587536334056121)
  ·
    refine ⟨46658691538190652250542091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62211588717587536334056121 46658691538190652250542091)
    ·
      refine ⟨69988037307285978375813137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46658691538190652250542091 69988037307285978375813137)
      ·
        refine ⟨52491027980464483781859853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69988037307285978375813137 52491027980464483781859853)
        ·
          refine ⟨19684135492674181418197445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52491027980464483781859853 19684135492674181418197445)
          ·
            refine ⟨3690775404876409015912021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19684135492674181418197445 3690775404876409015912021)
            ·
              refine ⟨43251274275895418155219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3690775404876409015912021 43251274275895418155219)
              ·
                rfl

theorem cell21_1705689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 8].length) (baseStart_1705689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705689 prefixEnd_1705689 := by exact prefixLift 1705689
  have htrace : WordTrace (prefixWord ++ tailWord_1705689) baseStart_1705689 baseEnd_1705689 := by
    simpa [prefixWord, tailWord_1705689, baseEnd_1705689] using wordTrace_append hprefix tailTrace_1705689
  have hstable : (prefixWord ++ tailWord_1705689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705689).length < 2 ^ (prefixWord ++ tailWord_1705689).sum := by decide
  have hdescent : baseEnd_1705689 < baseStart_1705689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705709 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1705709 : Nat := 118140960795 + 1705709 * 2 ^ 59
def prefixEnd_1705709 : Nat := 4983230072969 + 3 ^ 40 * 1705709 * 2
def baseEnd_1705709 : Nat := 389266032755543173063597

theorem tailTrace_1705709 : CollatzResearch.WordTrace tailWord_1705709 prefixEnd_1705709 389266032755543173063597 := by
  unfold tailWord_1705709
  simp only [CollatzResearch.WordTrace]
  refine ⟨62212318177515079749784181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41474878785010053166522787 62212318177515079749784181)
  ·
    refine ⟨5832404829142038726542267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62212318177515079749784181 5832404829142038726542267)
    ·
      refine ⟨8748607243713058089813401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5832404829142038726542267 8748607243713058089813401)
      ·
        refine ⟨6561455432784793567360051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8748607243713058089813401 6561455432784793567360051)
        ·
          refine ⟨9842183149177190351040077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561455432784793567360051 9842183149177190351040077)
          ·
            refine ⟨3690818680941446381640029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9842183149177190351040077 3690818680941446381640029)
            ·
              refine ⟨1384057005353042393115011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3690818680941446381640029 1384057005353042393115011)
              ·
                refine ⟨2076085508029563589672517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384057005353042393115011 2076085508029563589672517)
                ·
                  refine ⟨389266032755543173063597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076085508029563589672517 389266032755543173063597)
                  ·
                    rfl

theorem cell21_1705709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1705709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705709 prefixEnd_1705709 := by exact prefixLift 1705709
  have htrace : WordTrace (prefixWord ++ tailWord_1705709) baseStart_1705709 baseEnd_1705709 := by
    simpa [prefixWord, tailWord_1705709, baseEnd_1705709] using wordTrace_append hprefix tailTrace_1705709
  have hstable : (prefixWord ++ tailWord_1705709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705709).length < 2 ^ (prefixWord ++ tailWord_1705709).sum := by decide
  have hdescent : baseEnd_1705709 < baseStart_1705709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705751 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 6]
def baseStart_1705751 : Nat := 118140960795 + 1705751 * 2 ^ 59
def prefixEnd_1705751 : Nat := 4983230072969 + 3 ^ 40 * 1705751 * 2
def baseEnd_1705751 : Nat := 389275617727760433363511

theorem tailTrace_1705751 : CollatzResearch.WordTrace tailWord_1705751 prefixEnd_1705751 389275617727760433363511 := by
  unfold tailWord_1705751
  simp only [CollatzResearch.WordTrace]
  refine ⟨62213850043362920922813107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41475900028908613948542071 62213850043362920922813107)
  ·
    refine ⟨93320775065044381384219661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62213850043362920922813107 93320775065044381384219661)
    ·
      refine ⟨34995290649391643019082373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93320775065044381384219661 34995290649391643019082373)
      ·
        refine ⟨6561616996760933066077945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34995290649391643019082373 6561616996760933066077945)
        ·
          refine ⟨4921212747570699799558459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6561616996760933066077945 4921212747570699799558459)
          ·
            refine ⟨7381819121356049699337689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921212747570699799558459 7381819121356049699337689)
            ·
              refine ⟨5536364341017037274503267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7381819121356049699337689 5536364341017037274503267)
              ·
                refine ⟨8304546511525555911754901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536364341017037274503267 8304546511525555911754901)
                ·
                  refine ⟨389275617727760433363511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8304546511525555911754901 389275617727760433363511)
                  ·
                    rfl

theorem cell21_1705751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_1705751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705751 prefixEnd_1705751 := by exact prefixLift 1705751
  have htrace : WordTrace (prefixWord ++ tailWord_1705751) baseStart_1705751 baseEnd_1705751 := by
    simpa [prefixWord, tailWord_1705751, baseEnd_1705751] using wordTrace_append hprefix tailTrace_1705751
  have hstable : (prefixWord ++ tailWord_1705751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705751).length < 2 ^ (prefixWord ++ tailWord_1705751).sum := by decide
  have hdescent : baseEnd_1705751 < baseStart_1705751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705765 : List Nat := [1, 3, 1, 2, 3, 2, 1, 8]
def baseStart_1705765 : Nat := 118140960795 + 1705765 * 2 ^ 59
def prefixEnd_1705765 : Nat := 4983230072969 + 3 ^ 40 * 1705765 * 2
def baseEnd_1705765 : Nat := 129759604239499840043383

theorem tailTrace_1705765 : CollatzResearch.WordTrace tailWord_1705765 prefixEnd_1705765 129759604239499840043383 := by
  unfold tailWord_1705765
  simp only [CollatzResearch.WordTrace]
  refine ⟨62214360665312201313822749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41476240443541467542548499 62214360665312201313822749)
  ·
    refine ⟨23330385249492075492683531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62214360665312201313822749 23330385249492075492683531)
    ·
      refine ⟨34995577874238113239025297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23330385249492075492683531 34995577874238113239025297)
      ·
        refine ⟨26246683405678584929268973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34995577874238113239025297 26246683405678584929268973)
        ·
          refine ⟨9842506277129469348475865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26246683405678584929268973 9842506277129469348475865)
          ·
            refine ⟨7381879707847102011356899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9842506277129469348475865 7381879707847102011356899)
            ·
              refine ⟨11072819561770653017035349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381879707847102011356899 11072819561770653017035349)
              ·
                refine ⟨129759604239499840043383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11072819561770653017035349 129759604239499840043383)
                ·
                  rfl

theorem cell21_1705765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 8].length) (baseStart_1705765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705765 prefixEnd_1705765 := by exact prefixLift 1705765
  have htrace : WordTrace (prefixWord ++ tailWord_1705765) baseStart_1705765 baseEnd_1705765 := by
    simpa [prefixWord, tailWord_1705765, baseEnd_1705765] using wordTrace_append hprefix tailTrace_1705765
  have hstable : (prefixWord ++ tailWord_1705765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705765).length < 2 ^ (prefixWord ++ tailWord_1705765).sum := by decide
  have hdescent : baseEnd_1705765 < baseStart_1705765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705768 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_1705768 : Nat := 118140960795 + 1705768 * 2 ^ 59
def prefixEnd_1705768 : Nat := 4983230072969 + 3 ^ 40 * 1705768 * 2
def baseEnd_1705768 : Nat := 389279497359372181580143

theorem tailTrace_1705768 : CollatzResearch.WordTrace tailWord_1705768 prefixEnd_1705768 389279497359372181580143 := by
  unfold tailWord_1705768
  simp only [CollatzResearch.WordTrace]
  refine ⟨31107235042150666413090979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41476313389534221884121305 31107235042150666413090979)
  ·
    refine ⟨46660852563225999619636469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31107235042150666413090979 46660852563225999619636469)
    ·
      refine ⟨4374454927802437464340919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46660852563225999619636469 4374454927802437464340919)
      ·
        refine ⟨6561682391703656196511379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374454927802437464340919 6561682391703656196511379)
        ·
          refine ⟨9842523587555484294767069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561682391703656196511379 9842523587555484294767069)
          ·
            refine ⟨3690946345333306610537651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9842523587555484294767069 3690946345333306610537651)
            ·
              refine ⟨5536419517999959915806477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690946345333306610537651 5536419517999959915806477)
              ·
                refine ⟨2076157319249984968427429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5536419517999959915806477 2076157319249984968427429)
                ·
                  refine ⟨389279497359372181580143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076157319249984968427429 389279497359372181580143)
                  ·
                    rfl

theorem cell21_1705768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_1705768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705768 prefixEnd_1705768 := by exact prefixLift 1705768
  have htrace : WordTrace (prefixWord ++ tailWord_1705768) baseStart_1705768 baseEnd_1705768 := by
    simpa [prefixWord, tailWord_1705768, baseEnd_1705768] using wordTrace_append hprefix tailTrace_1705768
  have hstable : (prefixWord ++ tailWord_1705768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705768).length < 2 ^ (prefixWord ++ tailWord_1705768).sum := by decide
  have hdescent : baseEnd_1705768 < baseStart_1705768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705855 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 9]
def baseStart_1705855 : Nat := 118140960795 + 1705855 * 2 ^ 59
def prefixEnd_1705855 : Nat := 4983230072969 + 3 ^ 40 * 1705855 * 2
def baseEnd_1705855 : Nat := 389299351944679363629965

theorem tailTrace_1705855 : CollatzResearch.WordTrace tailWord_1705855 prefixEnd_1705855 389299351944679363629965 := by
  unfold tailWord_1705855
  simp only [CollatzResearch.WordTrace]
  refine ⟨62217643234986146684599019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41478428823324097789732679 62217643234986146684599019)
  ·
    refine ⟨93326464852479220026898529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62217643234986146684599019 93326464852479220026898529)
    ·
      refine ⟨69994848639359415020173897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93326464852479220026898529 69994848639359415020173897)
      ·
        refine ⟨52496136479519561265130423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69994848639359415020173897 52496136479519561265130423)
        ·
          refine ⟨78744204719279341897695635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52496136479519561265130423 78744204719279341897695635)
          ·
            refine ⟨118116307078919012846543453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78744204719279341897695635 118116307078919012846543453)
            ·
              refine ⟨44293615154594629817453795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118116307078919012846543453 44293615154594629817453795)
              ·
                refine ⟨66440422731891944726180693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44293615154594629817453795 66440422731891944726180693)
                ·
                  refine ⟨389299351944679363629965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66440422731891944726180693 389299351944679363629965)
                  ·
                    rfl

theorem cell21_1705855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_1705855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705855 prefixEnd_1705855 := by exact prefixLift 1705855
  have htrace : WordTrace (prefixWord ++ tailWord_1705855) baseStart_1705855 baseEnd_1705855 := by
    simpa [prefixWord, tailWord_1705855, baseEnd_1705855] using wordTrace_append hprefix tailTrace_1705855
  have hstable : (prefixWord ++ tailWord_1705855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705855).length < 2 ^ (prefixWord ++ tailWord_1705855).sum := by decide
  have hdescent : baseEnd_1705855 < baseStart_1705855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705917 : List Nat := [1, 4, 1, 2, 3, 1, 9]
def baseStart_1705917 : Nat := 118140960795 + 1705917 * 2 ^ 59
def prefixEnd_1705917 : Nat := 4983230072969 + 3 ^ 40 * 1705917 * 2
def baseEnd_1705917 : Nat := 43257055687709003732945

theorem tailTrace_1705917 : CollatzResearch.WordTrace tailWord_1705917 prefixEnd_1705917 43257055687709003732945 := by
  unfold tailWord_1705917
  simp only [CollatzResearch.WordTrace]
  refine ⟨62219904560761531273356005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41479936373841020848904003 62219904560761531273356005)
  ·
    refine ⟨11666232105142787113754251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62219904560761531273356005 11666232105142787113754251)
    ·
      refine ⟨17499348157714180670631377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11666232105142787113754251 17499348157714180670631377)
      ·
        refine ⟨13124511118285635502973533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17499348157714180670631377 13124511118285635502973533)
        ·
          refine ⟨4921691669357113313615075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13124511118285635502973533 4921691669357113313615075)
          ·
            refine ⟨7382537504035669970422613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921691669357113313615075 7382537504035669970422613)
            ·
              refine ⟨43257055687709003732945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7382537504035669970422613 43257055687709003732945)
              ·
                rfl

theorem cell21_1705917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 9].length) (baseStart_1705917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1705917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1705917 prefixEnd_1705917 := by exact prefixLift 1705917
  have htrace : WordTrace (prefixWord ++ tailWord_1705917) baseStart_1705917 baseEnd_1705917 := by
    simpa [prefixWord, tailWord_1705917, baseEnd_1705917] using wordTrace_append hprefix tailTrace_1705917
  have hstable : (prefixWord ++ tailWord_1705917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705917).length < 2 ^ (prefixWord ++ tailWord_1705917).sum := by decide
  have hdescent : baseEnd_1705917 < baseStart_1705917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706010 : List Nat := [3, 1, 1, 3, 1, 4, 3, 5]
def baseStart_1706010 : Nat := 118140960795 + 1706010 * 2 ^ 59
def prefixEnd_1706010 : Nat := 4983230072969 + 3 ^ 40 * 1706010 * 2
def baseEnd_1706010 : Nat := 129778241685477846182105

theorem tailTrace_1706010 : CollatzResearch.WordTrace tailWord_1706010 prefixEnd_1706010 129778241685477846182105 := by
  unfold tailWord_1706010
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555824137356152039122871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41482197699616405437660989 15555824137356152039122871)
  ·
    refine ⟨23333736206034228058684307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15555824137356152039122871 23333736206034228058684307)
    ·
      refine ⟨35000604309051342088026461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23333736206034228058684307 35000604309051342088026461)
      ·
        refine ⟨13125226615894253283009923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35000604309051342088026461 13125226615894253283009923)
        ·
          refine ⟨19687839923841379924514885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125226615894253283009923 19687839923841379924514885)
          ·
            refine ⟨3691469985720258735846541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19687839923841379924514885 3691469985720258735846541)
            ·
              refine ⟨1384301244645097025942453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3691469985720258735846541 1384301244645097025942453)
              ·
                refine ⟨129778241685477846182105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1384301244645097025942453 129778241685477846182105)
                ·
                  rfl

theorem cell21_1706010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_1706010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706010 prefixEnd_1706010 := by exact prefixLift 1706010
  have htrace : WordTrace (prefixWord ++ tailWord_1706010) baseStart_1706010 baseEnd_1706010 := by
    simpa [prefixWord, tailWord_1706010, baseEnd_1706010] using wordTrace_append hprefix tailTrace_1706010
  have hstable : (prefixWord ++ tailWord_1706010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706010).length < 2 ^ (prefixWord ++ tailWord_1706010).sum := by decide
  have hdescent : baseEnd_1706010 < baseStart_1706010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706041 : List Nat := [1, 2, 1, 5, 3, 1, 2, 1, 5]
def baseStart_1706041 : Nat := 118140960795 + 1706041 * 2 ^ 59
def prefixEnd_1706041 : Nat := 4983230072969 + 3 ^ 40 * 1706041 * 2
def baseEnd_1706041 : Nat := 389341799678784373529585

theorem tailTrace_1706041 : CollatzResearch.WordTrace tailWord_1706041 prefixEnd_1706041 389341799678784373529585 := by
  unfold tailWord_1706041
  simp only [CollatzResearch.WordTrace]
  refine ⟨62224427212312300450869977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41482951474874866967246651 62224427212312300450869977)
  ·
    refine ⟨46668320409234225338152483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62224427212312300450869977 46668320409234225338152483)
    ·
      refine ⟨70002480613851338007228725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46668320409234225338152483 70002480613851338007228725)
      ·
        refine ⟨6562732557548562938177693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70002480613851338007228725 6562732557548562938177693)
        ·
          refine ⟨2461024709080711101816635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6562732557548562938177693 2461024709080711101816635)
          ·
            refine ⟨3691537063621066652724953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461024709080711101816635 3691537063621066652724953)
            ·
              refine ⟨2768652797715799989543715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691537063621066652724953 2768652797715799989543715)
              ·
                refine ⟨4152979196573699984315573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768652797715799989543715 4152979196573699984315573)
                ·
                  refine ⟨389341799678784373529585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4152979196573699984315573 389341799678784373529585)
                  ·
                    rfl

theorem cell21_1706041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_1706041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706041 prefixEnd_1706041 := by exact prefixLift 1706041
  have htrace : WordTrace (prefixWord ++ tailWord_1706041) baseStart_1706041 baseEnd_1706041 := by
    simpa [prefixWord, tailWord_1706041, baseEnd_1706041] using wordTrace_append hprefix tailTrace_1706041
  have hstable : (prefixWord ++ tailWord_1706041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706041).length < 2 ^ (prefixWord ++ tailWord_1706041).sum := by decide
  have hdescent : baseEnd_1706041 < baseStart_1706041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706069 : List Nat := [1, 3, 2, 2, 1, 4, 1, 7]
def baseStart_1706069 : Nat := 118140960795 + 1706069 * 2 ^ 59
def prefixEnd_1706069 : Nat := 4983230072969 + 3 ^ 40 * 1706069 * 2
def baseEnd_1706069 : Nat := 129782729886754182354287

theorem tailTrace_1706069 : CollatzResearch.WordTrace tailWord_1706069 prefixEnd_1706069 129782729886754182354287 := by
  unfold tailWord_1706069
  simp only [CollatzResearch.WordTrace]
  refine ⟨62225448456210861232889261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41483632304140574155259507 62225448456210861232889261)
  ·
    refine ⟨23334543171079072962333473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62225448456210861232889261 23334543171079072962333473)
    ·
      refine ⟨17500907378309304721750105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23334543171079072962333473 17500907378309304721750105)
      ·
        refine ⟨13125680533731978541312579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17500907378309304721750105 13125680533731978541312579)
        ·
          refine ⟨19688520800597967811968869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125680533731978541312579 19688520800597967811968869)
          ·
            refine ⟨3691597650112118964744163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19688520800597967811968869 3691597650112118964744163)
            ·
              refine ⟨5537396475168178447116245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691597650112118964744163 5537396475168178447116245)
              ·
                refine ⟨129782729886754182354287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5537396475168178447116245 129782729886754182354287)
                ·
                  rfl

theorem cell21_1706069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 7].length) (baseStart_1706069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706069 prefixEnd_1706069 := by exact prefixLift 1706069
  have htrace : WordTrace (prefixWord ++ tailWord_1706069) baseStart_1706069 baseEnd_1706069 := by
    simpa [prefixWord, tailWord_1706069, baseEnd_1706069] using wordTrace_append hprefix tailTrace_1706069
  have hstable : (prefixWord ++ tailWord_1706069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706069).length < 2 ^ (prefixWord ++ tailWord_1706069).sum := by decide
  have hdescent : baseEnd_1706069 < baseStart_1706069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706083 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 7]
def baseStart_1706083 : Nat := 118140960795 + 1706083 * 2 ^ 59
def prefixEnd_1706083 : Nat := 4983230072969 + 3 ^ 40 * 1706083 * 2
def baseEnd_1706083 : Nat := 389351384651001633829499

theorem tailTrace_1706083 : CollatzResearch.WordTrace tailWord_1706083 prefixEnd_1706083 389351384651001633829499 := by
  unfold tailWord_1706083
  simp only [CollatzResearch.WordTrace]
  refine ⟨62225959078160141623898903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41483972718773427749265935 62225959078160141623898903)
  ·
    refine ⟨93338938617240212435848355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62225959078160141623898903 93338938617240212435848355)
    ·
      refine ⟨140008407925860318653772533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93338938617240212435848355 140008407925860318653772533)
      ·
        refine ⟨13125788243049404873791175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140008407925860318653772533 13125788243049404873791175)
        ·
          refine ⟨19688682364574107310686763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125788243049404873791175 19688682364574107310686763)
          ·
            refine ⟨29533023546861160966030145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19688682364574107310686763 29533023546861160966030145)
            ·
              refine ⟨22149767660145870724522609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29533023546861160966030145 22149767660145870724522609)
              ·
                refine ⟨16612325745109403043391957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22149767660145870724522609 16612325745109403043391957)
                ·
                  refine ⟨389351384651001633829499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16612325745109403043391957 389351384651001633829499)
                  ·
                    rfl

theorem cell21_1706083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_1706083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706083 prefixEnd_1706083 := by exact prefixLift 1706083
  have htrace : WordTrace (prefixWord ++ tailWord_1706083) baseStart_1706083 baseEnd_1706083 := by
    simpa [prefixWord, tailWord_1706083, baseEnd_1706083] using wordTrace_append hprefix tailTrace_1706083
  have hstable : (prefixWord ++ tailWord_1706083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706083).length < 2 ^ (prefixWord ++ tailWord_1706083).sum := by decide
  have hdescent : baseEnd_1706083 < baseStart_1706083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706128 : List Nat := [2, 1, 1, 1, 1, 1, 5, 9]
def baseStart_1706128 : Nat := 118140960795 + 1706128 * 2 ^ 59
def prefixEnd_1706128 : Nat := 4983230072969 + 3 ^ 40 * 1706128 * 2
def baseEnd_1706128 : Nat := 129787218088030518526469

theorem tailTrace_1706128 : CollatzResearch.WordTrace tailWord_1706128 prefixEnd_1706128 129787218088030518526469 := by
  unfold tailWord_1706128
  simp only [CollatzResearch.WordTrace]
  refine ⟨31113800181498557154643519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41485066908664742872858025 31113800181498557154643519)
  ·
    refine ⟨46670700272247835731965279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31113800181498557154643519 46670700272247835731965279)
    ·
      refine ⟨70006050408371753597947919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46670700272247835731965279 70006050408371753597947919)
      ·
        refine ⟨105009075612557630396921879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70006050408371753597947919 105009075612557630396921879)
        ·
          refine ⟨157513613418836445595382819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105009075612557630396921879 157513613418836445595382819)
          ·
            refine ⟨236270420128254668393074229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157513613418836445595382819 236270420128254668393074229)
            ·
              refine ⟨22150351887023875161850709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236270420128254668393074229 22150351887023875161850709)
              ·
                refine ⟨129787218088030518526469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22150351887023875161850709 129787218088030518526469)
                ·
                  rfl

theorem cell21_1706128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_1706128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706128 prefixEnd_1706128 := by exact prefixLift 1706128
  have htrace : WordTrace (prefixWord ++ tailWord_1706128) baseStart_1706128 baseEnd_1706128 := by
    simpa [prefixWord, tailWord_1706128, baseEnd_1706128] using wordTrace_append hprefix tailTrace_1706128
  have hstable : (prefixWord ++ tailWord_1706128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706128).length < 2 ^ (prefixWord ++ tailWord_1706128).sum := by decide
  have hdescent : baseEnd_1706128 < baseStart_1706128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706148 : List Nat := [2, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1706148 : Nat := 118140960795 + 1706148 * 2 ^ 59
def prefixEnd_1706148 : Nat := 4983230072969 + 3 ^ 40 * 1706148 * 2
def baseEnd_1706148 : Nat := 389366218536575965246033

theorem tailTrace_1706148 : CollatzResearch.WordTrace tailWord_1706148 prefixEnd_1706148 389366218536575965246033 := by
  unfold tailWord_1706148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31114164911462328862507549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41485553215283105150010065 31114164911462328862507549)
  ·
    refine ⟨11667811841798373323440331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31114164911462328862507549 11667811841798373323440331)
    ·
      refine ⟨17501717762697559985160497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11667811841798373323440331 17501717762697559985160497)
      ·
        refine ⟨13126288322023169988870373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17501717762697559985160497 13126288322023169988870373)
        ·
          refine ⟨2461179060379344372913195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13126288322023169988870373 2461179060379344372913195)
          ·
            refine ⟨3691768590569016559369793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461179060379344372913195 3691768590569016559369793)
            ·
              refine ⟨2768826442926762419527345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691768590569016559369793 2768826442926762419527345)
              ·
                refine ⟨2076619832195071814645509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768826442926762419527345 2076619832195071814645509)
                ·
                  refine ⟨389366218536575965246033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076619832195071814645509 389366218536575965246033)
                  ·
                    rfl

theorem cell21_1706148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1706148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706148 prefixEnd_1706148 := by exact prefixLift 1706148
  have htrace : WordTrace (prefixWord ++ tailWord_1706148) baseStart_1706148 baseEnd_1706148 := by
    simpa [prefixWord, tailWord_1706148, baseEnd_1706148] using wordTrace_append hprefix tailTrace_1706148
  have hstable : (prefixWord ++ tailWord_1706148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706148).length < 2 ^ (prefixWord ++ tailWord_1706148).sum := by decide
  have hdescent : baseEnd_1706148 < baseStart_1706148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706159 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 5]
def baseStart_1706159 : Nat := 118140960795 + 1706159 * 2 ^ 59
def prefixEnd_1706159 : Nat := 4983230072969 + 3 ^ 40 * 1706159 * 2
def baseEnd_1706159 : Nat := 389368728886442390562677

theorem tailTrace_1706159 : CollatzResearch.WordTrace tailWord_1706159 prefixEnd_1706159 389368728886442390562677 := by
  unfold tailWord_1706159
  simp only [CollatzResearch.WordTrace]
  refine ⟨62228731025884806603665531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41485820683923204402443687 62228731025884806603665531)
  ·
    refine ⟨93343096538827209905498297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62228731025884806603665531 93343096538827209905498297)
    ·
      refine ⟨70007322404120407429123723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93343096538827209905498297 70007322404120407429123723)
      ·
        refine ⟨105010983606180611143685585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70007322404120407429123723 105010983606180611143685585)
        ·
          refine ⟨78758237704635458357764189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105010983606180611143685585 78758237704635458357764189)
          ·
            refine ⟨29534339139238296884161571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78758237704635458357764189 29534339139238296884161571)
            ·
              refine ⟨44301508708857445326242357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29534339139238296884161571 44301508708857445326242357)
              ·
                refine ⟨4153266441455385499335221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44301508708857445326242357 4153266441455385499335221)
                ·
                  refine ⟨389368728886442390562677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4153266441455385499335221 389368728886442390562677)
                  ·
                    rfl

theorem cell21_1706159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_1706159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706159 prefixEnd_1706159 := by exact prefixLift 1706159
  have htrace : WordTrace (prefixWord ++ tailWord_1706159) baseStart_1706159 baseEnd_1706159 := by
    simpa [prefixWord, tailWord_1706159, baseEnd_1706159] using wordTrace_append hprefix tailTrace_1706159
  have hstable : (prefixWord ++ tailWord_1706159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706159).length < 2 ^ (prefixWord ++ tailWord_1706159).sum := by decide
  have hdescent : baseEnd_1706159 < baseStart_1706159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706176 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_1706176 : Nat := 118140960795 + 1706176 * 2 ^ 59
def prefixEnd_1706176 : Nat := 4983230072969 + 3 ^ 40 * 1706176 * 2
def baseEnd_1706176 : Nat := 389372608518054138779309

theorem tailTrace_1706176 : CollatzResearch.WordTrace tailWord_1706176 prefixEnd_1706176 389372608518054138779309 := by
  unfold tailWord_1706176
  simp only [CollatzResearch.WordTrace]
  refine ⟨31114675533411609253517191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41486234044548812338022921 31114675533411609253517191)
  ·
    refine ⟨46672013300117413880275787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31114675533411609253517191 46672013300117413880275787)
    ·
      refine ⟨70008019950176120820413681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46672013300117413880275787 70008019950176120820413681)
      ·
        refine ⟨52506014962632090615310261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70008019950176120820413681 52506014962632090615310261)
        ·
          refine ⟨4922438902746758495185337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52506014962632090615310261 4922438902746758495185337)
          ·
            refine ⟨3691829177060068871389003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4922438902746758495185337 3691829177060068871389003)
            ·
              refine ⟨5537743765590103307083505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691829177060068871389003 5537743765590103307083505)
              ·
                refine ⟨4153307824192577480312629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537743765590103307083505 4153307824192577480312629)
                ·
                  refine ⟨389372608518054138779309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4153307824192577480312629 389372608518054138779309)
                  ·
                    rfl

theorem cell21_1706176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_1706176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706176 prefixEnd_1706176 := by exact prefixLift 1706176
  have htrace : WordTrace (prefixWord ++ tailWord_1706176) baseStart_1706176 baseEnd_1706176 := by
    simpa [prefixWord, tailWord_1706176, baseEnd_1706176] using wordTrace_append hprefix tailTrace_1706176
  have hstable : (prefixWord ++ tailWord_1706176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706176).length < 2 ^ (prefixWord ++ tailWord_1706176).sum := by decide
  have hdescent : baseEnd_1706176 < baseStart_1706176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706297 : List Nat := [1, 2, 1, 6, 1, 1, 2, 7]
def baseStart_1706297 : Nat := 118140960795 + 1706297 * 2 ^ 59
def prefixEnd_1706297 : Nat := 4983230072969 + 3 ^ 40 * 1706297 * 2
def baseEnd_1706297 : Nat := 129800074122194939087465

theorem tailTrace_1706297 : CollatzResearch.WordTrace tailWord_1706297 prefixEnd_1706297 129800074122194939087465 := by
  unfold tailWord_1706297
  simp only [CollatzResearch.WordTrace]
  refine ⟨62233764299384856172189145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41489176199589904114792763 62233764299384856172189145)
  ·
    refine ⟨46675323224538642129141859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62233764299384856172189145 46675323224538642129141859)
    ·
      refine ⟨70012984836807963193712789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46675323224538642129141859 70012984836807963193712789)
      ·
        refine ⟨3281858664225373274705287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70012984836807963193712789 3281858664225373274705287)
        ·
          refine ⟨4922787996338059912057931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3281858664225373274705287 4922787996338059912057931)
          ·
            refine ⟨7384181994507089868086897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922787996338059912057931 7384181994507089868086897)
            ·
              refine ⟨5538136495880317401065173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7384181994507089868086897 5538136495880317401065173)
              ·
                refine ⟨129800074122194939087465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5538136495880317401065173 129800074122194939087465)
                ·
                  rfl

theorem cell21_1706297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 7].length) (baseStart_1706297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706297 prefixEnd_1706297 := by exact prefixLift 1706297
  have htrace : WordTrace (prefixWord ++ tailWord_1706297) baseStart_1706297 baseEnd_1706297 := by
    simpa [prefixWord, tailWord_1706297, baseEnd_1706297] using wordTrace_append hprefix tailTrace_1706297
  have hstable : (prefixWord ++ tailWord_1706297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706297).length < 2 ^ (prefixWord ++ tailWord_1706297).sum := by decide
  have hdescent : baseEnd_1706297 < baseStart_1706297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706452 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1706452 : Nat := 118140960795 + 1706452 * 2 ^ 59
def prefixEnd_1706452 : Nat := 4983230072969 + 3 ^ 40 * 1706452 * 2
def baseEnd_1706452 : Nat := 389435595478338992178745

theorem tailTrace_1706452 : CollatzResearch.WordTrace tailWord_1706452 prefixEnd_1706452 389435595478338992178745 := by
  unfold tailWord_1706452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31119708806911658822040805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41492945075882211762721073 31119708806911658822040805)
  ·
    refine ⟨5834945401295936029132651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31119708806911658822040805 5834945401295936029132651)
    ·
      refine ⟨8752418101943904043698977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5834945401295936029132651 8752418101943904043698977)
      ·
        refine ⟨6564313576457928032774233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8752418101943904043698977 6564313576457928032774233)
        ·
          refine ⟨4923235182343446024580675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6564313576457928032774233 4923235182343446024580675)
          ·
            refine ⟨7384852773515169036871013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923235182343446024580675 7384852773515169036871013)
            ·
              refine ⟨1384659895034094194413315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7384852773515169036871013 1384659895034094194413315)
              ·
                refine ⟨2076989842551141291619973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384659895034094194413315 2076989842551141291619973)
                ·
                  refine ⟨389435595478338992178745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076989842551141291619973 389435595478338992178745)
                  ·
                    rfl

theorem cell21_1706452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1706452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706452 prefixEnd_1706452 := by exact prefixLift 1706452
  have htrace : WordTrace (prefixWord ++ tailWord_1706452) baseStart_1706452 baseEnd_1706452 := by
    simpa [prefixWord, tailWord_1706452, baseEnd_1706452] using wordTrace_append hprefix tailTrace_1706452
  have hstable : (prefixWord ++ tailWord_1706452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706452).length < 2 ^ (prefixWord ++ tailWord_1706452).sum := by decide
  have hdescent : baseEnd_1706452 < baseStart_1706452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706480 : List Nat := [2, 1, 1, 1, 3, 3, 2, 5, 3]
def baseStart_1706480 : Nat := 118140960795 + 1706480 * 2 ^ 59
def prefixEnd_1706480 : Nat := 4983230072969 + 3 ^ 40 * 1706480 * 2
def baseEnd_1706480 : Nat := 389441985459817165712021

theorem tailTrace_1706480 : CollatzResearch.WordTrace tailWord_1706480 prefixEnd_1706480 389441985459817165712021 := by
  unfold tailWord_1706480
  simp only [CollatzResearch.WordTrace]
  refine ⟨31120219428860939213050447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41493625905147918950733929 31120219428860939213050447)
  ·
    refine ⟨46680329143291408819575671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31120219428860939213050447 46680329143291408819575671)
    ·
      refine ⟨70020493714937113229363507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46680329143291408819575671 70020493714937113229363507)
      ·
        refine ⟨105030740572405669844045261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70020493714937113229363507 105030740572405669844045261)
        ·
          refine ⟨39386527714652126191516973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105030740572405669844045261 39386527714652126191516973)
          ·
            refine ⟨14769947892994547321818865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39386527714652126191516973 14769947892994547321818865)
            ·
              refine ⟨11077460919745910491364149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14769947892994547321818865 11077460919745910491364149)
              ·
                refine ⟨1038511961226179108565389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11077460919745910491364149 1038511961226179108565389)
                ·
                  refine ⟨389441985459817165712021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038511961226179108565389 389441985459817165712021)
                  ·
                    rfl

theorem cell21_1706480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_1706480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706480 prefixEnd_1706480 := by exact prefixLift 1706480
  have htrace : WordTrace (prefixWord ++ tailWord_1706480) baseStart_1706480 baseEnd_1706480 := by
    simpa [prefixWord, tailWord_1706480, baseEnd_1706480] using wordTrace_append hprefix tailTrace_1706480
  have hstable : (prefixWord ++ tailWord_1706480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706480).length < 2 ^ (prefixWord ++ tailWord_1706480).sum := by decide
  have hdescent : baseEnd_1706480 < baseStart_1706480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706497 : List Nat := [1, 2, 4, 1, 3, 2, 1, 4, 3]
def baseStart_1706497 : Nat := 118140960795 + 1706497 * 2 ^ 59
def prefixEnd_1706497 : Nat := 4983230072969 + 3 ^ 40 * 1706497 * 2
def baseEnd_1706497 : Nat := 389445865091428913928653

theorem tailTrace_1706497 : CollatzResearch.WordTrace tailWord_1706497 prefixEnd_1706497 389445865091428913928653 := by
  unfold tailWord_1706497
  simp only [CollatzResearch.WordTrace]
  refine ⟨62241058898660290329469745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41494039265773526886313163 62241058898660290329469745)
  ·
    refine ⟨46680794173995217747102309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62241058898660290329469745 46680794173995217747102309)
    ·
      refine ⟨8752648907624103327581683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46680794173995217747102309 8752648907624103327581683)
      ·
        refine ⟨13128973361436154991372525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8752648907624103327581683 13128973361436154991372525)
        ·
          refine ⟨4923365010538558121764697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13128973361436154991372525 4923365010538558121764697)
          ·
            refine ⟨3692523757903918591323523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4923365010538558121764697 3692523757903918591323523)
            ·
              refine ⟨5538785636855877886985285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692523757903918591323523 5538785636855877886985285)
              ·
                refine ⟨1038522306910477103809741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5538785636855877886985285 1038522306910477103809741)
                ·
                  refine ⟨389445865091428913928653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038522306910477103809741 389445865091428913928653)
                  ·
                    rfl

theorem cell21_1706497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_1706497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706497 prefixEnd_1706497 := by exact prefixLift 1706497
  have htrace : WordTrace (prefixWord ++ tailWord_1706497) baseStart_1706497 baseEnd_1706497 := by
    simpa [prefixWord, tailWord_1706497, baseEnd_1706497] using wordTrace_append hprefix tailTrace_1706497
  have hstable : (prefixWord ++ tailWord_1706497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706497).length < 2 ^ (prefixWord ++ tailWord_1706497).sum := by decide
  have hdescent : baseEnd_1706497 < baseStart_1706497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706556 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_1706556 : Nat := 118140960795 + 1706556 * 2 ^ 59
def prefixEnd_1706556 : Nat := 4983230072969 + 3 ^ 40 * 1706556 * 2
def baseEnd_1706556 : Nat := 389459329695257922445199

theorem tailTrace_1706556 : CollatzResearch.WordTrace tailWord_1706556 prefixEnd_1706556 389459329695257922445199 := by
  unfold tailWord_1706556
  simp only [CollatzResearch.WordTrace]
  refine ⟨31121605402723271702933761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41495473870297695603911681 31121605402723271702933761)
  ·
    refine ⟨23341204052042453777200321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31121605402723271702933761 23341204052042453777200321)
    ·
      refine ⟨17505903039031840332900241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23341204052042453777200321 17505903039031840332900241)
      ·
        refine ⟨13129427279273880249675181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17505903039031840332900241 13129427279273880249675181)
        ·
          refine ⟨4923535229727705093628193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13129427279273880249675181 4923535229727705093628193)
          ·
            refine ⟨3692651422295778820221145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4923535229727705093628193 3692651422295778820221145)
            ·
              refine ⟨2769488566721834115165859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692651422295778820221145 2769488566721834115165859)
              ·
                refine ⟨4154232850082751172748789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769488566721834115165859 4154232850082751172748789)
                ·
                  refine ⟨389459329695257922445199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4154232850082751172748789 389459329695257922445199)
                  ·
                    rfl

theorem cell21_1706556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_1706556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706556 prefixEnd_1706556 := by exact prefixLift 1706556
  have htrace : WordTrace (prefixWord ++ tailWord_1706556) baseStart_1706556 baseEnd_1706556 := by
    simpa [prefixWord, tailWord_1706556, baseEnd_1706556] using wordTrace_append hprefix tailTrace_1706556
  have hstable : (prefixWord ++ tailWord_1706556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706556).length < 2 ^ (prefixWord ++ tailWord_1706556).sum := by decide
  have hdescent : baseEnd_1706556 < baseStart_1706556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706615 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 5]
def baseStart_1706615 : Nat := 118140960795 + 1706615 * 2 ^ 59
def prefixEnd_1706615 : Nat := 4983230072969 + 3 ^ 40 * 1706615 * 2
def baseEnd_1706615 : Nat := 389472794299086930961745

theorem tailTrace_1706615 : CollatzResearch.WordTrace tailWord_1706615 prefixEnd_1706615 389472794299086930961745 := by
  unfold tailWord_1706615
  simp only [CollatzResearch.WordTrace]
  refine ⟨62245362712232796482265299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41496908474821864321510199 62245362712232796482265299)
  ·
    refine ⟨93368044068349194723397949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62245362712232796482265299 93368044068349194723397949)
    ·
      refine ⟨35013016525630948021274231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93368044068349194723397949 35013016525630948021274231)
      ·
        refine ⟨52519524788446422031911347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35013016525630948021274231 52519524788446422031911347)
        ·
          refine ⟨78779287182669633047867021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52519524788446422031911347 78779287182669633047867021)
          ·
            refine ⟨29542232693501112392950133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78779287182669633047867021 29542232693501112392950133)
            ·
              refine ⟨2769584315015729286839075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29542232693501112392950133 2769584315015729286839075)
              ·
                refine ⟨4154376472523593930258613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769584315015729286839075 4154376472523593930258613)
                ·
                  refine ⟨389472794299086930961745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4154376472523593930258613 389472794299086930961745)
                  ·
                    rfl

theorem cell21_1706615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_1706615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706615 prefixEnd_1706615 := by exact prefixLift 1706615
  have htrace : WordTrace (prefixWord ++ tailWord_1706615) baseStart_1706615 baseEnd_1706615 := by
    simpa [prefixWord, tailWord_1706615, baseEnd_1706615] using wordTrace_append hprefix tailTrace_1706615
  have hstable : (prefixWord ++ tailWord_1706615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706615).length < 2 ^ (prefixWord ++ tailWord_1706615).sum := by decide
  have hdescent : baseEnd_1706615 < baseStart_1706615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706621 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1706621 : Nat := 118140960795 + 1706621 * 2 ^ 59
def prefixEnd_1706621 : Nat := 4983230072969 + 3 ^ 40 * 1706621 * 2
def baseEnd_1706621 : Nat := 389474163580832253861733

theorem tailTrace_1706621 : CollatzResearch.WordTrace tailWord_1706621 prefixEnd_1706621 389474163580832253861733 := by
  unfold tailWord_1706621
  simp only [CollatzResearch.WordTrace]
  refine ⟨62245581550211059506983717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41497054366807373004655811 62245581550211059506983717)
  ·
    refine ⟨11671046540664573657559447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62245581550211059506983717 11671046540664573657559447)
    ·
      refine ⟨17506569810996860486339171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11671046540664573657559447 17506569810996860486339171)
      ·
        refine ⟨26259854716495290729508757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17506569810996860486339171 26259854716495290729508757)
        ·
          refine ⟨1230930689835716752945723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26259854716495290729508757 1230930689835716752945723)
          ·
            refine ⟨1846396034753575129418585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230930689835716752945723 1846396034753575129418585)
            ·
              refine ⟨1384797026065181347063939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846396034753575129418585 1384797026065181347063939)
              ·
                refine ⟨2077195539097772020595909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384797026065181347063939 2077195539097772020595909)
                ·
                  refine ⟨389474163580832253861733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077195539097772020595909 389474163580832253861733)
                  ·
                    rfl

theorem cell21_1706621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1706621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706621 prefixEnd_1706621 := by exact prefixLift 1706621
  have htrace : WordTrace (prefixWord ++ tailWord_1706621) baseStart_1706621 baseEnd_1706621 := by
    simpa [prefixWord, tailWord_1706621, baseEnd_1706621] using wordTrace_append hprefix tailTrace_1706621
  have hstable : (prefixWord ++ tailWord_1706621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706621).length < 2 ^ (prefixWord ++ tailWord_1706621).sum := by decide
  have hdescent : baseEnd_1706621 < baseStart_1706621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706677 : List Nat := [1, 3, 3, 3, 1, 1, 3, 6]
def baseStart_1706677 : Nat := 118140960795 + 1706677 * 2 ^ 59
def prefixEnd_1706677 : Nat := 4983230072969 + 3 ^ 40 * 1706677 * 2
def baseEnd_1706677 : Nat := 129828981181262866976095

theorem tailTrace_1706677 : CollatzResearch.WordTrace tailWord_1706677 prefixEnd_1706677 129828981181262866976095 := by
  unfold tailWord_1706677
  simp only [CollatzResearch.WordTrace]
  refine ⟨62247624038008181071022285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41498416025338787380681523 62247624038008181071022285)
  ·
    refine ⟨23342859014253067901633357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62247624038008181071022285 23342859014253067901633357)
    ·
      refine ⟨8753572130344900463112509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23342859014253067901633357 8753572130344900463112509)
      ·
        refine ⟨3282589548879337673667191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8753572130344900463112509 3282589548879337673667191)
        ·
          refine ⟨4923884323319006510500787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282589548879337673667191 4923884323319006510500787)
          ·
            refine ⟨7385826484978509765751181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923884323319006510500787 7385826484978509765751181)
            ·
              refine ⟨2769684931866941162156693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7385826484978509765751181 2769684931866941162156693)
              ·
                refine ⟨129828981181262866976095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2769684931866941162156693 129828981181262866976095)
                ·
                  rfl

theorem cell21_1706677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 6].length) (baseStart_1706677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706677 prefixEnd_1706677 := by exact prefixLift 1706677
  have htrace : WordTrace (prefixWord ++ tailWord_1706677) baseStart_1706677 baseEnd_1706677 := by
    simpa [prefixWord, tailWord_1706677, baseEnd_1706677] using wordTrace_append hprefix tailTrace_1706677
  have hstable : (prefixWord ++ tailWord_1706677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706677).length < 2 ^ (prefixWord ++ tailWord_1706677).sum := by decide
  have hdescent : baseEnd_1706677 < baseStart_1706677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706705 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 6]
def baseStart_1706705 : Nat := 118140960795 + 1706705 * 2 ^ 59
def prefixEnd_1706705 : Nat := 4983230072969 + 3 ^ 40 * 1706705 * 2
def baseEnd_1706705 : Nat := 389493333525266774461561

theorem tailTrace_1706705 : CollatzResearch.WordTrace tailWord_1706705 prefixEnd_1706705 389493333525266774461561 := by
  unfold tailWord_1706705
  simp only [CollatzResearch.WordTrace]
  refine ⟨62248645281906741853041569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41499096854604494568694379 62248645281906741853041569)
  ·
    refine ⟨46686483961430056389781177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62248645281906741853041569 46686483961430056389781177)
    ·
      refine ⟨35014862971072542292335883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46686483961430056389781177 35014862971072542292335883)
      ·
        refine ⟨52522294456608813438503825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35014862971072542292335883 52522294456608813438503825)
        ·
          refine ⟨39391720842456610078877869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52522294456608813438503825 39391720842456610078877869)
          ·
            refine ⟨14771895315921228779579201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39391720842456610078877869 14771895315921228779579201)
            ·
              refine ⟨11078921486940921584684401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14771895315921228779579201 11078921486940921584684401)
              ·
                refine ⟨8309191115205691188513301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11078921486940921584684401 8309191115205691188513301)
                ·
                  refine ⟨389493333525266774461561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8309191115205691188513301 389493333525266774461561)
                  ·
                    rfl

theorem cell21_1706705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_1706705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706705 prefixEnd_1706705 := by exact prefixLift 1706705
  have htrace : WordTrace (prefixWord ++ tailWord_1706705) baseStart_1706705 baseEnd_1706705 := by
    simpa [prefixWord, tailWord_1706705, baseEnd_1706705] using wordTrace_append hprefix tailTrace_1706705
  have hstable : (prefixWord ++ tailWord_1706705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706705).length < 2 ^ (prefixWord ++ tailWord_1706705).sum := by decide
  have hdescent : baseEnd_1706705 < baseStart_1706705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706770 : List Nat := [3, 2, 4, 1, 2, 2, 7]
def baseStart_1706770 : Nat := 118140960795 + 1706770 * 2 ^ 59
def prefixEnd_1706770 : Nat := 4983230072969 + 3 ^ 40 * 1706770 * 2
def baseEnd_1706770 : Nat := 43278685267871233986455

theorem tailTrace_1706770 : CollatzResearch.WordTrace tailWord_1706770 prefixEnd_1706770 43278685267871233986455 := by
  unfold tailWord_1706770
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562754006667814488539441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41500677351114171969438509 15562754006667814488539441)
  ·
    refine ⟨11672065505000860866404581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15562754006667814488539441 11672065505000860866404581)
    ·
      refine ⟨2188512282187661412450859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11672065505000860866404581 2188512282187661412450859)
      ·
        refine ⟨3282768423281492118676289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188512282187661412450859 3282768423281492118676289)
        ·
          refine ⟨2462076317461119089007217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3282768423281492118676289 2462076317461119089007217)
          ·
            refine ⟨1846557238095839316755413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462076317461119089007217 1846557238095839316755413)
            ·
              refine ⟨43278685267871233986455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1846557238095839316755413 43278685267871233986455)
              ·
                rfl

theorem cell21_1706770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 7].length) (baseStart_1706770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706770 prefixEnd_1706770 := by exact prefixLift 1706770
  have htrace : WordTrace (prefixWord ++ tailWord_1706770) baseStart_1706770 baseEnd_1706770 := by
    simpa [prefixWord, tailWord_1706770, baseEnd_1706770] using wordTrace_append hprefix tailTrace_1706770
  have hstable : (prefixWord ++ tailWord_1706770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706770).length < 2 ^ (prefixWord ++ tailWord_1706770).sum := by decide
  have hdescent : baseEnd_1706770 < baseStart_1706770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706784 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_1706784 : Nat := 118140960795 + 1706784 * 2 ^ 59
def prefixEnd_1706784 : Nat := 4983230072969 + 3 ^ 40 * 1706784 * 2
def baseEnd_1706784 : Nat := 389511362401580192644733

theorem tailTrace_1706784 : CollatzResearch.WordTrace tailWord_1706784 prefixEnd_1706784 389511362401580192644733 := by
  unfold tailWord_1706784
  simp only [CollatzResearch.WordTrace]
  refine ⟨31125763324310269172583703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41501017765747025563444937 31125763324310269172583703)
  ·
    refine ⟨46688644986465403758875555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31125763324310269172583703 46688644986465403758875555)
    ·
      refine ⟨70032967479698105638313333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46688644986465403758875555 70032967479698105638313333)
      ·
        refine ⟨6565590701221697403591875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70032967479698105638313333 6565590701221697403591875)
        ·
          refine ⟨9848386051832546105387813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6565590701221697403591875 9848386051832546105387813)
          ·
            refine ⟨1846572384718602394760215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9848386051832546105387813 1846572384718602394760215)
            ·
              refine ⟨2769858577077903592140323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846572384718602394760215 2769858577077903592140323)
              ·
                refine ⟨4154787865616855388210485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769858577077903592140323 4154787865616855388210485)
                ·
                  refine ⟨389511362401580192644733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4154787865616855388210485 389511362401580192644733)
                  ·
                    rfl

theorem cell21_1706784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_1706784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706784 prefixEnd_1706784 := by exact prefixLift 1706784
  have htrace : WordTrace (prefixWord ++ tailWord_1706784) baseStart_1706784 baseEnd_1706784 := by
    simpa [prefixWord, tailWord_1706784, baseEnd_1706784] using wordTrace_append hprefix tailTrace_1706784
  have hstable : (prefixWord ++ tailWord_1706784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706784).length < 2 ^ (prefixWord ++ tailWord_1706784).sum := by decide
  have hdescent : baseEnd_1706784 < baseStart_1706784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706795 : List Nat := [1, 1, 1, 1, 2, 1, 2, 12]
def baseStart_1706795 : Nat := 118140960795 + 1706795 * 2 ^ 59
def prefixEnd_1706795 : Nat := 4983230072969 + 3 ^ 40 * 1706795 * 2
def baseEnd_1706795 : Nat := 129837957583815539320459

theorem tailTrace_1706795 : CollatzResearch.WordTrace tailWord_1706795 prefixEnd_1706795 129837957583815539320459 := by
  unfold tailWord_1706795
  simp only [CollatzResearch.WordTrace]
  refine ⟨62251927851580687223817839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41501285234387124815878559 62251927851580687223817839)
  ·
    refine ⟨93377891777371030835726759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62251927851580687223817839 93377891777371030835726759)
    ·
      refine ⟨140066837666056546253590139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93377891777371030835726759 140066837666056546253590139)
      ·
        refine ⟨210100256499084819380385209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140066837666056546253590139 210100256499084819380385209)
        ·
          refine ⟨157575192374313614535288907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210100256499084819380385209 157575192374313614535288907)
          ·
            refine ⟨236362788561470421802933361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157575192374313614535288907 236362788561470421802933361)
            ·
              refine ⟨177272091421102816352200021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236362788561470421802933361 177272091421102816352200021)
              ·
                refine ⟨129837957583815539320459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 177272091421102816352200021 129837957583815539320459)
                ·
                  rfl

theorem cell21_1706795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_1706795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706795 prefixEnd_1706795 := by exact prefixLift 1706795
  have htrace : WordTrace (prefixWord ++ tailWord_1706795) baseStart_1706795 baseEnd_1706795 := by
    simpa [prefixWord, tailWord_1706795, baseEnd_1706795] using wordTrace_append hprefix tailTrace_1706795
  have hstable : (prefixWord ++ tailWord_1706795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706795).length < 2 ^ (prefixWord ++ tailWord_1706795).sum := by decide
  have hdescent : baseEnd_1706795 < baseStart_1706795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706826 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1706826 : Nat := 118140960795 + 1706826 * 2 ^ 59
def prefixEnd_1706826 : Nat := 4983230072969 + 3 ^ 40 * 1706826 * 2
def baseEnd_1706826 : Nat := 389520947373797452944647

theorem tailTrace_1706826 : CollatzResearch.WordTrace tailWord_1706826 prefixEnd_1706826 389520947373797452944647 := by
  unfold tailWord_1706826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15563264628617094879549083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41502039009645586345464221 15563264628617094879549083)
  ·
    refine ⟨23344896942925642319323625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15563264628617094879549083 23344896942925642319323625)
    ·
      refine ⟨17508672707194231739492719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23344896942925642319323625 17508672707194231739492719)
      ·
        refine ⟨26263009060791347609239079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17508672707194231739492719 26263009060791347609239079)
        ·
          refine ⟨39394513591187021413858619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26263009060791347609239079 39394513591187021413858619)
          ·
            refine ⟨59091770386780532120787929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39394513591187021413858619 59091770386780532120787929)
            ·
              refine ⟨44318827790085399090590947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59091770386780532120787929 44318827790085399090590947)
              ·
                refine ⟨66478241685128098635886421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44318827790085399090590947 66478241685128098635886421)
                ·
                  refine ⟨389520947373797452944647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66478241685128098635886421 389520947373797452944647)
                  ·
                    rfl

theorem cell21_1706826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1706826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706826 prefixEnd_1706826 := by exact prefixLift 1706826
  have htrace : WordTrace (prefixWord ++ tailWord_1706826) baseStart_1706826 baseEnd_1706826 := by
    simpa [prefixWord, tailWord_1706826, baseEnd_1706826] using wordTrace_append hprefix tailTrace_1706826
  have hstable : (prefixWord ++ tailWord_1706826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706826).length < 2 ^ (prefixWord ++ tailWord_1706826).sum := by decide
  have hdescent : baseEnd_1706826 < baseStart_1706826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706829 : List Nat := [1, 6, 1, 2, 2, 9]
def baseStart_1706829 : Nat := 118140960795 + 1706829 * 2 ^ 59
def prefixEnd_1706829 : Nat := 4983230072969 + 3 ^ 40 * 1706829 * 2
def baseEnd_1706829 : Nat := 14426727111654448681283

theorem tailTrace_1706829 : CollatzResearch.WordTrace tailWord_1706829 prefixEnd_1706829 14426727111654448681283 := by
  unfold tailWord_1706829
  simp only [CollatzResearch.WordTrace]
  refine ⟨62253167933457511030555541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41502111955638340687037027 62253167933457511030555541)
  ·
    refine ⟨2918117246880820829557291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62253167933457511030555541 2918117246880820829557291)
    ·
      refine ⟨4377175870321231244335937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918117246880820829557291 4377175870321231244335937)
      ·
        refine ⟨3282881902740923433251953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4377175870321231244335937 3282881902740923433251953)
        ·
          refine ⟨2462161427055692574938965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3282881902740923433251953 2462161427055692574938965)
          ·
            refine ⟨14426727111654448681283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2462161427055692574938965 14426727111654448681283)
            ·
              rfl

theorem cell21_1706829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 9].length) (baseStart_1706829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706829 prefixEnd_1706829 := by exact prefixLift 1706829
  have htrace : WordTrace (prefixWord ++ tailWord_1706829) baseStart_1706829 baseEnd_1706829 := by
    simpa [prefixWord, tailWord_1706829, baseEnd_1706829] using wordTrace_append hprefix tailTrace_1706829
  have hstable : (prefixWord ++ tailWord_1706829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706829).length < 2 ^ (prefixWord ++ tailWord_1706829).sum := by decide
  have hdescent : baseEnd_1706829 < baseStart_1706829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706871 : List Nat := [1, 1, 3, 1, 1, 2, 1, 11]
def baseStart_1706871 : Nat := 118140960795 + 1706871 * 2 ^ 59
def prefixEnd_1706871 : Nat := 4983230072969 + 3 ^ 40 * 1706871 * 2
def baseEnd_1706871 : Nat := 129843738995629124898185

theorem tailTrace_1706871 : CollatzResearch.WordTrace tailWord_1706871 prefixEnd_1706871 129843738995629124898185 := by
  unfold tailWord_1706871
  simp only [CollatzResearch.WordTrace]
  refine ⟨62254699799305352203584467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41503133199536901469056311 62254699799305352203584467)
  ·
    refine ⟨93382049698958028305376701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62254699799305352203584467 93382049698958028305376701)
    ·
      refine ⟨35018268637109260614516263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93382049698958028305376701 35018268637109260614516263)
      ·
        refine ⟨52527402955663890921774395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35018268637109260614516263 52527402955663890921774395)
        ·
          refine ⟨78791104433495836382661593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52527402955663890921774395 78791104433495836382661593)
          ·
            refine ⟨59093328325121877286996195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78791104433495836382661593 59093328325121877286996195)
            ·
              refine ⟨88639992487682815930494293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59093328325121877286996195 88639992487682815930494293)
              ·
                refine ⟨129843738995629124898185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 88639992487682815930494293 129843738995629124898185)
                ·
                  rfl

theorem cell21_1706871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_1706871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706871 prefixEnd_1706871 := by exact prefixLift 1706871
  have htrace : WordTrace (prefixWord ++ tailWord_1706871) baseStart_1706871 baseEnd_1706871 := by
    simpa [prefixWord, tailWord_1706871, baseEnd_1706871] using wordTrace_append hprefix tailTrace_1706871
  have hstable : (prefixWord ++ tailWord_1706871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706871).length < 2 ^ (prefixWord ++ tailWord_1706871).sum := by decide
  have hdescent : baseEnd_1706871 < baseStart_1706871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706888 : List Nat := [2, 1, 3, 3, 2, 2, 8]
def baseStart_1706888 : Nat := 118140960795 + 1706888 * 2 ^ 59
def prefixEnd_1706888 : Nat := 4983230072969 + 3 ^ 40 * 1706888 * 2
def baseEnd_1706888 : Nat := 43281677402055458101243

theorem tailTrace_1706888 : CollatzResearch.WordTrace tailWord_1706888 prefixEnd_1706888 43281677402055458101243 := by
  unfold tailWord_1706888
  simp only [CollatzResearch.WordTrace]
  refine ⟨31127659920121882053476659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41503546560162509404635545 31127659920121882053476659)
  ·
    refine ⟨46691489880182823080214989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31127659920121882053476659 46691489880182823080214989)
    ·
      refine ⟨17509308705068558655080621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46691489880182823080214989 17509308705068558655080621)
      ·
        refine ⟨6565990764400709495655233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17509308705068558655080621 6565990764400709495655233)
        ·
          refine ⟨4924493073300532121741425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6565990764400709495655233 4924493073300532121741425)
          ·
            refine ⟨3693369804975399091306069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924493073300532121741425 3693369804975399091306069)
            ·
              refine ⟨43281677402055458101243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3693369804975399091306069 43281677402055458101243)
              ·
                rfl

theorem cell21_1706888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 8].length) (baseStart_1706888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706888 prefixEnd_1706888 := by exact prefixLift 1706888
  have htrace : WordTrace (prefixWord ++ tailWord_1706888) baseStart_1706888 baseEnd_1706888 := by
    simpa [prefixWord, tailWord_1706888, baseEnd_1706888] using wordTrace_append hprefix tailTrace_1706888
  have hstable : (prefixWord ++ tailWord_1706888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706888).length < 2 ^ (prefixWord ++ tailWord_1706888).sum := by decide
  have hdescent : baseEnd_1706888 < baseStart_1706888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706908 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_1706908 : Nat := 118140960795 + 1706908 * 2 ^ 59
def prefixEnd_1706908 : Nat := 4983230072969 + 3 ^ 40 * 1706908 * 2
def baseEnd_1706908 : Nat := 389539660890983532577813

theorem tailTrace_1706908 : CollatzResearch.WordTrace tailWord_1706908 prefixEnd_1706908 389539660890983532577813 := by
  unfold tailWord_1706908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128024650085653761340689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41504032866780871681787585 31128024650085653761340689)
  ·
    refine ⟨23346018487564240321005517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31128024650085653761340689 23346018487564240321005517)
    ·
      refine ⟨8754756932836590120377069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23346018487564240321005517 8754756932836590120377069)
      ·
        refine ⟨3283033849813721295141401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8754756932836590120377069 3283033849813721295141401)
        ·
          refine ⟨2462275387360290971356051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3283033849813721295141401 2462275387360290971356051)
          ·
            refine ⟨3693413081040436457034077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462275387360290971356051 3693413081040436457034077)
            ·
              refine ⟨1385029905390163671387779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3693413081040436457034077 1385029905390163671387779)
              ·
                refine ⟨2077544858085245507081669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385029905390163671387779 2077544858085245507081669)
                ·
                  refine ⟨389539660890983532577813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077544858085245507081669 389539660890983532577813)
                  ·
                    rfl

theorem cell21_1706908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_1706908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706908 prefixEnd_1706908 := by exact prefixLift 1706908
  have htrace : WordTrace (prefixWord ++ tailWord_1706908) baseStart_1706908 baseEnd_1706908 := by
    simpa [prefixWord, tailWord_1706908, baseEnd_1706908] using wordTrace_append hprefix tailTrace_1706908
  have hstable : (prefixWord ++ tailWord_1706908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706908).length < 2 ^ (prefixWord ++ tailWord_1706908).sum := by decide
  have hdescent : baseEnd_1706908 < baseStart_1706908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706933 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1706933 : Nat := 118140960795 + 1706933 * 2 ^ 59
def prefixEnd_1706933 : Nat := 4983230072969 + 3 ^ 40 * 1706933 * 2
def baseEnd_1706933 : Nat := 389545366231589044661095

theorem tailTrace_1706933 : CollatzResearch.WordTrace tailWord_1706933 prefixEnd_1706933 389545366231589044661095 := by
  unfold tailWord_1706933
  simp only [CollatzResearch.WordTrace]
  refine ⟨62256961125080736792341453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41504640750053824528227635 62256961125080736792341453)
  ·
    refine ⟨23346360421905276297128045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62256961125080736792341453 23346360421905276297128045)
    ·
      refine ⟨8754885158214478611423017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23346360421905276297128045 8754885158214478611423017)
      ·
        refine ⟨6566163868660858958567263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8754885158214478611423017 6566163868660858958567263)
        ·
          refine ⟨9849245802991288437850895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6566163868660858958567263 9849245802991288437850895)
          ·
            refine ⟨14773868704486932656776343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9849245802991288437850895 14773868704486932656776343)
            ·
              refine ⟨22160803056730398985164515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14773868704486932656776343 22160803056730398985164515)
              ·
                refine ⟨33241204585095598477746773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22160803056730398985164515 33241204585095598477746773)
                ·
                  refine ⟨389545366231589044661095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33241204585095598477746773 389545366231589044661095)
                  ·
                    rfl

theorem cell21_1706933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1706933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706933 prefixEnd_1706933 := by exact prefixLift 1706933
  have htrace : WordTrace (prefixWord ++ tailWord_1706933) baseStart_1706933 baseEnd_1706933 := by
    simpa [prefixWord, tailWord_1706933, baseEnd_1706933] using wordTrace_append hprefix tailTrace_1706933
  have hstable : (prefixWord ++ tailWord_1706933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706933).length < 2 ^ (prefixWord ++ tailWord_1706933).sum := by decide
  have hdescent : baseEnd_1706933 < baseStart_1706933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706936 : List Nat := [2, 1, 2, 1, 2, 4, 3, 3, 3]
def baseStart_1706936 : Nat := 118140960795 + 1706936 * 2 ^ 59
def prefixEnd_1706936 : Nat := 4983230072969 + 3 ^ 40 * 1706936 * 2
def baseEnd_1706936 : Nat := 389546050872461706111089

theorem tailTrace_1706936 : CollatzResearch.WordTrace tailWord_1706936 prefixEnd_1706936 389546050872461706111089 := by
  unfold tailWord_1706936
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128535272034934152350331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41504713696046578869800441 31128535272034934152350331)
  ·
    refine ⟨46692802908052401228525497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31128535272034934152350331 46692802908052401228525497)
    ·
      refine ⟨35019602181039300921394123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46692802908052401228525497 35019602181039300921394123)
      ·
        refine ⟨52529403271558951382091185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35019602181039300921394123 52529403271558951382091185)
        ·
          refine ⟨39397052453669213536568389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52529403271558951382091185 39397052453669213536568389)
          ·
            refine ⟨7386947335062977538106573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39397052453669213536568389 7386947335062977538106573)
            ·
              refine ⟨2770105250648616576789965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7386947335062977538106573 2770105250648616576789965)
              ·
                refine ⟨1038789468993231216296237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2770105250648616576789965 1038789468993231216296237)
                ·
                  refine ⟨389546050872461706111089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038789468993231216296237 389546050872461706111089)
                  ·
                    rfl

theorem cell21_1706936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_1706936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706936 prefixEnd_1706936 := by exact prefixLift 1706936
  have htrace : WordTrace (prefixWord ++ tailWord_1706936) baseStart_1706936 baseEnd_1706936 := by
    simpa [prefixWord, tailWord_1706936, baseEnd_1706936] using wordTrace_append hprefix tailTrace_1706936
  have hstable : (prefixWord ++ tailWord_1706936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706936).length < 2 ^ (prefixWord ++ tailWord_1706936).sum := by decide
  have hdescent : baseEnd_1706936 < baseStart_1706936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706964 : List Nat := [2, 4, 1, 2, 1, 2, 1, 8]
def baseStart_1706964 : Nat := 118140960795 + 1706964 * 2 ^ 59
def prefixEnd_1706964 : Nat := 4983230072969 + 3 ^ 40 * 1706964 * 2
def baseEnd_1706964 : Nat := 129850813617979959881455

theorem tailTrace_1706964 : CollatzResearch.WordTrace tailWord_1706964 prefixEnd_1706964 129850813617979959881455 := by
  unfold tailWord_1706964
  simp only [CollatzResearch.WordTrace]
  refine ⟨31129045893984214543359973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41505394525312286057813297 31129045893984214543359973)
  ·
    refine ⟨5836696105122040226879995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31129045893984214543359973 5836696105122040226879995)
    ·
      refine ⟨8755044157683060340319993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836696105122040226879995 8755044157683060340319993)
      ·
        refine ⟨6566283118262295255239995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8755044157683060340319993 6566283118262295255239995)
        ·
          refine ⟨9849424677393442882859993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6566283118262295255239995 9849424677393442882859993)
          ·
            refine ⟨7387068508045082162144995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9849424677393442882859993 7387068508045082162144995)
            ·
              refine ⟨11080602762067623243217493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387068508045082162144995 11080602762067623243217493)
              ·
                refine ⟨129850813617979959881455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11080602762067623243217493 129850813617979959881455)
                ·
                  rfl

theorem cell21_1706964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_1706964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1706964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1706964 prefixEnd_1706964 := by exact prefixLift 1706964
  have htrace : WordTrace (prefixWord ++ tailWord_1706964) baseStart_1706964 baseEnd_1706964 := by
    simpa [prefixWord, tailWord_1706964, baseEnd_1706964] using wordTrace_append hprefix tailTrace_1706964
  have hstable : (prefixWord ++ tailWord_1706964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706964).length < 2 ^ (prefixWord ++ tailWord_1706964).sum := by decide
  have hdescent : baseEnd_1706964 < baseStart_1706964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707060 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1707060 : Nat := 118140960795 + 1707060 * 2 ^ 59
def prefixEnd_1707060 : Nat := 4983230072969 + 3 ^ 40 * 1707060 * 2
def baseEnd_1707060 : Nat := 389574349361865046044169

theorem tailTrace_1707060 : CollatzResearch.WordTrace tailWord_1707060 prefixEnd_1707060 389574349361865046044169 := by
  unfold tailWord_1707060
  simp only [CollatzResearch.WordTrace]
  refine ⟨31130796597810318741107317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41507728797080424988143089 31130796597810318741107317)
  ·
    refine ⟨2918512181044717381978811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31130796597810318741107317 2918512181044717381978811)
    ·
      refine ⟨4377768271567076072968217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918512181044717381978811 4377768271567076072968217)
      ·
        refine ⟨3283326203675307054726163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4377768271567076072968217 3283326203675307054726163)
        ·
          refine ⟨4924989305512960582089245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283326203675307054726163 4924989305512960582089245)
          ·
            refine ⟨1846870989567360218283467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4924989305512960582089245 1846870989567360218283467)
            ·
              refine ⟨2770306484351040327425201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846870989567360218283467 2770306484351040327425201)
              ·
                refine ⟨2077729863263280245568901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770306484351040327425201 2077729863263280245568901)
                ·
                  refine ⟨389574349361865046044169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077729863263280245568901 389574349361865046044169)
                  ·
                    rfl

theorem cell21_1707060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1707060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707060 prefixEnd_1707060 := by exact prefixLift 1707060
  have htrace : WordTrace (prefixWord ++ tailWord_1707060) baseStart_1707060 baseEnd_1707060 := by
    simpa [prefixWord, tailWord_1707060, baseEnd_1707060] using wordTrace_append hprefix tailTrace_1707060
  have hstable : (prefixWord ++ tailWord_1707060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707060).length < 2 ^ (prefixWord ++ tailWord_1707060).sum := by decide
  have hdescent : baseEnd_1707060 < baseStart_1707060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707181 : List Nat := [1, 5, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1707181 : Nat := 118140960795 + 1707181 * 2 ^ 59
def prefixEnd_1707181 : Nat := 4983230072969 + 3 ^ 40 * 1707181 * 2
def baseEnd_1707181 : Nat := 389601963210395724527255

theorem tailTrace_1707181 : CollatzResearch.WordTrace tailWord_1707181 prefixEnd_1707181 389601963210395724527255 := by
  unfold tailWord_1707181
  simp only [CollatzResearch.WordTrace]
  refine ⟨62266006428182275147369397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41510670952121516764912931 62266006428182275147369397)
  ·
    refine ⟨5837438102642088295065881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62266006428182275147369397 5837438102642088295065881)
    ·
      refine ⟨4378078576981566221299411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5837438102642088295065881 4378078576981566221299411)
      ·
        refine ⟨6567117865472349331949117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4378078576981566221299411 6567117865472349331949117)
        ·
          refine ⟨2462669199552130999480919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6567117865472349331949117 2462669199552130999480919)
          ·
            refine ⟨3694003799328196499221379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462669199552130999480919 3694003799328196499221379)
            ·
              refine ⟨5541005698992294748832069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694003799328196499221379 5541005698992294748832069)
              ·
                refine ⟨1038938568561055265406013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5541005698992294748832069 1038938568561055265406013)
                ·
                  refine ⟨389601963210395724527255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038938568561055265406013 389601963210395724527255)
                  ·
                    rfl

theorem cell21_1707181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1707181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707181 prefixEnd_1707181 := by exact prefixLift 1707181
  have htrace : WordTrace (prefixWord ++ tailWord_1707181) baseStart_1707181 baseEnd_1707181 := by
    simpa [prefixWord, tailWord_1707181, baseEnd_1707181] using wordTrace_append hprefix tailTrace_1707181
  have hstable : (prefixWord ++ tailWord_1707181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707181).length < 2 ^ (prefixWord ++ tailWord_1707181).sum := by decide
  have hdescent : baseEnd_1707181 < baseStart_1707181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707223 : List Nat := [1, 1, 3, 2, 1, 2, 3, 5, 3]
def baseStart_1707223 : Nat := 118140960795 + 1707223 * 2 ^ 59
def prefixEnd_1707223 : Nat := 4983230072969 + 3 ^ 40 * 1707223 * 2
def baseEnd_1707223 : Nat := 389611548182612984827169

theorem tailTrace_1707223 : CollatzResearch.WordTrace tailWord_1707223 prefixEnd_1707223 389611548182612984827169 := by
  unfold tailWord_1707223
  simp only [CollatzResearch.WordTrace]
  refine ⟨62267538294030116320398323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41511692196020077546932215 62267538294030116320398323)
  ·
    refine ⟨93401307441045174480597485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62267538294030116320398323 93401307441045174480597485)
    ·
      refine ⟨35025490290391940430224057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93401307441045174480597485 35025490290391940430224057)
      ·
        refine ⟨26269117717793955322668043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35025490290391940430224057 26269117717793955322668043)
        ·
          refine ⟨39403676576690932984002065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26269117717793955322668043 39403676576690932984002065)
          ·
            refine ⟨29552757432518199738001549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39403676576690932984002065 29552757432518199738001549)
            ·
              refine ⟨11082284037194324901750581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29552757432518199738001549 11082284037194324901750581)
              ·
                refine ⟨1038964128486967959539117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11082284037194324901750581 1038964128486967959539117)
                ·
                  refine ⟨389611548182612984827169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038964128486967959539117 389611548182612984827169)
                  ·
                    rfl

theorem cell21_1707223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 3].length) (baseStart_1707223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707223 prefixEnd_1707223 := by exact prefixLift 1707223
  have htrace : WordTrace (prefixWord ++ tailWord_1707223) baseStart_1707223 baseEnd_1707223 := by
    simpa [prefixWord, tailWord_1707223, baseEnd_1707223] using wordTrace_append hprefix tailTrace_1707223
  have hstable : (prefixWord ++ tailWord_1707223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707223).length < 2 ^ (prefixWord ++ tailWord_1707223).sum := by decide
  have hdescent : baseEnd_1707223 < baseStart_1707223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707268 : List Nat := [2, 3, 2, 2, 2, 2, 1, 7]
def baseStart_1707268 : Nat := 118140960795 + 1707268 * 2 ^ 59
def prefixEnd_1707268 : Nat := 4983230072969 + 3 ^ 40 * 1707268 * 2
def baseEnd_1707268 : Nat := 129873939265234302192359

theorem tailTrace_1707268 : CollatzResearch.WordTrace tailWord_1707268 prefixEnd_1707268 129873939265234302192359 := by
  unfold tailWord_1707268
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134589789433544502893229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41512786385911392670524305 31134589789433544502893229)
  ·
    refine ⟨11675471171037579188584961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31134589789433544502893229 11675471171037579188584961)
    ·
      refine ⟨8756603378278184391438721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11675471171037579188584961 8756603378278184391438721)
      ·
        refine ⟨6567452533708638293579041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8756603378278184391438721 6567452533708638293579041)
        ·
          refine ⟨4925589400281478720184281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6567452533708638293579041 4925589400281478720184281)
          ·
            refine ⟨3694192050211109040138211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4925589400281478720184281 3694192050211109040138211)
            ·
              refine ⟨5541288075316663560207317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694192050211109040138211 5541288075316663560207317)
              ·
                refine ⟨129873939265234302192359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5541288075316663560207317 129873939265234302192359)
                ·
                  rfl

theorem cell21_1707268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_1707268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707268 prefixEnd_1707268 := by exact prefixLift 1707268
  have htrace : WordTrace (prefixWord ++ tailWord_1707268) baseStart_1707268 baseEnd_1707268 := by
    simpa [prefixWord, tailWord_1707268, baseEnd_1707268] using wordTrace_append hprefix tailTrace_1707268
  have hstable : (prefixWord ++ tailWord_1707268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707268).length < 2 ^ (prefixWord ++ tailWord_1707268).sum := by decide
  have hdescent : baseEnd_1707268 < baseStart_1707268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707299 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 5]
def baseStart_1707299 : Nat := 118140960795 + 1707299 * 2 ^ 59
def prefixEnd_1707299 : Nat := 4983230072969 + 3 ^ 40 * 1707299 * 2
def baseEnd_1707299 : Nat := 389628892418053741560347

theorem tailTrace_1707299 : CollatzResearch.WordTrace tailWord_1707299 prefixEnd_1707299 389628892418053741560347 := by
  unfold tailWord_1707299
  simp only [CollatzResearch.WordTrace]
  refine ⟨62270310241754781300164951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41513540161169854200109967 62270310241754781300164951)
  ·
    refine ⟨93405465362632171950247427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62270310241754781300164951 93405465362632171950247427)
    ·
      refine ⟨140108198043948257925371141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93405465362632171950247427 140108198043948257925371141)
      ·
        refine ⟨26270287133240298361007089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140108198043948257925371141 26270287133240298361007089)
        ·
          refine ⟨19702715349930223770755317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26270287133240298361007089 19702715349930223770755317)
          ·
            refine ⟨1847129564055958478508311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19702715349930223770755317 1847129564055958478508311)
            ·
              refine ⟨2770694346083937717762467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847129564055958478508311 2770694346083937717762467)
              ·
                refine ⟨4156041519125906576643701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770694346083937717762467 4156041519125906576643701)
                ·
                  refine ⟨389628892418053741560347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4156041519125906576643701 389628892418053741560347)
                  ·
                    rfl

theorem cell21_1707299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5].length) (baseStart_1707299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707299 prefixEnd_1707299 := by exact prefixLift 1707299
  have htrace : WordTrace (prefixWord ++ tailWord_1707299) baseStart_1707299 baseEnd_1707299 := by
    simpa [prefixWord, tailWord_1707299, baseEnd_1707299] using wordTrace_append hprefix tailTrace_1707299
  have hstable : (prefixWord ++ tailWord_1707299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707299).length < 2 ^ (prefixWord ++ tailWord_1707299).sum := by decide
  have hdescent : baseEnd_1707299 < baseStart_1707299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707327 : List Nat := [1, 1, 2, 2, 4, 2, 2, 7]
def baseStart_1707327 : Nat := 118140960795 + 1707327 * 2 ^ 59
def prefixEnd_1707327 : Nat := 4983230072969 + 3 ^ 40 * 1707327 * 2
def baseEnd_1707327 : Nat := 129878427466510638364541

theorem tailTrace_1707327 : CollatzResearch.WordTrace tailWord_1707327 prefixEnd_1707327 129878427466510638364541 := by
  unfold tailWord_1707327
  simp only [CollatzResearch.WordTrace]
  refine ⟨62271331485653342082184235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41514220990435561388122823 62271331485653342082184235)
  ·
    refine ⟨93406997228480013123276353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62271331485653342082184235 93406997228480013123276353)
    ·
      refine ⟨70055247921360009842457265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93406997228480013123276353 70055247921360009842457265)
      ·
        refine ⟨52541435941020007381842949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70055247921360009842457265 52541435941020007381842949)
        ·
          refine ⟨9851519238941251384095553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52541435941020007381842949 9851519238941251384095553)
          ·
            refine ⟨7388639429205938538071665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9851519238941251384095553 7388639429205938538071665)
            ·
              refine ⟨5541479571904453903553749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7388639429205938538071665 5541479571904453903553749)
              ·
                refine ⟨129878427466510638364541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5541479571904453903553749 129878427466510638364541)
                ·
                  rfl

theorem cell21_1707327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_1707327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707327 prefixEnd_1707327 := by exact prefixLift 1707327
  have htrace : WordTrace (prefixWord ++ tailWord_1707327) baseStart_1707327 baseEnd_1707327 := by
    simpa [prefixWord, tailWord_1707327, baseEnd_1707327] using wordTrace_append hprefix tailTrace_1707327
  have hstable : (prefixWord ++ tailWord_1707327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707327).length < 2 ^ (prefixWord ++ tailWord_1707327).sum := by decide
  have hdescent : baseEnd_1707327 < baseStart_1707327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707406 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1707406 : Nat := 118140960795 + 1707406 * 2 ^ 59
def prefixEnd_1707406 : Nat := 4983230072969 + 3 ^ 40 * 1707406 * 2
def baseEnd_1707406 : Nat := 389653311275845333276795

theorem tailTrace_1707406 : CollatzResearch.WordTrace tailWord_1707406 prefixEnd_1707406 389653311275845333276795 := by
  unfold tailWord_1707406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784276606545892321788759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41516141901578092382873381 7784276606545892321788759)
  ·
    refine ⟨11676414909818838482683139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7784276606545892321788759 11676414909818838482683139)
    ·
      refine ⟨17514622364728257724024709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11676414909818838482683139 17514622364728257724024709)
      ·
        refine ⟨3283991693386548323254633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17514622364728257724024709 3283991693386548323254633)
        ·
          refine ⟨2462993770039911242440975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3283991693386548323254633 2462993770039911242440975)
          ·
            refine ⟨3694490655059866863661463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462993770039911242440975 3694490655059866863661463)
            ·
              refine ⟨5541735982589800295492195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694490655059866863661463 5541735982589800295492195)
              ·
                refine ⟨8312603973884700443238293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541735982589800295492195 8312603973884700443238293)
                ·
                  refine ⟨389653311275845333276795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8312603973884700443238293 389653311275845333276795)
                  ·
                    rfl

theorem cell21_1707406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1707406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1707406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1707406 prefixEnd_1707406 := by exact prefixLift 1707406
  have htrace : WordTrace (prefixWord ++ tailWord_1707406) baseStart_1707406 baseEnd_1707406 := by
    simpa [prefixWord, tailWord_1707406, baseEnd_1707406] using wordTrace_append hprefix tailTrace_1707406
  have hstable : (prefixWord ++ tailWord_1707406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707406).length < 2 ^ (prefixWord ++ tailWord_1707406).sum := by decide
  have hdescent : baseEnd_1707406 < baseStart_1707406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
